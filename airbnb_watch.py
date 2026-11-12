#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
Airbnb-Storno-Waechter
======================
Sucht regelmaessig bei Airbnb nach Gaeste-Favoriten, die fuer den Zeitraum,
die Gruppengroesse und das Budget buchbar und mit dem Auto in der maximalen
Fahrzeit erreichbar sind, und meldet jede Unterkunft, die NEU oder WIEDER
frei wird (z. B. weil jemand storniert hat).

Start:            python airbnb_watch.py
Nur ein Durchlauf: python airbnb_watch.py --einmal
Push testen:      python airbnb_watch.py --test-push
Uebersicht:       python airbnb_watch.py --zeigen   (oeffnet die Kachel-Seite im Browser)
Kostenlos hosten: python airbnb_watch.py --cloud-dateien   (legt die Dateien fuer GitHub an;
                  dort laeuft der Waechter dann alle 15 Minuten von selbst und die Seite ist
                  fuer alle mit dem Link erreichbar)

Braucht nur Python 3.9+, keine Zusatzpakete.
"""

import argparse
import base64
import csv
import json
import math
import os
import random
import re
import secrets
import sys
import time
import urllib.error
import urllib.parse
import urllib.request
import webbrowser
from datetime import datetime, timedelta
from pathlib import Path

# ----------------------------------------------------------------------------
# EINSTELLUNGEN
# ----------------------------------------------------------------------------
ZENTRUM_NAME = "Reutlingen"
ZENTRUM_LAT = 48.4914
ZENTRUM_LNG = 9.2043
MAX_FAHRZEIT_STD = 6.0          # Autofahrt ab Reutlingen, ohne Stau und Pausen
RADIUS_KM = 510                 # grober Vorfilter per Luftlinie, wird aus der Fahrzeit berechnet

CHECKIN = "2026-12-29"
CHECKOUT = "2027-01-02"
GAESTE = 8

NUR_GAESTE_FAVORIT = True
NUR_GANZE_UNTERKUNFT = True     # keine Einzelzimmer / Hotelzimmer
MIN_SCHLAFZIMMER = 0            # 0 = egal
MAX_GESAMTPREIS = 1400          # Euro fuer alle zusammen: Voreinstellung auf der Seite und Grenze fuer Pushes
SAMMEL_MAX_PREIS = 2000         # bis zu diesem Gesamtpreis wird gesammelt; auf der Seite filtert jeder selbst

INTERVALL_MIN = 15              # Pause zwischen zwei Durchlaeufen
PUSH_AKTIV = True               # Push aufs Handy ueber die ntfy-App
MAX_PUSH_PRO_LAUF = 10          # darueber gibt es eine Sammelmeldung

# ----------------------------------------------------------------------------
# Ab hier muss nichts angepasst werden
# ----------------------------------------------------------------------------
ORDNER = Path(__file__).resolve().parent
STATE_DATEI = ORDNER / "airbnb_watch_state.json"
CSV_DATEI = ORDNER / "airbnb_aktuell_frei.csv"
HTML_DATEI = ORDNER / "airbnb_uebersicht.html"
DATEN_DATEI = ORDNER / "airbnb_daten.js"
EINSTELL_DATEI = ORDNER / "einstellungen.json"
LOG_DATEI = ORDNER / "airbnb_treffer.log"

BASIS_URL = "https://www.airbnb.de/s/homes"
ROUTING_URL = "https://router.project-osrm.org/table/v1/driving/"
ROUTING_PAKET = 80              # Ziele pro Routing-Anfrage
MAX_ORTE_PRO_LAUF = 400         # so viele Orte werden pro Durchlauf hoechstens nachgeschlagen
NAECHTE = 0
PROFIL = ""
KANAL = ""                      # ntfy-Thema, ueber das die Seite Aenderungen an der Suche schickt
MAX_SEITEN = 15                 # Airbnb zeigt pro Suche hoechstens 15 Seiten
MIN_KACHEL_GRAD = 0.05
FEHLT_SCHWELLE = 2              # so oft muss ein Inserat fehlen, bevor "wieder frei" gilt
USER_AGENT = (
    "Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 "
    "(KHTML, like Gecko) Chrome/130.0.0.0 Safari/537.36"
)
STATE_RE = re.compile(
    r'<script id="data-deferred-state-0"[^>]*>(.*?)</script>', re.DOTALL
)


class AbrufFehler(Exception):
    pass


def profil_berechnen():
    """Leitet Naechte, Suchradius und Suchprofil aus den aktuellen Einstellungen ab."""
    global NAECHTE, PROFIL, RADIUS_KM
    NAECHTE = (datetime.strptime(CHECKOUT, "%Y-%m-%d") - datetime.strptime(CHECKIN, "%Y-%m-%d")).days
    RADIUS_KM = round(MAX_FAHRZEIT_STD * 85)    # weiter kommt man per Luftlinie in der Zeit nicht
    PROFIL = "|".join(str(x) for x in (
        ZENTRUM_LAT, ZENTRUM_LNG, MAX_FAHRZEIT_STD, RADIUS_KM, CHECKIN, CHECKOUT, GAESTE,
        NUR_GAESTE_FAVORIT, NUR_GANZE_UNTERKUNFT, MIN_SCHLAFZIMMER, SAMMEL_MAX_PREIS))


profil_berechnen()


def suche_pruefen(d):
    """Prueft eine von der Seite geschickte Suche. Gibt die bereinigten Werte oder None zurueck."""
    try:
        ein, aus, gaeste = str(d["checkin"]), str(d["checkout"]), int(d["gaeste"])
        if not (re.fullmatch(r"\d{4}-\d{2}-\d{2}", ein) and re.fullmatch(r"\d{4}-\d{2}-\d{2}", aus)):
            return None
        t1, t2 = datetime.strptime(ein, "%Y-%m-%d"), datetime.strptime(aus, "%Y-%m-%d")
        heute = datetime.now()
        if not (1 <= (t2 - t1).days <= 21 and t1 >= heute - timedelta(days=1)
                and t2 <= heute + timedelta(days=730) and 1 <= gaeste <= 16):
            return None
        sauber = {"checkin": ein, "checkout": aus, "gaeste": gaeste}
        if d.get("fahrzeit") is not None:
            fahrzeit = float(d["fahrzeit"])
            if not 2 <= fahrzeit <= 8:
                return None
            sauber["fahrzeit"] = round(fahrzeit * 2) / 2
        if d.get("preis") is not None:
            preis = int(d["preis"])
            if not 500 <= preis <= 5000:
                return None
            sauber["preis"] = preis
        return sauber
    except Exception:
        return None


def einstellungen_laden():
    """Liest einstellungen.json und holt neue Aenderungen ab, die jemand auf der Seite gespeichert hat."""
    global CHECKIN, CHECKOUT, GAESTE, KANAL, MAX_FAHRZEIT_STD, SAMMEL_MAX_PREIS
    if not EINSTELL_DATEI.exists():
        return
    try:
        e = json.loads(EINSTELL_DATEI.read_text(encoding="utf-8"))
    except ValueError:
        return
    KANAL = str(e.get("kanal") or "")
    if KANAL and re.fullmatch(r"[A-Za-z0-9_-]{8,64}", KANAL):
        try:
            neueste = None
            for zeile in http_get(f"https://ntfy.sh/{KANAL}/json?poll=1&since=12h").splitlines():
                try:
                    m = json.loads(zeile)
                    if m.get("event") != "message" or m.get("time", 0) <= e.get("geaendert", 0):
                        continue
                    suche = suche_pruefen(json.loads(m.get("message") or ""))
                except Exception:
                    continue
                if suche and (neueste is None or m["time"] > neueste[0]):
                    neueste = (m["time"], suche)
            if neueste:
                e.update(neueste[1], geaendert=neueste[0])
                with open(EINSTELL_DATEI, "w", encoding="utf-8", newline="\n") as f:
                    f.write(json.dumps(e, indent=1) + "\n")
                log(f"Suche wurde auf der Seite geaendert: {neueste[1]}")
        except Exception as fehler:
            log(f"Aenderungen von der Seite nicht abrufbar ({type(fehler).__name__})")
    else:
        KANAL = ""
    suche = suche_pruefen(e) if "checkin" in e else None
    if suche:
        CHECKIN, CHECKOUT, GAESTE = suche["checkin"], suche["checkout"], suche["gaeste"]
        MAX_FAHRZEIT_STD = suche.get("fahrzeit", MAX_FAHRZEIT_STD)
        SAMMEL_MAX_PREIS = suche.get("preis", SAMMEL_MAX_PREIS)
    profil_berechnen()


def jetzt():
    return datetime.now().strftime("%d.%m. %H:%M:%S")


def log(text):
    print(f"[{jetzt()}] {text}", flush=True)


# ------------------------------- Geometrie ---------------------------------
def distanz_km(lat1, lng1, lat2, lng2):
    r = 6371.0
    p1, p2 = math.radians(lat1), math.radians(lat2)
    dp = p2 - p1
    dl = math.radians(lng2 - lng1)
    a = math.sin(dp / 2) ** 2 + math.cos(p1) * math.cos(p2) * math.sin(dl / 2) ** 2
    return 2 * r * math.asin(math.sqrt(a))


def start_kachel():
    dlat = RADIUS_KM / 111.19
    dlng = RADIUS_KM / (111.19 * math.cos(math.radians(ZENTRUM_LAT)))
    # (sued, west, nord, ost)
    return (ZENTRUM_LAT - dlat, ZENTRUM_LNG - dlng, ZENTRUM_LAT + dlat, ZENTRUM_LNG + dlng)


def kachel_im_umkreis(k):
    s, w, n, o = k
    lat = min(max(ZENTRUM_LAT, s), n)
    lng = min(max(ZENTRUM_LNG, w), o)
    return distanz_km(ZENTRUM_LAT, ZENTRUM_LNG, lat, lng) <= RADIUS_KM


def kachel_teilen(k):
    s, w, n, o = k
    ml, mg = (s + n) / 2, (w + o) / 2
    return [(s, w, ml, mg), (s, mg, ml, o), (ml, w, n, mg), (ml, mg, n, o)]


# ------------------------------- Abruf -------------------------------------
def such_url(k, cursor=None):
    s, w, n, o = k
    p = [
        ("checkin", CHECKIN),
        ("checkout", CHECKOUT),
        ("adults", str(GAESTE)),
        ("sw_lat", f"{s:.5f}"),
        ("sw_lng", f"{w:.5f}"),
        ("ne_lat", f"{n:.5f}"),
        ("ne_lng", f"{o:.5f}"),
        ("zoom_level", "8"),
        ("search_by_map", "true"),
        ("search_type", "user_map_move"),
    ]
    if NUR_GAESTE_FAVORIT:
        p.append(("guest_favorite", "true"))
    if NUR_GANZE_UNTERKUNFT:
        p.append(("room_types[]", "Entire home/apt"))
    if MIN_SCHLAFZIMMER:
        p.append(("min_bedrooms", str(MIN_SCHLAFZIMMER)))
    if SAMMEL_MAX_PREIS:
        # input_type 2 = Gesamtpreis fuer den ganzen Aufenthalt
        p.append(("price_max", str(SAMMEL_MAX_PREIS)))
        p.append(("price_filter_input_type", "2"))
        p.append(("price_filter_num_nights", str(NAECHTE)))
    if cursor:
        p.append(("cursor", cursor))
    return BASIS_URL + "?" + urllib.parse.urlencode(p)


def http_get(url, absender=None):
    req = urllib.request.Request(
        url,
        headers={
            "User-Agent": absender or USER_AGENT,
            "Accept": "text/html,application/xhtml+xml,application/xml;q=0.9,*/*;q=0.8",
            "Accept-Language": "de-DE,de;q=0.9",
        },
    )
    with urllib.request.urlopen(req, timeout=40) as resp:
        return resp.read().decode("utf-8", errors="replace")


def seite_laden(url):
    """Laedt eine Suchseite und gibt (Treffer, Cursor-Liste) zurueck."""
    letzter = None
    for versuch in range(3):
        if versuch:
            time.sleep(30 * versuch + random.uniform(0, 10))
        try:
            html = http_get(url)
        except urllib.error.HTTPError as e:
            letzter = f"HTTP {e.code}"
            continue
        except Exception as e:  # Netzwerk weg, Timeout usw.
            letzter = f"{type(e).__name__}: {e}"
            continue
        m = STATE_RE.search(html)
        if not m:
            letzter = "Seite ohne Suchdaten (Airbnb blockt evtl. gerade)"
            continue
        try:
            daten = json.loads(m.group(1))
        except ValueError:
            letzter = "Suchdaten nicht lesbar"
            continue
        suche = finde_stays_search(daten)
        if suche is None:
            letzter = "Suchdaten haben ein unbekanntes Format"
            continue
        ergebnisse = suche.get("results") or {}
        treffer = [t for t in map(treffer_lesen, ergebnisse.get("searchResults") or []) if t]
        cursors = (ergebnisse.get("paginationInfo") or {}).get("pageCursors") or []
        return treffer, cursors
    raise AbrufFehler(letzter or "unbekannter Fehler")


def finde_stays_search(o, tiefe=0):
    if tiefe > 14 or not isinstance(o, (dict, list)):
        return None
    if isinstance(o, dict):
        s = o.get("staysSearch")
        if isinstance(s, dict) and isinstance(s.get("results"), dict):
            return s
        werte = o.values()
    else:
        werte = o
    for v in werte:
        r = finde_stays_search(v, tiefe + 1)
        if r is not None:
            return r
    return None


def preis_als_zahl(text):
    m = re.search(r"\d[\d.\s  ]*", text or "")
    if not m:
        return None
    ziffern = re.sub(r"\D", "", m.group(0))
    return int(ziffern) if ziffern else None


def treffer_lesen(t):
    try:
        dsl = t.get("demandStayListing") or {}
        roh_id = dsl.get("id") or ""
        try:
            lid = base64.b64decode(roh_id + "=" * (-len(roh_id) % 4)).decode().split(":")[-1]
        except Exception:
            lid = str(t.get("propertyId") or "")
        if not lid.isdigit():
            return None
        koord = (dsl.get("location") or {}).get("coordinate") or {}
        lat, lng = koord.get("latitude"), koord.get("longitude")
        if lat is None or lng is None:
            return None

        name = ((t.get("nameLocalized") or {}).get("localizedStringWithTranslationPreference")
                or (((dsl.get("description") or {}).get("name") or {})
                    .get("localizedStringWithTranslationPreference"))
                or "Unterkunft")

        zeile = (t.get("structuredDisplayPrice") or {}).get("primaryLine") or {}
        preis_text = (zeile.get("price") or zeile.get("discountedPrice")
                      or zeile.get("accessibilityLabel") or "")

        details = []
        sc = t.get("structuredContent") or {}
        for schluessel in ("mapPrimaryLine", "primaryLine"):
            for teil in sc.get(schluessel) or []:
                body = (teil or {}).get("body")
                if body and body not in details:
                    details.append(body)
            if details:
                break

        def anzahl(muster):
            for teil in details:
                m = re.search(r"(\d+(?:,\d)?)\s*(?:" + muster + ")", teil)
                if m:
                    return float(m.group(1).replace(",", "."))
            return 0

        bilder = []
        for b in t.get("contextualPictures") or []:
            adresse = (b or {}).get("picture")
            if isinstance(adresse, str) and adresse.startswith("https://") and adresse not in bilder:
                bilder.append(adresse)

        return {
            "id": lid,
            "bilder": bilder[:6],
            "name": " ".join(str(name).split()),
            "lat": float(lat),
            "lng": float(lng),
            "km": round(distanz_km(ZENTRUM_LAT, ZENTRUM_LNG, float(lat), float(lng))),
            "preis_text": " ".join(str(preis_text).split()),
            "preis": preis_als_zahl(preis_text),
            "bewertung": t.get("avgRatingLocalized") or "",
            "details": ", ".join(details[:3]),
            "betten": anzahl("Bett"), "schlafzimmer": anzahl("Schlafzimmer"), "baeder": anzahl("Bad|Bäder"),
            "url": (f"https://www.airbnb.de/rooms/{lid}"
                    f"?check_in={CHECKIN}&check_out={CHECKOUT}&adults={GAESTE}"),
        }
    except Exception:
        return None


def pause():
    time.sleep(random.uniform(2.0, 4.5))


def fahrzeit_text(minuten):
    return f"{int(minuten) // 60} h {int(minuten) % 60:02d} min"


def fahrzeiten_ergaenzen(state, treffer):
    """Haengt an jeden Treffer die Auto-Fahrzeit ab Zentrum (Minuten) an."""
    cache = state.setdefault("fahrzeit", {})
    offen = [t for t in treffer.values() if t["id"] not in cache]
    for i in range(0, len(offen), ROUTING_PAKET):
        paket = offen[i:i + ROUTING_PAKET]
        punkte = [f"{ZENTRUM_LNG:.5f},{ZENTRUM_LAT:.5f}"] + [f"{t['lng']:.5f},{t['lat']:.5f}" for t in paket]
        url = ROUTING_URL + ";".join(punkte) + "?sources=0&annotations=duration&skip_waypoints=true"
        try:
            daten = json.loads(http_get(url))
            zeiten = daten["durations"][0][1:]
            if daten.get("code") != "Ok" or len(zeiten) != len(paket):
                raise ValueError("unerwartete Antwort")
            for t, sek in zip(paket, zeiten):
                cache[t["id"]] = round(sek / 60) if sek is not None else -1
        except Exception as e:
            log(f"  Routing nicht erreichbar ({type(e).__name__}) - Fahrzeit wird geschaetzt")
        time.sleep(1.5)
    for t in treffer.values():
        minuten = cache.get(t["id"])
        if minuten is None:
            # Schaetzung: Strasse ca. 30 % laenger als Luftlinie, Schnitt 85 km/h
            minuten = round(t["km"] * 1.3 / 85 * 60)
            t["geschaetzt"] = True
        t["fahrzeit"] = minuten
        t["fahrzeit_text"] = ("ca. " if t.get("geschaetzt") else "") + (
            fahrzeit_text(minuten) if minuten >= 0 else "keine Route")


def ort_nachschlagen(lat, lng):
    """Fragt Ort und Land zu einer Koordinate ab (OpenStreetMap, als Ersatz Photon)."""
    absender = "silvester-airbnb-waechter/1.0 (privates Gruppenprojekt)"
    try:
        d = json.loads(http_get(
            "https://nominatim.openstreetmap.org/reverse?format=jsonv2&zoom=10&accept-language=de"
            f"&lat={lat:.4f}&lon={lng:.4f}", absender))
        a = d.get("address") or {}
        if a.get("country"):
            ort = (a.get("city") or a.get("town") or a.get("village") or a.get("municipality")
                   or a.get("county") or d.get("name") or "")
            return {"ort": ort, "land": a["country"], "code": (a.get("country_code") or "").upper()}
    except Exception:
        pass
    try:
        d = json.loads(http_get(f"https://photon.komoot.io/reverse?lang=de&lat={lat:.4f}&lon={lng:.4f}", absender))
        e = d["features"][0]["properties"]
        if e.get("country"):
            return {"ort": e.get("city") or e.get("locality") or e.get("county") or "",
                    "land": e["country"], "code": (e.get("countrycode") or "").upper()}
    except Exception:
        pass
    return None


def orte_ergaenzen(state, treffer):
    """Haengt an jeden Treffer Ort und Land an. Jede Unterkunft wird nur einmal nachgeschlagen."""
    cache = state.setdefault("ort", {})
    offen = [t for t in treffer.values() if t["id"] not in cache][:MAX_ORTE_PRO_LAUF]
    fehler = 0
    for t in offen:
        ergebnis = ort_nachschlagen(t["lat"], t["lng"])
        time.sleep(1.1)                     # hoechstens eine Anfrage pro Sekunde
        if ergebnis:
            cache[t["id"]] = ergebnis
            fehler = 0
        else:
            fehler += 1
            if fehler >= 3:
                log("  Ortssuche nicht erreichbar - wird beim naechsten Durchlauf nachgeholt")
                break
    for t in treffer.values():
        e = cache.get(t["id"]) or {}
        t["ort"], t["land"], t["land_code"] = e.get("ort", ""), e.get("land", ""), e.get("code", "")


def durchlauf(state):
    """Sucht das ganze Gebiet ab. Gibt (Treffer nach ID, vollstaendig?) zurueck."""
    gefunden = {}
    vollstaendig = True
    abrufe = 0
    offen = [start_kachel()]
    while offen:
        k = offen.pop()
        if not kachel_im_umkreis(k):
            continue
        try:
            treffer, cursors = seite_laden(such_url(k))
            abrufe += 1
            pause()
            for t in treffer:
                gefunden[t["id"]] = t
            teilbar = (k[2] - k[0]) > MIN_KACHEL_GRAD
            if len(cursors) >= MAX_SEITEN and teilbar:
                # Zu viele Treffer fuer eine Suche -> Gebiet vierteln
                offen.extend(kachel_teilen(k))
                continue
            for cursor in cursors[1:]:
                treffer, _ = seite_laden(such_url(k, cursor))
                abrufe += 1
                pause()
                for t in treffer:
                    gefunden[t["id"]] = t
        except AbrufFehler as e:
            vollstaendig = False
            log(f"  Abruf fehlgeschlagen ({e}) - Gebiet wird diesmal uebersprungen")
            time.sleep(60)

    passend = {}
    for lid, t in gefunden.items():
        if t["km"] > RADIUS_KM:
            continue
        if SAMMEL_MAX_PREIS and t["preis"] and t["preis"] > SAMMEL_MAX_PREIS:
            continue
        passend[lid] = t
    fahrzeiten_ergaenzen(state, passend)
    limit = MAX_FAHRZEIT_STD * 60
    passend = {lid: t for lid, t in passend.items() if 0 <= t["fahrzeit"] <= limit}
    orte_ergaenzen(state, passend)
    log(f"  {len(passend)} passende Unterkuenfte frei ({abrufe} Abrufe)")
    return passend, vollstaendig


# ------------------------------- Zustand -----------------------------------
def state_laden():
    if STATE_DATEI.exists():
        try:
            state = json.loads(STATE_DATEI.read_text(encoding="utf-8"))
            if state.get("profil") != PROFIL:
                # Suche wurde geaendert: Bestand neu aufnehmen, Push-Thema behalten
                if state.get("listings"):
                    log("Sucheinstellungen wurden geaendert - Bestand wird neu aufgenommen")
                state.update(profil=PROFIL, initialisiert=False, listings={})
            state.setdefault("fahrzeit", {})
            state.setdefault("ort", {})
            return state
        except ValueError:
            log("Zustandsdatei war kaputt und wird neu angelegt")
    in_der_cloud = bool(os.environ.get("NTFY_TOPIC") or os.environ.get("GITHUB_ACTIONS"))
    return {"topic": "" if in_der_cloud else "airbnb-" + secrets.token_hex(8), "profil": PROFIL,
            "initialisiert": False, "listings": {}, "fahrzeit": {}, "ort": {}}


def push_thema(state):
    return os.environ.get("NTFY_TOPIC") or state.get("topic") or ""


def state_speichern(state):
    tmp = STATE_DATEI.with_suffix(".tmp")
    tmp.write_text(json.dumps(state, ensure_ascii=False, indent=1), encoding="utf-8")
    tmp.replace(STATE_DATEI)


def abgleichen(state, aktuell, vollstaendig, melden=True):
    """Traegt den Durchlauf in den Zustand ein und gibt die Meldungen zurueck."""
    bekannt = state["listings"]
    stempel = datetime.now().isoformat(timespec="seconds")
    meldungen = []
    for lid, t in aktuell.items():
        alt = bekannt.get(lid)
        if alt is None:
            bekannt[lid] = {"zuerst": stempel}
            if melden:
                meldungen.append(("NEU FREI", t))
                bekannt[lid]["gemeldet"] = stempel
        elif alt.get("fehlt", 0) >= FEHLT_SCHWELLE:
            if melden:
                meldungen.append(("WIEDER FREI", t))
                alt["gemeldet"] = stempel
        bekannt[lid].update(
            name=t["name"], url=t["url"], preis_text=t["preis_text"],
            km=t["km"], fahrzeit=t["fahrzeit"], zuletzt=stempel, fehlt=0,
        )
    if vollstaendig:
        # Nur bei komplettem Durchlauf zaehlen, was fehlt - sonst gaebe es Fehlalarme
        for lid, alt in bekannt.items():
            if lid not in aktuell:
                alt["fehlt"] = alt.get("fehlt", 0) + 1
    return meldungen


def csv_schreiben(aktuell):
    zeilen = sorted(aktuell.values(), key=lambda t: t["fahrzeit"])
    with CSV_DATEI.open("w", newline="", encoding="utf-8-sig") as f:
        w = csv.writer(f, delimiter=";")
        w.writerow(["Name", "Ort", "Land", "Gesamtpreis", "Pro Person", "Bewertung", "Fahrzeit", "Luftlinie km", "Details", "Link"])
        for t in zeilen:
            pro_kopf = f"{round(t['preis'] / GAESTE)} €" if t["preis"] else ""
            w.writerow([t["name"], t.get("ort", ""), t.get("land", ""), t["preis_text"], pro_kopf, t["bewertung"], t["fahrzeit_text"],
                        t["km"], t["details"], t["url"]])


def daten_schreiben(state, aktuell):
    """Schreibt die Daten fuer die Uebersichtsseite. Die Seite holt sie sich selbst nach."""
    grenze = (datetime.now() - timedelta(hours=24)).isoformat(timespec="seconds")
    eintraege = []
    for t in aktuell.values():
        gemeldet = (state["listings"].get(t["id"]) or {}).get("gemeldet", "")
        eintraege.append({
            "id": t["id"], "name": t["name"], "url": t["url"], "bilder": t.get("bilder") or [],
            "preis": t["preis"] or 0, "preis_text": t["preis_text"],
            "pro_kopf": round(t["preis"] / GAESTE) if t["preis"] else 0,
            "bewertung": t["bewertung"], "fahrzeit": t["fahrzeit"],
            "fahrzeit_text": t["fahrzeit_text"], "details": t["details"],
            "betten": t.get("betten", 0), "schlafzimmer": t.get("schlafzimmer", 0), "baeder": t.get("baeder", 0),
            "ort": t.get("ort", ""), "land": t.get("land", ""),
            "neu": bool(gemeldet and gemeldet >= grenze), "gemeldet": gemeldet,
        })
    daten = {
        "stand": int(time.time()),
        "intervall_min": INTERVALL_MIN,
        "suche": (f"{GAESTE} Personen · {datetime.strptime(CHECKIN, '%Y-%m-%d'):%d.%m.} bis "
                  f"{datetime.strptime(CHECKOUT, '%Y-%m-%d'):%d.%m.%Y} · {NAECHTE} Nächte · "
                  f"Gäste-Favoriten · Fahrzeit ab {ZENTRUM_NAME}"),
        "checkin": CHECKIN, "checkout": CHECKOUT, "gaeste": GAESTE, "kanal": KANAL,
        "grenze_preis": SAMMEL_MAX_PREIS, "grenze_fahrzeit": MAX_FAHRZEIT_STD,
        "standard_preis": MAX_GESAMTPREIS or SAMMEL_MAX_PREIS,
        "eintraege": eintraege,
    }
    text = ("window.AIRBNB_DATEN = " + json.dumps(daten, ensure_ascii=False)
            + ";\nif (window.aktualisiere) window.aktualisiere(window.AIRBNB_DATEN);\n")
    tmp = DATEN_DATEI.with_suffix(".tmp")
    tmp.write_text(text, encoding="utf-8")
    tmp.replace(DATEN_DATEI)


def seite_schreiben():
    HTML_DATEI.write_text(SEITE, encoding="utf-8")


SEITE = r"""<!DOCTYPE html>
<html lang="de"><head><meta charset="utf-8">
<meta name="viewport" content="width=device-width, initial-scale=1">
<title>Airbnb – frei für Silvester</title>
<style>
*{box-sizing:border-box}
body{margin:0;font-family:system-ui,"Segoe UI",Roboto,sans-serif;background:#f4f2ee;color:#1d1d1f}
header{position:sticky;top:0;z-index:5;background:rgba(244,242,238,.94);backdrop-filter:blur(8px);
  border-bottom:1px solid #e2ded6;padding:14px 24px;display:flex;flex-wrap:wrap;gap:8px 24px;align-items:center}
h1{font-size:20px;margin:0;font-weight:700}
.suche{font-size:13px;color:#6b6760;margin-top:2px}
.rechts{margin-left:auto;display:flex;gap:16px;align-items:center;flex-wrap:wrap}
.live{font-size:13px;color:#6b6760;display:flex;align-items:center;gap:7px}
.punkt{width:9px;height:9px;border-radius:50%;background:#2fa66a;box-shadow:0 0 0 0 rgba(47,166,106,.6);animation:puls 2s infinite}
.alt .punkt{background:#d98b1f;animation:none}
@keyframes puls{70%{box-shadow:0 0 0 8px rgba(47,166,106,0)}100%{box-shadow:0 0 0 0 rgba(47,166,106,0)}}
select,button,input[type=date],input[type=number]{font:inherit;font-size:14px;padding:7px 10px;border-radius:10px;border:1px solid #d5d0c6;background:#fff;color:inherit}
button{cursor:pointer} button:hover{border-color:#a9a397}
button.haupt{background:#1d1d1f;color:#fff;border-color:#1d1d1f} button.haupt:hover{background:#000}
.filter{display:flex;flex-wrap:wrap;gap:14px 26px;align-items:flex-end;padding:14px 24px;background:#fbfaf7;border-bottom:1px solid #e2ded6}
.feld{display:flex;flex-direction:column;gap:5px;font-size:12.5px;color:#6b6760}
.feld b{color:#1d1d1f;font-size:14px;font-weight:600}
.feld input[type=range]{width:190px;accent-color:#ff385c;margin:3px 0 0}
.filter .ende{margin-left:auto;display:flex;gap:10px}
.chips{display:flex;flex-wrap:wrap;gap:8px}
.chip{padding:6px 12px;border-radius:999px;font-size:13.5px}
.chip.an{background:#1d1d1f;color:#fff;border-color:#1d1d1f}
.laender{flex-basis:100%}
.land{font-size:18px;font-weight:700;margin:28px 0 12px;display:flex;align-items:baseline;gap:10px}
.land:first-child{margin-top:0}
.land span{font-size:14px;font-weight:400;color:#6b6760}
.hinweis{margin:16px 24px 0;padding:12px 16px;border-radius:12px;background:#fff4d6;border:1px solid #ecd9a0;font-size:14px}
main{padding:20px 24px 48px}
.raster{display:grid;grid-template-columns:repeat(auto-fill,minmax(250px,1fr));gap:16px}
.kachel{position:relative;display:block;aspect-ratio:1/1;border-radius:18px;overflow:hidden;background:#d9d5cc;
  color:#fff;text-decoration:none;box-shadow:0 1px 3px rgba(0,0,0,.12);transition:transform .15s,box-shadow .15s}
.kachel:hover{transform:translateY(-3px);box-shadow:0 10px 24px rgba(0,0,0,.18)}
.kachel img{position:absolute;inset:0;width:100%;height:100%;object-fit:cover}
.kachel::after{content:"";position:absolute;inset:0;background:linear-gradient(to top,rgba(0,0,0,.82) 0%,rgba(0,0,0,.35) 38%,rgba(0,0,0,0) 62%)}
.text{position:absolute;left:14px;right:14px;bottom:12px;z-index:2}
.name{font-weight:700;font-size:16px;line-height:1.25;display:-webkit-box;-webkit-line-clamp:2;-webkit-box-orient:vertical;overflow:hidden}
.details{font-size:12.5px;opacity:.85;margin-top:3px;white-space:nowrap;overflow:hidden;text-overflow:ellipsis}
.zeile{display:flex;justify-content:space-between;align-items:baseline;gap:8px;margin-top:8px;font-size:13.5px}
.preis b{font-size:18px}
.marke{position:absolute;z-index:2;top:12px;padding:5px 10px;border-radius:999px;font-size:12.5px;font-weight:700}
.stern{right:12px;background:rgba(255,255,255,.94);color:#1d1d1f}
.neu{left:12px;background:#ff385c;color:#fff}
.pfeil{position:absolute;z-index:3;top:42%;width:34px;height:34px;padding:0;border-radius:50%;border:0;background:rgba(255,255,255,.92);
  color:#1d1d1f;font-size:18px;line-height:1;cursor:pointer;opacity:0;transition:opacity .15s}
.kachel:hover .pfeil{opacity:1} .pfeil.l{left:10px} .pfeil.r{right:10px}
.frisch{animation:blink 1.6s ease-out 2}
@keyframes blink{0%{box-shadow:0 0 0 0 rgba(255,56,92,.9)}100%{box-shadow:0 0 0 18px rgba(255,56,92,0)}}
.leer{padding:80px 20px;text-align:center;color:#6b6760;font-size:16px}
dialog{border:0;border-radius:18px;padding:24px;width:min(420px,calc(100vw - 32px));box-shadow:0 20px 60px rgba(0,0,0,.3);color:inherit}
dialog::backdrop{background:rgba(0,0,0,.45)}
dialog h2{margin:0 0 6px;font-size:19px} dialog p{margin:0 0 16px;font-size:14px;color:#6b6760;line-height:1.45}
dialog .feld{margin-bottom:12px} dialog .feld input,dialog .feld select{width:100%}
dialog .knoepfe{display:flex;justify-content:flex-end;gap:10px;margin-top:18px}
#dialogstatus{font-size:14px;margin-top:10px;min-height:20px}
@media (max-width:600px){header,main,.filter{padding-left:14px;padding-right:14px}.hinweis{margin-left:14px;margin-right:14px}
  .raster{grid-template-columns:1fr;gap:14px}.pfeil{opacity:.9;top:34%}.feld{flex:1 1 44%}.feld input[type=range]{width:100%}.filter .ende{margin-left:0;width:100%}}
</style></head><body>
<header>
  <div><h1 id="titel">Unterkünfte werden geladen …</h1><div class="suche" id="suche"></div></div>
  <div class="rechts">
    <div class="live" id="live"><span class="punkt"></span><span id="stand">wartet auf den ersten Durchlauf</span></div>
    <select id="sortierung" aria-label="Sortierung">
      <option value="neu">Neu frei zuerst</option>
      <option value="fahrzeit">Kürzeste Fahrt</option>
      <option value="preis">Günstigster Preis</option>
      <option value="bewertung">Beste Bewertung</option>
    </select>
  </div>
</header>
<div class="filter" id="filter" hidden>
  <label class="feld">Max. Gesamtpreis<b id="preiswert"></b><input type="range" id="f_preis" min="400" step="50"></label>
  <label class="feld">Max. Fahrzeit<b id="fahrtwert"></b><input type="range" id="f_fahrt" min="1" step="0.5"></label>
  <label class="feld">Schlafzimmer<select id="f_zimmer"><option value="0">egal</option><option value="2">ab 2</option><option value="3">ab 3</option><option value="4">ab 4</option><option value="5">ab 5</option><option value="6">ab 6</option></select></label>
  <label class="feld">Betten<select id="f_betten"><option value="0">egal</option><option value="4">ab 4</option><option value="6">ab 6</option><option value="8">ab 8</option><option value="10">ab 10</option></select></label>
  <label class="feld">Bäder<select id="f_baeder"><option value="0">egal</option><option value="2">ab 2</option><option value="3">ab 3</option></select></label>
  <label class="feld">Bewertung<select id="f_sterne"><option value="0">egal</option><option value="4.5">ab 4,5</option><option value="4.8">ab 4,8</option><option value="4.9">ab 4,9</option></select></label>
  <div class="ende">
    <button type="button" id="zurueck">Filter zurücksetzen</button>
    <button type="button" id="suchknopf" class="haupt" hidden>Suche für alle ändern</button>
  </div>
  <div class="feld laender" id="laenderfeld" hidden>Länder<div class="chips" id="chips"></div></div>
</div>
<div class="hinweis" id="hinweis" hidden></div>
<main>
  <div id="bereiche"></div>
  <div class="leer" id="leer">Der erste Durchlauf läuft gerade. Die Unterkünfte erscheinen hier von selbst, du musst nichts neu laden.</div>
</main>
<dialog id="dialog">
  <form method="dialog" id="suchform">
    <h2>Suche für alle ändern</h2>
    <p>Das ändert die Suche <b>für alle</b>, die diese Seite nutzen. Die neue Suche startet beim nächsten Durchlauf, die Ergebnisse stehen nach etwa 15 bis 30 Minuten hier. Preis und Fahrzeit kann danach jeder oben für sich enger stellen.</p>
    <label class="feld">Anreise<input type="date" id="s_ein" required></label>
    <label class="feld">Abreise<input type="date" id="s_aus" required></label>
    <label class="feld">Personen<input type="number" id="s_gaeste" min="1" max="16" required></label>
    <label class="feld">Umkreis: Fahrzeit ab Startort bis<select id="s_fahrt"><option value="3">3 Stunden</option><option value="4">4 Stunden</option><option value="5">5 Stunden</option><option value="6">6 Stunden</option><option value="7">7 Stunden</option><option value="8">8 Stunden</option></select></label>
    <label class="feld">Gesamtpreis bis<select id="s_preis"><option value="1000">1.000 €</option><option value="1500">1.500 €</option><option value="2000">2.000 €</option><option value="2500">2.500 €</option><option value="3000">3.000 €</option><option value="4000">4.000 €</option></select></label>
    <div id="dialogstatus"></div>
    <div class="knoepfe"><button type="button" id="abbrechen">Abbrechen</button><button type="submit" class="haupt">Für alle speichern</button></div>
  </form>
</dialog>
<script>
var daten = null, karten = {}, ersterAufbau = true, filterBereit = false;
var bereiche = document.getElementById('bereiche'), auswahl = document.getElementById('sortierung');
function $(id) { return document.getElementById(id); }
function merken(k, v) { try { localStorage.setItem(k, JSON.stringify(v)); } catch (e) {} }
function holen(k) { try { return JSON.parse(localStorage.getItem(k)); } catch (e) { return null; } }
auswahl.value = holen('sortierung') || 'neu'; if (!auswahl.value) auswahl.value = 'neu';
auswahl.onchange = function () { merken('sortierung', auswahl.value); zeichnen(false); };

function el(tag, klasse, text) { var e = document.createElement(tag); if (klasse) e.className = klasse; if (text != null) e.textContent = text; return e; }
function zahl(t) { return parseFloat(String(t || '0').replace(',', '.')) || 0; }
function euro(n) { return Math.round(n).toString().replace(/\B(?=(\d{3})+(?!\d))/g, '.') + ' €'; }
function stunden(h) { return (h % 1 ? Math.floor(h) + ',5' : h) + ' h'; }
function datum(iso) { var t = iso.split('-'); return t[2] + '.' + t[1] + '.' + t[0]; }

/* ---------- Filter (gelten nur für dich) ---------- */
var F = { preis: 0, fahrt: 0, zimmer: 0, betten: 0, baeder: 0, sterne: 0, laender: [] };
function filterStandard() { return { preis: Math.min(daten.standard_preis, daten.grenze_preis), fahrt: daten.grenze_fahrzeit, zimmer: 0, betten: 0, baeder: 0, sterne: 0, laender: [] }; }
function landVon(d) { return d.land || 'Land noch unbekannt'; }
function filterEinrichten() {
  var p = $('f_preis'), f = $('f_fahrt');
  p.max = daten.grenze_preis; f.max = daten.grenze_fahrzeit;
  if (!filterBereit) {
    var g = holen('filter'), s = filterStandard();
    F = g && typeof g === 'object' ? { preis: +g.preis || s.preis, fahrt: +g.fahrt || s.fahrt, zimmer: +g.zimmer || 0, betten: +g.betten || 0, baeder: +g.baeder || 0, sterne: +g.sterne || 0, laender: Array.isArray(g.laender) ? g.laender.map(String) : [] } : s;
    ['f_preis', 'f_fahrt', 'f_zimmer', 'f_betten', 'f_baeder', 'f_sterne'].forEach(function (id) {
      $(id).oninput = $(id).onchange = function () {
        F = { preis: +p.value, fahrt: +f.value, zimmer: +$('f_zimmer').value, betten: +$('f_betten').value, baeder: +$('f_baeder').value, sterne: +$('f_sterne').value, laender: F.laender };
        merken('filter', F); filterZeigen(); zeichnen(false);
      };
    });
    $('zurueck').onclick = function () { F = filterStandard(); merken('filter', F); filterZeigen(); zeichnen(false); };
    $('filter').hidden = false; filterBereit = true;
  }
  F.preis = Math.min(F.preis, daten.grenze_preis); F.fahrt = Math.min(F.fahrt, daten.grenze_fahrzeit);
  filterZeigen();
}
function filterZeigen() {
  $('f_preis').value = F.preis; $('f_fahrt').value = F.fahrt;
  $('f_zimmer').value = F.zimmer; $('f_betten').value = F.betten; $('f_baeder').value = F.baeder; $('f_sterne').value = F.sterne;
  $('preiswert').textContent = euro(F.preis) + '  ·  ' + euro(F.preis / daten.gaeste) + ' p. P.';
  $('fahrtwert').textContent = stunden(F.fahrt);
}
function chipsZeigen() {
  var zahl = {}, box = $('chips');
  daten.eintraege.forEach(function (d) { if (passt(d, true)) zahl[landVon(d)] = (zahl[landVon(d)] || 0) + 1; });
  daten.eintraege.forEach(function (d) { if (!(landVon(d) in zahl)) zahl[landVon(d)] = 0; });
  var namen = Object.keys(zahl).sort(landReihenfolge(zahl));
  F.laender = F.laender.filter(function (l) { return l in zahl; });
  box.textContent = '';
  namen.forEach(function (name) {
    var c = el('button', 'chip' + (F.laender.indexOf(name) >= 0 ? ' an' : ''), name + ' · ' + zahl[name]); c.type = 'button';
    c.onclick = function () {
      var i = F.laender.indexOf(name); if (i >= 0) F.laender.splice(i, 1); else F.laender.push(name);
      merken('filter', F); zeichnen(false);
    };
    box.appendChild(c);
  });
  $('laenderfeld').hidden = namen.length < 2;
}
function landReihenfolge(zahl) {
  return function (x, y) {
    var ux = x === 'Land noch unbekannt', uy = y === 'Land noch unbekannt';
    if (ux !== uy) return ux ? 1 : -1;
    if ((x === 'Deutschland') !== (y === 'Deutschland')) return x === 'Deutschland' ? -1 : 1;
    return zahl[y] - zahl[x] || x.localeCompare(y);
  };
}
function passt(d, ohneLand) {
  if (!ohneLand && F.laender.length && F.laender.indexOf(landVon(d)) < 0) return false;
  return (!d.preis || d.preis <= F.preis) && d.fahrzeit <= F.fahrt * 60 && d.schlafzimmer >= F.zimmer &&
    d.betten >= F.betten && d.baeder >= F.baeder && (!F.sterne || zahl(d.bewertung) >= F.sterne);
}

/* ---------- Kacheln ---------- */
function karteBauen() {
  var a = el('a', 'kachel'); a.target = '_blank'; a.rel = 'noopener';
  var bild = el('img'); bild.loading = 'lazy'; bild.referrerPolicy = 'no-referrer'; bild.alt = '';
  a.appendChild(bild); a._bild = bild; a._nr = 0;
  a._neu = el('span', 'marke neu', 'NEU FREI'); a.appendChild(a._neu);
  a._stern = el('span', 'marke stern'); a.appendChild(a._stern);
  ['l', 'r'].forEach(function (seite) {
    var p = el('button', 'pfeil ' + seite, seite === 'l' ? '‹' : '›'); p.type = 'button';
    p.setAttribute('aria-label', seite === 'l' ? 'Vorheriges Bild' : 'Nächstes Bild');
    p.onclick = function (ev) { ev.preventDefault(); ev.stopPropagation();
      var b = a._daten.bilder; if (!b.length) return;
      a._nr = (a._nr + (seite === 'l' ? b.length - 1 : 1)) % b.length; bild.src = b[a._nr] + '?im_w=720'; };
    a.appendChild(p);
  });
  var t = el('div', 'text');
  a._name = el('div', 'name'); a._details = el('div', 'details');
  var z = el('div', 'zeile'); a._preis = el('span', 'preis'); a._fahrt = el('span');
  z.appendChild(a._preis); z.appendChild(a._fahrt);
  t.appendChild(a._name); t.appendChild(a._details); t.appendChild(z); a.appendChild(t);
  return a;
}
function karteFuellen(a, d) {
  a._daten = d; a.href = d.url;
  var erstes = d.bilder.length ? d.bilder[Math.min(a._nr, d.bilder.length - 1)] + '?im_w=720' : '';
  if (erstes && a._bild.getAttribute('src') !== erstes) a._bild.src = erstes;
  a._neu.style.display = d.neu ? '' : 'none';
  a._stern.textContent = d.bewertung ? '★ ' + d.bewertung : ''; a._stern.style.display = d.bewertung ? '' : 'none';
  a._name.textContent = d.name; a._details.textContent = (d.ort ? d.ort + '  ·  ' : '') + d.details;
  a._preis.textContent = ''; a._preis.appendChild(el('b', null, d.preis_text));
  if (d.pro_kopf) a._preis.appendChild(document.createTextNode('  ·  ' + d.pro_kopf + ' € p. P.'));
  a._fahrt.textContent = '🚗 ' + d.fahrzeit_text;
}
function zeichnen(markieren) {
  if (!daten) return;
  var alle = daten.eintraege, liste = alle.filter(function (d) { return passt(d); }), art = auswahl.value;
  liste.sort(function (x, y) {
    if (art === 'preis') return (x.preis || 1e9) - (y.preis || 1e9) || x.fahrzeit - y.fahrzeit;
    if (art === 'bewertung') return zahl(y.bewertung) - zahl(x.bewertung) || x.fahrzeit - y.fahrzeit;
    if (art === 'neu') return (y.neu - x.neu) || (y.gemeldet > x.gemeldet ? 1 : y.gemeldet < x.gemeldet ? -1 : 0) || x.fahrzeit - y.fahrzeit;
    return x.fahrzeit - y.fahrzeit;
  });
  var da = {}, sichtbar = {}, gruppen = {}, zahl = {};
  alle.forEach(function (d) { da[d.id] = 1; });
  liste.forEach(function (d) {
    var k = karten[d.id], frisch = !k;
    if (!k) k = karten[d.id] = karteBauen();
    karteFuellen(k, d); sichtbar[d.id] = 1;
    if (frisch && markieren && !ersterAufbau) k.classList.add('frisch');
    (gruppen[landVon(d)] = gruppen[landVon(d)] || []).push(k); zahl[landVon(d)] = gruppen[landVon(d)].length;
  });
  Object.keys(karten).forEach(function (id) {
    if (!sichtbar[id]) karten[id].remove();
    if (!da[id]) delete karten[id];
  });
  var neuBereiche = document.createDocumentFragment(), laender = Object.keys(gruppen).sort(landReihenfolge(zahl));
  laender.forEach(function (name) {
    if (laender.length > 1 || name !== 'Land noch unbekannt') {
      var h = el('h2', 'land', name); h.appendChild(el('span', null, gruppen[name].length + (gruppen[name].length === 1 ? ' Unterkunft' : ' Unterkünfte')));
      neuBereiche.appendChild(h);
    }
    var r = el('div', 'raster'); gruppen[name].forEach(function (k) { r.appendChild(k); }); neuBereiche.appendChild(r);
  });
  bereiche.textContent = ''; bereiche.appendChild(neuBereiche);
  chipsZeigen();
  var n = liste.length, neu = liste.filter(function (d) { return d.neu; }).length;
  $('titel').textContent = (n < alle.length ? n + ' von ' + alle.length + ' Unterkünften frei' : n + (n === 1 ? ' Unterkunft frei' : ' Unterkünfte frei')) + (neu ? '  ·  ' + neu + ' neu' : '');
  document.title = (neu ? '(' + neu + ' neu) ' : '') + n + ' frei – Airbnb Silvester';
  $('suche').textContent = daten.suche;
  $('leer').style.display = n ? 'none' : '';
  if (!n) $('leer').textContent = alle.length ? 'Mit deinen Filtern passt gerade nichts. Stell Preis oder Fahrzeit etwas höher.' : 'Gerade ist nichts Passendes frei. Die Seite aktualisiert sich von selbst.';
  ersterAufbau = false;
}
function standZeigen() {
  if (!daten) return;
  var min = Math.max(0, Math.round((Date.now() / 1000 - daten.stand) / 60));
  var alt = min > daten.intervall_min * 3 + 15;
  $('live').className = 'live' + (alt ? ' alt' : '');
  $('stand').textContent = alt
    ? 'Stand vor ' + (min >= 120 ? Math.round(min / 60) + ' h' : min + ' min') + ' – läuft der Wächter noch?'
    : 'Live · Stand ' + (min < 1 ? 'gerade eben' : 'vor ' + min + ' min');
  hinweisZeigen();
}

/* ---------- Suche für alle ändern ---------- */
function hinweisZeigen() {
  var w = holen('wunsch'), h = $('hinweis');
  if (w && daten && (w.checkin !== daten.checkin || w.checkout !== daten.checkout || w.gaeste !== daten.gaeste || w.fahrzeit !== daten.grenze_fahrzeit || w.preis !== daten.grenze_preis) && Date.now() - w.zeit < 90 * 60000) {
    h.textContent = 'Neue Suche ist angefragt: ' + w.gaeste + ' Personen, ' + datum(w.checkin) + ' bis ' + datum(w.checkout) + ', bis ' + stunden(w.fahrzeit) + ' Fahrt und ' + euro(w.preis) + '. Sie wird beim nächsten Durchlauf eingerichtet, die Ergebnisse erscheinen dann von selbst.';
    h.hidden = false;
  } else { h.hidden = true; }
}
$('suchknopf').onclick = function () {
  $('s_ein').value = daten.checkin; $('s_aus').value = daten.checkout; $('s_gaeste').value = daten.gaeste;
  [['s_fahrt', daten.grenze_fahrzeit, stunden(daten.grenze_fahrzeit)], ['s_preis', daten.grenze_preis, euro(daten.grenze_preis)]].forEach(function (x) {
    var sel = $(x[0]); if (![].some.call(sel.options, function (o) { return +o.value === +x[1]; })) { var o = el('option', null, x[2]); o.value = x[1]; sel.appendChild(o); }
    sel.value = x[1];
  });
  $('dialogstatus').textContent = ''; $('dialog').showModal();
};
$('abbrechen').onclick = function () { $('dialog').close(); };
$('suchform').oninput = function () { $('dialogstatus').textContent = ''; };
$('suchform').onsubmit = function (ev) {
  ev.preventDefault();
  var w = { checkin: $('s_ein').value, checkout: $('s_aus').value, gaeste: parseInt($('s_gaeste').value, 10), fahrzeit: +$('s_fahrt').value, preis: +$('s_preis').value }, st = $('dialogstatus');
  var naechte = (new Date(w.checkout) - new Date(w.checkin)) / 86400000;
  if (!(naechte >= 1 && naechte <= 21)) { st.textContent = 'Die Abreise muss 1 bis 21 Nächte nach der Anreise liegen.'; return; }
  if (!(w.gaeste >= 1 && w.gaeste <= 16)) { st.textContent = 'Bitte 1 bis 16 Personen angeben.'; return; }
  st.textContent = 'Wird gespeichert …';
  fetch('https://ntfy.sh/' + daten.kanal, { method: 'POST', body: JSON.stringify(w) }).then(function (r) {
    if (!r.ok) throw new Error(r.status);
    w.zeit = Date.now(); merken('wunsch', w); $('dialog').close(); hinweisZeigen();
  }).catch(function () { st.textContent = 'Speichern hat nicht geklappt. Bitte gleich noch einmal versuchen.'; });
};

window.aktualisiere = function (d) {
  if (daten && daten.stand === d.stand) return;
  d.gaeste = d.gaeste || 8; d.grenze_fahrzeit = d.grenze_fahrzeit || 6;
  d.grenze_preis = d.grenze_preis || Math.max.apply(null, d.eintraege.map(function (x) { return x.preis || 0; }).concat([1000]));
  d.standard_preis = d.standard_preis || d.grenze_preis;
  d.eintraege.forEach(function (x) { x.schlafzimmer = x.schlafzimmer || 0; x.betten = x.betten || 0; x.baeder = x.baeder || 0; x.land = x.land || ''; x.ort = x.ort || ''; });
  daten = d; filterEinrichten(); $('suchknopf').hidden = !d.kanal;
  zeichnen(true); standZeigen();
};
function nachladen() {
  var s = document.createElement('script');
  s.src = 'airbnb_daten.js?t=' + Date.now();
  s.onload = s.onerror = function () { s.remove(); };
  document.head.appendChild(s);
}
nachladen(); setInterval(nachladen, 30000); setInterval(standZeigen, 30000);
</script></body></html>
"""

# ------------------------------- Meldungen ---------------------------------
def push(state, titel, text, link=None):
    thema = push_thema(state)
    if not PUSH_AKTIV or not thema:
        return
    daten = {"topic": thema, "title": titel, "message": text, "tags": ["house"]}
    if link:
        daten["click"] = link
    req = urllib.request.Request(
        "https://ntfy.sh/",
        data=json.dumps(daten).encode("utf-8"),
        headers={"Content-Type": "application/json"},
    )
    try:
        urllib.request.urlopen(req, timeout=20).read()
    except Exception as e:
        log(f"  Push fehlgeschlagen: {e}")


def melden(state, meldungen):
    meldungen.sort(key=lambda m: m[1]["fahrzeit"])
    for art, t in meldungen:
        wo = ", ".join(x for x in (t.get("ort"), t.get("land")) if x)
        zeile = (f"{art}: {t['name']} | {wo} | {t['preis_text']} | {t['bewertung']} Sterne | "
                 f"{t['fahrzeit_text']} Fahrt | {t['details']} | {t['url']}")
        log("  >>> " + zeile)
        with LOG_DATEI.open("a", encoding="utf-8") as f:
            f.write(f"{jetzt()} {zeile}\n")
    meldungen = [m for m in meldungen
                 if not (MAX_GESAMTPREIS and m[1]["preis"] and m[1]["preis"] > MAX_GESAMTPREIS)]
    for art, t in meldungen[:MAX_PUSH_PRO_LAUF]:
        push(
            state,
            f"{art}: {t['name']}"[:120],
            (", ".join(x for x in (t.get("ort"), t.get("land")) if x) + "\n"
             f"{t['preis_text']} gesamt, {t['bewertung']} Sterne, {t['fahrzeit_text']} Fahrt\n{t['details']}").strip(),
            t["url"],
        )
    rest = len(meldungen) - MAX_PUSH_PRO_LAUF
    if rest > 0:
        push(state, f"{rest} weitere Unterkuenfte frei", "Details stehen in airbnb_treffer.log")


# ------------------------------- GitHub ------------------------------------
WORKFLOW = r"""name: Airbnb-Waechter

on:
  schedule:
    - cron: "7,22,37,52 * * * *"
  workflow_dispatch:

permissions:
  contents: write
  pages: write
  id-token: write

concurrency:
  group: airbnb-waechter
  cancel-in-progress: false

jobs:
  lauf:
    runs-on: ubuntu-latest
    timeout-minutes: 25
    environment:
      name: github-pages
      url: ${{ steps.deployment.outputs.page_url }}
    env:
      TZ: Europe/Berlin
      NTFY_TOPIC: ${{ secrets.NTFY_TOPIC }}
    steps:
      - uses: actions/checkout@v6
        with:
          ref: main

      - name: Airbnb abfragen
        id: abfrage
        continue-on-error: true
        run: python3 airbnb_watch.py --einmal --kein-browser --web-ordner site

      - name: Stand sichern
        run: |
          git config user.name "airbnb-waechter"
          git config user.email "airbnb-waechter@users.noreply.github.com"
          git add -A
          git diff --cached --quiet || git commit -m "Stand $(date '+%d.%m. %H:%M')"
          git push

      - uses: actions/upload-pages-artifact@v5
        with:
          path: site

      - id: deployment
        uses: actions/deploy-pages@v5

      - name: Fehler anzeigen
        if: steps.abfrage.outcome == 'failure'
        run: exit 1
"""


def cloud_dateien_schreiben():
    ziel = ORDNER / ".github" / "workflows"
    ziel.mkdir(parents=True, exist_ok=True)
    for datei, text in ((ziel / "watch.yml", WORKFLOW), (ORDNER / ".gitignore", "*.tmp\n__pycache__/\n")):
        with open(datei, "w", encoding="utf-8", newline="\n") as f:
            f.write(text)
    if not EINSTELL_DATEI.exists():
        with open(EINSTELL_DATEI, "w", encoding="utf-8", newline="\n") as f:
            f.write(json.dumps({"kanal": "airbnb-suche-" + secrets.token_hex(8)}, indent=1) + "\n")
    log("Angelegt: .github/workflows/watch.yml, .gitignore und einstellungen.json")


# ------------------------------- Hauptprogramm -----------------------------
def ersteinrichtung(state):
    log("Erster Start: Bestand wird aufgenommen (2 Durchlaeufe, ein paar Minuten).")
    gesamt = {}
    for nr in (1, 2):
        aktuell, vollstaendig = durchlauf(state)
        if not vollstaendig and not aktuell:
            raise AbrufFehler("Airbnb liefert gerade keine Daten")
        abgleichen(state, aktuell, vollstaendig, melden=False)
        gesamt.update(aktuell)
    for alt in state["listings"].values():
        alt["fehlt"] = 0
    state["initialisiert"] = True
    state_speichern(state)
    csv_schreiben(gesamt)
    daten_schreiben(state, gesamt)
    log(f"Bestand steht: {len(gesamt)} Unterkuenfte sind aktuell frei -> {CSV_DATEI.name}")
    log("Ab jetzt wird nur noch gemeldet, was neu oder wieder frei wird.")


def ein_lauf(state):
    aktuell, vollstaendig = durchlauf(state)
    if not vollstaendig and not aktuell:
        raise AbrufFehler("Airbnb liefert gerade keine Daten")
    meldungen = abgleichen(state, aktuell, vollstaendig)
    state_speichern(state)
    if vollstaendig:
        csv_schreiben(aktuell)
        daten_schreiben(state, aktuell)
    if meldungen:
        melden(state, meldungen)
    else:
        log("  nichts Neues")


def main():
    try:
        sys.stdout.reconfigure(encoding="utf-8", errors="replace")
    except Exception:
        pass
    ap = argparse.ArgumentParser(description="Meldet frei werdende Airbnb-Unterkuenfte")
    ap.add_argument("--einmal", action="store_true", help="nur ein Durchlauf, dann Ende")
    ap.add_argument("--test-push", action="store_true", help="Test-Push schicken und Ende")
    ap.add_argument("--zeigen", action="store_true", help="nur die Uebersicht im Browser oeffnen")
    ap.add_argument("--kein-browser", action="store_true", help="Uebersicht beim Start nicht oeffnen")
    ap.add_argument("--web-ordner", help="Uebersicht als index.html in diesen Ordner schreiben")
    ap.add_argument("--cloud-dateien", action="store_true", help="Dateien fuer GitHub anlegen und Ende")
    args = ap.parse_args()

    if args.cloud_dateien:
        cloud_dateien_schreiben()
        return
    if args.web_ordner:
        global HTML_DATEI, DATEN_DATEI
        ordner = Path(args.web_ordner).resolve()
        ordner.mkdir(parents=True, exist_ok=True)
        HTML_DATEI = ordner / "index.html"
        DATEN_DATEI = ordner / "airbnb_daten.js"
    seite_schreiben()
    if args.zeigen:
        webbrowser.open(HTML_DATEI.as_uri())
        log(f"Uebersicht im Browser geoeffnet ({HTML_DATEI.name})")
        return

    einstellungen_laden()
    state = state_laden()
    state_speichern(state)

    preis = f", bis {SAMMEL_MAX_PREIS} Euro gesamt" if SAMMEL_MAX_PREIS else ""
    log(f"Suche: {GAESTE} Gaeste, {CHECKIN} bis {CHECKOUT} ({NAECHTE} Naechte){preis}, "
        f"max. {MAX_FAHRZEIT_STD:g} h Autofahrt ab {ZENTRUM_NAME}")
    if PUSH_AKTIV and push_thema(state):
        log(f"Push: in der ntfy-App das Thema  {push_thema(state)}  abonnieren")
    elif PUSH_AKTIV:
        log("Push ist aus: kein NTFY_TOPIC hinterlegt")

    if args.test_push:
        push(state, "Airbnb-Waechter", "Test: Push funktioniert.")
        log("Test-Push verschickt.")
        return

    if not args.kein_browser:
        webbrowser.open(HTML_DATEI.as_uri())
        log(f"Uebersicht im Browser geoeffnet - sie aktualisiert sich nach jedem Durchlauf selbst")

    while True:
        try:
            if not state.get("initialisiert"):
                ersteinrichtung(state)
            else:
                log("Durchlauf startet")
                ein_lauf(state)
        except AbrufFehler as e:
            log(f"Durchlauf abgebrochen: {e}")
            fehler = True
        except KeyboardInterrupt:
            raise
        except Exception as e:
            log(f"Unerwarteter Fehler: {type(e).__name__}: {e}")
            fehler = True
        else:
            fehler = False
        if args.einmal:
            if fehler:
                sys.exit(1)
            break
        warte = INTERVALL_MIN * 60 * random.uniform(0.85, 1.15)
        log(f"Naechster Durchlauf in {round(warte / 60)} Minuten (Strg+C beendet)")
        time.sleep(warte)


if __name__ == "__main__":
    try:
        main()
    except KeyboardInterrupt:
        print("\nBeendet.")

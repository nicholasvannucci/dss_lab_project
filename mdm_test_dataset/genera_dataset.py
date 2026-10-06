#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
Generatore del dataset di TEST per un sistema di Master Data Management.

Simula il gruppo industriale fittizio "Ferraboli" con cinque sistemi:
  odoo_it   Odoo 16 (capogruppo italiana, due societa' nello stesso database)
  jde_de    JD Edwards EnterpriseOne 9.2 (controllate Germania e Austria)
  exact_nl  Exact Globe Next (controllata Benelux)
  ebs_es    Oracle E-Business Suite R12, modello TCA (controllata Spagna/Portogallo)
  suitecrm  SuiteCRM 7 (CRM di gruppo)

Produce un CSV per tabella (sistema__tabella.csv), il file verita.csv,
verifica la coerenza fra verita.csv e i CSV e crea lo zip finale.

Uso:   python3 genera_dataset.py [cartella_di_uscita]
Solo libreria standard. Seme fisso: l'output e' sempre identico.
"""
import csv
import datetime as dt
import json
import os
import random
import re
import sys
import unicodedata
import uuid
import zipfile

SEED = 20261006
rng = random.Random(SEED)
TODAY = dt.datetime(2026, 9, 30, 18, 0, 0)
SYSTEMS = ["odoo_it", "jde_de", "exact_nl", "ebs_es", "suitecrm"]
GOLIVE = {
    "odoo_it": dt.datetime(2017, 1, 9, 7, 30),
    "jde_de": dt.datetime(2011, 4, 4, 6, 0),
    "exact_nl": dt.datetime(2014, 1, 2, 8, 0),
    "ebs_es": dt.datetime(2012, 7, 2, 9, 0),
    "suitecrm": dt.datetime(2018, 3, 5, 9, 0),
}
CONCEPTS = ["codice cliente", "ragione sociale", "partita_iva", "codice_fiscale", "indirizzo",
            "cap", "citta", "provincia", "paese", "telefono", "email", "sito_web",
            "stato_cliente", "tipo_anagrafica", "data_creazione"]

# =============================================================================
# Cifre di controllo delle partite IVA
# =============================================================================


def it_check(d10):
    s = 0
    for i, ch in enumerate(d10):
        n = int(ch)
        if i % 2 == 1:
            n *= 2
            if n > 9:
                n -= 9
        s += n
    return str((10 - s % 10) % 10)


def de_check(d8):
    p = 10
    for ch in d8:
        s = (int(ch) + p) % 10
        if s == 0:
            s = 10
        p = (2 * s) % 11
    c = 11 - p
    return "0" if c == 10 else str(c)


def at_check(d7):
    s = 0
    for i, ch in enumerate(d7):
        n = int(ch)
        if i % 2 == 1:
            n *= 2
            n = n // 10 + n % 10
        s += n
    return str((10 - (s + 4) % 10) % 10)


def nl_check(d8):
    s = sum(w * int(x) for w, x in zip(range(9, 1, -1), d8))
    return s % 11


def be_check(d8):
    return "%02d" % (97 - int(d8) % 97)


def es_check(d7):
    a = sum(int(d7[i]) for i in (1, 3, 5))
    b = 0
    for i in (0, 2, 4, 6):
        n = int(d7[i]) * 2
        b += n // 10 + n % 10
    return str((10 - (a + b) % 10) % 10)


def luhn_digit(s):
    tot = 0
    for i, ch in enumerate(reversed(s)):
        n = int(ch)
        if i % 2 == 0:
            n *= 2
            if n > 9:
                n -= 9
        tot += n
    return str((10 - tot % 10) % 10)


def fr_key(siren):
    return "%02d" % ((12 + 3 * (int(siren) % 97)) % 97)


def ch_check(d8):
    s = sum(w * int(x) for w, x in zip([5, 4, 3, 2, 7, 6, 5, 4], d8))
    c = 11 - s % 11
    if c == 11:
        return "0"
    return None if c == 10 else str(c)


def vat_ok(v):
    """True se v e' una partita IVA con prefisso paese e cifra di controllo corretta."""
    v = v or ""
    m = re.fullmatch(r"IT(\d{11})", v)
    if m:
        return it_check(m[1][:10]) == m[1][10] and (1 <= int(m[1][7:10]) <= 100 or m[1][7:10] in ("120", "121", "888", "999"))
    m = re.fullmatch(r"DE([1-9]\d{8})", v)
    if m:
        return de_check(m[1][:8]) == m[1][8]
    m = re.fullmatch(r"ATU(\d{8})", v)
    if m:
        return at_check(m[1][:7]) == m[1][7]
    m = re.fullmatch(r"NL(\d{9})B\d\d", v)
    if m:
        return nl_check(m[1][:8]) == int(m[1][8])
    m = re.fullmatch(r"BE([01]\d{9})", v)
    if m:
        return be_check(m[1][:8]) == m[1][8:]
    m = re.fullmatch(r"ES([ABCDEFGHJNPQRSUVW])(\d{7})(\d)", v)
    if m:
        return es_check(m[2]) == m[3]
    m = re.fullmatch(r"FR(\d\d)(\d{9})", v)
    if m:
        return luhn_digit(m[2][:8]) == m[2][8] and fr_key(m[2]) == m[1]
    m = re.fullmatch(r"CHE-(\d{3})\.(\d{3})\.(\d{3}) MWST", v)
    if m:
        d = m[1] + m[2] + m[3]
        return ch_check(d[:8]) == d[8]
    return False


# posizione della cifra di controllo nella forma canonica (per gli errori)
CHECK_POS = {"IT": -1, "DE": -1, "AT": -1, "NL": 10, "BE": -1, "ES": -1, "FR": 3, "CH": 14}
VAT_USED = set()


def digits(n):
    return "".join(str(rng.randint(0, 9)) for _ in range(n))


def new_vat(cc, lf=""):
    """Restituisce (forma canonica con prefisso, forma senza prefisso, codice fiscale)."""
    while True:
        if cc == "IT":
            body = digits(7) + "%03d" % rng.randint(1, 100)
            num = body + it_check(body)
            res = ("IT" + num, num, num)
        elif cc == "DE":
            body = str(rng.randint(1, 9)) + digits(7)
            num = body + de_check(body)
            res = ("DE" + num, num, "")
        elif cc == "AT":
            body = digits(7)
            res = ("ATU" + body + at_check(body), "U" + body + at_check(body), "")
        elif cc == "NL":
            body = digits(8)
            c = nl_check(body)
            if c > 9:
                continue
            num = body + str(c) + "B01"
            res = ("NL" + num, num, "")
        elif cc == "BE":
            body = "0" + "%07d" % rng.randint(2000000, 9999999)
            num = body + be_check(body)
            res = ("BE" + num, num, "")
        elif cc == "ES":
            letter = "A" if lf == "S.A." else "B"
            body = digits(7)
            num = letter + body + es_check(body)
            res = ("ES" + num, num, num)
        elif cc == "FR":
            body = str(rng.randint(3, 9)) + digits(7)
            siren = body + luhn_digit(body)
            num = fr_key(siren) + siren
            res = ("FR" + num, num, "")
        elif cc == "CH":
            body = str(rng.randint(1, 9)) + digits(7)
            c = ch_check(body)
            if c is None:
                continue
            d = body + c
            res = ("CHE-%s.%s.%s MWST" % (d[:3], d[3:6], d[6:]), "", "")
        else:
            raise ValueError(cc)
        if res[0] not in VAT_USED:
            VAT_USED.add(res[0])
            assert vat_ok(res[0]), res
            return res


def bad_check(v, cc):
    i = CHECK_POS[cc] % len(v)
    d = int(v[i])
    for k in rng.sample(range(1, 10), 9):
        w = v[:i] + str((d + k) % 10) + v[i + 1:]
        if not vat_ok(w):
            return w
    raise RuntimeError(v)


def iban_it():
    bban = (rng.choice("ABCDEFGHIJKLMNOPRSTUVWXYZ") + "%05d" % rng.choice([3069, 5034, 2008, 3111, 5696, 8327, 1030])
            + "%05d" % rng.randint(1000, 99999) + "%012d" % rng.randint(1, 10 ** 11))
    num = "".join(str(int(c, 36)) for c in bban + "IT00")
    return "IT%02d%s" % (98 - int(num) % 97, bban)


# =============================================================================
# Dati di base
# =============================================================================
COUNTRY = {
    "IT": dict(en="Italy", it="Italia", odoo=109, pfx="39", lang="it_IT", tld="it"),
    "DE": dict(en="Germany", it="Germania", odoo=57, pfx="49", lang="de_DE", tld="de"),
    "AT": dict(en="Austria", it="Austria", odoo=13, pfx="43", lang="de_DE", tld="at"),
    "NL": dict(en="Netherlands", it="Paesi Bassi", odoo=166, pfx="31", lang="nl_NL", tld="nl"),
    "BE": dict(en="Belgium", it="Belgio", odoo=21, pfx="32", lang="nl_BE", tld="be"),
    "ES": dict(en="Spain", it="Spagna", odoo=68, pfx="34", lang="es_ES", tld="es"),
    "FR": dict(en="France", it="Francia", odoo=75, pfx="33", lang="fr_FR", tld="fr"),
    "CH": dict(en="Switzerland", it="Svizzera", odoo=43, pfx="41", lang="de_CH", tld="ch"),
}
EXTRA_COUNTRIES = [(192, "San Marino", "San Marino", "SM", "378"), (199, "Slovenia", "Slovenia", "SI", "386"),
                   (180, "Poland", "Polonia", "PL", "48"), (233, "United States", "Stati Uniti", "US", "1"),
                   (174, "Portugal", "Portogallo", "PT", "351")]
NEIGH = {"IT": ["CH", "FR", "AT", "DE", "ES"], "DE": ["AT", "CH", "NL"], "AT": ["DE", "CH", "IT"],
         "NL": ["BE", "DE"], "BE": ["NL", "FR"], "ES": ["FR", "IT"], "FR": ["BE", "CH", "ES"], "CH": ["DE", "IT", "AT"]}

# (citta', sigla provincia/regione, nome provincia/regione, CAP, prefisso, peso)
CITIES = {
    "IT": [
        ("Milano", "MI", "Milano", ["20121", "20124", "20129", "20135", "20141", "20151", "20156"], "02", 7),
        ("Sesto San Giovanni", "MI", "Milano", ["20099"], "02", 2), ("Rho", "MI", "Milano", ["20017"], "02", 2),
        ("Legnano", "MI", "Milano", ["20025"], "0331", 2), ("Monza", "MB", "Monza e della Brianza", ["20900"], "039", 3),
        ("Brescia", "BS", "Brescia", ["25121", "25124", "25128"], "030", 5), ("Lumezzane", "BS", "Brescia", ["25065"], "030", 3),
        ("Bergamo", "BG", "Bergamo", ["24121", "24126"], "035", 4), ("Dalmine", "BG", "Bergamo", ["24044"], "035", 2),
        ("Varese", "VA", "Varese", ["21100"], "0332", 2), ("Busto Arsizio", "VA", "Varese", ["21052"], "0331", 2),
        ("Como", "CO", "Como", ["22100"], "031", 2), ("Cantù", "CO", "Como", ["22063"], "031", 2),
        ("Lecco", "LC", "Lecco", ["23900"], "0341", 2), ("Cremona", "CR", "Cremona", ["26100"], "0372", 1),
        ("Mantova", "MN", "Mantova", ["46100"], "0376", 1),
        ("Torino", "TO", "Torino", ["10121", "10126", "10135", "10141", "10156"], "011", 5),
        ("Ivrea", "TO", "Torino", ["10015"], "0125", 1), ("Cuneo", "CN", "Cuneo", ["12100"], "0171", 1),
        ("Alessandria", "AL", "Alessandria", ["15121"], "0131", 1), ("Novara", "NO", "Novara", ["28100"], "0321", 1),
        ("Biella", "BI", "Biella", ["13900"], "015", 1), ("Genova", "GE", "Genova", ["16121", "16149", "16152"], "010", 2),
        ("Verona", "VR", "Verona", ["37121", "37135", "37138"], "045", 3), ("Vicenza", "VI", "Vicenza", ["36100"], "0444", 3),
        ("Schio", "VI", "Vicenza", ["36015"], "0445", 2), ("Padova", "PD", "Padova", ["35121", "35127", "35129"], "049", 3),
        ("Treviso", "TV", "Treviso", ["31100"], "0422", 2), ("Conegliano", "TV", "Treviso", ["31015"], "0438", 2),
        ("Castelfranco Veneto", "TV", "Treviso", ["31033"], "0423", 1), ("Venezia", "VE", "Venezia", ["30121", "30175"], "041", 2),
        ("Udine", "UD", "Udine", ["33100"], "0432", 2), ("Pordenone", "PN", "Pordenone", ["33170"], "0434", 2),
        ("Trento", "TN", "Trento", ["38121"], "0461", 1), ("Bolzano", "BZ", "Bolzano", ["39100"], "0471", 1),
        ("Bologna", "BO", "Bologna", ["40121", "40128", "40132", "40138"], "051", 4), ("Imola", "BO", "Bologna", ["40026"], "0542", 1),
        ("Modena", "MO", "Modena", ["41121", "41122", "41126"], "059", 3), ("Carpi", "MO", "Modena", ["41012"], "059", 1),
        ("Sassuolo", "MO", "Modena", ["41049"], "0536", 2), ("Reggio Emilia", "RE", "Reggio Emilia", ["42121", "42122", "42124"], "0522", 3),
        ("Parma", "PR", "Parma", ["43121", "43122", "43126"], "0521", 2), ("Piacenza", "PC", "Piacenza", ["29121", "29122"], "0523", 1),
        ("Forlì", "FC", "Forlì-Cesena", ["47121", "47122"], "0543", 2), ("Faenza", "RA", "Ravenna", ["48018"], "0546", 1),
        ("Firenze", "FI", "Firenze", ["50121", "50127", "50145"], "055", 2), ("Prato", "PO", "Prato", ["59100"], "0574", 1),
        ("Arezzo", "AR", "Arezzo", ["52100"], "0575", 1), ("Lucca", "LU", "Lucca", ["55100"], "0583", 1),
        ("Pisa", "PI", "Pisa", ["56121", "56122"], "050", 1), ("Ancona", "AN", "Ancona", ["60121", "60131"], "071", 1),
        ("Pesaro", "PU", "Pesaro e Urbino", ["61121", "61122"], "0721", 1), ("Perugia", "PG", "Perugia", ["06121", "06128", "06135"], "075", 1),
        ("Roma", "RM", "Roma", ["00118", "00144", "00155", "00184", "00195"], "06", 3), ("Pomezia", "RM", "Roma", ["00071"], "06", 1),
        ("Pescara", "PE", "Pescara", ["65121", "65129"], "085", 1), ("Napoli", "NA", "Napoli", ["80121", "80142", "80146"], "081", 2),
        ("Bari", "BA", "Bari", ["70121", "70123", "70132"], "080", 1), ("Taranto", "TA", "Taranto", ["74121", "74123"], "099", 1),
        ("Catania", "CT", "Catania", ["95121", "95131"], "095", 1), ("Paternò", "CT", "Catania", ["95047"], "095", 1),
        ("Palermo", "PA", "Palermo", ["90133", "90145"], "091", 1), ("Cagliari", "CA", "Cagliari", ["09121", "09122"], "070", 1),
    ],
    "DE": [("München", "BY", "Bayern", ["80331", "80939", "81249"], "089", 2), ("Stuttgart", "BW", "Baden-Württemberg", ["70173", "70469"], "0711", 2),
           ("Nürnberg", "BY", "Bayern", ["90402", "90431"], "0911", 1), ("Köln", "NW", "Nordrhein-Westfalen", ["50667", "50829"], "0221", 1),
           ("Düsseldorf", "NW", "Nordrhein-Westfalen", ["40210", "40472"], "0211", 1), ("Hamburg", "HH", "Hamburg", ["20095", "22525"], "040", 1),
           ("Frankfurt am Main", "HE", "Hessen", ["60311", "60528"], "069", 1)],
    "AT": [("Wien", "W", "Wien", ["1010", "1100", "1230"], "01", 2), ("Graz", "ST", "Steiermark", ["8010", "8055"], "0316", 1),
           ("Linz", "OÖ", "Oberösterreich", ["4020", "4030"], "0732", 1), ("Innsbruck", "T", "Tirol", ["6020"], "0512", 1)],
    "NL": [("Amsterdam", "NH", "Noord-Holland", ["1012 AB", "1043 DR"], "020", 1), ("Rotterdam", "ZH", "Zuid-Holland", ["3011 AA", "3089 KE"], "010", 1),
           ("Eindhoven", "NB", "Noord-Brabant", ["5611 AA", "5652 AL"], "040", 1), ("Utrecht", "UT", "Utrecht", ["3511 AA"], "030", 1)],
    "BE": [("Bruxelles", "BRU", "Bruxelles-Capitale", ["1000", "1070"], "02", 1), ("Antwerpen", "VAN", "Antwerpen", ["2000", "2030"], "03", 1),
           ("Gent", "VOV", "Oost-Vlaanderen", ["9000", "9042"], "09", 1), ("Liège", "WLG", "Liège", ["4000"], "04", 1)],
    "ES": [("Madrid", "M", "Madrid", ["28001", "28045"], "91", 2), ("Barcelona", "B", "Barcelona", ["08001", "08040"], "93", 2),
           ("Valencia", "V", "Valencia", ["46001", "46014"], "96", 1), ("Bilbao", "BI", "Bizkaia", ["48001", "48015"], "94", 1),
           ("Zaragoza", "Z", "Zaragoza", ["50001", "50014"], "976", 1)],
    "FR": [("Lyon", "69", "Rhône", ["69001", "69007"], "04", 1), ("Paris", "75", "Paris", ["75001", "75015"], "01", 1),
           ("Grenoble", "38", "Isère", ["38000"], "04", 1), ("Annecy", "74", "Haute-Savoie", ["74000"], "04", 1),
           ("Mulhouse", "68", "Haut-Rhin", ["68100"], "03", 1)],
    "CH": [("Lugano", "TI", "Ticino", ["6900"], "091", 1), ("Zürich", "ZH", "Zürich", ["8001", "8048"], "044", 1),
           ("Basel", "BS", "Basel-Stadt", ["4051"], "061", 1)],
}
IT_PROVS = {}
for _c in CITIES["IT"]:
    IT_PROVS[_c[1]] = _c[2]
for _code, _name in [("SO", "Sondrio"), ("PV", "Pavia"), ("LO", "Lodi"), ("RO", "Rovigo"), ("BL", "Belluno"),
                     ("GO", "Gorizia"), ("TS", "Trieste"), ("SV", "Savona"), ("VC", "Vercelli"), ("AT", "Asti")]:
    IT_PROVS[_code] = _name
STATE_ID = {code: 150 + i for i, code in enumerate(sorted(IT_PROVS))}

IT_SURNAMES = ["Rossi", "Bianchi", "Colombo", "Ferrari", "Galli", "Bertoli", "Brambilla", "Fumagalli", "Cattaneo", "Ghidini",
               "Zanetti", "Bonomi", "Pellegrini", "Marchetti", "Lombardi", "Moretti", "Barbieri", "Fontana", "Santoro", "Mariani",
               "Rinaldi", "Caruso", "Ferri", "Gatti", "Testa", "Martinelli", "Sala", "Villa", "Riva", "Mazza", "Bassi", "Pagani",
               "Cremonesi", "Tosi", "Zanardi", "Benedetti", "Rizzi", "Corradini", "Montanari", "Guerra", "Valentini", "Vitali",
               "Bellini", "Gentile", "Ruggeri", "Silvestri", "Bergamaschi", "Ravelli", "Belotti", "Locatelli", "Pozzi", "Bettoni",
               "Signorini", "Facchinetti", "Zucchi", "Cavalli", "Arrighi", "Donati", "Morandi", "Pasini", "Frigerio",
               "Sironi", "Mauri", "Galbiati", "Redaelli", "Meroni", "Pirovano", "Panzeri", "Tagliabue", "Bonetti", "Gualtieri",
               "Ferrandi", "Scalvini", "Ongaro", "Perotti", "Tonoli", "Gnutti", "Pedretti", "Zani", "Lanfranchi"]
IT_SECTORS = ["Meccanica", "Fonderia", "Plastica", "Trafilerie", "Stampaggi", "Automazione", "Imballaggi",
              "Minuterie Metalliche", "Carpenteria", "Elettromeccanica", "Oleodinamica", "Utensileria", "Componenti",
              "Vernici", "Ricambi Industriali", "Trasmissioni", "Lamiere", "Torneria", "Idraulica", "Cablaggi",
              "Guarnizioni", "Viteria", "Pressofusioni", "Ingranaggi", "Tubi", "Valvole", "Molle", "Cuscinetti",
              "Saldature", "Termoplastici", "Rettifiche", "Stampi", "Motori Elettrici", "Quadri Elettrici"]
IT_FEM = ["Meccanica", "Fonderia", "Plastica", "Carpenteria", "Torneria", "Utensileria", "Viteria", "Oleodinamica",
          "Elettromeccanica", "Idraulica"]
IT_ADJ = ["Lombarda", "Veneta", "Emiliana", "Padana", "Adriatica", "Brianzola", "Bresciana", "Piemontese",
          "Toscana", "Friulana", "Italiana", "Alpina", "Tirrenica", "Orobica"]
IT_ACR = ["OMB", "CMS", "FMT", "IMS", "SIMA", "OMR", "MTC", "ICM", "SAMP", "CEMA", "TECNA", "EUROMEC", "ITALMEC", "MECTRON"]
IT_FIRST = ["Marco", "Luca", "Giulia", "Francesca", "Andrea", "Paolo", "Laura", "Stefano", "Chiara", "Davide", "Elena",
            "Matteo", "Silvia", "Roberto", "Alessandro", "Federica", "Simone", "Valentina", "Giorgio", "Martina", "Nicola", "Sara"]
IT_ROLES = ["Responsabile acquisti", "Amministrazione", "Ufficio tecnico", "Titolare", "Logistica", "Contabilità fornitori"]
DE_LAST = ["Müller", "Schmidt", "Schneider", "Fischer", "Weber", "Wagner", "Becker", "Hoffmann", "Schäfer", "Koch", "Bauer",
           "Richter", "Klein", "Wolf", "Schröder", "Neumann", "Zimmermann", "Krüger", "Hartmann", "Lange"]
DE_FIRST = ["Thomas", "Michael", "Andreas", "Stefan", "Sabine", "Claudia", "Markus", "Julia", "Jürgen", "Katrin"]
DE_SECTORS = ["Maschinenbau", "Antriebstechnik", "Präzisionsteile", "Metallbau", "Hydraulik", "Kunststofftechnik",
              "Stahlbau", "Zerspanungstechnik", "Fördertechnik"]
DE_ROLES = ["Einkauf", "Buchhaltung", "Geschäftsführer", "Technik", "Logistik"]
NL_LAST = ["de Vries", "Jansen", "Bakker", "Visser", "Smit", "Meijer", "de Boer", "Mulder", "van Dijk", "Bos"]
NL_FIRST = ["Jan", "Pieter", "Sanne", "Eva", "Bram", "Lotte", "Daan", "Femke"]
NL_SECTORS = ["Techniek", "Metaalbewerking", "Industrie", "Aandrijftechniek", "Machinebouw"]
BE_LAST = ["Peeters", "Janssens", "Maes", "Jacobs", "Willems", "Claes", "Dubois", "Lambert"]
BE_FIRST = ["Wouter", "Lies", "Pieter", "Sophie", "Luc", "Nathalie"]
ES_LAST = ["García", "Martínez", "López", "Sánchez", "Fernández", "Gómez", "Ruiz", "Echeverría", "Navarro", "Ibáñez"]
ES_FIRST = ["Javier", "Carmen", "Miguel", "Lucía", "Pablo", "Elena", "Jorge", "Marta"]
FR_LAST = ["Martin", "Bernard", "Dubois", "Moreau", "Laurent", "Lefèvre", "Girard", "Roux", "Fournier"]
FR_FIRST = ["Pierre", "Sophie", "Nicolas", "Camille", "Julien", "Isabelle"]
FR_SECTORS = ["Mécanique", "Usinage", "Ateliers", "Fonderie"]
NL_ROLES = ["Inkoop", "Administratie", "Directeur", "Techniek"]
ES_ROLES = ["Compras", "Administración", "Gerente", "Oficina técnica"]
FR_ROLES = ["Achats", "Comptabilité", "Directeur", "Bureau d'études"]

IT_STREETS = ["Roma", "Garibaldi", "Mazzini", "Matteotti", "dell'Industria", "dell'Artigianato", "Galileo Galilei", "Enrico Fermi",
              "Alessandro Volta", "dei Mille", "Cavour", "del Lavoro", "Edison", "Marconi", "Leonardo da Vinci", "della Libertà",
              "Niccolò Tommaseo", "dell'Università", "Unità d'Italia", "Brennero", "Nazionale", "Torino", "Milano", "Bergamo",
              "dei Mestieri", "delle Industrie", "Primo Maggio", "XXV Aprile", "Kennedy", "Einstein", "Copernico", "Pacinotti",
              "San Francesco", "Sant'Antonio", "Isonzo", "Piave", "Vittorio Veneto", "Nicolò Copernico", "Pietro Nenni"]
IT_STREET2 = ["Zona Industriale", "Z.I. Nord", "Località Prato Grande", "Frazione San Martino", "Capannone 3", "Zona Artigianale"]
DE_STREETS = ["Industriestraße", "Hauptstraße", "Gewerbestraße", "Bahnhofstraße", "Siemensstraße", "Daimlerstraße",
              "Mühlenweg", "Robert-Bosch-Straße", "Max-Planck-Straße", "Carl-Benz-Straße"]
CH_STREETS = ["Industriestrasse", "Bahnhofstrasse", "Hardstrasse", "Werkstrasse"]
CHI_STREETS = ["Via Cantonale", "Via Industria", "Via Pian Scairolo", "Via Serafino Balestra"]
NL_STREETS = ["Industrieweg", "Kanaalweg", "Havenstraat", "Molenweg", "Edisonstraat", "Ampèrestraat"]
BE_STREETS = ["Industrielaan", "Nijverheidsstraat", "Kanaaldijk", "Brusselsesteenweg"]
BEF_STREETS = ["Rue de l'Industrie", "Avenue de la Gare", "Rue du Parc", "Boulevard Frère-Orban"]
ES_STREETS = ["Calle Mayor", "Calle de Alcalá", "Avenida de la Industria", "Calle Ibáñez de Bilbao", "Calle de la Constitución", "Camino de Ronda"]
FR_STREETS = ["rue de l'Industrie", "avenue Jean Jaurès", "rue des Frères Lumière", "boulevard de l'Europe", "rue de la République"]

LF_VARIANTS = {"S.r.l.": ["SRL", "Srl", "s.r.l.", "S.R.L.", "srl"], "S.p.A.": ["SPA", "Spa", "S.P.A.", "s.p.a."],
               "S.n.c.": ["SNC", "Snc", "s.n.c."], "S.a.s.": ["SAS", "Sas", "s.a.s."], "GmbH": ["GMBH", "Gmbh", "G.m.b.H."],
               "GmbH & Co. KG": ["GmbH & Co KG", "GmbH&Co.KG", "Gmbh & Co. Kg"], "AG": ["A.G."], "B.V.": ["BV", "B.V", "bv"],
               "NV": ["N.V."], "BV": ["B.V."], "S.L.": ["SL", "S.L", "SOCIEDAD LIMITADA"], "S.A.": ["SA", "S.A"],
               "SAS": ["S.A.S.", "Sas"], "SARL": ["S.A.R.L.", "Sarl"], "SA": ["S.A."], "SRL": ["S.R.L."]}

# =============================================================================
# Utilita'
# =============================================================================
MON = ["JAN", "FEB", "MAR", "APR", "MAY", "JUN", "JUL", "AUG", "SEP", "OCT", "NOV", "DEC"]


def rand_dt(a, b):
    d = a + dt.timedelta(seconds=rng.randint(0, max(0, int((b - a).total_seconds()))))
    return d.replace(microsecond=rng.randint(0, 999) * 1000)


def clamp(d):
    lim = TODAY - dt.timedelta(days=1)
    return d if d < lim else lim - dt.timedelta(days=rng.randint(0, 30))


def jul(d):
    return str((d.year - 1900) * 1000 + d.timetuple().tm_yday)


def fmt_date(s, d):
    if s in ("odoo_it", "suitecrm"):
        return d.strftime("%Y-%m-%d %H:%M:%S")
    if s == "exact_nl":
        return d.strftime("%Y-%m-%d %H:%M:%S.") + "%03d" % (d.microsecond // 1000)
    if s == "ebs_es":
        return "%02d-%s-%02d" % (d.day, MON[d.month - 1], d.year % 100)
    if s == "jde_de":
        return jul(d)
    raise ValueError(s)


def slug(s):
    s = unicodedata.normalize("NFKD", s).encode("ascii", "ignore").decode()
    return re.sub(r"[^a-z0-9]", "", s.lower())


def new_uuid():
    return str(uuid.UUID(int=rng.getrandbits(128), version=4))


def area_intl(cc, area):
    return area if cc == "IT" else area.lstrip("0")


def ph_intl(cc, area, sub):
    return "+%s %s %s" % (COUNTRY[cc]["pfx"], area_intl(cc, area), sub)


def phone_sub(cc, area):
    if cc == "DE":
        n = 7
    elif cc == "AT":
        n = 6 if len(area) > 2 else 7
    else:
        n = max(6, {"IT": 10, "NL": 10, "BE": 9, "ES": 9, "FR": 10, "CH": 10}[cc] - len(area))
    return str(rng.randint(2, 9)) + digits(n - 1)


def mobile(cc):
    if cc == "IT":
        return "+39 3%s %s" % (digits(2), digits(7))
    return "+%s %s %s" % (COUNTRY[cc]["pfx"], {"DE": "151", "AT": "664", "NL": "6", "BE": "475", "ES": "6" + digits(2),
                                               "FR": "6", "CH": "79"}[cc], digits(7 if cc != "NL" else 8))


def country_val(s, cc):
    if s == "odoo_it":
        return str(COUNTRY[cc]["odoo"])
    if s == "suitecrm":
        return COUNTRY[cc]["en"]
    return cc


def prov_val(s, cc, code, name):
    if s == "odoo_it":
        return str(STATE_ID[code]) if cc == "IT" else ""
    if s in ("ebs_es", "suitecrm"):
        return code if cc == "IT" else name
    return code


# =============================================================================
# Aziende
# =============================================================================
class Co:
    @property
    def name(self):
        return "%s %s" % (self.base, self.lf)


NAMES_USED = set()


def pick_city(cc, exclude=None):
    lst = [c for c in CITIES[cc] if c[0] != exclude]
    return rng.choices(lst, weights=[c[5] for c in lst])[0]


def make_street(cc, city):
    n = rng.randint(1, 180)
    if cc == "IT":
        t = rng.choices(["Via", "Viale", "Corso", "Strada"], weights=[12, 3, 1, 1])[0]
        suf = rng.choice(["/A", "/B", "/C"]) if rng.random() < 0.08 else ""
        sep = ", " if rng.random() < 0.4 else " "
        return "%s %s%s%d%s" % (t, rng.choice(IT_STREETS), sep, n, suf)
    if cc in ("DE", "AT"):
        return "%s %d" % (rng.choice(DE_STREETS), n)
    if cc == "CH":
        if city == "Lugano":
            return "%s %d" % (rng.choice(CHI_STREETS), n)
        return "%s %d" % (rng.choice(CH_STREETS), n)
    if cc == "NL":
        return "%s %d" % (rng.choice(NL_STREETS), n)
    if cc == "BE":
        if city in ("Liège", "Bruxelles"):
            return "%s %d" % (rng.choice(BEF_STREETS), n)
        return "%s %d" % (rng.choice(BE_STREETS), n)
    if cc == "ES":
        if rng.random() < 0.3:
            return "Polígono Industrial %s, nave %d" % (rng.choice(["Las Mercedes", "Can Roqueta", "Plaza", "Fuente del Jarro"]), rng.randint(1, 40))
        return "%s, %d" % (rng.choice(ES_STREETS), n)
    if cc == "FR":
        return "%d %s" % (n, rng.choice(FR_STREETS))
    raise ValueError(cc)


def make_address(cc, exclude_city=None):
    city, prov, provname, zips, area, _w = pick_city(cc, exclude_city)
    return dict(street=make_street(cc, city),
                street2=rng.choice(IT_STREET2) if cc == "IT" and rng.random() < 0.12 else "",
                zip=rng.choice(zips), city=city, prov=prov, prov_name=provname, area=area, sub=phone_sub(cc, area))


def gen_name(cc, city):
    if cc == "IT":
        p = rng.random()
        sn, sec = rng.choice(IT_SURNAMES), rng.choice(IT_SECTORS)
        if p < 0.28:
            base = "%s %s" % (sec, sn)
        elif p < 0.52:
            base = "%s %s" % (sn, sec)
        elif p < 0.60:
            base = "Officine %s" % sn
        elif p < 0.68:
            base = "F.lli %s" % sn
        elif p < 0.76:
            base = "%s & %s" % (sn, rng.choice(IT_SURNAMES))
        elif p < 0.88:
            base = "%s %s" % (rng.choice(IT_FEM), rng.choice(IT_ADJ))
        else:
            base = "%s %s" % (rng.choice(IT_ACR), sec)
        lf = rng.choices(["S.r.l.", "S.p.A.", "S.n.c.", "S.a.s."], weights=[62, 22, 9, 7])[0]
        if lf in ("S.n.c.", "S.a.s.") and "&" not in base and rng.random() < 0.5:
            base = "%s di %s %s & C." % (base, rng.choice(IT_FIRST), sn)
        return base, lf
    if cc in ("DE", "AT"):
        lf = rng.choice(["GmbH", "GmbH", "GmbH & Co. KG", "AG"]) if cc == "DE" else rng.choice(["GmbH", "GmbH", "AG"])
        return "%s %s" % (rng.choice(DE_LAST), rng.choice(DE_SECTORS)), lf
    if cc == "CH":
        if city == "Lugano":
            return "Officine %s" % rng.choice(IT_SURNAMES), "SA"
        return "%s %s" % (rng.choice(DE_LAST), rng.choice(["Mechanik", "Präzision", "Antriebe"])), "AG"
    if cc == "NL":
        return "%s %s" % (rng.choice(NL_LAST).replace("de ", "De ").replace("van ", "Van "), rng.choice(NL_SECTORS)), "B.V."
    if cc == "BE":
        if city in ("Liège", "Bruxelles"):
            return "%s %s" % (rng.choice(FR_SECTORS), rng.choice(BE_LAST)), rng.choice(["SA", "SRL"])
        return "%s %s" % (rng.choice(BE_LAST), rng.choice(["Metaal", "Techniek", "Industrie"])), rng.choice(["NV", "BV"])
    if cc == "ES":
        pat = rng.choice(["Talleres %s", "Mecanizados %s", "%s Componentes", "Industrias %s"])
        return pat % rng.choice(ES_LAST), rng.choice(["S.L.", "S.L.", "S.A."])
    if cc == "FR":
        if rng.random() < 0.5:
            return "%s %s" % (rng.choice(FR_SECTORS), rng.choice(FR_LAST)), rng.choice(["SAS", "SARL", "SA"])
        return "%s Industries" % rng.choice(FR_LAST), rng.choice(["SAS", "SA"])
    raise ValueError(cc)


def unique_name(cc, city):
    for _ in range(500):
        base, lf = gen_name(cc, city)
        if ("%s %s" % (base, lf)).lower() not in NAMES_USED:
            NAMES_USED.add(("%s %s" % (base, lf)).lower())
            return base, lf
    raise RuntimeError("nomi esauriti")


def person(cc):
    if cc == "IT" or (cc == "CH" and rng.random() < 0.5):
        f, l, roles = rng.choice(IT_FIRST), rng.choice(IT_SURNAMES), IT_ROLES
    elif cc in ("DE", "AT", "CH"):
        f, l, roles = rng.choice(DE_FIRST), rng.choice(DE_LAST), DE_ROLES
    elif cc == "NL":
        f, l, roles = rng.choice(NL_FIRST), rng.choice(NL_LAST), NL_ROLES
    elif cc == "BE":
        f, l, roles = rng.choice(BE_FIRST), rng.choice(BE_LAST), NL_ROLES
    elif cc == "ES":
        f, l, roles = rng.choice(ES_FIRST), rng.choice(ES_LAST), ES_ROLES
    else:
        f, l, roles = rng.choice(FR_FIRST), rng.choice(FR_LAST), FR_ROLES
    return dict(first=f, last=l, role=rng.choice(roles))


def make_company(az, cc, kind="customer"):
    c = Co()
    c.az, c.cc, c.kind = az, cc, kind
    c.__dict__.update(make_address(cc))
    c.base, c.lf = unique_name(cc, c.city)
    c.vat, c.vat_nat, c.cf = new_vat(cc, c.lf)
    c.created = rand_dt(dt.datetime(2006, 1, 1), dt.datetime(2026, 6, 30))
    c.status, c.parent, c.desc, c.systems = "active", None, [], []
    return c


def finalize(c):
    c.domain = slug(c.base)[:24] + "." + COUNTRY[c.cc]["tld"]
    boxes = {"IT": ["amministrazione", "commerciale", "ordini", "acquisti", "info"], "DE": ["info", "verkauf", "einkauf", "buchhaltung"],
             "AT": ["office", "einkauf", "buchhaltung"], "CH": ["info", "einkauf"], "NL": ["info", "inkoop", "administratie"],
             "BE": ["info", "aankoop", "boekhouding"], "ES": ["info", "compras", "administracion"], "FR": ["contact", "achats", "comptabilite"]}[c.cc]
    c.emails = ["info@" + c.domain if c.cc != "FR" else "contact@" + c.domain] + ["%s@%s" % (b, c.domain) for b in rng.sample(boxes, 2)]
    c.web = "www." + c.domain
    c.contacts = []
    for _ in range(rng.choice([0, 1, 1, 2, 2, 3])):
        p = person(c.cc)
        p["email"] = "%s.%s@%s" % (slug(p["first"])[0], slug(p["last"]), c.domain)
        p["sub"] = phone_sub(c.cc, c.area)
        p["mobile"] = mobile(c.cc) if rng.random() < 0.6 else ""
        c.contacts.append(p)


def similar_base(b):
    words = b.split()
    PL = {"Meccanica": "Meccaniche", "Fonderia": "Fonderie", "Carpenteria": "Carpenterie", "Torneria": "Tornerie",
          "Officine": "Officina", "Plastica": "Plastiche", "Lamiere": "Lamiera", "Componenti": "Componentistica",
          "Trasmissioni": "Trasmissione", "Stampaggi": "Stampaggio", "Cablaggi": "Cablaggio", "Ingranaggi": "Ingranaggio",
          "Pressofusioni": "Pressofusione", "Saldature": "Saldatura", "Guarnizioni": "Guarnizione", "Imballaggi": "Imballaggio",
          "Stampi": "Stampaggi", "Rettifiche": "Rettifica", "Valvole": "Valvolame", "Utensileria": "Utensilerie"}
    opts = []
    for i, w in enumerate(words):
        if w in PL:
            opts.append(" ".join(words[:i] + [PL[w]] + words[i + 1:]))
        if w in IT_SURNAMES:
            m = re.search(r"([bcdfglmnprstvz])\1", w)
            alt = w[:m.start()] + w[m.start() + 1:] if m else w[:-2] + w[-2] + w[-2:]
            opts.append(" ".join(words[:i] + [alt] + words[i + 1:]))
    opts.append("Nuova " + b)
    if len(words) == 2 and "&" not in b:
        opts.append(words[1] + " " + words[0])
    return rng.choice(opts)


# =============================================================================
# Tabelle e registri
# =============================================================================
class Table:
    def __init__(self, s, name, cols, key, client=False):
        self.sys, self.name, self.cols, self.key, self.client = s, name, cols, key, client
        self.rows, self.idx = [], {}

    def add(self, **kw):
        bad = set(kw) - set(self.cols)
        if bad:
            raise KeyError((self.name, bad))
        r = {c: ("" if kw.get(c) is None else str(kw.get(c))) for c in self.cols}
        k = "/".join(r[c] for c in self.key)
        if k in self.idx:
            raise ValueError(("chiave duplicata", self.name, k))
        self.rows.append(r)
        self.idx[k] = r
        return k


TABLES = {}
ENTS = {s: [] for s in SYSTEMS}
SAME = []        # stesso_cliente: (sys, tabella, chiave, az, categoria, descrizione)
CELLS = {}       # uid -> {concetto_breve: (sys, tabella, chiave, colonna)}
ERRS = []        # errori inseriti
USED = set()
ERR_COUNT = {}   # uid -> numero errori
CONCEPT_MAP = []  # (sys, tabella, colonna, concetto, descrizione)
FKS = []         # collegamenti


def table(s, name, cols, key, client=False):
    t = Table(s, name, cols, key, client)
    TABLES[(s, name)] = t
    return t


def concept(s, t, mapping):
    for col, val in mapping.items():
        c, d = (val, "") if isinstance(val, str) else val
        assert c in CONCEPTS, c
        CONCEPT_MAP.append((s, t, col, c, d))


def fk(s, t, cols, tt, tcols, desc="", cond=None, tf=None):
    FKS.append(dict(sys=s, table=t, cols=cols, ttable=tt, tcols=tcols, desc=desc, cond=cond, tf=tf))


def log_orphan(s, t, key, col, desc):
    ERRS.append(dict(sys=s, table=t, key=key, col=col, wrong=TABLES[(s, t)].idx[key][col], ref="",
                     cat="struttura", desc=desc))


CAT = {"dup": "doppione interno", "filiale": "filiale", "dest": "destinatario", "dest_child": "destinatario", "test": "prova"}


def reg_same(e, t, key):
    cat = CAT.get(e["kind"], "")
    if not cat and e["co"].kind == "prospect":
        cat = "potenziale cliente"
    SAME.append((e["sys"], t, key, e["az"], cat, "; ".join(e["desc"])))


UID = [0]


def new_ent(co, s, kind="main", **over):
    UID[0] += 1
    e = dict(uid=UID[0], sys=s, kind=kind, az=co.az, co=co, desc=list(co.desc),
             name=co.name, base=co.base, lf=co.lf, vat=co.vat, vat_nat=co.vat_nat, cf=co.cf,
             street=co.street, street2=co.street2, zip=co.zip, city=co.city, prov=co.prov, prov_name=co.prov_name,
             cc=co.cc, area=co.area, sub=co.sub, email=rng.choice(co.emails), web=co.web,
             created=sys_created(co, s), status="active", parent_az=co.parent, contacts=[], force_err=False,
             parent_uid=None, special=False)
    e.update(over)
    ENTS[s].append(e)
    return e


def clone_ent(b, kind, **over):
    UID[0] += 1
    e = dict(b)
    e.update(uid=UID[0], kind=kind, desc=[], contacts=[], force_err=False, special=True, parent_az=None)
    e.update(over)
    ENTS[e["sys"]].append(e)
    return e


def sys_created(co, s):
    g = GOLIVE[s]
    if co.created < g:
        d = g + dt.timedelta(days=rng.randint(0, 25), seconds=rng.randint(0, 36000))
    else:
        d = co.created + dt.timedelta(days=rng.randint(0, 90), seconds=rng.randint(0, 30000))
    return clamp(d.replace(microsecond=rng.randint(0, 999) * 1000))


# =============================================================================
# Costruzione delle aziende e dei record per sistema
# =============================================================================
def build():
    countries = ["IT"] * 198 + ["DE"] * 6 + ["AT"] * 3 + ["NL"] * 3 + ["BE"] * 2 + ["ES"] * 4 + ["FR"] * 2 + ["CH"] * 2
    rng.shuffle(countries)
    cos = [make_company("AZ-%04d" % (i + 1), cc) for i, cc in enumerate(countries)]
    primary = {"DE": "jde_de", "AT": "jde_de", "CH": "jde_de", "NL": "exact_nl", "BE": "exact_nl", "FR": "exact_nl", "ES": "ebs_es"}
    for c in cos:
        if c.cc == "IT":
            p = rng.choices(["odoo_it", "jde_de", "exact_nl", "ebs_es"], weights=[76, 8, 8, 8])[0]
        else:
            p = primary[c.cc]
        k = rng.choices([1, 2, 3], weights=[50, 35, 15])[0]
        syss = [p]
        w = {"suitecrm": 5, "odoo_it": 3, "jde_de": 2, "exact_nl": 2, "ebs_es": 2}
        while len(syss) < k:
            cand = [s for s in SYSTEMS if s not in syss]
            syss.append(rng.choices(cand, weights=[w[s] for s in cand])[0])
        c.systems = syss

    it_odoo = [c for c in cos if c.cc == "IT" and c.systems[0] == "odoo_it"]
    rng.shuffle(it_odoo)
    taken = set()

    # gruppi societari
    for size in [2, 3, 2, 4, 2]:
        h = next(c for c in it_odoo if c.az not in taken)
        taken.add(h.az)
        subs = [c for c in it_odoo if c.az not in taken][:size]
        sn = rng.choice([s for s in IT_SURNAMES if all(s not in n for n in NAMES_USED)] or IT_SURNAMES)
        NAMES_USED.discard(h.name.lower())
        h.base, h.lf = rng.choice(["Gruppo %s", "%s Holding", "%s Industrie"]) % sn, "S.p.A."
        NAMES_USED.add(h.name.lower())
        h.desc.append("capogruppo")
        secs = rng.sample(IT_SECTORS, size)
        for s_, sec in zip(subs, secs):
            taken.add(s_.az)
            NAMES_USED.discard(s_.name.lower())
            s_.base, s_.lf = "%s %s" % (sn, sec), rng.choice(["S.r.l.", "S.r.l.", "S.p.A."])
            NAMES_USED.add(s_.name.lower())
            s_.parent = h.az
            s_.desc.append("controllata di %s" % h.az)
            if not set(s_.systems) & set(h.systems):
                s_.systems = s_.systems[:2] + ["odoo_it"] if "odoo_it" not in s_.systems else s_.systems

    # aziende diverse con nome quasi uguale
    for _ in range(8):
        a = next(c for c in it_odoo if c.az not in taken)
        b = next(c for c in it_odoo if c.az not in taken and c is not a and c.city != a.city)
        taken.update([a.az, b.az])
        NAMES_USED.discard(b.name.lower())
        for _try in range(50):
            if rng.random() < 0.25:
                nb, nlf = a.base, rng.choice([x for x in ["S.r.l.", "S.n.c.", "S.p.A.", "S.a.s."] if x != a.lf])
            else:
                nb, nlf = similar_base(a.base), a.lf
            if ("%s %s" % (nb, nlf)).lower() not in NAMES_USED:
                break
        b.base, b.lf = nb, nlf
        NAMES_USED.add(b.name.lower())
        a.desc.append("nome simile a %s (azienda diversa)" % b.az)
        b.desc.append("nome simile a %s (azienda diversa)" % a.az)

    # clienti bloccati o inattivi
    pool = [c for c in cos if c.az not in taken]
    rng.shuffle(pool)
    for c in pool[:9]:
        c.status = "blocked"
    for c in pool[9:16]:
        c.status = "inactive"

    # potenziali clienti (solo CRM)
    prospects = []
    for j in range(15):
        cc = "IT" if rng.random() < 0.9 else rng.choice(["DE", "FR", "AT"])
        c = make_company("AZ-%04d" % (len(cos) + j + 1), cc, "prospect")
        c.created = rand_dt(dt.datetime(2019, 1, 1), dt.datetime(2026, 8, 31))
        c.systems = ["suitecrm"]
        prospects.append(c)
    for c in cos + prospects:
        finalize(c)

    # record principali per sistema
    for c in cos + prospects:
        for s in c.systems:
            st = c.status if (s == c.systems[0] or rng.random() < 0.5) else "active"
            e = new_ent(c, s, contacts=rng.sample(c.contacts, rng.randint(0, len(c.contacts))), status=st)
            if st == "blocked":
                e["desc"].append("cliente bloccato")
            elif st == "inactive":
                e["desc"].append("cliente inattivo")

    def pick(s, n, cond=lambda e: True):
        cands = [e for e in ENTS[s] if e["kind"] == "main" and e["co"].kind == "customer" and not e["special"]
                 and e["status"] == "active" and cond(e)]
        rng.shuffle(cands)
        for e in cands[:n]:
            e["special"] = True
        return cands[:n]

    # doppioni nello stesso sistema
    for s, n in [("odoo_it", 5), ("suitecrm", 3), ("jde_de", 2), ("exact_nl", 1), ("ebs_es", 1)]:
        for e in pick(s, n):
            d = clone_ent(e, "dup", created=clamp(e["created"] + dt.timedelta(days=rng.randint(30, 1500))),
                          email=rng.choice(e["co"].emails), force_err=True, dup_of=e["uid"])
            if rng.random() < 0.4:
                d["sub"] = phone_sub(d["cc"], d["area"])
    # filiali (stessa partita IVA, indirizzo diverso)
    for s, n in [("odoo_it", 4), ("jde_de", 2), ("exact_nl", 1), ("ebs_es", 1), ("suitecrm", 2)]:
        for e in pick(s, n):
            a = make_address(e["cc"], e["city"])
            nm = rng.choice([e["name"], "%s - Stabilimento di %s" % (e["name"], a["city"]),
                             "%s Unità locale %s" % (e["name"], a["city"]), "%s (filiale %s)" % (e["name"], a["city"])])
            f = clone_ent(e, "filiale", name=nm, email=rng.choice(e["co"].emails),
                          created=clamp(e["created"] + dt.timedelta(days=rng.randint(10, 2000))), **a)
            f["desc"].append("sede secondaria a %s" % a["city"])
    # destinatari merce
    for e in pick("odoo_it", 10):
        a = make_address(e["cc"]) if rng.random() < 0.6 else dict(street=make_street(e["cc"], e["city"]), street2="", zip=e["zip"],
                                                                     city=e["city"], prov=e["prov"], prov_name=e["prov_name"],
                                                                     area=e["area"], sub=phone_sub(e["cc"], e["area"]))
        nm = rng.choice(["Magazzino", "Magazzino %s" % a["city"], "Stabilimento di %s" % a["city"], "", "Consegna merci", "Ricevimento merci"])
        clone_ent(e, "dest_child", name=nm, email="", parent_uid=e["uid"],
                  created=clamp(e["created"] + dt.timedelta(days=rng.randint(1, 900))), **a)
    for s, n, word in [("odoo_it", 2, "Magazzino"), ("jde_de", 4, "Lager"), ("exact_nl", 2, "Afleveradres"), ("ebs_es", 2, "Almacén")]:
        for e in pick(s, n):
            a = make_address(e["cc"])
            clone_ent(e, "dest", name="%s - %s %s" % (e["name"], word, a["city"]), vat="" if rng.random() < 0.7 else e["vat"],
                      cf="", email="", parent_uid=e["uid"], web="",
                      created=clamp(e["created"] + dt.timedelta(days=rng.randint(1, 900))), **a)
    # record di prova
    tests = [("odoo_it", "CLIENTE DI PROVA", "", "IT"), ("odoo_it", "Test Fatturazione Elettronica S.r.l.", "IT12345678901", "IT"),
             ("odoo_it", "XXX NON USARE", "IT00000000000", "IT"), ("jde_de", "TEST CUSTOMER DO NOT USE", "DE000000000", "DE"),
             ("exact_nl", "Testklant B.V.", "NL000000000B00", "NL"), ("ebs_es", "PRUEBA CLIENTE TEST", "ESB00000000", "ES"),
             ("suitecrm", "Test Account", "", "IT"), ("suitecrm", "prova prova", "12345678901", "IT")]
    for i, (s, nm, vat, cc) in enumerate(tests):
        t = Co()
        t.az, t.cc, t.kind, t.desc, t.parent = "AZ-9%03d" % (i + 1), cc, "test", [], None
        ce = CITIES[cc][0]
        t.base, t.lf = nm, ""
        t.vat, t.vat_nat, t.cf = vat, "", ""
        t.street, t.street2 = {"IT": "Via Prova 1", "DE": "Teststraße 1", "NL": "Teststraat 1", "ES": "Calle Prueba, 1"}[cc], ""
        t.zip, t.city, t.prov, t.prov_name, t.area = ce[3][0], ce[0], ce[1], ce[2], ce[4]
        t.sub = "0000000"
        t.emails = [rng.choice(["test@test.it", "prova@example.com", "noreply@ferraboli.example"])]
        t.web, t.created = "", rand_dt(GOLIVE[s], TODAY - dt.timedelta(days=30))
        e = new_ent(t, s, "test", name=nm)
        e["desc"] = ["record di prova da escludere"]
    return cos, prospects


def make_noise(cc, kind):
    c = make_company(None, cc, kind)
    finalize(c)
    return c


# =============================================================================
# odoo_it - Odoo 16
# =============================================================================
def render_odoo():
    S = "odoo_it"
    ents = ENTS[S]
    tc = table(S, "res_country", ["id", "name", "code", "phone_code"], ["id"])
    rows = [(m["odoo"], m["en"], m["it"], cc, m["pfx"]) for cc, m in COUNTRY.items()] + EXTRA_COUNTRIES
    for oid, en, it, cc, pfx in sorted(rows):
        tc.add(id=oid, name=json.dumps({"en_US": en, "it_IT": it}, ensure_ascii=False), code=cc, phone_code=pfx)
    ts = table(S, "res_country_state", ["id", "country_id", "name", "code"], ["id"])
    for code in sorted(IT_PROVS):
        ts.add(id=STATE_ID[code], country_id=109, name=IT_PROVS[code], code=code)

    rp = table(S, "res_partner", ["id", "name", "company_id", "create_date", "write_date", "type", "parent_id",
                                  "commercial_partner_id", "is_company", "ref", "vat", "l10n_it_codice_fiscale",
                                  "l10n_it_pa_index", "street", "street2", "zip", "city", "state_id", "country_id",
                                  "phone", "mobile", "email", "website", "lang", "active", "customer_rank",
                                  "supplier_rank", "sale_warn", "sale_warn_msg", "comment"], ["id"], client=True)
    concept(S, "res_partner", {"id": "codice cliente", "ref": "codice cliente", "name": "ragione sociale", "vat": "partita_iva",
                               "l10n_it_codice_fiscale": "codice_fiscale", "street": "indirizzo", "street2": "indirizzo",
                               "zip": "cap", "city": "citta", "state_id": "provincia", "country_id": "paese",
                               "phone": "telefono", "mobile": "telefono", "email": "email", "website": "sito_web",
                               "active": "stato_cliente", "sale_warn": "stato_cliente", "is_company": "tipo_anagrafica",
                               "type": "tipo_anagrafica", "customer_rank": "tipo_anagrafica", "supplier_rank": "tipo_anagrafica",
                               "create_date": "data_creazione"})
    fk(S, "res_partner", ["parent_id"], "res_partner", ["id"], "per type delivery/contact/invoice con is_company=f: azienda a cui appartiene l'indirizzo o la persona; per is_company=t: società controllante")
    fk(S, "res_partner", ["commercial_partner_id"], "res_partner", ["id"], "entità commerciale (l'azienda) a cui fanno capo indirizzi e contatti; per le aziende è il record stesso")
    fk(S, "res_partner", ["country_id"], "res_country", ["id"])
    fk(S, "res_partner", ["state_id"], "res_country_state", ["id"], "valorizzato solo per indirizzi italiani (provincia)")
    fk(S, "res_country_state", ["country_id"], "res_country", ["id"])

    own = [(1, "Ferraboli Industrie S.p.A.", "1", "t", "", "IT02716340983"),
           (2, "OdooBot", "", "f", "", ""), (3, "Amministratore", "1", "f", "1", ""),
           (7, "Ferraboli Componenti S.r.l.", "2", "t", "", "IT03561270171")]
    for pid, nm, comp, isc, par, vat in own:
        rp.add(id=pid, name=nm, company_id=comp, create_date="2017-01-09 07:30:12", write_date="2025-11-03 10:12:44",
               type="contact", parent_id=par, commercial_partner_id=par or pid, is_company=isc, vat=vat,
               l10n_it_codice_fiscale=vat[2:] if vat else "", street="Via dell'Industria 21" if isc == "t" else "",
               zip="25065" if isc == "t" else "", city="Lumezzane" if isc == "t" else "", state_id=STATE_ID["BS"] if isc == "t" else "",
               country_id=109 if isc == "t" else "", email="info@ferraboli.example" if isc == "t" else "", lang="it_IT",
               active="f" if pid == 2 else "t", customer_rank=0, supplier_rank=0, sale_warn="no-message")

    items = []
    for e in ents:
        items.append((e["created"], "ent", e))
        for p in e["contacts"]:
            items.append((clamp(e["created"] + dt.timedelta(days=rng.randint(0, 600), seconds=60)), "person", (e, p)))
    suppliers = [make_noise("IT" if rng.random() < 0.85 else rng.choice(["DE", "FR", "ES"]), "supplier") for _ in range(18)]
    for sp in suppliers:
        items.append((max(sp.created, GOLIVE[S]), "supplier", sp))
    items.sort(key=lambda x: x[0])
    ID, pid = {}, 9
    for _, typ, obj in items:
        pid += 1 if rng.random() < 0.8 else rng.randint(2, 4)
        ID[id(obj) if typ != "ent" else obj["uid"]] = pid
    # società Odoo (company_id): vuoto = condiviso fra le due società
    for e in ents:
        if e["kind"] == "dest_child":
            continue
        e["ocomp"] = rng.choice(["", "", "", "", "1", "1", "2"])
    for e in ents:
        if e["kind"] == "dup":
            m = next(x for x in ents if x["uid"] == e["dup_of"])
            e["ocomp"] = "2" if m["ocomp"] == "1" else ("1" if m["ocomp"] == "2" else rng.choice(["", "1"]))
            if rng.random() < 0.4:
                e["status"] = "inactive"
                e["desc"].append("archiviato")
        if e["kind"] == "dest_child":
            e["ocomp"] = next(x for x in ents if x["uid"] == e["parent_uid"])["ocomp"]
    holding = {e["az"]: e for e in ents if e["kind"] == "main"}

    def web(w):
        return "" if not w else rng.choice(["https://", "http://", "https://", ""]) + w

    for created, typ, obj in items:
        if typ == "ent":
            e = obj
            i = ID[e["uid"]]
            child = e["kind"] == "dest_child"
            parent = ""
            if child:
                parent = ID[e["parent_uid"]]
            elif e["kind"] == "main" and e["parent_az"] and e["parent_az"] in holding:
                parent = ID[holding[e["parent_az"]]["uid"]]
            it = e["cc"] == "IT"
            key = rp.add(id=i, name=e["name"], company_id=e["ocomp"], create_date=fmt_date(S, created),
                         write_date=fmt_date(S, rand_dt(created, TODAY)), type="delivery" if child else "contact",
                         parent_id=parent, commercial_partner_id=ID[e["parent_uid"]] if child else i,
                         is_company="f" if child else "t",
                         ref="" if child or rng.random() < 0.45 else "C%05d" % rng.randint(100, 99999),
                         vat=e["vat"], l10n_it_codice_fiscale=e["cf"] if it else "",
                         l10n_it_pa_index=("".join(rng.choice("ABCDEFGHJKLMNPQRSTUVWXYZ0123456789") for _ in range(7))
                                           if it and not child and rng.random() < 0.5 else ""),
                         street=e["street"], street2=e["street2"], zip=e["zip"], city=e["city"],
                         state_id=prov_val(S, e["cc"], e["prov"], e["prov_name"]), country_id=country_val(S, e["cc"]),
                         phone=ph_intl(e["cc"], e["area"], e["sub"]) if e["sub"] and (not child or rng.random() < 0.5) else "",
                         mobile=mobile(e["cc"]) if not child and rng.random() < 0.15 else "",
                         email=e["email"], website=web(e["web"]) if not child else "",
                         lang=COUNTRY[e["cc"]]["lang"], active="f" if e["status"] == "inactive" else "t",
                         customer_rank=0 if e["kind"] in ("dest_child", "dest") else rng.randint(1, 60),
                         supplier_rank=rng.randint(1, 12) if e["kind"] == "main" and rng.random() < 0.08 else 0,
                         sale_warn="block" if e["status"] == "blocked" else "no-message",
                         sale_warn_msg="Cliente bloccato per insoluti: contattare l'amministrazione" if e["status"] == "blocked" else "",
                         comment="")
            e["oid"] = i
            reg_same(e, "res_partner", key)
            c = dict(name="name", vat="vat", street="street", zip="zip", city="city", country="country_id",
                     phone="phone", email="email", created="create_date")
            if it:
                c.update(cf="l10n_it_codice_fiscale", prov="state_id")
            CELLS[e["uid"]] = {k: (S, "res_partner", key, v) for k, v in c.items()}
        elif typ == "person":
            e, p = obj
            par = ID[e["uid"]]
            rp.add(id=ID[id(obj)], name="%s %s" % (p["first"], p["last"]), company_id=e["ocomp"], create_date=fmt_date(S, created),
                   write_date=fmt_date(S, rand_dt(created, TODAY)), type="contact", parent_id=par, commercial_partner_id=par,
                   is_company="f", vat=e["vat"], street=e["street"], street2=e["street2"], zip=e["zip"], city=e["city"],
                   state_id=prov_val(S, e["cc"], e["prov"], e["prov_name"]), country_id=country_val(S, e["cc"]),
                   phone=ph_intl(e["cc"], e["area"], p["sub"]) if rng.random() < 0.6 else "", mobile=p["mobile"],
                   email=p["email"], lang=COUNTRY[e["cc"]]["lang"], active="t", customer_rank=0, supplier_rank=0,
                   sale_warn="no-message", comment=p["role"])
        else:
            sp = obj
            rp.add(id=ID[id(obj)], name=sp.name, company_id=rng.choice(["", "1", "2"]), create_date=fmt_date(S, created),
                   write_date=fmt_date(S, rand_dt(created, TODAY)), type="contact", commercial_partner_id=ID[id(obj)],
                   is_company="t", vat=sp.vat, l10n_it_codice_fiscale=sp.cf if sp.cc == "IT" else "",
                   street=sp.street, zip=sp.zip, city=sp.city, state_id=prov_val(S, sp.cc, sp.prov, sp.prov_name),
                   country_id=country_val(S, sp.cc), phone=ph_intl(sp.cc, sp.area, sp.sub), email=sp.emails[0],
                   website="https://" + sp.web, lang=COUNTRY[sp.cc]["lang"], active="t", customer_rank=0,
                   supplier_rank=rng.randint(1, 80), sale_warn="no-message")
    max_id = max(int(k) for k in rp.idx)

    # ir_property: attributi per societa' in forma chiave-valore
    ip = table(S, "ir_property", ["id", "name", "res_id", "company_id", "fields_id", "type", "value_reference",
                                  "value_float", "value_text"], ["id"], client=True)
    concept(S, "ir_property", {"res_id": ("codice cliente", "nel formato 'res.partner,<id>'")})
    fk(S, "ir_property", ["res_id"], "res_partner", ["id"],
       "res_id nel formato 'res.partner,<id>' solo per le righe con name che inizia con 'property_' riferite a res.partner; res_id vuoto = valore predefinito della società (company_id)",
       cond=lambda r: r["res_id"].startswith("res.partner,"), tf=lambda v: [v[0].split(",", 1)[1]])
    n = 0
    for nm, fid, ref, comp in [("property_account_receivable_id", 2451, "account.account,121", 1),
                               ("property_account_payable_id", 2453, "account.account,170", 1),
                               ("property_account_receivable_id", 2451, "account.account,412", 2),
                               ("property_account_payable_id", 2453, "account.account,455", 2),
                               ("property_product_pricelist", 2463, "product.pricelist,1", 1)]:
        n += 1
        ip.add(id=n, name=nm, res_id="", company_id=comp, fields_id=fid, type="many2one", value_reference=ref)
    for e in sorted(ents, key=lambda x: x["oid"]):
        if e["kind"] in ("dest_child", "test"):
            continue
        comps = [e["ocomp"]] if e["ocomp"] else (["1", "2"] if rng.random() < 0.3 else ["1"])
        for comp in comps:
            if rng.random() < 0.65:
                n += 1
                ip.add(id=n, name="property_payment_term_id", res_id="res.partner,%d" % e["oid"], company_id=comp,
                       fields_id=2457, type="many2one", value_reference="account.payment.term,%d" % rng.randint(1, 9))
            if rng.random() < 0.35:
                n += 1
                ip.add(id=n, name="property_product_pricelist", res_id="res.partner,%d" % e["oid"], company_id=comp,
                       fields_id=2463, type="many2one", value_reference="product.pricelist,%d" % rng.randint(1, 4))
            if e["cc"] != "IT":
                n += 1
                ip.add(id=n, name="property_account_position_id", res_id="res.partner,%d" % e["oid"], company_id=comp,
                       fields_id=2449, type="many2one", value_reference="account.fiscal.position,%d" % (2 if e["cc"] != "CH" else 3))
    for k in range(2):
        n += 1
        key = ip.add(id=n, name="property_payment_term_id", res_id="res.partner,%d" % (max_id + 37 + k * 11), company_id=1,
                     fields_id=2457, type="many2one", value_reference="account.payment.term,%d" % rng.randint(1, 9))
        log_orphan(S, "ir_property", key, "res_id", "riga orfana: res_id punta a un partner inesistente")

    bk = table(S, "res_partner_bank", ["id", "partner_id", "acc_number", "acc_holder_name", "company_id", "active"], ["id"], client=True)
    concept(S, "res_partner_bank", {"partner_id": "codice cliente"})
    fk(S, "res_partner_bank", ["partner_id"], "res_partner", ["id"])
    n = 0
    for e in sorted(ents, key=lambda x: x["oid"]):
        if e["kind"] in ("main", "dup") and e["cc"] == "IT" and rng.random() < 0.3:
            n += 1
            bk.add(id=n, partner_id=e["oid"], acc_number=iban_it(), acc_holder_name=e["name"] if rng.random() < 0.4 else "",
                   company_id=e["ocomp"] or "1", active="t")
    for k in range(2):
        n += 1
        key = bk.add(id=n, partner_id=max_id + 52 + k * 9, acc_number=iban_it(), company_id="1", active="t")
        log_orphan(S, "res_partner_bank", key, "partner_id", "riga orfana: partner_id inesistente")

    pt = table(S, "product_template", ["id", "name", "default_code", "type", "list_price", "sale_ok", "active", "create_date"], ["id"])
    for i, (it_, en, code, price) in enumerate(PRODUCTS, 1):
        pt.add(id=i, name=json.dumps({"en_US": en, "it_IT": it_}, ensure_ascii=False), default_code=code,
               type="service" if code.startswith("SRV") else "product", list_price="%.2f" % price, sale_ok="t",
               active="t" if rng.random() < 0.92 else "f", create_date=fmt_date(S, rand_dt(GOLIVE[S], TODAY)))
    so = table(S, "sale_order", ["id", "name", "partner_id", "partner_invoice_id", "partner_shipping_id", "company_id",
                                 "date_order", "state", "amount_total", "currency_id"], ["id"])
    buyers = [e for e in ents if e["kind"] in ("main", "filiale", "dup") and e["status"] == "active"]
    dests = {}
    for e in ents:
        if e["kind"] in ("dest_child", "dest"):
            dests.setdefault(e["parent_uid"], []).append(e)
    orders = sorted((rand_dt(max(b["created"], GOLIVE[S]), TODAY), b) for b in rng.sample(buyers, 90) for _ in [0])
    for i, (d, b) in enumerate(orders, 1):
        ship = rng.choice(dests[b["uid"]])["oid"] if b["uid"] in dests else b["oid"]
        so.add(id=i, name="S%05d" % (i + 120), partner_id=b["oid"], partner_invoice_id=b["oid"], partner_shipping_id=ship,
               company_id=b["ocomp"] or "1", date_order=fmt_date(S, d), state=rng.choice(["sale", "sale", "done", "draft", "cancel"]),
               amount_total="%.2f" % rng.uniform(300, 48000), currency_id=1)


PRODUCTS = [("Flangia DN50", "Flange DN50", "FR-1001", 38.5), ("Albero di trasmissione 40mm", "Drive shaft 40mm", "FR-1002", 212.0),
            ("Riduttore epicicloidale PL90", "Planetary gearbox PL90", "FR-2001", 1280.0), ("Motoriduttore MR63", "Gear motor MR63", "FR-2002", 640.0),
            ("Giunto elastico GE28", "Flexible coupling GE28", "FR-3001", 74.9), ("Cuscinetto a sfere 6204", "Ball bearing 6204", "FR-3002", 6.2),
            ("Pignone Z17", "Pinion Z17", "FR-3003", 41.0), ("Corona dentata Z60", "Ring gear Z60", "FR-3004", 188.0),
            ("Supporto motore SM100", "Motor bracket SM100", "FR-4001", 59.0), ("Kit guarnizioni PL90", "Seal kit PL90", "FR-4002", 22.5),
            ("Carter riduttore", "Gearbox housing", "FR-4003", 315.0), ("Albero cavo 30mm", "Hollow shaft 30mm", "FR-1003", 156.0),
            ("Freno elettromagnetico FE20", "Electromagnetic brake FE20", "FR-5001", 420.0),
            ("Encoder incrementale 1024", "Incremental encoder 1024", "FR-5002", 265.0), ("Riduttore a vite senza fine RV50", "Worm gearbox RV50", "FR-2003", 390.0),
            ("Puleggia dentata HTD", "Timing pulley HTD", "FR-3005", 33.0), ("Cinghia dentata HTD 8M", "Timing belt HTD 8M", "FR-3006", 27.8),
            ("Servizio di assistenza tecnica", "Technical service", "SRV-001", 85.0), ("Collaudo in sede cliente", "On-site testing", "SRV-002", 640.0),
            ("Spese di trasporto", "Shipping costs", "SRV-003", 45.0)]


# =============================================================================
# jde_de - JD Edwards EnterpriseOne
# =============================================================================
def render_jde():
    S = "jde_de"
    ents = ENTS[S]
    ab = table(S, "F0101", ["ABAN8", "ABALKY", "ABTAX", "ABTX2", "ABALPH", "ABMCU", "ABAT1", "ABAC01", "ABAC02",
                            "ABTAXC", "ABPA8", "ABUSER", "ABUPMJ"], ["ABAN8"], client=True)
    ad = table(S, "F0116", ["ALAN8", "ALEFTB", "ALADD1", "ALADD2", "ALADD3", "ALADD4", "ALADDZ", "ALCTY1", "ALCOUN",
                            "ALADDS", "ALCTR"], ["ALAN8", "ALEFTB"], client=True)
    ww = table(S, "F0111", ["WWAN8", "WWIDLN", "WWMLNM", "WWALPH", "WWGNNM", "WWSRNM", "WWTYC"], ["WWAN8", "WWIDLN"], client=True)
    ph = table(S, "F0115", ["WPAN8", "WPIDLN", "WPRCK7", "WPPHTP", "WPAR1", "WPPH1"], ["WPAN8", "WPIDLN", "WPRCK7"], client=True)
    em = table(S, "F01151", ["EAAN8", "EAIDLN", "EARCK7", "EAETP", "EAEMAL"], ["EAAN8", "EAIDLN", "EARCK7"], client=True)
    cm = table(S, "F03012", ["AIAN8", "AICO", "AICRCD", "AITRAR", "AIACL", "AIHDAR", "AIDAOJ", "AITXA1"], ["AIAN8", "AICO"], client=True)
    concept(S, "F0101", {"ABAN8": "codice cliente", "ABALKY": "codice cliente", "ABTAX": "partita_iva", "ABTX2": "codice_fiscale",
                         "ABALPH": "ragione sociale", "ABAT1": "tipo_anagrafica", "ABTAXC": "tipo_anagrafica"})
    concept(S, "F0116", {"ALAN8": "codice cliente", "ALADD1": "indirizzo", "ALADD2": "indirizzo", "ALADD3": "indirizzo",
                         "ALADD4": "indirizzo", "ALADDZ": "cap", "ALCTY1": "citta", "ALADDS": "provincia", "ALCTR": "paese"})
    concept(S, "F0111", {"WWAN8": "codice cliente", "WWMLNM": ("ragione sociale", "solo nella riga WWIDLN=0; nelle altre righe è il nome della persona")})
    concept(S, "F0115", {"WPAN8": "codice cliente", "WPAR1": "telefono", "WPPH1": "telefono"})
    concept(S, "F01151", {"EAAN8": "codice cliente", "EAEMAL": "email"})
    concept(S, "F03012", {"AIAN8": "codice cliente", "AIHDAR": "stato_cliente", "AIDAOJ": "data_creazione"})
    fk(S, "F0116", ["ALAN8"], "F0101", ["ABAN8"], "più righe per indirizzo con data di validità ALEFTB (data giuliana JDE CYYDDD): vale la riga con ALEFTB più recente")
    fk(S, "F0111", ["WWAN8"], "F0101", ["ABAN8"], "WWIDLN=0 è l'anagrafica stessa, WWIDLN>0 sono le persone di contatto")
    fk(S, "F0115", ["WPAN8"], "F0101", ["ABAN8"], "WPIDLN=0 telefono dell'azienda; WPPHTP vuoto=ufficio, FAX, CAR=cellulare")
    fk(S, "F0115", ["WPAN8", "WPIDLN"], "F0111", ["WWAN8", "WWIDLN"])
    fk(S, "F01151", ["EAAN8"], "F0101", ["ABAN8"], "EAIDLN=0 email dell'azienda")
    fk(S, "F01151", ["EAAN8", "EAIDLN"], "F0111", ["WWAN8", "WWIDLN"])
    fk(S, "F03012", ["AIAN8"], "F0101", ["ABAN8"], "una riga per società (AICO 00100 Germania, 00200 Austria)")
    fk(S, "F0101", ["ABPA8"], "F0101", ["ABAN8"], "capogruppo o cliente principale (per i destinatari merce); uguale ad ABAN8 se non c'è")

    items = [(e["created"], "ent", e) for e in ents]
    for _ in range(15):
        sp = make_noise(rng.choice(["DE", "DE", "AT", "IT"]), "supplier")
        items.append((max(sp.created, GOLIVE[S]), "sup", sp))
    for _ in range(6):
        p = person("DE")
        p["addr"] = make_address("DE")
        items.append((rand_dt(GOLIVE[S], TODAY), "emp", p))
    items.sort(key=lambda x: x[0])
    an8, ID = 1000, {}
    for _, typ, obj in items:
        an8 += rng.randint(1, 9)
        ID[obj["uid"] if typ == "ent" else id(obj)] = an8
    by_az = {e["az"]: e for e in ents if e["kind"] == "main"}
    users = ["JDE", "KHUBER", "SMEIER", "ABAUER", "MLEITNER"]

    def addr_rows(a8, cr, street, street2, zp, city, prov, cc):
        if rng.random() < 0.2:
            old = make_address(cc, None)
            ad.add(ALAN8=a8, ALEFTB=jul(cr), ALADD1=old["street"], ALADD2="", ALADDZ=old["zip"], ALCTY1=old["city"],
                   ALADDS=old["prov"], ALCTR=cc)
            cur = clamp(cr + dt.timedelta(days=rng.randint(200, 2500)))
        else:
            cur = cr
        return ad.add(ALAN8=a8, ALEFTB=jul(cur), ALADD1=street, ALADD2=street2, ALADDZ=zp, ALCTY1=city, ALADDS=prov, ALCTR=cc)

    def wpar(cc, area):
        return area if cc == "DE" else "+%s %s" % (COUNTRY[cc]["pfx"], area_intl(cc, area))

    for created, typ, obj in items:
        if typ == "ent":
            e = obj
            a8 = ID[e["uid"]]
            e["an8"] = a8
            co_codes = ["00200"] if e["cc"] == "AT" else (["00100", "00200"] if rng.random() < 0.15 else ["00100"])
            pa8 = a8
            if e["kind"] == "dest":
                pa8 = ID[e["parent_uid"]]
            elif e["kind"] == "main" and e["parent_az"] in by_az:
                pa8 = ID[by_az[e["parent_az"]]["uid"]]
            k = ab.add(ABAN8=a8, ABALKY="" if rng.random() < 0.85 else "K%06d" % rng.randint(1000, 999999), ABTAX=e["vat"],
                       ABTX2=e["cf"] if e["cc"] == "IT" else "", ABALPH=e["name"],
                       ABMCU=("1000" if co_codes[0] == "00100" else "2000").rjust(12), ABAT1="C",
                       ABAC01={"IT": "ITA", "DE": "DEU", "AT": "AUT"}.get(e["cc"], "EXP"), ABAC02=rng.choice(["MAS", "AUT", "OEM", "HAN"]),
                       ABTAXC="C", ABPA8=pa8, ABUSER=rng.choice(users), ABUPMJ=jul(rand_dt(created, TODAY)))
            ka = addr_rows(a8, created, e["street"], e["street2"], e["zip"], e["city"], e["prov"], e["cc"])
            ww.add(WWAN8=a8, WWIDLN=0, WWMLNM=e["name"], WWALPH=e["name"])
            kp = ph.add(WPAN8=a8, WPIDLN=0, WPRCK7=1, WPPHTP="", WPAR1=wpar(e["cc"], e["area"]), WPPH1=e["sub"])
            if rng.random() < 0.35:
                ph.add(WPAN8=a8, WPIDLN=0, WPRCK7=2, WPPHTP="FAX", WPAR1=wpar(e["cc"], e["area"]), WPPH1=phone_sub(e["cc"], e["area"]))
            ke = em.add(EAAN8=a8, EAIDLN=0, EARCK7=1, EAETP="E", EAEMAL=e["email"]) if e["email"] else None
            for i, p in enumerate(e["contacts"], 1):
                ww.add(WWAN8=a8, WWIDLN=i, WWMLNM="%s %s" % (p["first"], p["last"]), WWALPH="%s, %s" % (p["last"], p["first"]),
                       WWGNNM=p["first"], WWSRNM=p["last"], WWTYC="C")
                ph.add(WPAN8=a8, WPIDLN=i, WPRCK7=1, WPPHTP="", WPAR1=wpar(e["cc"], e["area"]), WPPH1=p["sub"])
                if p["mobile"]:
                    ph.add(WPAN8=a8, WPIDLN=i, WPRCK7=2, WPPHTP="CAR", WPAR1="", WPPH1=p["mobile"])
                em.add(EAAN8=a8, EAIDLN=i, EARCK7=1, EAETP="E", EAEMAL=p["email"])
            kc = None
            for j, aico in enumerate(co_codes):
                d = created if j == 0 else clamp(created + dt.timedelta(days=rng.randint(100, 1500)))
                kk = cm.add(AIAN8=a8, AICO=aico, AICRCD="CHF" if e["cc"] == "CH" else "EUR", AITRAR=rng.choice(["N30", "N60", "N90", "D10", "N45"]),
                            AIACL=rng.choice([0, 5000, 10000, 25000, 50000, 100000]),
                            AIHDAR={"blocked": "C", "inactive": "I"}.get(e["status"], ""), AIDAOJ=jul(d),
                            AITXA1={"DE": "DE19", "AT": "AT20", "CH": "CH0"}.get(e["cc"], "EU0"))
                kc = kc or kk
            reg_same(e, "F0101", k)
            c = {"name": (S, "F0101", k, "ABALPH"), "vat": (S, "F0101", k, "ABTAX"), "street": (S, "F0116", ka, "ALADD1"),
                 "zip": (S, "F0116", ka, "ALADDZ"), "city": (S, "F0116", ka, "ALCTY1"), "prov": (S, "F0116", ka, "ALADDS"),
                 "country": (S, "F0116", ka, "ALCTR"), "phone": (S, "F0115", kp, "WPPH1"), "created": (S, "F03012", kc, "AIDAOJ")}
            if e["cc"] == "IT":
                c["cf"] = (S, "F0101", k, "ABTX2")
            if ke:
                c["email"] = (S, "F01151", ke, "EAEMAL")
            CELLS[e["uid"]] = c
        elif typ == "sup":
            sp, a8 = obj, ID[id(obj)]
            ab.add(ABAN8=a8, ABTAX=sp.vat, ABTX2=sp.cf, ABALPH=sp.name, ABMCU="1000".rjust(12), ABAT1="V", ABAC01="LIE",
                   ABTAXC="C", ABPA8=a8, ABUSER=rng.choice(users), ABUPMJ=jul(rand_dt(created, TODAY)))
            addr_rows(a8, created, sp.street, sp.street2, sp.zip, sp.city, sp.prov, sp.cc)
            ww.add(WWAN8=a8, WWIDLN=0, WWMLNM=sp.name, WWALPH=sp.name)
            ph.add(WPAN8=a8, WPIDLN=0, WPRCK7=1, WPPHTP="", WPAR1=wpar(sp.cc, sp.area), WPPH1=sp.sub)
            em.add(EAAN8=a8, EAIDLN=0, EARCK7=1, EAETP="E", EAEMAL=sp.emails[0])
        else:
            p, a8 = obj, ID[id(obj)]
            a = p["addr"]
            ab.add(ABAN8=a8, ABALPH="%s, %s" % (p["last"], p["first"]), ABMCU="1000".rjust(12), ABAT1="E", ABTAXC="P",
                   ABPA8=a8, ABUSER="HR", ABUPMJ=jul(rand_dt(created, TODAY)))
            addr_rows(a8, created, a["street"], "", a["zip"], a["city"], a["prov"], "DE")
            ww.add(WWAN8=a8, WWIDLN=0, WWMLNM="%s %s" % (p["first"], p["last"]), WWALPH="%s, %s" % (p["last"], p["first"]),
                   WWGNNM=p["first"], WWSRNM=p["last"])
    mx = max(int(k) for k in ab.idx)
    for n, (t, cols) in enumerate([("F0116", None), ("F0116", None), ("F0115", None), ("F01151", None), ("F03012", None)]):
        ghost = mx + 17 + n * 13
        if t == "F0116":
            a = make_address(rng.choice(["DE", "IT"]))
            key = ad.add(ALAN8=ghost, ALEFTB=jul(rand_dt(GOLIVE[S], TODAY)), ALADD1=a["street"], ALADDZ=a["zip"], ALCTY1=a["city"],
                         ALADDS=a["prov"], ALCTR="DE" if a["city"] in [c[0] for c in CITIES["DE"]] else "IT")
            log_orphan(S, t, key, "ALAN8", "riga orfana: ALAN8 non esiste in F0101")
        elif t == "F0115":
            key = ph.add(WPAN8=ghost, WPIDLN=0, WPRCK7=1, WPPHTP="", WPAR1="089", WPPH1=phone_sub("DE", "089"))
            log_orphan(S, t, key, "WPAN8", "riga orfana: WPAN8 non esiste in F0101")
        elif t == "F01151":
            key = em.add(EAAN8=ghost, EAIDLN=0, EARCK7=1, EAETP="E", EAEMAL="einkauf@%s.de" % slug(rng.choice(DE_LAST) + "technik"))
            log_orphan(S, t, key, "EAAN8", "riga orfana: EAAN8 non esiste in F0101")
        else:
            key = cm.add(AIAN8=ghost, AICO="00100", AICRCD="EUR", AITRAR="N30", AIACL=10000, AIDAOJ=jul(rand_dt(GOLIVE[S], TODAY)), AITXA1="DE19")
            log_orphan(S, t, key, "AIAN8", "riga orfana: AIAN8 non esiste in F0101")

    it = table(S, "F4101", ["IMITM", "IMLITM", "IMDSC1", "IMDSC2", "IMSTKT", "IMUOM1"], ["IMITM"])
    for i, (it_, en, code, _p) in enumerate(PRODUCTS, 1):
        it.add(IMITM=60000 + i * 7, IMLITM=code, IMDSC1=en.upper()[:30], IMDSC2="", IMSTKT="S" if not code.startswith("SRV") else "N", IMUOM1="EA")
    so = table(S, "F4201", ["SHKCOO", "SHDOCO", "SHDCTO", "SHAN8", "SHSHAN", "SHTRDJ", "SHCRCD", "SHOTOT"], ["SHKCOO", "SHDOCO", "SHDCTO"])
    buyers = [e for e in ents if e["kind"] in ("main", "filiale") and e["status"] == "active"]
    dest = {e["parent_uid"]: e for e in ents if e["kind"] == "dest"}
    for i in range(45):
        b = rng.choice(buyers)
        sh = dest[b["uid"]]["an8"] if b["uid"] in dest and rng.random() < 0.7 else b["an8"]
        so.add(SHKCOO="00100", SHDOCO=24000 + i * 3, SHDCTO="SO", SHAN8=b["an8"], SHSHAN=sh,
               SHTRDJ=jul(rand_dt(max(b["created"], GOLIVE[S]), TODAY)), SHCRCD="EUR", SHOTOT="%.2f" % rng.uniform(500, 60000))


# =============================================================================
# exact_nl - Exact Globe Next
# =============================================================================
def render_exact():
    S = "exact_nl"
    ents = ENTS[S]
    cc_t = table(S, "cicmpy", ["cmp_wwn", "cmp_code", "cmp_name", "cmp_type", "cmp_status", "cmp_fadd1", "cmp_fadd2", "cmp_fpc",
                               "cmp_fcity", "cmp_fctry", "cmp_tel", "cmp_fax", "cmp_e_mail", "cmp_web", "VatNumber", "cmp_parent",
                               "debnr", "crdnr", "PaymentCondition", "CreditLine", "syscreated", "sysmodified"], ["cmp_wwn"], client=True)
    adr = table(S, "Addresses", ["ID", "Account", "Type", "Main", "AddressLine1", "AddressLine2", "AddressLine3", "PostCode", "City",
                                 "State", "Country", "Phone", "syscreated"], ["ID"], client=True)
    cnt = table(S, "cicntp", ["cnt_id", "cmp_wwn", "cnt_f_name", "cnt_l_name", "FullName", "cnt_job_desc", "cnt_email",
                              "cnt_f_tel", "cnt_f_mobile", "syscreated"], ["cnt_id"], client=True)
    concept(S, "cicmpy", {"cmp_wwn": "codice cliente", "cmp_code": "codice cliente", "debnr": "codice cliente", "cmp_name": "ragione sociale",
                          "cmp_type": "tipo_anagrafica", "cmp_status": "stato_cliente", "cmp_fadd1": "indirizzo", "cmp_fadd2": "indirizzo",
                          "cmp_fpc": "cap", "cmp_fcity": "citta", "cmp_fctry": "paese", "cmp_tel": "telefono", "cmp_fax": "telefono",
                          "cmp_e_mail": "email", "cmp_web": "sito_web", "VatNumber": "partita_iva", "syscreated": "data_creazione"})
    concept(S, "Addresses", {"Account": "codice cliente", "AddressLine1": "indirizzo", "AddressLine2": "indirizzo", "AddressLine3": "indirizzo",
                             "PostCode": "cap", "City": "citta", "State": "provincia", "Country": "paese", "Phone": "telefono"})
    concept(S, "cicntp", {"cmp_wwn": "codice cliente", "cnt_email": "email", "cnt_f_tel": "telefono", "cnt_f_mobile": "telefono"})
    fk(S, "Addresses", ["Account"], "cicmpy", ["cmp_wwn"], "Type: INV=fatturazione, DEL=consegna, VIS=visita; Main=1 indirizzo principale")
    fk(S, "cicntp", ["cmp_wwn"], "cicmpy", ["cmp_wwn"])
    fk(S, "cicmpy", ["cmp_parent"], "cicmpy", ["cmp_wwn"], "account capogruppo")

    def tel(cc, area, sub):
        if cc == "NL":
            return "%s-%s" % (area, sub)
        return "00%s %s %s" % (COUNTRY[cc]["pfx"], area_intl(cc, area), sub)

    items = [(e["created"], "ent", e) for e in ents]
    for _ in range(12):
        sp = make_noise(rng.choice(["NL", "NL", "BE", "DE", "IT"]), "supplier")
        items.append((max(sp.created, GOLIVE[S]), "sup", sp))
    items.sort(key=lambda x: x[0])
    for e in ents:
        e["wwn"] = new_uuid().upper()
    by_az = {e["az"]: e for e in ents if e["kind"] == "main"}
    deb, crd, aid = 1000, 50000, 0
    for created, typ, obj in items:
        if typ == "ent":
            e = obj
            deb += rng.randint(1, 4)
            e["debnr"] = str(deb).rjust(6)
            parent = by_az[e["parent_az"]]["wwn"] if e["kind"] == "main" and e["parent_az"] in by_az else ""
            k = cc_t.add(cmp_wwn=e["wwn"], cmp_code=str(deb).rjust(20), cmp_name=e["name"], cmp_type="C",
                         cmp_status={"blocked": "B", "inactive": "E"}.get(e["status"], "A"), cmp_fadd1=e["street"], cmp_fadd2=e["street2"],
                         cmp_fpc=e["zip"], cmp_fcity=e["city"], cmp_fctry=e["cc"], cmp_tel=tel(e["cc"], e["area"], e["sub"]),
                         cmp_fax=tel(e["cc"], e["area"], phone_sub(e["cc"], e["area"])) if rng.random() < 0.3 else "",
                         cmp_e_mail=e["email"], cmp_web=e["web"], VatNumber=e["vat"], cmp_parent=parent, debnr=e["debnr"],
                         PaymentCondition=rng.choice(["14", "30", "30", "60", "90"]), CreditLine=rng.choice(["0", "5000", "10000", "25000"]),
                         syscreated=fmt_date(S, created), sysmodified=fmt_date(S, rand_dt(created, TODAY)))
            aid += 1
            adr.add(ID=aid, Account=e["wwn"], Type="INV", Main=1, AddressLine1=e["street"], AddressLine2=e["street2"], PostCode=e["zip"],
                    City=e["city"], State=e["prov"], Country=e["cc"], Phone=tel(e["cc"], e["area"], e["sub"]), syscreated=fmt_date(S, created))
            if e["kind"] == "main" and rng.random() < 0.3:
                a = make_address(e["cc"])
                aid += 1
                adr.add(ID=aid, Account=e["wwn"], Type="DEL", Main=0, AddressLine1=a["street"], PostCode=a["zip"], City=a["city"],
                        State=a["prov"], Country=e["cc"], syscreated=fmt_date(S, clamp(created + dt.timedelta(days=rng.randint(1, 500)))))
            for p in e["contacts"]:
                cnt.add(cnt_id=new_uuid().upper(), cmp_wwn=e["wwn"], cnt_f_name=p["first"], cnt_l_name=p["last"],
                        FullName="%s %s" % (p["first"], p["last"]), cnt_job_desc=p["role"], cnt_email=p["email"],
                        cnt_f_tel=tel(e["cc"], e["area"], p["sub"]), cnt_f_mobile=p["mobile"],
                        syscreated=fmt_date(S, clamp(created + dt.timedelta(days=rng.randint(0, 400)))))
            reg_same(e, "cicmpy", k)
            CELLS[e["uid"]] = {kk: (S, "cicmpy", k, v) for kk, v in dict(
                name="cmp_name", vat="VatNumber", street="cmp_fadd1", zip="cmp_fpc", city="cmp_fcity", country="cmp_fctry",
                phone="cmp_tel", email="cmp_e_mail", created="syscreated").items()}
        else:
            sp = obj
            crd += rng.randint(1, 5)
            wwn = new_uuid().upper()
            cc_t.add(cmp_wwn=wwn, cmp_code=str(crd).rjust(20), cmp_name=sp.name, cmp_type="S", cmp_status="A", cmp_fadd1=sp.street,
                     cmp_fpc=sp.zip, cmp_fcity=sp.city, cmp_fctry=sp.cc, cmp_tel=tel(sp.cc, sp.area, sp.sub), cmp_e_mail=sp.emails[0],
                     cmp_web=sp.web, VatNumber=sp.vat, crdnr=str(crd).rjust(6), PaymentCondition="30", CreditLine="0",
                     syscreated=fmt_date(S, created), sysmodified=fmt_date(S, rand_dt(created, TODAY)))
            aid += 1
            adr.add(ID=aid, Account=wwn, Type="INV", Main=1, AddressLine1=sp.street, PostCode=sp.zip, City=sp.city, State=sp.prov,
                    Country=sp.cc, syscreated=fmt_date(S, created))
    for _ in range(2):
        aid += 1
        a = make_address("NL")
        key = adr.add(ID=aid, Account=new_uuid().upper(), Type="DEL", Main=0, AddressLine1=a["street"], PostCode=a["zip"], City=a["city"],
                      State=a["prov"], Country="NL", syscreated=fmt_date(S, rand_dt(GOLIVE[S], TODAY)))
        log_orphan(S, "Addresses", key, "Account", "riga orfana: Account non esiste in cicmpy")
    p = person("NL")
    key = cnt.add(cnt_id=new_uuid().upper(), cmp_wwn=new_uuid().upper(), cnt_f_name=p["first"], cnt_l_name=p["last"],
                  FullName="%s %s" % (p["first"], p["last"]), cnt_job_desc=p["role"], syscreated=fmt_date(S, rand_dt(GOLIVE[S], TODAY)))
    log_orphan(S, "cicntp", key, "cmp_wwn", "riga orfana: cmp_wwn non esiste in cicmpy")

    itm = table(S, "Items", ["ItemCode", "Description", "Type", "Condition", "CostPriceStandard", "SalesPackagePrice"], ["ItemCode"])
    for it_, en, code, price in PRODUCTS:
        itm.add(ItemCode=code, Description=en, Type="S" if not code.startswith("SRV") else "L", Condition="A",
                CostPriceStandard="%.2f" % (price * 0.55), SalesPackagePrice="%.2f" % price)
    ok = table(S, "orkrg", ["ordernr", "ord_soort", "debnr", "fakdebnr", "verzdebnr", "orddat", "refer", "valcode"], ["ordernr"])
    buyers = [e for e in ents if e["kind"] in ("main", "filiale") and e["status"] == "active"]
    dest = {e["parent_uid"]: e for e in ents if e["kind"] == "dest"}
    for i in range(35):
        b = rng.choice(buyers)
        ok.add(ordernr=str(31000 + i * 2).rjust(8), ord_soort="V", debnr=b["debnr"], fakdebnr=b["debnr"],
               verzdebnr=dest[b["uid"]]["debnr"] if b["uid"] in dest else b["debnr"],
               orddat=rand_dt(max(b["created"], GOLIVE[S]), TODAY).strftime("%Y-%m-%d 00:00:00.000"),
               refer="PO-%d" % rng.randint(1000, 99999), valcode="EUR")


# =============================================================================
# ebs_es - Oracle E-Business Suite R12 (TCA)
# =============================================================================
def render_ebs():
    S = "ebs_es"
    ents = ENTS[S]
    hp = table(S, "HZ_PARTIES", ["PARTY_ID", "PARTY_NUMBER", "PARTY_NAME", "PARTY_TYPE", "KNOWN_AS", "JGZZ_FISCAL_CODE",
                                 "TAX_REFERENCE", "STATUS", "CATEGORY_CODE", "CREATION_DATE", "CREATED_BY"], ["PARTY_ID"], client=True)
    ca = table(S, "HZ_CUST_ACCOUNTS", ["CUST_ACCOUNT_ID", "PARTY_ID", "ACCOUNT_NUMBER", "ACCOUNT_NAME", "STATUS", "CUSTOMER_TYPE",
                                       "CUSTOMER_CLASS_CODE", "SALES_CHANNEL_CODE", "CREATION_DATE"], ["CUST_ACCOUNT_ID"], client=True)
    ps = table(S, "HZ_PARTY_SITES", ["PARTY_SITE_ID", "PARTY_ID", "LOCATION_ID", "PARTY_SITE_NUMBER", "IDENTIFYING_ADDRESS_FLAG",
                                     "STATUS", "PARTY_SITE_NAME"], ["PARTY_SITE_ID"], client=True)
    lo = table(S, "HZ_LOCATIONS", ["LOCATION_ID", "ADDRESS1", "ADDRESS2", "ADDRESS3", "ADDRESS4", "CITY", "POSTAL_CODE", "STATE",
                                   "PROVINCE", "COUNTY", "COUNTRY", "CREATION_DATE"], ["LOCATION_ID"], client=True)
    cas = table(S, "HZ_CUST_ACCT_SITES_ALL", ["CUST_ACCT_SITE_ID", "CUST_ACCOUNT_ID", "PARTY_SITE_ID", "ORG_ID", "STATUS",
                                              "BILL_TO_FLAG", "SHIP_TO_FLAG"], ["CUST_ACCT_SITE_ID"], client=True)
    su = table(S, "HZ_CUST_SITE_USES_ALL", ["SITE_USE_ID", "CUST_ACCT_SITE_ID", "SITE_USE_CODE", "PRIMARY_FLAG", "STATUS", "LOCATION",
                                            "BILL_TO_SITE_USE_ID", "PAYMENT_TERM_ID", "ORG_ID"], ["SITE_USE_ID"], client=True)
    cp = table(S, "HZ_CONTACT_POINTS", ["CONTACT_POINT_ID", "CONTACT_POINT_TYPE", "OWNER_TABLE_NAME", "OWNER_TABLE_ID", "STATUS",
                                        "PRIMARY_FLAG", "PHONE_LINE_TYPE", "PHONE_COUNTRY_CODE", "PHONE_AREA_CODE", "PHONE_NUMBER",
                                        "EMAIL_ADDRESS", "URL", "CREATION_DATE"], ["CONTACT_POINT_ID"], client=True)
    concept(S, "HZ_PARTIES", {"PARTY_ID": "codice cliente", "PARTY_NUMBER": "codice cliente", "PARTY_NAME": "ragione sociale",
                              "KNOWN_AS": "ragione sociale", "PARTY_TYPE": "tipo_anagrafica", "JGZZ_FISCAL_CODE": "codice_fiscale",
                              "TAX_REFERENCE": "partita_iva", "STATUS": "stato_cliente", "CATEGORY_CODE": "tipo_anagrafica",
                              "CREATION_DATE": "data_creazione"})
    concept(S, "HZ_CUST_ACCOUNTS", {"CUST_ACCOUNT_ID": "codice cliente", "PARTY_ID": "codice cliente", "ACCOUNT_NUMBER": "codice cliente",
                                    "ACCOUNT_NAME": "ragione sociale", "STATUS": "stato_cliente", "CUSTOMER_TYPE": "tipo_anagrafica",
                                    "CREATION_DATE": "data_creazione"})
    concept(S, "HZ_PARTY_SITES", {"PARTY_ID": "codice cliente"})
    concept(S, "HZ_LOCATIONS", {"ADDRESS1": "indirizzo", "ADDRESS2": "indirizzo", "ADDRESS3": "indirizzo", "ADDRESS4": "indirizzo",
                                "CITY": "citta", "POSTAL_CODE": "cap", "STATE": "provincia", "PROVINCE": "provincia", "COUNTRY": "paese"})
    concept(S, "HZ_CUST_ACCT_SITES_ALL", {"CUST_ACCOUNT_ID": "codice cliente"})
    concept(S, "HZ_CONTACT_POINTS", {"PHONE_COUNTRY_CODE": "telefono", "PHONE_AREA_CODE": "telefono", "PHONE_NUMBER": "telefono",
                                     "EMAIL_ADDRESS": "email", "URL": "sito_web"})
    fk(S, "HZ_CUST_ACCOUNTS", ["PARTY_ID"], "HZ_PARTIES", ["PARTY_ID"])
    fk(S, "HZ_PARTY_SITES", ["PARTY_ID"], "HZ_PARTIES", ["PARTY_ID"])
    fk(S, "HZ_PARTY_SITES", ["LOCATION_ID"], "HZ_LOCATIONS", ["LOCATION_ID"])
    fk(S, "HZ_CUST_ACCT_SITES_ALL", ["CUST_ACCOUNT_ID"], "HZ_CUST_ACCOUNTS", ["CUST_ACCOUNT_ID"], "una riga per unità operativa ORG_ID (101 Spagna, 102 Portogallo)")
    fk(S, "HZ_CUST_ACCT_SITES_ALL", ["PARTY_SITE_ID"], "HZ_PARTY_SITES", ["PARTY_SITE_ID"])
    fk(S, "HZ_CUST_SITE_USES_ALL", ["CUST_ACCT_SITE_ID"], "HZ_CUST_ACCT_SITES_ALL", ["CUST_ACCT_SITE_ID"], "SITE_USE_CODE BILL_TO=fatturazione, SHIP_TO=consegna")
    fk(S, "HZ_CUST_SITE_USES_ALL", ["BILL_TO_SITE_USE_ID"], "HZ_CUST_SITE_USES_ALL", ["SITE_USE_ID"], "solo per SHIP_TO: indirizzo di fatturazione collegato")
    fk(S, "HZ_CONTACT_POINTS", ["OWNER_TABLE_ID"], "HZ_PARTIES", ["PARTY_ID"], "solo se OWNER_TABLE_NAME='HZ_PARTIES'",
       cond=lambda r: r["OWNER_TABLE_NAME"] == "HZ_PARTIES")
    fk(S, "HZ_CONTACT_POINTS", ["OWNER_TABLE_ID"], "HZ_PARTY_SITES", ["PARTY_SITE_ID"], "solo se OWNER_TABLE_NAME='HZ_PARTY_SITES'",
       cond=lambda r: r["OWNER_TABLE_NAME"] == "HZ_PARTY_SITES")

    seq = dict(party=1040, pnum=10000, loc=5000, site=3000, snum=1000, acc=1040, anum=1000, cas=2000, su=4000, cp=6000)

    def nxt(k, step=(1, 6)):
        seq[k] += rng.randint(*step)
        return seq[k]

    def party(name, ptype, cc, vat, cf, status, cat, created, street, street2, zp, city, prov, prov_name, known=""):
        pid = nxt("party")
        hp.add(PARTY_ID=pid, PARTY_NUMBER=nxt("pnum", (1, 1)), PARTY_NAME=name, PARTY_TYPE=ptype, KNOWN_AS=known, JGZZ_FISCAL_CODE=cf,
               TAX_REFERENCE=vat, STATUS=status, CATEGORY_CODE=cat, CREATION_DATE=fmt_date(S, created), CREATED_BY=rng.choice([1013, 1318, 0]))
        lid = nxt("loc")
        lo.add(LOCATION_ID=lid, ADDRESS1=street, ADDRESS2=street2, CITY=city, POSTAL_CODE=zp,
               PROVINCE=prov_val(S, cc, prov, prov_name), COUNTRY=cc, CREATION_DATE=fmt_date(S, created))
        sid = nxt("site")
        ps.add(PARTY_SITE_ID=sid, PARTY_ID=pid, LOCATION_ID=lid, PARTY_SITE_NUMBER=nxt("snum", (1, 1)), IDENTIFYING_ADDRESS_FLAG="Y", STATUS="A")
        return pid, lid, sid

    items = [(e["created"], "ent", e) for e in ents]
    for _ in range(8):
        sp = make_noise(rng.choice(["ES", "ES", "IT", "FR"]), "supplier")
        items.append((max(sp.created, GOLIVE[S]), "sup", sp))
    items.sort(key=lambda x: x[0])
    for created, typ, obj in items:
        if typ == "sup":
            sp = obj
            pid, lid, sid = party(sp.name, "ORGANIZATION", sp.cc, sp.vat, sp.cf or sp.vat_nat, "A", "SUPPLIER", created, sp.street,
                                  sp.street2, sp.zip, sp.city, sp.prov, sp.prov_name)
            cp.add(CONTACT_POINT_ID=nxt("cp"), CONTACT_POINT_TYPE="PHONE", OWNER_TABLE_NAME="HZ_PARTIES", OWNER_TABLE_ID=pid, STATUS="A",
                   PRIMARY_FLAG="Y", PHONE_LINE_TYPE="GEN", PHONE_COUNTRY_CODE=COUNTRY[sp.cc]["pfx"], PHONE_AREA_CODE=area_intl(sp.cc, sp.area),
                   PHONE_NUMBER=sp.sub, CREATION_DATE=fmt_date(S, created))
            continue
        e = obj
        jg = e["cf"] if e["cc"] in ("IT", "ES") else ""
        pid, lid, sid = party(e["name"], "ORGANIZATION", e["cc"], e["vat"], jg, "I" if e["status"] == "inactive" else "A",
                              "CUSTOMER", created, e["street"], e["street2"], e["zip"], e["city"], e["prov"], e["prov_name"],
                              known=e["base"].upper() if e["kind"] == "main" and rng.random() < 0.15 else "")
        aid = nxt("acc")
        e["acc"] = aid
        ka = ca.add(CUST_ACCOUNT_ID=aid, PARTY_ID=pid, ACCOUNT_NUMBER=nxt("anum", (1, 3)),
                    ACCOUNT_NAME=e["base"] if e["kind"] != "dest" and rng.random() < 0.5 else "",
                    STATUS="I" if e["status"] in ("inactive", "blocked") else "A", CUSTOMER_TYPE="R",
                    CUSTOMER_CLASS_CODE=rng.choice(["INDUSTRIAL", "OEM", "DISTRIBUTOR"]), SALES_CHANNEL_CODE=rng.choice(["DIRECT", "INDIRECT"]),
                    CREATION_DATE=fmt_date(S, created))
        orgs = [101, 102] if rng.random() < 0.15 else [101]
        e["bill"], e["ship"] = {}, {}
        for org in orgs:
            csid = nxt("cas")
            dest = e["kind"] == "dest"
            cas.add(CUST_ACCT_SITE_ID=csid, CUST_ACCOUNT_ID=aid, PARTY_SITE_ID=sid, ORG_ID=org, STATUS="A",
                    BILL_TO_FLAG="" if dest else "P", SHIP_TO_FLAG="P")
            bill = ""
            if not dest:
                bill = nxt("su")
                su.add(SITE_USE_ID=bill, CUST_ACCT_SITE_ID=csid, SITE_USE_CODE="BILL_TO", PRIMARY_FLAG="Y", STATUS="A",
                       LOCATION="%s-%s" % (e["city"].upper()[:12], aid), PAYMENT_TERM_ID=rng.choice([1000, 1001, 1002, 1004]), ORG_ID=org)
                e["bill"][org] = bill
            sh = nxt("su")
            su.add(SITE_USE_ID=sh, CUST_ACCT_SITE_ID=csid, SITE_USE_CODE="SHIP_TO", PRIMARY_FLAG="Y", STATUS="A",
                   LOCATION="%s-%s" % (e["city"].upper()[:12], sh), BILL_TO_SITE_USE_ID=bill, ORG_ID=org)
            e["ship"][org] = sh
        on_site = rng.random() < 0.2
        kp = cp.add(CONTACT_POINT_ID=nxt("cp"), CONTACT_POINT_TYPE="PHONE", OWNER_TABLE_NAME="HZ_PARTY_SITES" if on_site else "HZ_PARTIES",
                    OWNER_TABLE_ID=sid if on_site else pid, STATUS="A", PRIMARY_FLAG="Y", PHONE_LINE_TYPE="GEN",
                    PHONE_COUNTRY_CODE=COUNTRY[e["cc"]]["pfx"], PHONE_AREA_CODE=area_intl(e["cc"], e["area"]), PHONE_NUMBER=e["sub"],
                    CREATION_DATE=fmt_date(S, created))
        ke = None
        if e["email"]:
            ke = cp.add(CONTACT_POINT_ID=nxt("cp"), CONTACT_POINT_TYPE="EMAIL", OWNER_TABLE_NAME="HZ_PARTIES", OWNER_TABLE_ID=pid,
                        STATUS="A", PRIMARY_FLAG="Y", EMAIL_ADDRESS=e["email"], CREATION_DATE=fmt_date(S, created))
        if e["web"] and rng.random() < 0.5:
            cp.add(CONTACT_POINT_ID=nxt("cp"), CONTACT_POINT_TYPE="WEB", OWNER_TABLE_NAME="HZ_PARTIES", OWNER_TABLE_ID=pid,
                   STATUS="A", PRIMARY_FLAG="Y", URL="http://" + e["web"], CREATION_DATE=fmt_date(S, created))
        reg_same(e, "HZ_CUST_ACCOUNTS", ka)
        c = {"name": (S, "HZ_PARTIES", str(pid), "PARTY_NAME"), "vat": (S, "HZ_PARTIES", str(pid), "TAX_REFERENCE"),
             "street": (S, "HZ_LOCATIONS", str(lid), "ADDRESS1"), "zip": (S, "HZ_LOCATIONS", str(lid), "POSTAL_CODE"),
             "city": (S, "HZ_LOCATIONS", str(lid), "CITY"), "prov": (S, "HZ_LOCATIONS", str(lid), "PROVINCE"),
             "country": (S, "HZ_LOCATIONS", str(lid), "COUNTRY"), "phone": (S, "HZ_CONTACT_POINTS", kp, "PHONE_NUMBER"),
             "created": (S, "HZ_CUST_ACCOUNTS", ka, "CREATION_DATE")}
        if e["cc"] == "IT":
            c["cf"] = (S, "HZ_PARTIES", str(pid), "JGZZ_FISCAL_CODE")
        if ke:
            c["email"] = (S, "HZ_CONTACT_POINTS", ke, "EMAIL_ADDRESS")
        CELLS[e["uid"]] = c
    # righe orfane
    e = rng.choice([x for x in ents if x["kind"] == "main"])
    key = cas.add(CUST_ACCT_SITE_ID=nxt("cas"), CUST_ACCOUNT_ID=e["acc"], PARTY_SITE_ID=seq["site"] + 41, ORG_ID=102, STATUS="A",
                  SHIP_TO_FLAG="Y")
    log_orphan(S, "HZ_CUST_ACCT_SITES_ALL", key, "PARTY_SITE_ID", "riga orfana: PARTY_SITE_ID non esiste in HZ_PARTY_SITES")
    key = cp.add(CONTACT_POINT_ID=nxt("cp"), CONTACT_POINT_TYPE="EMAIL", OWNER_TABLE_NAME="HZ_PARTIES", OWNER_TABLE_ID=seq["party"] + 77,
                 STATUS="A", PRIMARY_FLAG="Y", EMAIL_ADDRESS="compras@%s.es" % slug("Talleres " + rng.choice(ES_LAST)),
                 CREATION_DATE=fmt_date(S, rand_dt(GOLIVE[S], TODAY)))
    log_orphan(S, "HZ_CONTACT_POINTS", key, "OWNER_TABLE_ID", "riga orfana: OWNER_TABLE_ID non esiste in HZ_PARTIES")

    mi = table(S, "MTL_SYSTEM_ITEMS_B", ["INVENTORY_ITEM_ID", "ORGANIZATION_ID", "SEGMENT1", "DESCRIPTION", "PRIMARY_UOM_CODE",
                                          "INVENTORY_ITEM_STATUS_CODE", "ENABLED_FLAG"], ["INVENTORY_ITEM_ID", "ORGANIZATION_ID"])
    for i, (it_, en, code, _p) in enumerate(PRODUCTS, 1):
        for org in (204, 207):
            mi.add(INVENTORY_ITEM_ID=8800 + i * 2, ORGANIZATION_ID=org, SEGMENT1=code, DESCRIPTION=en,
                   PRIMARY_UOM_CODE="Ea", INVENTORY_ITEM_STATUS_CODE="Active", ENABLED_FLAG="Y")
    oh = table(S, "OE_ORDER_HEADERS_ALL", ["HEADER_ID", "ORG_ID", "ORDER_NUMBER", "ORDERED_DATE", "SOLD_TO_ORG_ID", "SHIP_TO_ORG_ID",
                                            "INVOICE_TO_ORG_ID", "FLOW_STATUS_CODE", "TRANSACTIONAL_CURR_CODE"], ["HEADER_ID"])
    buyers = [e for e in ents if e["kind"] in ("main", "filiale") and e["status"] == "active"]
    dest = {e["parent_uid"]: e for e in ents if e["kind"] == "dest"}
    for i in range(35):
        b = rng.choice(buyers)
        ship = dest[b["uid"]]["ship"][101] if b["uid"] in dest else b["ship"][101]
        oh.add(HEADER_ID=91000 + i * 5, ORG_ID=101, ORDER_NUMBER=60100 + i, ORDERED_DATE=fmt_date(S, rand_dt(max(b["created"], GOLIVE[S]), TODAY)),
               SOLD_TO_ORG_ID=b["acc"], SHIP_TO_ORG_ID=ship, INVOICE_TO_ORG_ID=b["bill"][101],
               FLOW_STATUS_CODE=rng.choice(["BOOKED", "CLOSED", "CLOSED", "ENTERED", "CANCELLED"]), TRANSACTIONAL_CURR_CODE="EUR")


# =============================================================================
# suitecrm - SuiteCRM 7
# =============================================================================
def render_suite():
    S = "suitecrm"
    ents = ENTS[S]
    ac = table(S, "accounts", ["id", "name", "date_entered", "date_modified", "modified_user_id", "created_by", "deleted",
                               "assigned_user_id", "account_type", "industry", "billing_address_street", "billing_address_city",
                               "billing_address_state", "billing_address_postalcode", "billing_address_country",
                               "shipping_address_street", "shipping_address_city", "shipping_address_state",
                               "shipping_address_postalcode", "shipping_address_country", "phone_office", "phone_alternate",
                               "phone_fax", "website", "employees", "parent_id", "description"], ["id"], client=True)
    cs = table(S, "accounts_cstm", ["id_c", "partita_iva_c", "codice_fiscale_c", "codice_destinatario_c"], ["id_c"], client=True)
    ea = table(S, "email_addresses", ["id", "email_address", "invalid_email", "opt_out", "date_created", "date_modified", "deleted"], ["id"], client=True)
    er = table(S, "email_addr_bean_rel", ["id", "email_address_id", "bean_id", "bean_module", "primary_address", "reply_to_address",
                                          "date_created", "date_modified", "deleted"], ["id"], client=True)
    ct = table(S, "contacts", ["id", "date_entered", "deleted", "salutation", "first_name", "last_name", "title", "phone_work",
                               "phone_mobile"], ["id"], client=True)
    acc_ct = table(S, "accounts_contacts", ["id", "contact_id", "account_id", "date_modified", "deleted"], ["id"], client=True)
    concept(S, "accounts", {"id": "codice cliente", "name": "ragione sociale", "date_entered": "data_creazione",
                            "deleted": ("stato_cliente", "1 = record cancellato logicamente"), "account_type": "tipo_anagrafica",
                            "billing_address_street": "indirizzo", "billing_address_city": "citta", "billing_address_state": "provincia",
                            "billing_address_postalcode": "cap", "billing_address_country": "paese", "shipping_address_street": "indirizzo",
                            "shipping_address_city": "citta", "shipping_address_state": "provincia", "shipping_address_postalcode": "cap",
                            "shipping_address_country": "paese", "phone_office": "telefono", "phone_alternate": "telefono",
                            "phone_fax": "telefono", "website": "sito_web"})
    concept(S, "accounts_cstm", {"id_c": "codice cliente", "partita_iva_c": "partita_iva", "codice_fiscale_c": "codice_fiscale"})
    concept(S, "email_addresses", {"email_address": "email"})
    concept(S, "email_addr_bean_rel", {"bean_id": "codice cliente"})
    concept(S, "contacts", {"phone_work": "telefono", "phone_mobile": "telefono"})
    concept(S, "accounts_contacts", {"account_id": "codice cliente"})
    fk(S, "accounts_cstm", ["id_c"], "accounts", ["id"], "relazione 1:1 con i campi personalizzati")
    fk(S, "email_addr_bean_rel", ["email_address_id"], "email_addresses", ["id"])
    fk(S, "email_addr_bean_rel", ["bean_id"], "accounts", ["id"], "solo se bean_module='Accounts'", cond=lambda r: r["bean_module"] == "Accounts")
    fk(S, "email_addr_bean_rel", ["bean_id"], "contacts", ["id"], "solo se bean_module='Contacts'", cond=lambda r: r["bean_module"] == "Contacts")
    fk(S, "accounts_contacts", ["account_id"], "accounts", ["id"])
    fk(S, "accounts_contacts", ["contact_id"], "contacts", ["id"])
    fk(S, "accounts", ["parent_id"], "accounts", ["id"], "account capogruppo (\"Member of\")")

    users = ["1", new_uuid(), new_uuid(), new_uuid()]
    for e in ents:
        e["sid"] = new_uuid()
    by_az = {e["az"]: e for e in ents if e["kind"] == "main"}

    def phone(cc, area, sub):
        if cc == "IT":
            return rng.choice(["%s %s", "%s/%s", "%s-%s", "%s%s"]) % (area, sub) if rng.random() < 0.7 else ph_intl(cc, area, sub)
        return ph_intl(cc, area, sub)

    def add_email(addr, bean, module, created):
        eid = new_uuid()
        k = ea.add(id=eid, email_address=addr, invalid_email=0, opt_out=0, date_created=fmt_date(S, created),
                   date_modified=fmt_date(S, created), deleted=0)
        er.add(id=new_uuid(), email_address_id=eid, bean_id=bean, bean_module=module, primary_address=1, reply_to_address=0,
               date_created=fmt_date(S, created), date_modified=fmt_date(S, created), deleted=0)
        return k

    noise = []
    for typ in ["Competitor", "Competitor", "Partner", "Partner", "Press", "Reseller"]:
        n_ = make_noise("IT" if rng.random() < 0.8 else "DE", typ)
        noise.append(n_)
    for e in sorted(ents, key=lambda x: x["created"]):
        created = e["created"]
        street = e["street"] + ("\n" + e["street2"] if e["street2"] else "")
        ship = {}
        if e["kind"] == "main" and rng.random() < 0.15:
            a = make_address(e["cc"])
            ship = dict(shipping_address_street=a["street"], shipping_address_city=a["city"],
                        shipping_address_state=prov_val(S, e["cc"], a["prov"], a["prov_name"]),
                        shipping_address_postalcode=a["zip"], shipping_address_country=COUNTRY[e["cc"]]["en"])
        deleted = 1 if e["kind"] == "dup" and rng.random() < 0.34 else 0
        if deleted:
            e["desc"].append("cancellato logicamente (deleted=1)")
        prospect = e["co"].kind == "prospect"
        k = ac.add(id=e["sid"], name=e["name"], date_entered=fmt_date(S, created), date_modified=fmt_date(S, rand_dt(created, TODAY)),
                   modified_user_id=rng.choice(users), created_by=rng.choice(users), deleted=deleted, assigned_user_id=rng.choice(users),
                   account_type="Prospect" if prospect else "Customer",
                   industry=rng.choice(["Machinery", "Manufacturing", "Engineering", "Electronics", "Chemicals", "Transportation", ""]),
                   billing_address_street=street, billing_address_city=e["city"],
                   billing_address_state=prov_val(S, e["cc"], e["prov"], e["prov_name"]), billing_address_postalcode=e["zip"],
                   billing_address_country=COUNTRY[e["cc"]]["en"], phone_office=phone(e["cc"], e["area"], e["sub"]),
                   phone_fax=phone(e["cc"], e["area"], phone_sub(e["cc"], e["area"])) if rng.random() < 0.2 else "",
                   website=rng.choice(["", "http://", "https://"]) + e["web"] if e["web"] else "",
                   employees=rng.choice(["", "", "10", "25", "50", "120", "250", "500"]),
                   parent_id=by_az[e["parent_az"]]["sid"] if e["kind"] == "main" and e["parent_az"] in by_az else "",
                   description="", **ship)
        cs.add(id_c=e["sid"], partita_iva_c=e["vat"], codice_fiscale_c=e["cf"] if e["cc"] == "IT" else "",
               codice_destinatario_c=("".join(rng.choice("ABCDEFGHJKLMNPQRSTUVWXYZ0123456789") for _ in range(7))
                                      if rng.random() < 0.6 else "0000000") if e["cc"] == "IT" and e["kind"] != "test" else "")
        ke = add_email(e["email"], e["sid"], "Accounts", created) if e["email"] else None
        for p in e["contacts"]:
            cid = new_uuid()
            cd = clamp(created + dt.timedelta(days=rng.randint(0, 300)))
            ct.add(id=cid, date_entered=fmt_date(S, cd), deleted=0, salutation=rng.choice(["", "Mr.", "Ms."]), first_name=p["first"],
                   last_name=p["last"], title=p["role"], phone_work=phone(e["cc"], e["area"], p["sub"]), phone_mobile=p["mobile"])
            acc_ct.add(id=new_uuid(), contact_id=cid, account_id=e["sid"], date_modified=fmt_date(S, cd), deleted=0)
            add_email(p["email"], cid, "Contacts", cd)
        reg_same(e, "accounts", k)
        c = {kk: (S, "accounts", k, v) for kk, v in dict(name="name", street="billing_address_street", zip="billing_address_postalcode",
                                                          city="billing_address_city", prov="billing_address_state",
                                                          country="billing_address_country", phone="phone_office",
                                                          created="date_entered").items()}
        c["vat"] = (S, "accounts_cstm", k, "partita_iva_c")
        if e["cc"] == "IT":
            c["cf"] = (S, "accounts_cstm", k, "codice_fiscale_c")
        if ke:
            c["email"] = (S, "email_addresses", ke, "email_address")
        CELLS[e["uid"]] = c
    for n_ in noise:
        sid = new_uuid()
        cr = rand_dt(GOLIVE[S], TODAY)
        ac.add(id=sid, name=n_.name, date_entered=fmt_date(S, cr), date_modified=fmt_date(S, rand_dt(cr, TODAY)), modified_user_id="1",
               created_by="1", deleted=0, assigned_user_id=rng.choice(users), account_type=n_.kind, industry="Machinery",
               billing_address_street=n_.street, billing_address_city=n_.city, billing_address_postalcode=n_.zip,
               billing_address_state=prov_val(S, n_.cc, n_.prov, n_.prov_name), billing_address_country=COUNTRY[n_.cc]["en"],
               phone_office=ph_intl(n_.cc, n_.area, n_.sub), website=n_.web)
        cs.add(id_c=sid, partita_iva_c=n_.vat)
        add_email(n_.emails[0], sid, "Accounts", cr)
    # righe orfane
    for _ in range(2):
        eid = new_uuid()
        cr = rand_dt(GOLIVE[S], TODAY)
        ea.add(id=eid, email_address="%s@%s.it" % (rng.choice(["ordini", "info", "acquisti"]), slug(rng.choice(IT_SURNAMES) + rng.choice(IT_SECTORS))),
               invalid_email=0, opt_out=0, date_created=fmt_date(S, cr), date_modified=fmt_date(S, cr), deleted=0)
        key = er.add(id=new_uuid(), email_address_id=eid, bean_id=new_uuid(), bean_module="Accounts", primary_address=1, reply_to_address=0,
                     date_created=fmt_date(S, cr), date_modified=fmt_date(S, cr), deleted=0)
        log_orphan(S, "email_addr_bean_rel", key, "bean_id", "riga orfana: bean_id non esiste in accounts")
    cid = rng.choice(list(ct.idx))
    key = acc_ct.add(id=new_uuid(), contact_id=cid, account_id=new_uuid(), date_modified=fmt_date(S, rand_dt(GOLIVE[S], TODAY)), deleted=0)
    log_orphan(S, "accounts_contacts", key, "account_id", "riga orfana: account_id non esiste in accounts")
    key = cs.add(id_c=new_uuid(), partita_iva_c=new_vat("IT")[0], codice_fiscale_c="", codice_destinatario_c="0000000")
    log_orphan(S, "accounts_cstm", key, "id_c", "riga orfana: id_c non esiste in accounts")

    op = table(S, "opportunities", ["id", "name", "date_entered", "deleted", "amount", "currency_id", "date_closed", "sales_stage", "probability"], ["id"])
    ao = table(S, "accounts_opportunities", ["id", "opportunity_id", "account_id", "date_modified", "deleted"], ["id"])
    cands = [e for e in ents if e["kind"] == "main"]
    for i in range(45):
        e = rng.choice(cands)
        oid = new_uuid()
        d = rand_dt(max(e["created"], GOLIVE[S]), TODAY)
        stage, prob = rng.choice([("Prospecting", 10), ("Qualification", 20), ("Proposal/Price Quote", 65), ("Negotiation/Review", 80),
                                  ("Closed Won", 100), ("Closed Lost", 0)])
        op.add(id=oid, name="%s - %s" % (e["base"], rng.choice(PRODUCTS)[0]), date_entered=fmt_date(S, d), deleted=0,
               amount="%.2f" % rng.uniform(2000, 150000), currency_id="-99", date_closed=(d + dt.timedelta(days=rng.randint(20, 200))).strftime("%Y-%m-%d"),
               sales_stage=stage, probability=prob)
        ao.add(id=new_uuid(), opportunity_id=oid, account_id=e["sid"], date_modified=fmt_date(S, d), deleted=0)


# =============================================================================
# Inserimento degli errori nei valori
# =============================================================================
def cur(cell):
    s, t, k, c = cell
    return TABLES[(s, t)].idx[k][c]


def typo(s):
    for _ in range(50):
        i = rng.randrange(1, len(s) - 1)
        if not s[i].isalpha():
            continue
        op = rng.choice(["drop", "swap", "dup", "vowel"])
        if op == "drop":
            t = s[:i] + s[i + 1:]
        elif op == "swap":
            if not s[i + 1].isalpha() or s[i] == s[i + 1]:
                continue
            t = s[:i] + s[i + 1] + s[i] + s[i + 2:]
        elif op == "dup":
            t = s[:i] + s[i] + s[i:]
        else:
            if s[i].lower() not in "aeiou":
                continue
            t = s[:i] + rng.choice([v for v in "aeiou" if v != s[i].lower()]) + s[i + 1:]
        if t.lower() != s.lower():
            return t
    return None


def mojibake(s):
    out = []
    for ch in s:
        if ord(ch) < 128:
            out.append(ch)
            continue
        for b in ch.encode("utf-8"):
            try:
                out.append(bytes([b]).decode("cp1252"))
            except UnicodeDecodeError:
                out.append("?")
    return "".join(out)


def bad_email(v):
    local, dom = v.split("@", 1)
    return rng.choice([local + dom, local + "@@" + dom, local + "@" + dom.rsplit(".", 1)[0], local + " @" + dom,
                       local + "@" + dom.replace(".", ",", 1), local + "@." + dom, "@" + dom])


PLACEHOLDER = {"odoo_it": ["0000000000", "+39 0000000000", "1234567890", "999999999", "+39 000 000 0000"],
               "jde_de": ["0000000", "1234567", "9999999", "0"], "exact_nl": ["0000000000", "0039 0000000", "123456", "00000"],
               "ebs_es": ["0000000", "1234567", "9999999", "000000000"], "suitecrm": ["000000", "1234567890", "0000 000000", "111111"]}


def err_vat_missing(e):
    return [("vat", "", "mancante", "partita IVA mancante")]


def err_vat_badcheck(e):
    if e["cc"] not in CHECK_POS:
        return None
    return [("vat", bad_check(e["vat"], e["cc"]), "non_valido", "cifra di controllo della partita IVA errata")]


def err_vat_noprefix(e):
    if not e["vat_nat"]:
        return None
    return [("vat", e["vat_nat"], "formato", "partita IVA senza prefisso del paese")]


def err_zip_incomplete(e):
    z = e["zip"]
    if e["cc"] == "IT" and z.startswith("0"):
        return [("zip", z.lstrip("0"), "non_valido", "CAP senza zeri iniziali (perso in un'importazione numerica)")]
    if e["cc"] == "NL":
        return [("zip", z.split()[0], "non_valido", "CAP olandese incompleto (mancano le lettere)")]
    return [("zip", z[:-1], "non_valido", "CAP incompleto (manca una cifra)")]


def err_zip_missing(e):
    return [("zip", "", "mancante", "CAP mancante")]


def err_city_typo(e):
    t = typo(e["city"])
    return [("city", t, "non_valido", "nome della città scritto male")] if t else None


def err_country(e):
    other = rng.choice(NEIGH[e["cc"]])
    return [("country", country_val(e["sys"], other), "incoerente",
             "paese %s incoerente con partita IVA, CAP e città (%s)" % (other, e["cc"]))]


def err_prov(e):
    if e["cc"] != "IT":
        return None
    other = rng.choice([p for p in IT_PROVS if p != e["prov"]])
    return [("prov", prov_val(e["sys"], "IT", other, IT_PROVS[other]), "incoerente",
             "provincia %s incoerente con CAP e città (%s)" % (other, e["prov"]))]


def err_phone(e):
    return [("phone", rng.choice(PLACEHOLDER[e["sys"]]), "non_valido", "numero di telefono segnaposto")]


def err_email(e):
    return [("email", bad_email(e["email"]), "non_valido", "indirizzo email non valido")] if e["email"] else None


def err_name_case(e):
    if rng.random() < 0.7:
        return [("name", e["name"].upper(), "formato", "ragione sociale tutta in maiuscolo")]
    return [("name", e["name"].lower(), "formato", "ragione sociale tutta in minuscolo")]


def err_lf(e):
    if not e["lf"] or not e["name"].endswith(e["lf"]) or e["lf"] not in LF_VARIANTS:
        return None
    v = rng.choice(LF_VARIANTS[e["lf"]])
    sep = rng.choice([" ", " ", ""]) if v[0].isupper() and e["lf"] != "GmbH & Co. KG" else " "
    return [("name", e["name"][:-len(e["lf"])].rstrip() + sep + v, "formato", "forma giuridica scritta in modo non standard")]


def err_spaces(e):
    n = e["name"]
    v = rng.choice([n + "  ", "  " + n, n.replace(" ", "  ", 1), " " + n.replace(" ", "   ", 1)])
    return [("name", v, "formato", "spazi superflui nella ragione sociale")]


def err_mojibake(e):
    opts = [c for c in ("name", "street", "city") if any(ord(ch) > 127 for ch in e[c])]
    if not opts:
        return None
    c = rng.choice(opts)
    return [(c, mojibake(e[c]), "altro", "caratteri accentati corrotti (testo UTF-8 letto come Windows-1252)")]


def err_cf(e):
    if e["cc"] != "IT" or not e["cf"]:
        return None
    return [("cf", new_vat("IT")[1], "incoerente", "codice fiscale diverso dalla partita IVA della società")]


def err_date(e):
    d = TODAY + dt.timedelta(days=rng.randint(200, 2500), seconds=rng.randint(0, 80000))
    return [("created", fmt_date(e["sys"], d), "non_valido", "data di creazione nel futuro")]


def err_onefield(e):
    full = "%s, %s %s" % (e["street"], e["zip"], e["city"]) + (" (%s)" % e["prov"] if e["cc"] == "IT" else "")
    return [("street", full, "struttura", "indirizzo completo (via, CAP, città) scritto tutto nel campo dell'indirizzo"),
            ("zip", "", "struttura", "CAP vuoto: è scritto nel campo dell'indirizzo"),
            ("city", "", "struttura", "città vuota: è scritta nel campo dell'indirizzo")]


def err_swap(e):
    return [("zip", e["city"], "struttura", "CAP e città invertiti"), ("city", e["zip"], "struttura", "CAP e città invertiti")]


ERROR_PLAN = [(err_vat_missing, 18), (err_vat_badcheck, 16), (err_vat_noprefix, 16), (err_zip_incomplete, 15),
              (err_zip_missing, 6), (err_city_typo, 18), (err_country, 10), (err_prov, 8), (err_phone, 16),
              (err_email, 15), (err_name_case, 12), (err_lf, 14), (err_spaces, 12), (err_mojibake, 10),
              (err_cf, 6), (err_date, 8), (err_onefield, 8), (err_swap, 6)]
# valore atteso nella cella (prima dell'errore) per ciascun concetto, nella rappresentazione del sistema
EXPECT = {"vat": lambda e: e["vat"], "zip": lambda e: e["zip"], "city": lambda e: e["city"], "street": lambda e: e["street"],
          "name": lambda e: e["name"], "email": lambda e: e["email"], "cf": lambda e: e["cf"]}


def apply(e, changes):
    cells = CELLS.get(e["uid"], {})
    plan = []
    for concept_, wrong, cat, desc in changes:
        if concept_ not in cells or cells[concept_] in USED:
            return False
        cell = cells[concept_]
        ref = cur(cell)
        if concept_ in EXPECT and ref != EXPECT[concept_](e):
            return False          # la cella non contiene il valore canonico (es. via con riga 2 in SuiteCRM)
        if wrong == ref or (ref == "" and wrong == ""):
            return False
        if ref == "" and cat != "struttura":
            return False
        plan.append((concept_, cell, wrong, ref, cat, desc))
    for concept_, cell, wrong, ref, cat, desc in plan:
        s, t, k, c = cell
        TABLES[(s, t)].idx[k][c] = wrong
        USED.add(cell)
        ERRS.append(dict(sys=s, table=t, key=k, col=c, wrong=wrong, ref=ref, cat=cat, desc=desc, concept=concept_))
    ERR_COUNT[e["uid"]] = ERR_COUNT.get(e["uid"], 0) + 1
    return True


def inject_errors():
    # i doppioni ricevono sempre almeno una differenza
    for s in SYSTEMS:
        for e in ENTS[s]:
            if e["force_err"]:
                fns = [err_lf, err_name_case, err_vat_missing, err_vat_noprefix, err_spaces, err_phone]
                rng.shuffle(fns)
                for fn in fns:
                    ch = fn(e)
                    if ch and apply(e, ch):
                        break
    per_sys = {s: [e for e in ENTS[s] if e["kind"] != "test"] for s in SYSTEMS}
    for fn, target in ERROR_PLAN:
        for s in SYSTEMS:
            rng.shuffle(per_sys[s])
        order, i = [], 0
        while any(i < len(per_sys[s]) for s in SYSTEMS):
            for s in SYSTEMS:
                if i < len(per_sys[s]):
                    order.append(per_sys[s][i])
            i += 1
        done = 0
        for e in order:
            if done >= target:
                break
            if ERR_COUNT.get(e["uid"], 0) >= 2:
                continue
            ch = fn(e)
            if ch and apply(e, ch):
                done += 1
        if done < target:
            print("ATTENZIONE: %s inseriti %d su %d" % (fn.__name__, done, target))


# =============================================================================
# Scrittura dei file
# =============================================================================
VERITA_COLS = ["tipo", "sistema", "tabella", "codice_record", "colonna", "riferimento", "categoria", "descrizione"]


def write_all(out):
    os.makedirs(out, exist_ok=True)
    for f in os.listdir(out):
        if f.endswith(".csv"):
            os.remove(os.path.join(out, f))
    for (s, name), t in TABLES.items():
        with open(os.path.join(out, "%s__%s.csv" % (s, name)), "w", encoding="utf-8", newline="") as fh:
            w = csv.DictWriter(fh, fieldnames=t.cols, lineterminator="\n")
            w.writeheader()
            w.writerows(t.rows)
    rows = []
    for (s, name), t in TABLES.items():
        if t.client:
            rows.append(dict(tipo="tabella_clienti", sistema=s, tabella=name))
    for f in FKS:
        rows.append(dict(tipo="collegamento", sistema=f["sys"], tabella=f["table"], colonna="/".join(f["cols"]),
                         riferimento="%s.%s" % (f["ttable"], "/".join(f["tcols"])), descrizione=f["desc"]))
    for s, t, col, c, d in CONCEPT_MAP:
        rows.append(dict(tipo="concetto", sistema=s, tabella=t, colonna=col, riferimento=c, descrizione=d))
    for s, t, k, az, cat, desc in SAME:
        rows.append(dict(tipo="stesso_cliente", sistema=s, tabella=t, codice_record=k, riferimento=az, categoria=cat, descrizione=desc))
    for er in ERRS:
        rows.append(dict(tipo="errore", sistema=er["sys"], tabella=er["table"], codice_record=er["key"], colonna=er["col"],
                         riferimento=er["ref"], categoria=er["cat"], descrizione=er["desc"]))
    with open(os.path.join(out, "verita.csv"), "w", encoding="utf-8", newline="") as fh:
        w = csv.DictWriter(fh, fieldnames=VERITA_COLS, lineterminator="\n")
        w.writeheader()
        for r in rows:
            w.writerow({c: r.get(c, "") for c in VERITA_COLS})


# =============================================================================
# Verifica di coerenza (rilegge i file dal disco)
# =============================================================================
def verify(out):
    problems = []

    def bad(msg):
        problems.append(msg)

    files = sorted(f for f in os.listdir(out) if f.endswith(".csv") and f != "verita.csv")
    if not 20 <= len(files) <= 40:
        bad("numero di tabelle fuori intervallo: %d" % len(files))
    data, keys = {}, {}
    for f in files:
        m = re.fullmatch(r"([a-z0-9_]+?)__(.+)\.csv", f)
        if not m or not re.fullmatch(r"[a-z0-9_]+", m[1]):
            bad("nome file non valido: " + f)
            continue
        with open(os.path.join(out, f), encoding="utf-8", newline="") as fh:
            rd = csv.DictReader(fh)
            rows = list(rd)
            data[(m[1], m[2])] = (rd.fieldnames, rows)
        for word in ("err", "dup", "test", "prova", "orfan", "fake", "wrong", "bad"):
            if word in m[2].lower() or any(word in c.lower() for c in data[(m[1], m[2])][0]):
                bad("possibile indizio nel nome di file o colonna: %s" % f)
    for (s, name), t in TABLES.items():
        cols, rows = data[(s, name)]
        idx = {}
        for r in rows:
            k = "/".join(r[c] for c in t.key)
            if k in idx:
                bad("chiave duplicata %s.%s %s" % (s, name, k))
            idx[k] = r
        keys[(s, name)] = idx
    with open(os.path.join(out, "verita.csv"), encoding="utf-8", newline="") as fh:
        rd = csv.DictReader(fh)
        if rd.fieldnames != VERITA_COLS:
            bad("intestazione di verita.csv errata")
        ver = list(rd)
    client = {(r["sistema"], r["tabella"]) for r in ver if r["tipo"] == "tabella_clienti"}
    for k in client:
        if k not in data:
            bad("tabella_clienti inesistente %s" % (k,))
    orphan_rows = {(r["sistema"], r["tabella"], r["codice_record"]) for r in ver if r["tipo"] == "errore" and r["descrizione"].startswith("riga orfana")}
    for r in ver:
        s, t = r["sistema"], r["tabella"]
        if r["tipo"] == "collegamento":
            cols = r["colonna"].split("/")
            tt, tc = r["riferimento"].split(".", 1)
            if (s, t) not in data or (s, tt) not in data:
                bad("collegamento con tabella inesistente: %s" % r)
                continue
            if any(c not in data[(s, t)][0] for c in cols) or any(c not in data[(s, tt)][0] for c in tc.split("/")):
                bad("collegamento con colonna inesistente: %s" % r)
        elif r["tipo"] == "concetto":
            if (s, t) not in client or r["colonna"] not in data[(s, t)][0] or r["riferimento"] not in CONCEPTS:
                bad("concetto non valido: %s" % r)
        elif r["tipo"] == "stesso_cliente":
            if r["codice_record"] not in keys.get((s, t), {}):
                bad("stesso_cliente: record inesistente %s" % r)
            if not re.fullmatch(r"AZ-\d{4}", r["riferimento"]):
                bad("stesso_cliente: riferimento non valido %s" % r)
        elif r["tipo"] == "errore":
            rec = keys.get((s, t), {}).get(r["codice_record"])
            if rec is None or r["colonna"] not in rec:
                bad("errore: record o colonna inesistente %s" % r)
                continue
            if rec[r["colonna"]] == r["riferimento"] and r["riferimento"] != "":
                bad("errore: il valore nel file coincide con il valore corretto %s" % r)
    # confronto puntuale con i valori errati inseriti
    for er in ERRS:
        v = keys[(er["sys"], er["table"])][er["key"]][er["col"]]
        if v != er["wrong"]:
            bad("errore non riscontrato nel file: %s (file=%r)" % (er, v))
        if er.get("concept") == "vat" and er["ref"] and not vat_ok(er["ref"]):
            bad("partita IVA di riferimento non valida: %s" % er)
        if "cifra di controllo" in er["desc"] and vat_ok(er["wrong"]):
            bad("partita IVA errata che risulta valida: %s" % er)
    # le partite IVA non segnalate come errate devono essere valide
    err_cells = {(e_["sys"], e_["table"], e_["key"], e_["col"]) for e_ in ERRS}
    test_keys = set()
    for s in SYSTEMS:
        for e in ENTS[s]:
            if e["kind"] == "test":
                test_keys |= {(c[0], c[1], c[2]) for c in CELLS.get(e["uid"], {}).values()}
    for s in SYSTEMS:
        for e in ENTS[s]:
            cell = CELLS.get(e["uid"], {}).get("vat")
            if not cell or e["kind"] == "test" or cell in err_cells:
                continue
            v = keys[(cell[0], cell[1])][cell[2]][cell[3]]
            if v and not vat_ok(v):
                bad("partita IVA non valida senza errore registrato: %s %s" % (cell, v))
    # integrita' referenziale: ogni riferimento esiste, salvo le righe orfane dichiarate
    n_orph = 0
    for f in FKS:
        tidx = {}
        for r in keys[(f["sys"], f["ttable"])].values():
            tidx["/".join(r[c] for c in f["tcols"])] = 1
        tkey = TABLES[(f["sys"], f["table"])].key
        for r in keys[(f["sys"], f["table"])].values():
            if f["cond"] and not f["cond"](r):
                continue
            vals = [r[c] for c in f["cols"]]
            if f["tf"]:
                vals = f["tf"](vals)
            if any(v == "" for v in vals):
                continue
            if "/".join(vals) not in tidx:
                rk = "/".join(r[c] for c in tkey)
                if (f["sys"], f["table"], rk) in orphan_rows:
                    n_orph += 1
                else:
                    bad("riferimento non risolto non dichiarato: %s.%s %s -> %s" % (f["sys"], f["table"], rk, vals))
    if n_orph < len(orphan_rows):
        bad("righe orfane dichiarate ma non orfane")
    # ogni record anagrafico di cliente ha una riga stesso_cliente
    same = {(r["sistema"], r["tabella"], r["codice_record"]) for r in ver if r["tipo"] == "stesso_cliente"}
    if len(same) != len(SAME):
        bad("righe stesso_cliente duplicate")
    # ogni azienda reale in 1-3 sistemi
    per_az = {}
    for s, t, k, az, cat, d in SAME:
        if cat != "prova":
            per_az.setdefault(az, set()).add(s)
    for az, ss in per_az.items():
        if not 1 <= len(ss) <= 3:
            bad("%s presente in %d sistemi" % (az, len(ss)))
    return problems, ver


def stats(ver):
    from collections import Counter
    print("Tabelle: %d (di cui anagrafiche %d)" % (len(TABLES), sum(t.client for t in TABLES.values())))
    print("Righe verita.csv per tipo:", dict(Counter(r["tipo"] for r in ver)))
    same = [r for r in ver if r["tipo"] == "stesso_cliente"]
    print("Categorie stesso_cliente:", dict(Counter(r["categoria"] or "-" for r in same)))
    az = {}
    for r in same:
        if r["categoria"] != "prova":
            az.setdefault(r["riferimento"], set()).add(r["sistema"])
    print("Aziende reali: %d; per numero di sistemi: %s" % (len(az), dict(Counter(len(v) for v in az.values()))))
    print("Record cliente per sistema:", dict(Counter(r["sistema"] for r in same)))
    print("Errori per categoria:", dict(Counter(r["categoria"] for r in ver if r["tipo"] == "errore")))
    print("Errori per sistema:", dict(Counter(r["sistema"] for r in ver if r["tipo"] == "errore")))


def main():
    out = os.path.abspath(sys.argv[1] if len(sys.argv) > 1 else "dataset_mdm")
    cos, prospects = build()
    it_share = sum(c.cc == "IT" for c in cos) / len(cos)
    render_odoo()
    render_jde()
    render_exact()
    render_ebs()
    render_suite()
    inject_errors()
    write_all(out)
    problems, ver = verify(out)
    stats(ver)
    print("Clienti italiani: %.0f%%" % (it_share * 100))
    if problems:
        print("\nPROBLEMI DI COERENZA:")
        for p in problems[:50]:
            print(" -", p)
        sys.exit(1)
    print("Verifica di coerenza superata.")
    zpath = out.rstrip("/") + ".zip"
    with zipfile.ZipFile(zpath, "w", zipfile.ZIP_DEFLATED) as z:
        for f in sorted(os.listdir(out)):
            if f.endswith(".csv"):
                z.write(os.path.join(out, f), f)
        z.write(os.path.abspath(__file__), "genera_dataset.py")
    print("Creato", zpath)


if __name__ == "__main__":
    main()

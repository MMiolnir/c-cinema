#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
Genere un fichier .ics des sorties cinema en France, titres en francais,
avec affiche, realisateur, scenaristes, directeur de la photographie,
acteurs principaux, genres et synopsis.

Toutes les donnees proviennent exclusivement de The Movie Database (TMDB).
Ce produit utilise l'API TMDB mais n'est ni approuve ni certifie par TMDB.

Version 1.0

Aucune dependance externe : uniquement la bibliotheque standard de Python.
"""

VERSION = "1.0"

import difflib
import json
import re
import os
import sys
import time
import unicodedata
import urllib.parse
import urllib.request
from concurrent.futures import ThreadPoolExecutor
from datetime import date, datetime, timedelta, timezone
from zoneinfo import ZoneInfo

# ---------------------------------------------------------------------------
# REGLAGES  -  la seule partie que vous aurez besoin de modifier
# ---------------------------------------------------------------------------

# Mode rapide : pour tester une modification en quelques secondes au lieu de
# plusieurs minutes. Reduit tout - une page de sorties, deux jours de seances.
# Le resultat est incomplet : c'est fait pour verifier qu'un changement marche,
# pas pour produire le vrai calendrier. A laisser sur False sur GitHub.
MODE_RAPIDE = False

REGION = "FR"          # pays dont on veut les dates de sortie
LANGUE = "fr-FR"       # langue des titres, genres et synopsis

# Types de sortie TMDB : 1=Premiere 2=Salles(limite) 3=Salles 4=Numerique 5=Physique 6=TV
TYPES_DE_SORTIE = "3|2"

# --- Complement AlloCine : les films de VOTRE cinema absents de TMDB --------
# Repere les ressorties, seances evenementielles et reprises que TMDB ignore.
# ATTENTION : ce n'est pas une API officielle mais une page interne d'AlloCine.
# Aucune garantie de fonctionnement, et l'usage releve de leurs conditions.
# Une panne de ce complement n'empeche JAMAIS le calendrier de se generer.
ALLOCINE_ACTIF = True
ALLOCINE_CINEMA = "P0702"          # identifiant du cinema chez AlloCine
ALLOCINE_NOM = "Pathé Montpellier Odysseum"
# Plafond du releve. Le script s'arrete de lui-meme bien avant si AlloCine ne
# publie plus rien (voir ALLOCINE_JOURS_VIDES_MAX), donc cette valeur ne sert
# que de garde-fou : elle borne le pire cas si la detection des jours vides ne
# se declenchait pas. Si le journal signale des seances jusqu'au dernier jour
# lu, c'est le moment de l'augmenter.
ALLOCINE_JOURS = 120               # plafond du releve, en jours
# Arret anticipe apres autant de jours vides d'affilee. Mettre cette valeur a
# ALLOCINE_JOURS (ou plus) desactive l'arret : la fenetre est alors lue en
# entier. C'est le choix retenu, car Pathe programme par cycles hebdomadaires :
# les seances ordinaires s'arretent apres 1 a 2 semaines, mais un evenement
# peut etre place bien plus loin, precede d'une longue plage vide.
ALLOCINE_JOURS_VIDES_MAX = 120     # = ALLOCINE_JOURS -> fenetre lue en entier
ALLOCINE_PAUSE = 0.2               # pause entre deux requetes, en secondes
ALLOCINE_JOURNAL_DETAILLE = True   # liste chaque film vu et pourquoi il est retenu ou non

# Rapprochement AlloCine -> TMDB. Un film n'est retenu que si le titre correspond
# vraiment : sans ce garde-fou, une seance evenement sans equivalent TMDB
# ramenait le premier resultat venu (Endgame, Star Wars...) et polluait le
# calendrier. Mieux vaut un film manquant qu'un film faux.
SEUIL_CORRESPONDANCE = 0.85        # 1.0 = titre identique, 0.85 = tres proche
# En ANNEES, pas en mois. Un film peut sortir en France bien apres son pays
# d'origine : Bleach, 2006 au Japon, 2015 en France, soit 9 ans d'ecart.
# Ce controle ne s'applique QUE si le titre ne correspond pas presque a
# l'identique (score < 0.97) : un titre exact l'emporte toujours.
TOLERANCE_ANNEE = 12               # annees

# Un film est considere comme "seance evenement" si sa sortie d'origine remonte
# a plus de X mois : c'est ce qui distingue une reprise (Akira 1988, Terminator 2
# 1991, Harry Potter 2001) d'un film normalement a l'affiche.
ANCIENNETE_REPRISE_MOIS = 12       # mois
INCLURE_AVANT_PREMIERES = True     # les avant-premieres du cinema comptent comme evenements

# Ecart minimal, en jours, entre la sortie d'origine et la date retenue pour
# qu'un film soit signale comme une reprise. Evite de marquer comme "reprise"
# une simple progression sortie limitee -> sortie nationale.
ECART_REPRISE_JOURS = 180
NOM_CALENDRIER_EVENEMENTS = "Séances événement - Pathé Odysseum"

# Troisieme calendrier : TOUTES les seances du cinema, avec horaires reels.
# Volume important (un multiplexe programme 60 a 120 seances par jour), d'ou
# une fenetre courte.
SEANCES_ACTIVES = True
SEANCES_JOURS = 14                 # profondeur, en jours
SEANCES_PUB_MINUTES = 15           # publicites et bandes-annonces avant le film
NOM_CALENDRIER_SEANCES = "Séances - Pathé Odysseum"
FICHIER_SEANCES = "docs/c-cinema-seances.ics"
FUSEAU_CINEMA = "Europe/Paris"
FICHIER_EVENEMENTS = "docs/c-cinema-evenements.ics"

# Profondeur d'historique. Un calendrier abonne est remplace en entier a chaque
# rafraichissement : un film disparait de votre agenda des qu'il sort de cette
# fenetre. Monter cette valeur garde les sorties plus longtemps, au prix d'une
# requete TMDB par film et par jour (environ 700 sorties par an en France).
JOURS_AVANT = 14       # on garde les sorties des 2 dernieres semaines
JOURS_APRES = 240      # et on anticipe sur environ 8 mois

# Filtre anti-bruit, base sur le champ "popularity" de TMDB.
# ATTENTION : cette valeur n'a pas de plafond, ce n'est pas une note sur 20.
# C'est un score d'attention recalcule chaque jour (pages vues, notes, ajouts
# en favoris et en liste de suivi, date de sortie, score de la veille).
# Consequence importante pour un calendrier tourne vers l'avenir : un film qui
# sort dans huit mois a un score faible parce que personne ne l'a encore
# consulte, pas parce qu'il est confidentiel. Un seuil eleve couperait donc
# surtout les sorties lointaines. Le journal affiche la repartition reelle
# pour vous aider a choisir : commencez a 0, montez seulement si necessaire.
# Deux seuils de popularite, parce que la mesure de TMDB est biaisee : elle
# reflete l'attention d'un public surtout anglophone. Un petit film francais y
# est mal note alors qu'il passe pres de chez vous ; un petit film international
# confidentiel ne passera jamais. On filtre donc plus severement l'etranger.
POPULARITE_MINIMALE = 3.0          # films en langue etrangere
POPULARITE_MINIMALE_FR = 1.0       # films en langue francaise
LANGUES_FRANCAISES = ("fr",)       # langues beneficiant du seuil francais

# TMDB classe la distribution par ordre de generique, tete d'affiche en premier.
# On reprend cet ordre et on plafonne : le premier role est donc toujours present.
ACTEURS_MAX = 12           # nombre d'acteurs affiches au maximum
NOMBRE_SCENARISTES = 3     # nombre de scenaristes affiches au maximum
# Taille de l'image source. Le format .ics ne permet PAS d'imposer une taille
# d'affichage : on choisit donc une resolution adaptee a la taille visee.
# Cible : moitie de la largeur d'un iPhone 13 = 195 points x3 = 585 px reels.
# w780 est la premiere taille TMDB au-dessus de 585 px -> image nette.
# Les affiches TMDB sont au format 2:3, la hauteur suit donc toute seule
# (585 px de large = 877 px de haut) : l'affiche est toujours entiere.
TAILLE_AFFICHE = "w780"            # w92 w154 w185 w342 w500 w780 original

LARGEUR_AFFICHE_HTML = 220         # largeur d'affichage de l'affiche dans Outlook, en pixels
ECART_AFFICHE_TEXTE = 16           # espace entre l'affiche et la colonne de texte, en pixels

NOM_DU_CALENDRIER = "Sorties cinema France"
PREFIXE_TITRE = ""                 # texte place devant le titre, ex. "🎬 "

# Le titre affiche dans l'agenda doit rester en alphabet latin. Ordre de repli :
#   1. le titre francais, s'il est en alphabet latin
#   2. sa romanisation, si TMDB en fournit une
#   3. le titre anglais, uniquement si REPLI_TITRE_ANGLAIS vaut True
#   4. sinon le film est ecarte du calendrier
#
# Laisse volontairement a False : un film dont personne n'a saisi le titre
# francais sur TMDB est, en pratique, un film trop confidentiel pour interesser.
# Le repli anglais le ferait remonter alors qu'on ne le veut pas.
REPLI_TITRE_ANGLAIS = False
FICHIER_DE_SORTIE = "docs/c-cinema.ics"

# Mise en valeur par caracteres Unicode "gras". Ce ne sont pas des styles mais
# de vrais caracteres, seule facon d'obtenir un rendu appuye dans un champ texte.
# Ils n'existent pas avec accents : le texte est donc desaccentue avant conversion.
LIBELLES_EN_GRAS = True
LANGUES_MAX = 3                    # langues parlees affichees a cote du pays

ESPACEMENT_SCORE = "   "           # entre le titre original et le score de popularite
SEPARATEUR_ROMANISATION = " — "    # entre le titre original et sa version en alphabet latin
LIGNES_AVANT_SYNOPSIS = 2          # aeration avant le synopsis (1 = comme les autres blocs)
LIGNES_AVANT_MENTION = 2           # aeration avant la mention legale TMDB

# Ce que doit contenir la ligne "Production" :
#   "societes"    -> les societes de production (Legendary Pictures, Studio Ghibli...)
#   "producteurs" -> les personnes creditees comme producteur
SOURCE_PRODUCTION = "societes"
NOMBRE_PRODUCTION = 3              # nombre d'entrees affichees au maximum
JOBS_PRODUCTION = ("Producer",)    # utilise seulement si SOURCE_PRODUCTION = "producteurs"
INCLURE_VERSION_HTML = True        # False sur Apple Calendrier : divise le fichier par deux
FILS_PARALLELES = 8                # requetes simultanees vers TMDB

# ---------------------------------------------------------------------------

BASE_API = "https://api.themoviedb.org/3"
LIEN_TMDB = "https://www.themoviedb.org/movie/"
BASE_IMAGES = "https://image.tmdb.org/t/p/"  # confirme au demarrage via /configuration

# Intitules de metiers TMDB, par ordre de priorite.
# Liste officielle : https://api.themoviedb.org/3/configuration/jobs
JOBS_REALISATION = ("Director",)
JOBS_SCENARIO = ("Screenplay", "Writer", "Co-Writer", "Scenario Writer", "Screenstory", "Teleplay")
JOBS_PHOTOGRAPHIE = ("Director of Photography", "Cinematography")


def cle_api():
    cle = os.environ.get("TMDB_API_KEY", "").strip()
    if not cle:
        sys.exit(
            "ERREUR : la variable d'environnement TMDB_API_KEY est vide.\n"
            "Sur GitHub : Settings > Secrets and variables > Actions > New repository secret."
        )
    return cle


def appel_api(chemin, parametres=None, tentatives=4):
    """Appelle l'API TMDB et renvoie le JSON. Reessaie en cas d'erreur reseau."""
    parametres = dict(parametres or {})
    parametres["api_key"] = cle_api()
    url = f"{BASE_API}{chemin}?{urllib.parse.urlencode(parametres)}"

    derniere_erreur = None
    for essai in range(tentatives):
        try:
            requete = urllib.request.Request(
                url, headers={"Accept": "application/json", "User-Agent": "calendrier-cine-fr"}
            )
            with urllib.request.urlopen(requete, timeout=30) as reponse:
                return json.loads(reponse.read().decode("utf-8"))
        except Exception as erreur:  # noqa: BLE001
            derniere_erreur = erreur
            if essai < tentatives - 1:
                time.sleep(2 ** essai)

    raise RuntimeError(
        f"Appel TMDB impossible ({chemin}) apres {tentatives} essais : {derniere_erreur}"
    )


def charger_base_images():
    """Recupere l'adresse de base des images telle que TMDB la publie."""
    global BASE_IMAGES
    try:
        config = appel_api("/configuration")
        base = config.get("images", {}).get("secure_base_url")
        if base:
            BASE_IMAGES = base
            print(f"Base images TMDB : {BASE_IMAGES}")
    except Exception as erreur:  # noqa: BLE001
        print(f"  (configuration indisponible, on garde {BASE_IMAGES} : {erreur})", file=sys.stderr)


# --- Recuperation des donnees ----------------------------------------------


def seuil_popularite(langue):
    """Seuil applicable a un film, selon sa langue d'origine."""
    if (langue or "").lower() in LANGUES_FRANCAISES:
        return POPULARITE_MINIMALE_FR
    return POPULARITE_MINIMALE


def lister_sorties():
    """Liste les films sortant dans la fenetre de dates choisie."""
    aujourdhui = date.today()
    debut = (aujourdhui - timedelta(days=JOURS_AVANT)).isoformat()
    fin = (aujourdhui + timedelta(days=JOURS_APRES)).isoformat()

    commun = {
        "language": LANGUE,
        "region": REGION,
        "with_release_type": TYPES_DE_SORTIE,
        "release_date.gte": debut,
        "release_date.lte": fin,
        "include_adult": "false",
        "include_video": "false",
        "sort_by": "primary_release_date.asc",
    }

    print(f"Sorties {REGION} du {debut} au {fin}")

    films = {}
    scores = []
    exemptes = []
    page, total_pages = 1, 1
    pages_max = 1 if MODE_RAPIDE else 500
    while page <= total_pages and page <= pages_max:
        donnees = appel_api("/discover/movie", {**commun, "page": page})
        total_pages = min(donnees.get("total_pages", 1), 500)
        for film in donnees.get("results", []):
            if not film.get("release_date"):
                continue
            popularite = float(film.get("popularity") or 0)
            scores.append((popularite, film.get("title") or "?",
                           (film.get("original_language") or "").lower()))
            langue = (film.get("original_language") or "").lower()
            if popularite < seuil_popularite(langue):
                continue
            if langue in LANGUES_FRANCAISES and popularite < POPULARITE_MINIMALE:
                exemptes.append(film.get("title") or "?")
            films[film["id"]] = {"id": film["id"], "date": film["release_date"], "impose": False}
        print(f"  page {page}/{total_pages} - {len(films)} films")
        page += 1

    afficher_repartition(scores)
    if exemptes:
        print(f"\n  {len(exemptes)} films francais gardes grace au seuil francais ({POPULARITE_MINIMALE_FR}) :")
        for titre in sorted(exemptes)[:15]:
            print(f"    - {titre}")
        if len(exemptes) > 15:
            print(f"    ... et {len(exemptes) - 15} autres")
    lister_sorties.derniers_scores = scores      # reutilise pour la couverture cinema
    return list(films.values())


PALIERS_POPULARITE_BASE = (0, 0.5, 1, 2, 3, 4, 5, 7, 10, 15, 20, 30, 50, 100)


def paliers_popularite():
    """Les paliers d'affichage, avec votre seuil actuel insere s'il en manque.

    Sans ca, un seuil a 3.5 n'apparait dans aucun tableau et vous perdez le
    repere qui vous sert justement a l'ajuster.
    """
    paliers = set(PALIERS_POPULARITE_BASE)
    paliers.add(POPULARITE_MINIMALE)
    return tuple(sorted(paliers))


def afficher_repartition(scores):
    """Montre, palier par palier, combien de films resteraient et lesquels partent.

    TMDB ne publie aucun bareme pour son champ popularity : la seule facon de
    choisir un seuil sans deviner est de regarder ses propres chiffres.
    """
    if not scores:
        return
    scores = sorted(scores)
    valeurs = [v for v, _, _ in scores]
    mediane = valeurs[len(valeurs) // 2]

    print(f"\nRepartition de la popularite ({len(scores)} sorties trouvees)")
    print(f"  minimum {valeurs[0]:.1f} | mediane {mediane:.1f} | maximum {valeurs[-1]:.1f}")
    print()
    print("  seuil  restants  perdus  exemples de films perdus a ce palier")
    print("  " + "-" * 68)

    precedent = -1.0
    for seuil in paliers_popularite():
        restants = sum(1 for v, _, lg in scores
                       if v >= (POPULARITE_MINIMALE_FR if lg in LANGUES_FRANCAISES else seuil))
        perdus = [t for v, t, lg in scores
                  if precedent <= v < seuil and lg not in LANGUES_FRANCAISES]
        exemples = ", ".join(t[:24] for t in perdus[:5])
        if len(perdus) > 5:
            exemples += f", +{len(perdus) - 5}"
        marque = " <-" if abs(seuil - POPULARITE_MINIMALE) < 0.001 else "   "
        print(f"  {seuil:>5}{marque} {restants:>7}  {len(perdus):>6}  {exemples}")
        precedent = seuil

    # Ce que votre reglage actuel ecarte, du plus populaire au moins populaire.
    # Si aucun de ces titres ne vous interesse, le seuil est bien choisi.
    # Deux listes separees : melangees, les films francais exclus (tous sous le
    # seuil francais) seraient noyes tout en bas et jamais visibles.
    for libelle, francais, seuil in (
        ("etrangers", False, POPULARITE_MINIMALE),
        ("francais", True, POPULARITE_MINIMALE_FR),
    ):
        exclus = sorted(
            ((v, t) for v, t, lg in scores
             if (lg in LANGUES_FRANCAISES) == francais and v < seuil),
            reverse=True,
        )
        if not exclus:
            print(f"\n  Aucun film {libelle} exclu au seuil {seuil}.")
            continue
        print(f"\n  Les {min(20, len(exclus))} films {libelle} les plus populaires"
              f" que vous excluez (seuil {seuil}) :")
        for valeur, titre in exclus[:20]:
            print(f"    {valeur:6.2f}  {titre}")
        if len(exclus) > 20:
            print(f"    ... et {len(exclus) - 20} autres, moins populaires encore")


def est_en_alphabet_latin(texte):
    """True si le texte ne contient aucune lettre hors alphabet latin.

    Les accents, cedilles et autres diacritiques restent du latin : seuls les
    kanji, hangul, cyrillique, arabe, grec, thai... declenchent une romanisation.
    """
    for caractere in texte:
        if caractere.isalpha():
            nom = unicodedata.name(caractere, "")
            if not nom.startswith("LATIN"):
                return False
    return True


def pays_d_origine(fiche):
    """Codes pays d'origine du film, tels que TMDB les renvoie."""
    pays = list(fiche.get("origin_country") or [])
    for bloc in fiche.get("production_countries") or []:
        code = bloc.get("iso_3166_1")
        if code and code not in pays:
            pays.append(code)
    return pays


def noms_des_pays(fiche):
    """Noms des pays de production, tels que TMDB les ecrit dans la fiche.

    Aucune traduction : TMDB ne traduit pas les noms de pays sur son API, et
    cela evite d'introduire une source exterieure. Pas d'appel supplementaire
    non plus : le nom est deja dans la fiche du film.
    """
    noms = []
    for bloc in fiche.get("production_countries") or []:
        nom = (bloc.get("name") or "").strip()
        if nom and nom not in noms:
            noms.append(nom)
    if not noms:  # a defaut, les codes ISO bruts
        noms = list(fiche.get("origin_country") or [])
    return noms


def romanisation(fiche, titre_original):
    """Version en alphabet latin du titre original, cherchee UNIQUEMENT sur TMDB.

    TMDB n'a pas de champ dedie au romaji : sa charte demande de ranger les
    titres romanises dans les titres alternatifs, avec le pays d'origine comme
    pays. On cherche donc, dans l'ordre :
      1. un titre alternatif dont le type mentionne romanisation ou translitteration
      2. un titre alternatif du pays d'origine ecrit en alphabet latin
      3. rien - on renvoie None et on laisse le titre original tel quel
    """
    if not titre_original or est_en_alphabet_latin(titre_original):
        return None

    alternatifs = (fiche.get("alternative_titles") or {}).get("titles") or []
    latins = [
        t for t in alternatifs
        if (t.get("title") or "").strip() and est_en_alphabet_latin(t["title"])
    ]

    for entree in latins:                       # 1. le type l'annonce explicitement
        type_ = (entree.get("type") or "").lower()
        if "roman" in type_ or "translit" in type_:
            return entree["title"].strip()

    origines = pays_d_origine(fiche)            # 2. depose sur le pays d'origine
    for entree in latins:
        if entree.get("iso_3166_1") in origines:
            return entree["title"].strip()

    return None


def traduction(fiche, langue):
    """Bloc 'data' de la traduction demandee, ou {} si elle n'existe pas.

    TMDB ne fait pas de repli automatique entre langues sur l'API, contrairement
    au site : il faut donc aller chercher la traduction nous-memes. On privilegie
    la variante americaine, puis britannique, puis n'importe laquelle.
    """
    blocs = (fiche.get("translations") or {}).get("translations") or []
    candidats = [t for t in blocs if t.get("iso_639_1") == langue]
    candidats.sort(key=lambda t: {"US": 0, "GB": 1}.get(t.get("iso_3166_1"), 2))
    for candidat in candidats:
        donnees = candidat.get("data") or {}
        if donnees.get("title") or donnees.get("overview"):
            return donnees
    return {}


def acteurs_principaux(distribution):
    """Tete d'affiche : l'ordre du generique TMDB, plafonne a ACTEURS_MAX.

    TMDB classe deja la distribution par importance, le premier role en tete.
    On s'y fie plutot que de deviner : le premier acteur est ainsi toujours
    present, et la liste ne bouge pas d'un mois a l'autre.
    """
    classee = sorted(
        [p for p in distribution if (p.get("name") or "").strip()],
        key=lambda p: p.get("order", 999),
    )
    return [p["name"].strip() for p in classee[:ACTEURS_MAX]]


def personnes_par_metier(equipe, metiers):
    """Noms des membres de l'equipe occupant l'un des metiers, sans doublon.

    Les noms sont repris tels quels depuis TMDB, sans transformation.
    L'ordre suit la priorite des metiers : un 'Screenplay' passe avant un 'Writer'.
    """
    trouves = []
    for metier in metiers:
        for personne in equipe:
            nom = (personne.get("name") or "").strip()
            if personne.get("job") == metier and nom and nom not in trouves:
                trouves.append(nom)
    return trouves


def sorties_salle_francaises(fiche):
    """Toutes les dates de sortie en salles en France, triees."""
    types_voulus = {int(t) for t in TYPES_DE_SORTIE.split("|") if t.strip().isdigit()}
    jours = []
    for pays in (fiche.get("release_dates") or {}).get("results", []):
        if pays.get("iso_3166_1") != REGION:
            continue
        for sortie in pays.get("release_dates", []):
            if sortie.get("type") not in types_voulus:
                continue
            try:
                jours.append(datetime.strptime((sortie.get("release_date") or "")[:10], "%Y-%m-%d").date())
            except ValueError:
                continue
    return sorted(jours)


def date_de_sortie_francaise(fiche):
    """Date de sortie en SALLES en France dans la fenetre, ou None.

    Deux roles :

    1. Les RESSORTIES : un film ancien peut avoir plusieurs dates francaises
       (1991 pour la sortie d'origine, 2026 pour la reprise). On prend celle qui
       tombe dans la fenetre, sinon un film de 1988 atterrirait en 1988.

    2. Le CONTROLE. /discover evalue with_release_type et release_date de facon
       independante : un film qui a DEJA eu une sortie salle par le passe et qui
       recoit aujourd'hui une sortie numerique ou TV en France ressort dans les
       resultats. C'est ainsi qu'Endgame ou Star Wars atterrissaient dans un
       calendrier de sorties cinema. On revalide donc chaque film sur sa fiche
       detaillee, et on renvoie None s'il n'a aucune sortie salle francaise dans
       la fenetre - le film est alors ecarte.
    """
    debut = date.today() - timedelta(days=JOURS_AVANT)
    fin = date.today() + timedelta(days=JOURS_APRES)
    candidates = [j for j in sorties_salle_francaises(fiche) if debut <= j <= fin]
    return min(candidates).isoformat() if candidates else None


def details_du_film(film):
    if not isinstance(film.get("id"), int):
        raise TypeError(f"identifiant TMDB invalide : {film.get('id')!r} (un entier est attendu)")

    """Une requete par film : fiche + generique, grace a append_to_response."""
    try:
        fiche = appel_api(
            f"/movie/{film['id']}",
            {"language": LANGUE, "append_to_response": "credits,translations,alternative_titles,release_dates"},
        )
    except Exception as erreur:  # noqa: BLE001
        print(f"  film {film['id']} ignore : {erreur}", file=sys.stderr)
        return None

    # TMDB ne fait aucun repli automatique entre langues : on lit les traductions
    # renvoyees dans le meme appel pour recuperer le titre et le synopsis anglais.
    anglais = traduction(fiche, "en")

    synopsis = (fiche.get("overview") or "").strip()
    synopsis_en_anglais = False
    if not synopsis:
        synopsis = (anglais.get("overview") or "").strip()
        synopsis_en_anglais = bool(synopsis)

    generique = fiche.get("credits") or {}

    equipe = generique.get("crew", [])
    realisateurs = personnes_par_metier(equipe, JOBS_REALISATION)
    scenaristes = personnes_par_metier(equipe, JOBS_SCENARIO)[:NOMBRE_SCENARISTES]
    photographie = personnes_par_metier(equipe, JOBS_PHOTOGRAPHIE)

    acteurs = acteurs_principaux(generique.get("cast", []))

    genres = [g["name"] for g in fiche.get("genres", []) if g.get("name")]

    if SOURCE_PRODUCTION == "producteurs":
        production = personnes_par_metier(equipe, JOBS_PRODUCTION)
    else:
        production = []
        for societe in fiche.get("production_companies") or []:
            nom = (societe.get("name") or "").strip()
            if nom and nom not in production:
                production.append(nom)
    production = production[:NOMBRE_PRODUCTION]

    titre = (fiche.get("title") or "").strip()
    titre_original = (fiche.get("original_title") or "").strip()
    titre_romanise = romanisation(fiche, titre_original)
    titre_anglais = (anglais.get("title") or "").strip()
    pays = noms_des_pays(fiche)

    sortie_initiale = None
    if film.get("impose"):
        jour_retenu = film["date"]          # seance evenement : la date du cinema prime
    else:
        jour_retenu = date_de_sortie_francaise(fiche)
        if jour_retenu:
            toutes = sorties_salle_francaises(fiche)
            retenu = datetime.strptime(jour_retenu, "%Y-%m-%d").date()
            if toutes and (retenu - toutes[0]).days >= ECART_REPRISE_JOURS:
                sortie_initiale = toutes[0].strftime("%d/%m/%Y")   # c'est une reprise
        if not jour_retenu:
            titre = (fiche.get("title") or film["id"])
            print(f"  ecarte : {titre} - pas de sortie salle FR dans la fenetre", file=sys.stderr)
            return None

    return {
        "id": film["id"],
        "date": jour_retenu,
        "titre": titre or titre_original or "Sans titre",
        "titre_original": titre_original,
        "titre_romanise": titre_romanise,
        "sortie_initiale": sortie_initiale,
        "titre_anglais": titre_anglais,
        "realisateurs": realisateurs,
        "scenaristes": scenaristes,
        "photographie": photographie,
        "production": production,
        "acteurs": acteurs,
        "genres": genres,
        "pays": pays,
        "synopsis": synopsis,
        "synopsis_en_anglais": synopsis_en_anglais,
        "affiche": fiche.get("poster_path"),
        "duree": duree_en_minutes(fiche.get("runtime")),
        "popularite": float(fiche.get("popularity") or 0) or None,
        "langue_origine": langue_originale(fiche),
        "langues": langues_du_film(fiche),
    }


def enrichir(films):
    print(f"\nRecuperation des fiches detaillees ({len(films)} films)...")
    with ThreadPoolExecutor(max_workers=FILS_PARALLELES) as executeur:
        resultats = list(executeur.map(details_du_film, films))

    complets = [r for r in resultats if r]
    rejetes = len(films) - len(complets)
    print(f"  {len(complets)} fiches retenues")
    if rejetes:
        print(f"  {rejetes} films ecartes : pas de sortie salle FR dans la fenetre")
        print("    (sortie numerique, TV ou physique remontee a tort par /discover)")
    return sorted(complets, key=lambda f: (f["date"], f["titre"]))


# --- Complement AlloCine ----------------------------------------------------

ALLOCINE_URL = "https://www.allocine.fr/_/showtimes/theater-{cinema}/d-{jour}/p-{page}"
NAVIGATEUR = (
    "Mozilla/5.0 (Macintosh; Intel Mac OS X 10_15_7) AppleWebKit/537.36 "
    "(KHTML, like Gecko) Chrome/126.0 Safari/537.36"
)


def cle_de_titre(titre):
    """Forme simplifiee d'un titre, pour comparer TMDB et AlloCine.

    On retire accents, ponctuation, articles initiaux et espaces multiples :
    "L'Odyssée" et "Odyssee" se rejoignent. Reste approximatif par nature.
    """
    texte = unicodedata.normalize("NFKD", (titre or "").lower())
    texte = "".join(c for c in texte if not unicodedata.combining(c))
    texte = "".join(c if c.isalnum() else " " for c in texte)
    mots = texte.split()
    while mots and mots[0] in {"le", "la", "les", "l", "un", "une", "des", "the", "a"}:
        mots.pop(0)
    return " ".join(mots)


def seances_du_cinema():
    """Films projetes dans le cinema, avec la date de leur premiere seance.

    Toute erreur est avalee : le calendrier TMDB doit rester generable meme si
    AlloCine change sa page, bloque la requete ou tombe en panne.
    """
    trouves = {}
    aujourdhui = date.today()
    dernier_jour_garni = None
    jours_garnis = 0
    jours_vides = 0

    debut = aujourdhui.isoformat()
    fin = (aujourdhui + timedelta(days=ALLOCINE_JOURS - 1)).isoformat()
    print(f"  releve du {debut} au {fin}")

    for decalage in range(2 if MODE_RAPIDE else ALLOCINE_JOURS):
        jour = (aujourdhui + timedelta(days=decalage)).isoformat()
        avant = len(trouves)
        page, total_pages = 1, 1
        while page <= total_pages and page <= 10:
            url = ALLOCINE_URL.format(cinema=ALLOCINE_CINEMA, jour=jour, page=page)
            try:
                requete = urllib.request.Request(url, headers={
                    "User-Agent": NAVIGATEUR,
                    "Accept": "application/json",
                })
                with urllib.request.urlopen(requete, timeout=20) as reponse:
                    donnees = json.loads(reponse.read().decode("utf-8"))
            except Exception as erreur:  # noqa: BLE001
                print(f"  AlloCine {jour} p{page} : {erreur}", file=sys.stderr)
                break

            total_pages = int((donnees.get("pagination") or {}).get("totalPages", 1))
            for entree in donnees.get("results", []):
                fiche = entree.get("movie")
                if not fiche or not fiche.get("internalId"):
                    continue
                identifiant = fiche["internalId"]
                if identifiant not in trouves:      # premiere projection = premier jour vu
                    trouves[identifiant] = (jour, fiche)
            page += 1
            time.sleep(ALLOCINE_PAUSE)   # on n'assomme pas le serveur

        if len(trouves) > avant or page > 1:
            jours_garnis += 1
            dernier_jour_garni = jour
            jours_vides = 0
        else:
            jours_vides += 1
            if jours_vides >= ALLOCINE_JOURS_VIDES_MAX:
                print(f"  arret au {jour} : {jours_vides} jours vides d'affilee")
                break

    print(f"  {jours_garnis} jours avec des seances, dernier : {dernier_jour_garni or 'aucun'}")
    if dernier_jour_garni == fin:
        print("  -> des seances jusqu'au dernier jour lu :"
              " augmentez ALLOCINE_JOURS pour voir plus loin.")
    elif dernier_jour_garni:
        print(f"  -> AlloCine ne publie rien au-dela du {dernier_jour_garni}")

    return trouves


def sortie_originale(fiche):
    """Date de sortie d'ORIGINE du film : (jour, annee) ou (None, annee).

    AlloCine peut lister plusieurs sorties pour un meme film : celle d'origine
    et la ressortie. Rien ne garantit l'ordre, on prend donc systematiquement la
    plus ancienne - sinon une retrospective Harry Potter serait vue comme un
    film de 2026 et rejetee par le filtre d'anciennete.
    """
    sorties = []   # (annee, date complete ou None)
    for sortie in fiche.get("releases") or []:
        brut = (sortie.get("releaseDate") or {}).get("date")
        if not brut:
            continue
        try:
            jour = datetime.strptime(brut[:10], "%Y-%m-%d").date()
            sorties.append((jour.year, jour))
        except ValueError:
            if len(brut) >= 4 and brut[:4].isdigit():
                # annee seule : on ne fabrique pas de jour qui n'existe pas
                sorties.append((int(brut[:4]), None))

    if sorties:
        plus_ancienne = min(a for a, _ in sorties)
        precises = [j for a, j in sorties if a == plus_ancienne and j]
        return (min(precises) if precises else None), plus_ancienne

    production = fiche.get("productionYear")            # a defaut, l'annee de production
    return None, int(production) if production else None


def annee_de_sortie(fiche):
    """Raccourci : l'annee seule."""
    return sortie_originale(fiche)[1]


SEPARATEURS_TITRE = (" - ", " – ", " — ", " : ", ": ", " partie ", " chapitre ", " vol ")
PLAFOND_VARIANTE = 0.95            # une troncature ne vaut jamais un titre exact


def variantes_de_titre(titre):
    """Le titre complet, puis ses versions tronquees aux separateurs.

    AlloCine ajoute souvent un sous-titre absent de TMDB :
    'La Bataille de Gaulle - partie 1 : L'Age de Fer' contre 'La Bataille de
    Gaulle'. Comparer les titres entiers fait chuter la proximite a 0.62 et
    rejette un film pourtant present sur TMDB.
    """
    vues, sorties = set(), []
    candidats = [titre]
    bas = titre.lower()
    for separateur in SEPARATEURS_TITRE:
        if separateur in bas:
            debut = titre[:bas.index(separateur)].strip(" -–—:,")
            # Un seul mot est trop generique : "Bleach" capterait toute la
            # franchise. On exige au moins deux mots pour une troncature.
            if len(debut) >= 4 and len(cle_de_titre(debut).split()) >= 2:
                candidats.append(debut)
    for candidat in candidats:
        cle = cle_de_titre(candidat)
        if cle and cle not in vues:
            vues.add(cle)
            sorties.append(candidat)
    return sorties


def ressemblance(a, b):
    """Proximite de deux titres, entre 0 et 1.

    On compare toutes les variantes tronquees de chaque cote et on garde la
    meilleure. Un titre qui est le debut mot-a-mot de l'autre est traite comme
    une correspondance forte : c'est le cas des films en plusieurs parties.
    """
    # Le titre complet d'abord : lui seul peut atteindre 1.00.
    meilleur = difflib.SequenceMatcher(None, cle_de_titre(a or ""), cle_de_titre(b or "")).ratio()

    # Puis les versions tronquees, plafonnees a 0.95 pour qu'une correspondance
    # exacte l'emporte toujours : sinon 'Dune' capterait 'Dune : Deuxieme Partie'
    # aussi bien que le vrai 'Dune'.
    for va in variantes_de_titre(a or ""):
        for vb in variantes_de_titre(b or ""):
            ca, cb = cle_de_titre(va), cle_de_titre(vb)
            if not ca or not cb:
                continue
            score = difflib.SequenceMatcher(None, ca, cb).ratio()
            court, long_ = sorted((ca.split(), cb.split()), key=len)
            # Tous les mots du titre court figurent dans le long : c'est le cas
            # de "Bleach : Hell Verse" dans "Bleach - Le Film 4 : Hell Verse".
            # TROIS mots minimum : a deux, "Star Wars" capterait "Cine-concert
            # Star Wars", et "Alien" capterait "Alien vs Predator".
            if len(court) >= 3 and set(court) <= set(long_):
                score = max(score, 0.90)
            meilleur = max(meilleur, min(score, PLAFOND_VARIANTE))
    return meilleur


def chercher_sur_tmdb(titre, titre_original, annee):
    """Retrouve le film sur TMDB. Renvoie (id, titre TMDB, score) ou None.

    Sans ca, les notes seraient bien plus pauvres : AlloCine ne fournit ni
    scenariste, ni photographie, ni acteurs, ni pays.

    Regle stricte : on n'accepte que si le titre correspond vraiment. Beaucoup
    de seances evenement (cine-concerts, retransmissions, soirees a theme) n'ont
    aucun equivalent sur TMDB - il ne faut surtout pas leur attribuer un film au
    hasard. L'annee sert de second garde-fou, avec une tolerance large car la
    sortie francaise peut suivre la sortie d'origine de plusieurs annees.
    """
    tentatives = []
    for variante in variantes_de_titre(titre or ""):
        tentatives.append((variante, annee))
        tentatives.append((variante, None))
    if titre_original and titre_original != titre:
        for variante in variantes_de_titre(titre_original):
            tentatives.append((variante, annee))

    meilleur = None
    for recherche, an in tentatives:
        parametres = {"query": recherche, "language": LANGUE, "include_adult": "false"}
        if an:
            parametres["primary_release_year"] = an
        try:
            resultats = appel_api("/search/movie", parametres).get("results") or []
        except Exception:  # noqa: BLE001
            continue

        for trouve in resultats[:10]:
            score = max(
                ressemblance(titre or recherche, trouve.get("title") or ""),
                ressemblance(titre or recherche, trouve.get("original_title") or ""),
                ressemblance(recherche, trouve.get("title") or ""),
            )
            # L'annee ne sert que de garde-fou secondaire : un titre quasi
            # identique l'emporte. Un anime sorti en France dix ans apres le
            # Japon serait sinon rejete a tort.
            annee_tmdb = (trouve.get("release_date") or "")[:4]
            if score < 0.97 and annee and annee_tmdb.isdigit():
                if abs(int(annee_tmdb) - annee) > TOLERANCE_ANNEE:
                    continue
            # Departage : a score egal, le titre TMDB le plus proche du titre
            # complet d'AlloCine l'emporte. Sans ca, "Bleach" et
            # "Bleach : Hell Verse" sont a egalite et le hasard tranche.
            complet = max(
                difflib.SequenceMatcher(None, cle_de_titre(titre or recherche),
                                        cle_de_titre(trouve.get("title") or "")).ratio(),
                difflib.SequenceMatcher(None, cle_de_titre(titre or recherche),
                                        cle_de_titre(trouve.get("original_title") or "")).ratio(),
            )
            if score >= SEUIL_CORRESPONDANCE and (
                    meilleur is None or (score, complet) > (meilleur[2], meilleur[3])):
                meilleur = (trouve["id"], trouve.get("title") or "", score, complet)

        if meilleur and meilleur[2] > 0.99:      # correspondance exacte, inutile d'insister
            break

    return meilleur[:3] if meilleur else None


def couverture_du_cinema(scores, seances):
    """Quel seuil de popularite faut-il pour voir les films de VOTRE cinema ?

    Le tableau de repartition dit combien de films on garde sur l'ensemble des
    sorties nationales. Ce n'est pas la bonne question : ce qui compte, c'est
    combien de films REELLEMENT PROJETES pres de chez vous survivent au filtre.
    On croise donc la programmation du cinema avec la popularite TMDB.
    """
    if not scores or not seances:
        return

    # popularite des sorties TMDB, indexee par titre simplifie
    popularites = {}
    for valeur, titre, langue in scores:
        cle = cle_de_titre(titre)
        if cle and valeur >= popularites.get(cle, (-1, ""))[0]:
            popularites[cle] = (valeur, langue)

    apparies, absents = [], []
    for _, (_, fiche) in seances.items():
        titre = (fiche.get("title") or "").strip()
        cle = cle_de_titre(titre)
        if cle in popularites:
            valeur, langue = popularites[cle]
            apparies.append((valeur, titre, langue))
        else:
            absents.append(titre)

    print(f"\n=== Couverture de {ALLOCINE_NOM} selon le seuil ===")
    print(f"  {len(seances)} films a l'affiche, {len(apparies)} retrouves dans les sorties TMDB")
    if absents:
        print(f"  {len(absents)} absents des sorties TMDB (reprises, evenements, titres differents)")
    if not apparies:
        return

    print(f"\n  seuil etranger  films du cinema conserves"
          f"  (seuil francais fixe a {POPULARITE_MINIMALE_FR})")
    print("  " + "-" * 40)
    for seuil in paliers_popularite():
        gardes = sum(1 for v, _, lg in apparies
                     if v >= (POPULARITE_MINIMALE_FR if lg in LANGUES_FRANCAISES else seuil))
        part = gardes / len(apparies) * 100
        marque = " <- actuel" if abs(seuil - POPULARITE_MINIMALE) < 0.001 else ""
        barre = "#" * round(part / 5)
        print(f"  {seuil:>5}  {gardes:>3}/{len(apparies)} ({part:>3.0f}%) {barre}{marque}")

    perdus = sorted((v, t) for v, t, lg in apparies if v < seuil_popularite(lg))
    if perdus:
        print(f"\n  Films projetes chez vous mais ABSENTS de votre calendrier"
              f" (seuil {POPULARITE_MINIMALE}) :")
        for valeur, titre in reversed(perdus):
            print(f"    {valeur:6.2f}  {titre}")
    else:
        print(f"\n  Aucun film de votre cinema n'est perdu au seuil {POPULARITE_MINIMALE}.")


# Formats de seance, d'apres la structure reelle renvoyee par AlloCine :
#   experience = ["E_4DX", "PLF"]   projection = ["DIGITAL"]
#   picture / sound / comfort = null ou une valeur
# Une valeur a None est reconnue mais volontairement pas affichee.
FORMATS_LISIBLES = {
    "E_4DX": "4DX", "FOUR_DX": "4DX", "4DX": "4DX",
    "E_IMAX": "IMAX", "IMAX": "IMAX", "IMAX_EXPERIENCE": "IMAX", "IMAX_3D": "IMAX 3D",
    "E_SCREENX": "ScreenX", "SCREENX": "ScreenX",
    "E_DOLBY_CINEMA": "Dolby Cinema", "DOLBY_CINEMA": "Dolby Cinema",
    # PLF = Premium Large Format. AlloCine l'emploie au sens large de "salle
    # haut de gamme" : votre seance 4DX en porte la mention, alors qu'une salle
    # 4DX n'est pas une salle grand ecran.
    "PLF": "Salle premium", "E_PLF": "Salle premium", "PREMIUM_LARGE_FORMAT": "Salle premium",
    "THREE_D": "3D", "3D": "3D", "SEVENTY_MM": "70mm", "70MM": "70mm",
    "ICE": "ICE", "E_ICE": "ICE",
    "DOLBY_ATMOS": "Dolby Atmos", "ATMOS": "Dolby Atmos", "DTS_X": "DTS:X",
    "HDR": "HDR", "LASER": "Laser", "IMAX_LASER": "IMAX Laser", "FOUR_K": "4K",
    "IMAX70MM": "IMAX 70mm", "IMAX_70MM": "IMAX 70mm", "E_IMAX_70MM": "IMAX 70mm",
    "70": "70mm", "FILM_70MM": "70mm", "35MM": "35mm", "PELLICULE": "Pellicule",
    "CONFORT": "Confort", "PREMIUM": "Premium", "VIP": "VIP",
    # reconnus mais sans interet a l'affichage
    "DIGITAL": None, "TWO_D": None, "STANDARD": None, "CLASSIC": None,
}

# Seuls ces champs decrivent le format. "service" contient l'accessibilite
# (DISABLED_ACCESS), "tags" des libelles techniques et "data" les liens de
# billetterie : les inclure polluerait le titre des evenements.
CHAMPS_FORMAT = ("experience", "projection", "picture", "sound", "comfort")

# Les "tags" melangent du format et du bruit. On ne garde que ces prefixes :
#   Auditorium.Experience.4dx  Format.Projection.70mm  -> retenus
#   Localization.Language.French  Showtime.Accessibility.*  -> ignores
PREFIXES_TAGS = ("format.", "auditorium.")
PREFIXES_TAGS_EXCLUS = ("auditorium.accessibility",)

# Certains formats se combinent : IMAX 70mm n'est ni IMAX seul ni 70mm seul.
COMBINAISONS_FORMAT = (
    (("IMAX", "70mm"), "IMAX 70mm"),
    (("IMAX", "3D"), "IMAX 3D"),
    (("IMAX", "Laser"), "IMAX Laser"),
    (("4DX", "3D"), "4DX 3D"),
    (("ScreenX", "3D"), "ScreenX 3D"),
    (("Dolby Cinema", "3D"), "Dolby Cinema 3D"),
)

CODES_RENCONTRES = set()   # diagnostic : tout ce qu'AlloCine a envoye


def jetons(valeur, profondeur=0):
    """Aplati une valeur JSON en une liste de chaines exploitables."""
    if profondeur > 2:
        return []
    if isinstance(valeur, str):
        return [valeur]
    if isinstance(valeur, (list, tuple)):
        return [j for v in valeur for j in jetons(v, profondeur + 1)]
    if isinstance(valeur, dict):
        return [j for v in valeur.values() for j in jetons(v, profondeur + 1)]
    return []


def formats_de_seance(seance):
    """Marqueurs de format d'une seance : IMAX, 4DX, 3D, Grand format...

    Un code inconnu est remis en forme plutot qu'ignore, mais seuls les champs
    de CHAMPS_FORMAT sont lus : le reste de la seance contient de
    l'accessibilite et des liens de billetterie qui n'ont rien a faire ici.
    """
    candidats = []
    for cle in CHAMPS_FORMAT:
        candidats += [j for j in jetons(seance.get(cle)) if isinstance(j, str)]

    # les tags apportent parfois une precision absente des autres champs
    for tag in jetons(seance.get("tags")):
        if not isinstance(tag, str):
            continue
        bas = tag.lower()
        if bas.startswith(PREFIXES_TAGS_EXCLUS) or not bas.startswith(PREFIXES_TAGS):
            continue
        candidats.append(tag.rsplit(".", 1)[-1])

    trouves = []
    for jeton in candidats:
        if not (2 <= len(jeton) <= 30):
            continue
        CODES_RENCONTRES.add(jeton.strip())
        brut = jeton.strip().upper().replace(" ", "_").replace("-", "_")
        # AlloCine prefixe ses codes : E_ pour une experience (E_4DX),
        # F_ pour un format (F_3D). On les retire avant de chercher, ce qui
        # rend inutile d'enumerer chaque variante.
        noyau = brut
        for prefixe in ("E_", "F_", "A_", "P_"):
            if noyau.startswith(prefixe) and len(noyau) > len(prefixe) + 1:
                noyau = noyau[len(prefixe):]
                break
        if brut in FORMATS_LISIBLES:
            lisible = FORMATS_LISIBLES[brut]
        elif noyau in FORMATS_LISIBLES:
            lisible = FORMATS_LISIBLES[noyau]
        else:
            lisible = noyau.replace("_", " ").title()
        if lisible and lisible not in trouves:
            trouves.append(lisible)

    # IMAX + 70mm doit devenir "IMAX 70mm", pas deux mentions separees
    for morceaux, ensemble in COMBINAISONS_FORMAT:
        if all(m in trouves for m in morceaux):
            for m in morceaux:
                trouves.remove(m)
            trouves.insert(0, ensemble)

    # "IMAX 70mm - Salle premium" est redondant : IMAX est deja du premium
    if any(t.startswith("IMAX") for t in trouves) and "Salle premium" in trouves:
        trouves.remove("Salle premium")
    return trouves


def horaires_du_cinema():
    """Toutes les seances du cinema sur SEANCES_JOURS jours.

    Renvoie {identifiant film: (fiche, [seances])}, chaque seance etant un
    dictionnaire avec son debut, sa version (VF/VO) et son identifiant propre.
    """
    trouves = {}
    echantillon = []
    aujourdhui = date.today()
    debut = aujourdhui.isoformat()
    fin = (aujourdhui + timedelta(days=SEANCES_JOURS - 1)).isoformat()
    print(f"  releve des horaires du {debut} au {fin}")

    for decalage in range(2 if MODE_RAPIDE else SEANCES_JOURS):
        jour = (aujourdhui + timedelta(days=decalage)).isoformat()
        page, total_pages = 1, 1
        while page <= total_pages and page <= 10:
            url = ALLOCINE_URL.format(cinema=ALLOCINE_CINEMA, jour=jour, page=page)
            try:
                requete = urllib.request.Request(url, headers={
                    "User-Agent": NAVIGATEUR, "Accept": "application/json"})
                with urllib.request.urlopen(requete, timeout=20) as reponse:
                    donnees = json.loads(reponse.read().decode("utf-8"))
            except Exception as erreur:  # noqa: BLE001
                print(f"  horaires {jour} p{page} : {erreur}", file=sys.stderr)
                break

            total_pages = int((donnees.get("pagination") or {}).get("totalPages", 1))
            for entree in donnees.get("results", []):
                fiche = entree.get("movie") or {}
                identifiant = fiche.get("internalId")
                if not identifiant:
                    continue
                if identifiant not in trouves:
                    trouves[identifiant] = (fiche, [])
                deja = {s["id"] for s in trouves[identifiant][1]}
                for groupe in (entree.get("showtimes") or {}).values():
                    for seance in groupe or []:
                        sid = seance.get("internalId")
                        if not sid or sid in deja or not seance.get("startsAt"):
                            continue
                        deja.add(sid)
                        if not echantillon:
                            echantillon.append(seance)
                        trouves[identifiant][1].append({
                            "id": sid,
                            "debut": seance.get("startsAt"),
                            "fin": seance.get("endsAt"),
                            "version": (seance.get("diffusionVersion") or "").upper(),
                            "formats": formats_de_seance(seance),
                            "avp": bool(seance.get("isPreview")),
                        })
            page += 1
            time.sleep(ALLOCINE_PAUSE)

    total = sum(len(v[1]) for v in trouves.values())
    print(f"  {len(trouves)} films, {total} seances relevees")

    # Diagnostic : la structure exacte d'une seance, pour savoir ce qu'AlloCine
    # expose reellement (formats, salle, version...). A lire une fois.
    if echantillon:
        print("\n  Structure d'une seance telle qu'AlloCine la renvoie :")
        for cle, valeur in echantillon[0].items():
            apercu = json.dumps(valeur, ensure_ascii=False)
            print(f"    {cle:22} = {apercu[:90]}")

    return trouves


def horodatage_utc(texte_local):
    """'2026-09-07T20:15:00' (heure du cinema) -> '20260907T181500Z'."""
    try:
        moment = datetime.fromisoformat(texte_local.replace("Z", "+00:00"))
    except (ValueError, AttributeError):
        return None
    if moment.tzinfo is None:
        try:
            moment = moment.replace(tzinfo=ZoneInfo(FUSEAU_CINEMA))
        except Exception:  # noqa: BLE001
            moment = moment.replace(tzinfo=timezone.utc)
    return moment.astimezone(timezone.utc).strftime("%Y%m%dT%H%M%SZ")


def seances_evenement():
    """Second calendrier : les reprises et seances ponctuelles du cinema.

    On part des films a l'affiche, on ne garde que ceux dont la sortie d'origine
    est ancienne, puis on va chercher leur fiche complete sur TMDB pour que la
    mise en forme soit identique au calendrier principal.
    """
    if not ALLOCINE_ACTIF:
        return []

    print(f"\n=== Seances evenement - {ALLOCINE_NOM} ({ALLOCINE_JOURS} jours) ===")
    try:
        seances = seances_du_cinema()
    except Exception as erreur:  # noqa: BLE001
        print(f"  abandonne : {erreur}", file=sys.stderr)
        return []

    if not seances:
        print("  aucune seance recuperee (page modifiee, requete bloquee, ou panne)")
        return []

    couverture_du_cinema(getattr(lister_sorties, "derniers_scores", []), seances)

    limite = date.today().year - (ANCIENNETE_REPRISE_MOIS // 12)
    retenus, ecartes = [], []
    for identifiant, (jour, fiche) in seances.items():
        premiere, annee = sortie_originale(fiche)
        titre = (fiche.get("title") or "?").strip()
        avant_premiere = bool((fiche.get("customFlags") or {}).get("isPremiere"))

        if avant_premiere and INCLURE_AVANT_PREMIERES:
            # une avant-premiere est un evenement quel que soit l'age du film
            retenus.append((jour, fiche, annee, premiere, True))
        elif annee is None:
            ecartes.append((titre, "annee de sortie inconnue"))
        elif annee > limite:
            ecartes.append((titre, f"sorti en {annee}, trop recent"))
        else:
            retenus.append((jour, fiche, annee, premiere, False))

    nb_avp = sum(1 for r in retenus if r[4])
    print(f"  {len(seances)} films a l'affiche, {len(retenus)} retenus"
          f" ({len(retenus) - nb_avp} reprises, {nb_avp} avant-premieres)")
    if ALLOCINE_JOURNAL_DETAILLE and ecartes:
        print(f"  ecartes ({len(ecartes)}) - seuil : sorti avant {limite + 1}")
        for titre, raison in sorted(ecartes):
            print(f"    - {titre} : {raison}")
    if not retenus:
        return []

    films = []
    for jour, fiche, annee, premiere, avant_premiere in sorted(retenus, key=lambda x: x[0]):
        titre = (fiche.get("title") or "").strip()
        trouve = chercher_sur_tmdb(titre, (fiche.get("originalTitle") or "").strip(), annee)
        if not trouve:
            print(f"    ? {jour}  {titre} ({annee}) - aucune correspondance fiable sur TMDB, ignore")
            continue
        identifiant_tmdb, titre_tmdb, score = trouve
        if score < 0.99:
            print(f"      {titre!r} rapproche de {titre_tmdb!r} (proximite {score:.2f})")
        detail = details_du_film({"id": identifiant_tmdb, "date": jour, "impose": True})
        if detail:
            detail["evenement"] = True
            detail["avant_premiere"] = avant_premiere
            if avant_premiere:
                # pour une avant-premiere, la date utile est la sortie nationale a venir
                detail["sortie_initiale"] = None
                detail["sortie_nationale"] = (
                    premiere.strftime("%d/%m/%Y")
                    if premiere and premiere.isoformat() > jour else None
                )
            else:
                detail["sortie_initiale"] = premiere.strftime("%d/%m/%Y") if premiere else str(annee)
            films.append(detail)
            marque = "AVP" if avant_premiere else "reprise"
            print(f"    + {jour}  [{marque}] {detail['titre']} ({annee})")

    return films


# --- Mise en forme ----------------------------------------------------------


def accorder(libelle_singulier, libelle_pluriel, personnes):
    """Choisit le libelle selon le nombre de personnes."""
    return libelle_pluriel if len(personnes) > 1 else libelle_singulier


def url_affiche(chemin):
    """Adresse de l'affiche. AlloCine fournit une adresse complete, TMDB un chemin."""
    if not chemin:
        return None
    if chemin.startswith("http"):
        return chemin
    return f"{BASE_IMAGES}{TAILLE_AFFICHE}{chemin}"


def titre_pour_agenda(film):
    """Titre de l'evenement, toujours en alphabet latin. None = film ecarte.

    Quand TMDB n'a pas de titre francais, il renvoie le titre d'origine dans son
    ecriture d'origine : un titre en arabe ou en coreen se retrouverait tel quel
    dans l'agenda, illisible. On cherche alors une version latine, et a defaut
    on n'affiche pas le film du tout.
    """
    titre = (film.get("titre") or "").strip()
    if titre and est_en_alphabet_latin(titre):
        return titre

    romanise = (film.get("titre_romanise") or "").strip()
    if romanise and est_en_alphabet_latin(romanise):
        return romanise

    if REPLI_TITRE_ANGLAIS:
        anglais = (film.get("titre_anglais") or "").strip()
        if anglais and est_en_alphabet_latin(anglais):
            return anglais

    return None


def langue_originale(fiche):
    """Nom de la langue d'origine du film, tel que TMDB le donne.

    Utile pour distinguer une VOST anglaise d'une VOST coreenne. Aucune requete
    supplementaire : spoken_languages arrive avec la fiche du film.
    """
    code = (fiche.get("original_language") or "").lower()
    if not code:
        return None
    for langue in fiche.get("spoken_languages") or []:
        if (langue.get("iso_639_1") or "").lower() == code:
            return (langue.get("english_name") or langue.get("name") or "").strip() or None
    return code.upper()


def duree_en_minutes(valeur):
    """Duree en minutes, quelle que soit la forme recue.

    TMDB renvoie un entier de minutes. AlloCine renvoie une chaine ISO 8601 du
    type 'PT1H50M0S' - c'est ce qui a fait planter une version precedente.
    """
    if isinstance(valeur, bool) or valeur is None:
        return 0
    if isinstance(valeur, (int, float)):
        entier = int(valeur)
        return round(entier / 60) if entier > 600 else entier   # secondes ou minutes
    if isinstance(valeur, str):
        texte = valeur.strip().upper()
        if texte.isdigit():
            entier = int(texte)
            return round(entier / 60) if entier > 600 else entier
        trouve = re.fullmatch(
            r"P(?:(\d+)D)?(?:T(?:(\d+)H)?(?:(\d+)M)?(?:(\d+(?:\.\d+)?)S)?)?", texte)
        if trouve:
            jours, heures, minutes, secondes = (float(g or 0) for g in trouve.groups())
            return round(jours * 1440 + heures * 60 + minutes + secondes / 60)
    return 0


def gras(texte):
    """Texte en caracteres Unicode gras, accents retires au prealable.

    L'alphabet gras d'Unicode ne couvre ni les accents ni les cedilles :
    'Realisateur' passe entierement en gras, 'Réalisateur' laisserait le 'é'
    en taille normale au milieu du mot. On desaccentue donc d'abord.
    """
    if not LIBELLES_EN_GRAS or not texte:
        return texte
    depouille = unicodedata.normalize("NFKD", str(texte))
    depouille = "".join(c for c in depouille if not unicodedata.combining(c))
    sortie = []
    for c in depouille:
        if "a" <= c <= "z":
            sortie.append(chr(0x1D5EE + ord(c) - ord("a")))
        elif "A" <= c <= "Z":
            sortie.append(chr(0x1D5D4 + ord(c) - ord("A")))
        elif "0" <= c <= "9":
            sortie.append(chr(0x1D7EC + ord(c) - ord("0")))
        else:
            sortie.append(c)
    return "".join(sortie)


def langues_du_film(fiche):
    """Langues parlees du film, celle d'origine en tete, telles que TMDB les nomme."""
    origine = (fiche.get("original_language") or "").lower()
    langues = []
    for bloc in fiche.get("spoken_languages") or []:
        nom = (bloc.get("english_name") or bloc.get("name") or "").strip()
        if not nom or nom in langues:
            continue
        if (bloc.get("iso_639_1") or "").lower() == origine:
            langues.insert(0, nom)
        else:
            langues.append(nom)
    return langues[:LANGUES_MAX]


def duree_lisible(minutes):
    """90 -> '1h30', 48 -> '48min', 0 ou None -> None."""
    try:
        minutes = int(minutes or 0)
    except (TypeError, ValueError):
        return None
    if minutes <= 0:
        return None
    heures, reste = divmod(minutes, 60)
    if not heures:
        return f"{reste}min"
    return f"{heures}h{reste:02d}" if reste else f"{heures}h"


def titre_original_a_afficher(film):
    """Titre original entre parentheses dans la note, avec sa romanisation.

    On le compare a ce qui est reellement affiche dans l'agenda, pas au titre
    francais : quand le titre francais manque, c'est la romanisation qui sert
    de titre d'evenement, et l'ecriture d'origine merite d'apparaitre dans la
    note. On evite en revanche de repeter deux fois la meme chaine.
    """
    original = (film.get("titre_original") or "").strip()
    if not original:
        return None

    affiche = (titre_pour_agenda(film) or film.get("titre") or "").strip()
    if original.casefold() == affiche.casefold():
        return None

    romanise = (film.get("titre_romanise") or "").strip()
    if (
        romanise
        and romanise.casefold() != original.casefold()
        and romanise.casefold() != affiche.casefold()
    ):
        return f"{original}{SEPARATEUR_ROMANISATION}{romanise}"
    return original


def bloc_equipe_technique(film):
    """Realisation, scenario et photographie : un poste par ligne."""
    lignes = []
    if film["realisateurs"]:
        libelle = accorder("Réalisateur", "Réalisateurs", film["realisateurs"])
        lignes.append((libelle, ", ".join(film["realisateurs"])))
    if film["scenaristes"]:
        lignes.append(("Scénario", ", ".join(film["scenaristes"])))
    if film["photographie"]:
        lignes.append(("Photographie", ", ".join(film["photographie"])))
    if film.get("production"):
        lignes.append(("Production", ", ".join(film["production"])))
    return lignes


def description_texte(film):
    """Texte brut : c'est cette version que lit Apple Calendrier.

    Structure : affiche, genre + pays, equipe technique, acteurs, synopsis,
    mention TMDB. Les blocs sont separes par une ligne vide, le synopsis par
    deux (reglable via LIGNES_AVANT_SYNOPSIS). Le synopsis n'est jamais tronque.
    """
    blocs = []

    # affiche, puis le titre original entre parentheses juste en dessous
    entete = []
    affiche = url_affiche(film["affiche"])
    if affiche:
        entete.append(affiche)
    original = titre_original_a_afficher(film)
    score = f"({film['popularite']:.1f})" if film.get("popularite") else ""
    if original:
        entete.append(f"({original}){ESPACEMENT_SCORE}{score}".rstrip())
    elif score:
        entete.append(score)
    duree = duree_lisible(film.get("duree"))
    if duree:
        entete.append(gras(duree))
    if entete:
        blocs.append("\n".join(entete))

    # le genre sans libelle, et juste dessous le pays d'origine
    identite = []
    if film["genres"]:
        identite.append(", ".join(gras(genre) for genre in film["genres"]))
    if film.get("pays"):
        ligne = ", ".join(film["pays"])
        if film.get("langues"):
            ligne += f" ({', '.join(film['langues'])})"
        identite.append(ligne)
    if film.get("avant_premiere"):
        texte = "Avant-première"
        if film.get("sortie_nationale"):
            texte += f" · sortie nationale le {film['sortie_nationale']}"
        identite.append(texte)
    elif film.get("sortie_initiale"):
        identite.append(f"(sortie initiale : {film['sortie_initiale']})")
    if identite:
        blocs.append("\n".join(identite))

    # l'equipe technique
    equipe = bloc_equipe_technique(film)
    if equipe:
        blocs.append("\n".join(f"{gras(libelle)} : {noms}" for libelle, noms in equipe))

    # les acteurs, en liste a puces
    if film["acteurs"]:
        libelle = accorder("Acteur", "Acteurs", film["acteurs"])
        blocs.append(f"{gras(libelle)} :\n" + "\n".join(f"- {nom}" for nom in film["acteurs"]))

    # le synopsis, en entier, un peu detache du reste
    if film["synopsis"]:
        respiration = "\n" * max(0, LIGNES_AVANT_SYNOPSIS - 1)
        texte = film["synopsis"]
        if film["synopsis_en_anglais"]:
            texte = "(synopsis non encore traduit sur TMDB)\n" + texte
        blocs.append(respiration + texte)

    # la mention legale, un peu detachee du synopsis
    respiration = "\n" * max(0, LIGNES_AVANT_MENTION - 1)
    if film.get("source") == "allocine":
        pied = "Séance et informations relevées sur AlloCiné"
    else:
        pied = f"Fiche TMDB : {LIEN_TMDB}{film['id']}\n\n"
        if film.get("evenement"):
            pied += "Séance relevée sur AlloCiné.\n"
        pied += "Données fournies par The Movie Database (TMDB)"
    blocs.append(respiration + pied)

    return "\n\n".join(blocs)


def echapper_html(texte):
    return (
        str(texte)
        .replace("&", "&amp;")
        .replace("<", "&lt;")
        .replace(">", "&gt;")
        .replace('"', "&quot;")
    )


def description_html(film):
    """Version HTML : affiche a gauche, fiche a droite, synopsis dessous.

    Lue par Outlook uniquement. Apple Calendrier et Google Agenda l'ignorent.
    Pas de point-virgule dans les styles : ils compliquent l'echappement iCalendar.
    """
    affiche = url_affiche(film["affiche"])

    # --- colonne de droite : le genre, puis la fiche ---
    droite = []
    identite = []
    if film["genres"]:
        identite.append(f"<i>{echapper_html(', '.join(film['genres']))}</i>")
    if film.get("pays"):
        ligne = ", ".join(film["pays"])
        if film.get("langues"):
            ligne += f" ({', '.join(film['langues'])})"
        identite.append(echapper_html(ligne))
    if film.get("avant_premiere"):
        texte = "Avant-première"
        if film.get("sortie_nationale"):
            texte += f" · sortie nationale le {film['sortie_nationale']}"
        identite.append(f"<b>{echapper_html(texte)}</b>")
    elif film.get("sortie_initiale"):
        identite.append(echapper_html(f"(sortie initiale : {film['sortie_initiale']})"))
    if identite:
        droite.append("<br>".join(identite))

    equipe = bloc_equipe_technique(film)
    if equipe:
        droite.append("<br>".join(
            f"<b>{libelle} :</b> {echapper_html(noms)}" for libelle, noms in equipe
        ))

    if film["acteurs"]:
        libelle = accorder("Acteur", "Acteurs", film["acteurs"])
        droite.append(
            f"<b>{libelle} :</b><ul>"
            + "".join(f"<li>{echapper_html(nom)}</li>" for nom in film["acteurs"])
            + "</ul>"
        )
    colonne_droite = "<br><br>".join(droite)

    # --- colonne de gauche : l'affiche, titre anglais dessous ---
    gauche = ""
    if affiche:
        gauche = (
            f'<img src="{echapper_html(affiche)}" width="{LARGEUR_AFFICHE_HTML}" '
            f'alt="Affiche de {echapper_html(film["titre"])}">'
        )
        original = titre_original_a_afficher(film)
        score = f"({film['popularite']:.1f})" if film.get("popularite") else ""
        if original:
            gauche += f"<br><small>{echapper_html(f'({original}){ESPACEMENT_SCORE}{score}'.rstrip())}</small>"
        elif score:
            gauche += f"<br><small>{echapper_html(score)}</small>"
        duree = duree_lisible(film.get("duree"))
        if duree:
            gauche += f"<br><small>{echapper_html(duree)}</small>"

    bouts = ["<!doctype html><html><body>"]
    if gauche:
        bouts.append(
            '<table cellpadding="0" cellspacing="0" border="0"><tr>'
            f'<td valign="top">{gauche}</td>'
            f'<td width="{ECART_AFFICHE_TEXTE}"></td>'
            f'<td valign="top">{colonne_droite}</td>'
            "</tr></table>"
        )
    else:
        bouts.append(f"<div>{colonne_droite}</div>")

    # --- sous l'affiche : le synopsis, en entier ---
    if film["synopsis"]:
        note = "<i>(synopsis non encore traduit sur TMDB)</i><br>" if film["synopsis_en_anglais"] else ""
        bouts.append(f"<p>{note}{echapper_html(film['synopsis'])}</p>")

    # --- sous le synopsis : la mention legale TMDB ---
    bouts.append(
        f'<p><small><a href="{LIEN_TMDB}{film["id"]}">Fiche TMDB</a><br><br>'
        "Données fournies par The Movie Database (TMDB)"
        "</small></p>"
    )
    bouts.append("</body></html>")
    return "".join(bouts)


# --- Fabrication du fichier iCalendar (RFC 5545) ----------------------------


def echapper(texte):
    if texte is None:
        return ""
    return (
        str(texte)
        .replace("\\", "\\\\")
        .replace(";", "\\;")
        .replace(",", "\\,")
        .replace("\r\n", "\\n")
        .replace("\n", "\\n")
        .replace("\r", "\\n")
    )


def plier(ligne):
    """Coupe une ligne a 75 octets, comme l'exige la norme, sans casser l'UTF-8."""
    octets = ligne.encode("utf-8")
    if len(octets) <= 75:
        return ligne

    morceaux, reste, limite = [], octets, 75
    while len(reste) > limite:
        coupe = limite
        while coupe > 0 and (reste[coupe] & 0xC0) == 0x80:
            coupe -= 1
        morceaux.append(reste[:coupe].decode("utf-8"))
        reste = reste[coupe:]
        limite = 74  # les lignes suivantes commencent par une espace
    morceaux.append(reste.decode("utf-8"))
    return "\r\n ".join(morceaux)


def construire_ics(films, nom_calendrier=NOM_DU_CALENDRIER):
    lignes = [
        "BEGIN:VCALENDAR",
        "VERSION:2.0",
        f"PRODID:-//calendrier-cine-fr//FR//{VERSION}",
        "CALSCALE:GREGORIAN",
        "METHOD:PUBLISH",
        f"X-WR-CALNAME:{echapper(nom_calendrier)}",
        f"NAME:{echapper(nom_calendrier)}",
        "X-WR-TIMEZONE:Europe/Paris",
        "X-WR-CALDESC:"
        + echapper("Sorties en salles en France. Données fournies par The Movie Database (TMDB)."),
        "REFRESH-INTERVAL;VALUE=DURATION:PT12H",
        "X-PUBLISHED-TTL:PT12H",
    ]

    for film in films:
        try:
            jour = datetime.strptime(film["date"], "%Y-%m-%d").date()
        except ValueError:
            continue

        titre_agenda = titre_pour_agenda(film)
        if not titre_agenda:
            continue  # aucun titre en alphabet latin : on n'affiche pas le film

        lignes += [
            "BEGIN:VEVENT",
            f"UID:{film['uid']}@calendrier-cine-fr" if film.get("uid") else
            f"UID:{'event' if film.get('evenement') else 'tmdb'}-{film['id']}@calendrier-cine-fr",
            f"DTSTAMP:{jour.strftime('%Y%m%d')}T000000Z",
            *(
                [f"DTSTART:{film['debut_utc']}", f"DTEND:{film['fin_utc']}"]
                if film.get("debut_utc") and film.get("fin_utc")
                else [f"DTSTART;VALUE=DATE:{jour.strftime('%Y%m%d')}",
                      f"DTEND;VALUE=DATE:{(jour + timedelta(days=1)).strftime('%Y%m%d')}"]
            ),
            f"SUMMARY:{echapper(PREFIXE_TITRE + titre_agenda)}",
            f"DESCRIPTION:{echapper(description_texte(film))}",
        ]
        if INCLURE_VERSION_HTML:
            lignes.append(f"X-ALT-DESC;FMTTYPE=text/html:{echapper(description_html(film))}")
        lignes += [
            *([] if film.get("source") == "allocine" else [f"URL:{LIEN_TMDB}{film['id']}"]),
            "TRANSP:OPAQUE" if film.get("debut_utc") else "TRANSP:TRANSPARENT",
        ]

        affiche = url_affiche(film["affiche"])
        if affiche:
            # DISPLAY=FULLSIZE : le seul reglage d'affichage prevu par la norme
            # (RFC 7986). Ce n'est pas une taille en pixels, juste une intention.
            lignes.append(f"IMAGE;VALUE=URI;DISPLAY=FULLSIZE;FMTTYPE=image/jpeg:{affiche}")

            lignes.append(f"ATTACH;FMTTYPE=image/jpeg:{affiche}")

        if film["genres"]:
            # Dans CATEGORIES la virgule separe les valeurs : on echappe chaque
            # genre individuellement, puis on les joint avec une virgule brute.
            lignes.append("CATEGORIES:" + ",".join(echapper(g) for g in film["genres"]))
        else:
            lignes.append("CATEGORIES:Cinema")

        lignes.append("END:VEVENT")

    lignes.append("END:VCALENDAR")
    return "\r\n".join(plier(ligne) for ligne in lignes) + "\r\n"


def film_depuis_allocine(fiche):
    """Fiche minimale batie sur les seules donnees AlloCine.

    Sert de repli quand le film n'est pas retrouve sur TMDB : sans cela, toutes
    les seances de ce film disparaitraient du calendrier. Les lignes qu'AlloCine
    ne fournit pas (scenario, photographie, acteurs, pays) restent absentes.
    """
    realisateurs = []
    for credit in fiche.get("credits") or []:
        if (credit.get("position") or {}).get("name") == "DIRECTOR":
            personne = credit.get("person") or {}
            nom = f"{personne.get('firstName') or ''} {personne.get('lastName') or ''}".strip()
            if nom and nom not in realisateurs:
                realisateurs.append(nom)

    duree = duree_en_minutes(fiche.get("runtime"))
    return {
        "source": "allocine",
        "id": fiche.get("internalId"),
        "date": date.today().isoformat(),
        "titre": (fiche.get("title") or "").strip(),
        "titre_original": (fiche.get("originalTitle") or "").strip(),
        "titre_romanise": None, "titre_anglais": "",
        "pays": [], "genres": [g.get("translate") for g in (fiche.get("genres") or []) if g.get("translate")],
        "realisateurs": realisateurs, "scenaristes": [], "photographie": [],
        "production": [], "acteurs": [],
        "synopsis": (fiche.get("synopsisFull") or "").strip(),
        "synopsis_en_anglais": False,
        "affiche": (fiche.get("poster") or {}).get("url"),
        "duree": duree,
        "popularite": None,
        "langue_origine": None, "langues": [], "sortie_initiale": None,
    }


def calendrier_des_seances():
    """Troisieme calendrier : chaque seance du cinema, a son horaire reel.

    Une fiche TMDB est recuperee une seule fois par film, puis reutilisee pour
    toutes ses seances : la note est donc identique aux deux autres calendriers.
    """
    if not (ALLOCINE_ACTIF and SEANCES_ACTIVES):
        return []

    print(f"\n=== Seances - {ALLOCINE_NOM} ({SEANCES_JOURS} jours) ===")
    try:
        programmes = horaires_du_cinema()
    except Exception as erreur:  # noqa: BLE001
        print(f"  abandonne : {erreur}", file=sys.stderr)
        return []
    if not programmes:
        print("  aucune seance recuperee")
        return []

    evenements, introuvables = [], 0
    for identifiant, (fiche, seances) in programmes.items():
        if not seances:
            continue
        titre = (fiche.get("title") or "").strip()
        _, annee = sortie_originale(fiche)
        trouve = chercher_sur_tmdb(titre, (fiche.get("originalTitle") or "").strip(), annee)
        detail = None
        if trouve:
            detail = details_du_film({"id": trouve[0], "date": date.today().isoformat(), "impose": True})
        if not detail:
            # plutot que de perdre toutes ses seances, on batit la fiche avec
            # ce qu'AlloCine fournit : note plus pauvre, mais rien ne disparait
            introuvables += 1
            print(f"    ~ {titre} ({annee}) - pas sur TMDB, fiche AlloCine utilisee")
            detail = film_depuis_allocine(fiche)
            if not detail["titre"]:
                continue

        duree = duree_en_minutes(detail.get("duree")) or 120
        for seance in sorted(seances, key=lambda x: x["debut"]):
            debut = horodatage_utc(seance["debut"])
            if not debut:
                continue
            fin = horodatage_utc(seance["fin"]) if seance.get("fin") else None
            if not fin:
                # AlloCine ne donne pas toujours la fin : debut + duree + publicites
                depart = datetime.strptime(debut, "%Y%m%dT%H%M%SZ")
                fin = (depart + timedelta(minutes=duree + SEANCES_PUB_MINUTES)).strftime("%Y%m%dT%H%M%SZ")

            version = {"DUBBED": "VF", "ORIGINAL": "VOST", "LOCAL": "VF"}.get(
                seance["version"], seance["version"])
            if version == "VOST" and detail.get("langue_origine"):
                version = f"VOST {detail['langue_origine']}"

            etiquettes = [e for e in [version] + seance.get("formats", []) if e]
            if seance.get("avp"):
                etiquettes.insert(0, "Avant-première")
            suffixe = " · ".join(etiquettes)
            evenements.append(dict(
                detail,
                uid=f"seance-{seance['id']}",
                date=seance["debut"][:10],
                debut_utc=debut,
                fin_utc=fin,
                seance_details=suffixe,
                titre=f"{detail['titre']} ({suffixe})" if suffixe else detail["titre"],
            ))

    if CODES_RENCONTRES:
        connus, inconnus = [], []
        for code in sorted(CODES_RENCONTRES):
            brut = code.upper().replace(" ", "_").replace("-", "_")
            noyau = brut
            for prefixe in ("E_", "F_", "A_", "P_"):
                if noyau.startswith(prefixe) and len(noyau) > len(prefixe) + 1:
                    noyau = noyau[len(prefixe):]
                    break
            connu = brut in FORMATS_LISIBLES or noyau in FORMATS_LISIBLES
            (connus if connu else inconnus).append(code)
        print(f"\n  Codes de format rencontres chez {ALLOCINE_NOM} :")
        print(f"    reconnus  : {', '.join(connus) or 'aucun'}")
        if inconnus:
            print(f"    INCONNUS  : {', '.join(inconnus)}")
            print("    (affiches tels quels - signalez-les moi pour les nommer correctement)")

    print(f"  {len(evenements)} seances retenues"
          + (f", dont les seances de {introuvables} films decrits par AlloCine" if introuvables else ""))
    return sorted(evenements, key=lambda e: e["debut_utc"])


def ecrire_calendrier(films, chemin, nom):
    """Ecrit un fichier .ics et renvoie le nombre d'evenements retenus."""
    contenu = construire_ics(films, nom)
    dossier = os.path.dirname(chemin)
    if dossier:
        os.makedirs(dossier, exist_ok=True)
    with open(chemin, "w", encoding="utf-8", newline="") as fichier:
        fichier.write(contenu)
    taille = len(contenu.encode("utf-8")) / 1024
    retenus = sum(1 for f in films if titre_pour_agenda(f))
    horodates = any(f.get("debut_utc") for f in films)
    quoi = "seances ecrites" if horodates else "films ecrits"
    print(f"  {retenus} {quoi} dans {chemin} ({taille:.0f} Ko)")
    return retenus


def main():
    if MODE_RAPIDE:
        print("*** MODE RAPIDE : resultat volontairement incomplet ***\n")
    charger_base_images()

    # --- calendrier principal : les sorties nationales ---
    sorties = lister_sorties()
    if not sorties:
        sys.exit("ERREUR : aucune sortie trouvee. Fichier non ecrit, pour ne pas vider le calendrier.")

    films = enrichir(sorties)
    if not films:
        sys.exit("ERREUR : aucune fiche exploitable. Fichier non ecrit.")

    ecartes = [f for f in films if not titre_pour_agenda(f)]
    print("\n=== Calendrier principal ===")
    ecrire_calendrier(films, FICHIER_DE_SORTIE, NOM_DU_CALENDRIER)

    sans_affiche = sum(1 for f in films if not f["affiche"])
    non_traduits = sum(1 for f in films if f["synopsis_en_anglais"])
    print(f"  sans affiche sur TMDB : {sans_affiche}")
    print(f"  synopsis non traduit  : {non_traduits}")
    if ecartes:
        print(f"  ecartes faute de titre lisible : {len(ecartes)}")
        for film in ecartes[:10]:
            anglais = film.get("titre_anglais") or "-"
            print(f"    - {film['titre']}  (titre anglais connu : {anglais})")

    # --- second calendrier : les seances evenement du cinema ---
    evenements = seances_evenement()
    if evenements:
        ecrire_calendrier(evenements, FICHIER_EVENEMENTS, NOM_CALENDRIER_EVENEMENTS)
    else:
        print("  aucune seance evenement : fichier inchange")

    # --- troisieme calendrier : toutes les seances, horaires reels ---
    seances = calendrier_des_seances()
    if seances:
        ecrire_calendrier(seances, FICHIER_SEANCES, NOM_CALENDRIER_SEANCES)
    else:
        print("  aucune seance horodatee : fichier inchange")


if __name__ == "__main__":
    main()

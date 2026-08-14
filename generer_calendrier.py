#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
Genere un fichier .ics des sorties cinema en France, titres en francais,
avec affiche, realisateur, scenaristes, directeur de la photographie,
acteurs principaux, genres et synopsis.

Toutes les donnees proviennent exclusivement de The Movie Database (TMDB).
Ce produit utilise l'API TMDB mais n'est ni approuve ni certifie par TMDB.

Aucune dependance externe : uniquement la bibliotheque standard de Python.
"""

import base64
import json
import os
import sys
import time
import unicodedata
import urllib.parse
import urllib.request
from concurrent.futures import ThreadPoolExecutor
from datetime import date, datetime, timedelta

# ---------------------------------------------------------------------------
# REGLAGES  -  la seule partie que vous aurez besoin de modifier
# ---------------------------------------------------------------------------

REGION = "FR"          # pays dont on veut les dates de sortie
LANGUE = "fr-FR"       # langue des titres, genres et synopsis

# Types de sortie TMDB : 1=Premiere 2=Salles(limite) 3=Salles 4=Numerique 5=Physique 6=TV
TYPES_DE_SORTIE = "3|2"

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
POPULARITE_MINIMALE = 5.0

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

# Piece jointe. Apple Calendrier sait afficher les pieces jointes d'un calendrier
# abonne, a condition de decocher "Supprimer : Pieces jointes" a l'abonnement.
# En mode integre, l'image est incorporee au fichier au lieu d'etre un simple lien :
# plus de chance d'etre affichee, mais le fichier grossit beaucoup.
AFFICHE_INTEGREE = True           # True = image incorporee (a tester)
TAILLE_AFFICHE_INTEGREE = "w342"   # resolution des images incorporees
JOURS_AFFICHE_INTEGREE = 45        # on n'incorpore que les sorties les plus proches
LARGEUR_AFFICHE_HTML = 220         # largeur d'affichage de l'affiche dans Outlook, en pixels
ECART_AFFICHE_TEXTE = 16           # espace entre l'affiche et la colonne de texte, en pixels

NOM_DU_CALENDRIER = "Sorties cinema France"
PREFIXE_TITRE = ""                 # texte place devant le titre, ex. "🎬 "

# Le titre affiche dans l'agenda doit rester en alphabet latin. Ordre de repli :
#   1. le titre francais, s'il est en alphabet latin
#   2. sa romanisation, si TMDB en fournit une
#   3. le titre anglais, uniquement si REPLI_TITRE_ANGLAIS vaut True
#   4. sinon le film est ecarte du calendrier
REPLI_TITRE_ANGLAIS = False
FICHIER_DE_SORTIE = "docs/c-cinema.ics"

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
    page, total_pages = 1, 1
    while page <= total_pages and page <= 500:
        donnees = appel_api("/discover/movie", {**commun, "page": page})
        total_pages = min(donnees.get("total_pages", 1), 500)
        for film in donnees.get("results", []):
            if not film.get("release_date"):
                continue
            scores.append(float(film.get("popularity") or 0))
            if float(film.get("popularity") or 0) < POPULARITE_MINIMALE:
                continue
            films[film["id"]] = {"id": film["id"], "date": film["release_date"]}
        print(f"  page {page}/{total_pages} - {len(films)} films")
        page += 1

    afficher_repartition(scores)
    return list(films.values())


def afficher_repartition(scores):
    """Montre combien de films resteraient selon le seuil de popularite."""
    if not scores:
        return
    tries = sorted(scores)
    mediane = tries[len(tries) // 2]
    print(f"\nRepartition de la popularite ({len(scores)} sorties trouvees)")
    print(f"  la plus faible {tries[0]:.1f} | mediane {mediane:.1f} | la plus forte {tries[-1]:.1f}")
    print("  films restants selon POPULARITE_MINIMALE :")
    for seuil in (0, 1, 2, 3, 5, 10, 20):
        restants = sum(1 for v in tries if v >= seuil)
        marque = "  <- reglage actuel" if abs(seuil - POPULARITE_MINIMALE) < 0.001 else ""
        print(f"    {seuil:>3} -> {restants:>4} films{marque}")


# Alphabets pour lesquels une romanisation est necessaire, si TMDB en fournit une.
# On se fie au nom Unicode de chaque caractere : "LATIN SMALL LETTER E" -> latin.
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

    # 1. le type l'annonce explicitement
    for entree in latins:
        type_ = (entree.get("type") or "").lower()
        if "roman" in type_ or "translit" in type_:
            return entree["title"].strip()

    # 2. a defaut, un titre alternatif depose sur le pays d'origine
    origines = pays_d_origine(fiche)
    for entree in latins:
        if entree.get("iso_3166_1") in origines:
            return entree["title"].strip()

    return None


def traduction(fiche, langue):
    """Bloc 'data' de la traduction demandee, ou {} si elle n'existe pas.

    TMDB ne fait pas de repli automatique entre langues sur l'API, contrairement
    au site : il faut donc aller chercher la traduction nous-memes.
    On privilegie la variante americaine, puis britannique, puis n'importe laquelle.
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
    present, et la liste ne bouge pas d'un mois a l'autre. Un film qui ne
    credite qu'un acteur n'en affichera qu'un.
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


def details_du_film(film):
    """Une requete par film : fiche + generique, grace a append_to_response."""
    try:
        fiche = appel_api(
            f"/movie/{film['id']}",
            {"language": LANGUE, "append_to_response": "credits,translations,alternative_titles"},
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

    return {
        "id": film["id"],
        "date": film["date"],
        "titre": titre or titre_original or "Sans titre",
        "titre_original": titre_original,
        "titre_romanise": titre_romanise,
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
        "affiche_base64": None,
    }


def enrichir(films):
    print(f"\nRecuperation des fiches detaillees ({len(films)} films)...")
    with ThreadPoolExecutor(max_workers=FILS_PARALLELES) as executeur:
        resultats = list(executeur.map(details_du_film, films))

    complets = [r for r in resultats if r]
    print(f"  {len(complets)} fiches recuperees")
    return sorted(complets, key=lambda f: (f["date"], f["titre"]))


# --- Mise en forme ----------------------------------------------------------


def accorder(libelle_singulier, libelle_pluriel, personnes):
    """Choisit le libelle selon le nombre de personnes."""
    return libelle_pluriel if len(personnes) > 1 else libelle_singulier


def telecharger_affiche(chemin):
    """Telecharge une affiche et la renvoie encodee en base64, ou None."""
    url = f"{BASE_IMAGES}{TAILLE_AFFICHE_INTEGREE}{chemin}"
    try:
        requete = urllib.request.Request(url, headers={"User-Agent": "calendrier-cine-fr"})
        with urllib.request.urlopen(requete, timeout=30) as reponse:
            return base64.b64encode(reponse.read()).decode("ascii")
    except Exception as erreur:  # noqa: BLE001
        print(f"  affiche non telechargee ({chemin}) : {erreur}", file=sys.stderr)
        return None


def integrer_affiches(films):
    """Incorpore les affiches des sorties proches. Les autres restent en lien."""
    if not AFFICHE_INTEGREE:
        return

    limite = date.today() + timedelta(days=JOURS_AFFICHE_INTEGREE)
    concernes = [
        f for f in films
        if f["affiche"] and datetime.strptime(f["date"], "%Y-%m-%d").date() <= limite
    ]
    if not concernes:
        return

    print(f"\nIncorporation des affiches ({len(concernes)} films sur {len(films)})...")
    with ThreadPoolExecutor(max_workers=FILS_PARALLELES) as executeur:
        images = list(executeur.map(lambda f: telecharger_affiche(f["affiche"]), concernes))

    poids = 0
    for film, image in zip(concernes, images):
        film["affiche_base64"] = image
        poids += len(image or "")
    print(f"  {sum(1 for i in images if i)} affiches incorporees ({poids / 1048576:.1f} Mo)")


def url_affiche(chemin):
    return f"{BASE_IMAGES}{TAILLE_AFFICHE}{chemin}" if chemin else None


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
    if original:
        entete.append(f"({original})")
    if entete:
        blocs.append("\n".join(entete))

    # le genre sans libelle, et juste dessous le pays d'origine
    identite = []
    if film["genres"]:
        identite.append(", ".join(film["genres"]))
    if film.get("pays"):
        identite.append(", ".join(film["pays"]))
    if identite:
        blocs.append("\n".join(identite))

    # l'equipe technique
    equipe = bloc_equipe_technique(film)
    if equipe:
        blocs.append("\n".join(f"{libelle} : {noms}" for libelle, noms in equipe))

    # les acteurs, en liste a puces
    if film["acteurs"]:
        libelle = accorder("Acteur", "Acteurs", film["acteurs"])
        blocs.append(f"{libelle} :\n" + "\n".join(f"- {nom}" for nom in film["acteurs"]))

    # le synopsis, en entier, un peu detache du reste
    if film["synopsis"]:
        respiration = "\n" * max(0, LIGNES_AVANT_SYNOPSIS - 1)
        texte = film["synopsis"]
        if film["synopsis_en_anglais"]:
            texte = "(synopsis non encore traduit sur TMDB)\n" + texte
        blocs.append(respiration + texte)

    # la mention legale TMDB, un peu detachee du synopsis
    blocs.append(
        "\n" * max(0, LIGNES_AVANT_MENTION - 1)
        + f"Fiche TMDB : {LIEN_TMDB}{film['id']}\n\n"
        "Données fournies par The Movie Database (TMDB).\n"
        "Ce produit utilise l'API TMDB."
    )

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
        identite.append(echapper_html(", ".join(film["pays"])))
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
        if original:
            gauche += f"<br><small>({echapper_html(original)})</small>"

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
        f'<p><small><a href="{LIEN_TMDB}{film["id"]}">Fiche TMDB</a><br>'
        "Données fournies par The Movie Database (TMDB).<br>"
        "Ce produit utilise l'API TMDB mais n'est ni approuvé ni certifié par TMDB."
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


def construire_ics(films):
    lignes = [
        "BEGIN:VCALENDAR",
        "VERSION:2.0",
        "PRODID:-//calendrier-cine-fr//FR",
        "CALSCALE:GREGORIAN",
        "METHOD:PUBLISH",
        f"X-WR-CALNAME:{echapper(NOM_DU_CALENDRIER)}",
        f"NAME:{echapper(NOM_DU_CALENDRIER)}",
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
            f"UID:tmdb-{film['id']}@calendrier-cine-fr",
            f"DTSTAMP:{jour.strftime('%Y%m%d')}T000000Z",
            f"DTSTART;VALUE=DATE:{jour.strftime('%Y%m%d')}",
            f"DTEND;VALUE=DATE:{(jour + timedelta(days=1)).strftime('%Y%m%d')}",
            f"SUMMARY:{echapper(PREFIXE_TITRE + titre_agenda)}",
            f"DESCRIPTION:{echapper(description_texte(film))}",
        ]
        if INCLURE_VERSION_HTML:
            lignes.append(f"X-ALT-DESC;FMTTYPE=text/html:{echapper(description_html(film))}")
        lignes += [
            f"URL:{LIEN_TMDB}{film['id']}",
            "TRANSP:TRANSPARENT",
        ]

        affiche = url_affiche(film["affiche"])
        if affiche:
            # DISPLAY=FULLSIZE : le seul reglage d'affichage prevu par la norme
            # (RFC 7986). Ce n'est pas une taille en pixels, juste une intention.
            lignes.append(f"IMAGE;VALUE=URI;DISPLAY=FULLSIZE;FMTTYPE=image/jpeg:{affiche}")

            integree = film.get("affiche_base64")
            if integree:
                # image incorporee au fichier : plus lourde, mais autonome
                lignes.append(
                    "ATTACH;FMTTYPE=image/jpeg;ENCODING=BASE64;VALUE=BINARY:" + integree
                )
            else:
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


def main():
    charger_base_images()

    sorties = lister_sorties()
    if not sorties:
        sys.exit("ERREUR : aucune sortie trouvee. Fichier non ecrit, pour ne pas vider le calendrier.")

    films = enrichir(sorties)
    integrer_affiches(films)
    if not films:
        sys.exit("ERREUR : aucune fiche exploitable. Fichier non ecrit.")

    contenu = construire_ics(films)

    dossier = os.path.dirname(FICHIER_DE_SORTIE)
    if dossier:
        os.makedirs(dossier, exist_ok=True)
    with open(FICHIER_DE_SORTIE, "w", encoding="utf-8", newline="") as fichier:
        fichier.write(contenu)

    taille = len(contenu.encode("utf-8")) / 1024
    sans_affiche = sum(1 for f in films if not f["affiche"])
    non_traduits = sum(1 for f in films if f["synopsis_en_anglais"])
    ecartes = [f for f in films if not titre_pour_agenda(f)]

    retenus = len(films) - len(ecartes)
    print(f"\n{retenus} films ecrits dans {FICHIER_DE_SORTIE} ({taille:.0f} Ko)")
    print(f"  sans affiche sur TMDB : {sans_affiche}")
    print(f"  synopsis non traduit  : {non_traduits}")
    if ecartes:
        print(f"  ecartes faute de titre lisible : {len(ecartes)}")
        for film in ecartes[:10]:
            anglais = film.get("titre_anglais") or "-"
            print(f"    - {film['titre']}  (titre anglais connu : {anglais})")
        if not REPLI_TITRE_ANGLAIS:
            print("    -> REPLI_TITRE_ANGLAIS = True permettrait d'en recuperer une partie")
    print("Trois premiers :")
    for film in films[:3]:
        real = film["realisateurs"][0] if film["realisateurs"] else "?"
        print(f"  {film['date']}  {film['titre']} - {real}")


if __name__ == "__main__":
    main()

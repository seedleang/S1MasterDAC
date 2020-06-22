/* ============================================================================================================*/

/* RESUME ------------------------------------------------------------------------------------------------------

Ce TME nous aura permis de reconstituer, petit à petit, 
une logique de description initialement inconnue de Prolog.
Il s'agit de FL-, dont certains aspects intrinsèques lui sont encore mystérieux.
Le quantificateur some(), par exemple, n'est correctement interprété que par amalgame syntaxique ; 
sa définition complète n'a pas été explicitée d'office.

Pour pouvoir programmer la grammaire de FL-, il nous fallait des références.
Nous nous sommes servis d'une T-Box et une A-Box construites à partir d'un texte donné, 
ce qui nous a permis d'avoir une base de connaissances assez large pour tester tous les cas de figure. 
Il a alors fallu en expliquer la sémantique.

La T-Box étant fondée sur des subsomptions et des équivalences factuelles, nous avons donc implémenté une à une 
- l'idée de subsomption structurelle (si C subsume B qui subsume A, alors C subsume A), 
par récursion, en prenant soin d'ajouter une détection de cycle pour éviter les boucles infinies ;
- la notion d'équivalence, traduite par deux faits de subsomption ;
- la notion d'intersection entre les concepts ;
- qui permet par ailleurs la détection de contradictions s'il existe un concept "nothing"
(le "faux" absolu n'étant pas défini en FL-, 
on s'est servi d'une contradiction explicite dans la liste des faits) ;
- et enfin la gestion des quantificateurs universels, qu'on applique aux rôles.

Cette approche ne nous a pas permis d'écrire un ensemble de règles complet pour FL-, bien que les modifications
à apporter semblent mineures. 
On note néanmoins que ce programme est adéquat. Toute subsomption qu'il reconnaît comme vraie l'est censément.

===============================================================================================================*/

/* Exercice 1 : Représentation préfixe en Prolog ==============================================================*/

/* T-Box : axiomes terminologiques ----------------------------------------------------------------------------*/
subs(chat, felin).
subs(lion, felin).
subs(chien, canide).
subs(canide, chien).
subs(souris, mammifere).
subs(felin, mammifere).
subs(canide, mammifere).
subs(mammifere, animal).
subs(canari, animal).
subs(animal, etreVivant).
subs(and(animal, plante), nothing).

subs(and(animal, some(aMaitre)), pet).
subs(pet, some(aMaitre)).
subs(some(aMaitre), all(aMaitre, humain)).
subs(chihuahua,and(pet,chien)).

subs(lion, carnivoreExc).
subs(carnivoreExc, predateur).
subs(animal, some(mange)).
subs(and(all(mange, nothing), some(mange)), nothing).

equiv(carnivoreExc, all(mange, animal)).
equiv(herbivoreExc, all(mange, plante)).

/* A-Box : assertions -----------------------------------------------------------------------------------------*/
inst(felix, chat).
inst(pierre, humain).
inst(princesse, chihuahua).
inst(marie, humain).
inst(jerry, souris).
inst(titi, canari).
instR(felix, aMaitre, pierre).
instR(princesse, aMaitre, marie).
instR(felix, mange, jerry).
instR(felix, mange, titi).

/* ============================================================================================================*/

/* Exercice 2 : Gestion des concepts atomiques ================================================================*/

/* Question 1 : premiers essais -------------------------------------------------------------------------------*/

subsS1(C,C). /*(1)*/
subsS1(C,D) :- subs(C,D), C\==D. /*(2)*/
subsS1(C,D) :- subs(C,E), subsS1(E,D). /*(3)*/

/* La règle (1) traduit la réflexivité : la classe C subsume la classe C.
   La règle (2) exprime le lien entre le nouveau prédicat subsS1 et la liste de faits :
   la subsomption qu'on définit comme "factuelle" implique donc une subsomption "structurelle".
   C'est en quelque sorte la définition d'un cas de base.
   La règle (3) traduit la transitivité, qui est le principe de la récursion : 
   si E subsume (factuellement) C, et si on peut *prouver* (structurellement) que D subsume E, 
   alors D subsume (structurellement) C. */ 

/* Question 2 : test des requêtes -----------------------------------------------------------------------------*/

/* ?- subsS1(canari,animal).
true ;
true ;
false.*/

/* ?- subsS1(chat,etreVivant).
true ;
true ;
false.*/

/* Un canari est bien un animal, un chat est bien un être vivant.
Par exemple, dans le deuxième cas, Prolog s'assure d'abord de l'existence d'une subsomption entre chat et felin, 
puis entre felin et mammifere, puis entre mammifere et animal, puis entre animal et etreVivant...
ce qui lui permet de déduire finalement ce qu'il faut.
On explique la multiplicité des true affichés par la multiplicité des chemins récursifs qui auraient pu mener à
prouver la subsomption. Utiliser l'opérateur ! permet de les réduire, mais on préfère l'éviter pour pouvoir 
afficher l'intégralité des énumérations ultérieures (question 3.7).
On décide à partir d'ici de terminer toute requête qui n'implique pas de variables à la première ligne renvoyée, 
c'est-à-dire sans avoir cité les alternatives avec ;. */

/* Question 3 : constatation de la boucle infinie -------------------------------------------------------------*/

/* La requête subsS1(chien, souris) entre dans une boucle infinie, sans renvoyer ni true, ni false.
Comme Prolog ne reconnaît pas subs(chien, souris) dans la liste de faits, il entre en récursion.
La classe chien est subsumée par la classe canide, laquelle est subsumée par chien, ... 
et la règle (3) joue à l'infini.
Pour y remédier, on s'empêche de réutiliser un élément déjà rencontré au cours des étapes précédentes de la
preuve de subsomption: */

subsS(C, D) :- subsS(C, D, [C]).
subsS(C, C, _).
subsS(C, D, _) :- subs(C, D), C \== D.
subsS(C, D, L) :- subs(C, E), not(member(E, L)), subsS(E, D, [E|L]), E \== D.

/* Question 4 : test des requêtes -----------------------------------------------------------------------------*/

/* ?- subsS(canari,animal).
true .*/
/* ?- subsS(chat,etreVivant).
true .*/
/* ?- subsS(chien,canide).
true .*/
/* ?- subsS(chien,chien).
true .*/

/* Question 5 : rencontre avec un quantificateur --------------------------------------------------------------*/

/* ?- subsS(souris,some(mange)).
true.
La requête réussit, c'est inattendu :
Prolog parvient à unifier souris avec animal, puis applique le fait subs(animal, some(mange)). 
De fait, some(mange) n'est pour lui qu'un bloc syntaxique, dépourvu de tout sens logique particulier. */

/* Question 6 : test des requêtes -----------------------------------------------------------------------------*/

/*?- subsS(chat,humain).
false.*/
/*?- subsS(chien,souris).
false.,
grâce aux nouvelles règles.*/
/* ...et on est rassuré.e sur l'état du monde.*/

/* Question 7 : requêtes avec variables -----------------------------------------------------------------------*/

/* On s'attend à ce que la requête subsS(chat,X) renvoie : 
chat, felin, mammifere, animal, etreVivant, mais aussi some(mange) comme vu plus haut,
c'est-à-dire tout ce qu'un chat peut prétendre à être.
On s'attend aussi à ce que subsS(X,mammifere) renvoie : 
mammifere, chat, lion, felin, chien, canide, souris, tout ce qui est un mammifère. */

/* ?- subsS(chat,X).
X = chat ;
X = felin ;
X = mammifere ;
X = animal ;
X = etreVivant ;
X = some(mange) ;
false. */

/* ?- subsS(X,mammifere).
X = mammifere ;
X = souris ;
X = felin ;
X = canide ;
X = chat ;
X = lion ;
X = chien ;
false. */

/* Question 8 : dérivation de l'équivalence -------------------------------------------------------------------*/

:- discontiguous subs/2.
subs(A,B) :- equiv(A,B).
subs(B,A) :- equiv(A,B).

/* Question 9 : test des requêtes -----------------------------------------------------------------------------*/

/*Précédemment,
?- subsS(lion,all(mange,animal)).
false.*/
/*L'ajout des règles a permis à Prolog de traduire l'équivalence :
?- subsS(lion,all(mange,animal)).
true .*/

/* Question 10 : Réflexion ------------------------------------------------------------------------------------*/

/* Comparons les intérêts respectifs de subsS(A,B) et subs(A,B) (on a traduit les notations de l'énoncé). 
subsS prend en compte l'existence d'un chemin récursif de subsomption et sera vrai dès lors qu'il y en a un, 
là où subs ne s'intéresse qu'aux simples faits : soit c'est écrit, soit ça ne l'est pas.
Utiliser des requêtes avec subsS nous donne la possibilité de valider toutes les subsomptions structurelles
qui peuvent l'être entre des concepts atomiques... et même un peu plus, comme on l'a vu dans le cas de 
subsS(souris,some(mange)). (D'où la complétude du système pour les subsomptions et équivalences atomiques.)
La question cela dit porte sur ce qu'il vaut mieux "dériver", et non pas "demander". Qu'est-ce qui serait plus 
intéressant à réutiliser par la suite, une subsomption directe ou l'existence d'un chemin ?
En fait, prouver qu'il y a subsomption factuelle permet de déduire qu'il existe une subsomption structurelle, 
car subs(A,B) est comme on l'a vu un cas de base pour subsS(A,B). Le contraire n'est pas vrai.
Il est donc plus intéressant de prouver ("dériver") une subsomption factuelle pour continuer à raisonner.*/

/* ============================================================================================================*/

/* Exercice 3 : Gestion des intersections =====================================================================*/

/* Question 1 : test des requêtes -----------------------------------------------------------------------------*/

:- discontiguous subsS/3.
subsS(C,and(D1,D2),L) :- D1\=D2, subsS(C,D1,L), subsS(C,D2,L). /*(1)*/
subsS(C,D,L) :- subs(and(D1,D2),D), E=and(D1,D2), not(member(E,L)), subsS(C,E,[E|L]), E\==C. /*(2)*/
subsS(and(C,C),D,L) :- nonvar(C),subsS(C,D,[C|L]). /*(3)*/
subsS(and(C1,C2),D,L) :- C1\=C2, subsS(C1,D,[C1|L]). /*(4)*/
subsS(and(C1,C2),D,L) :- C1\=C2, subsS(C2,D,[C2|L]). /*(5)*/
subsS(and(C1,C2),D,L) :- subs(C1,E1), E=and(E1,C2), not(member(E,L)), subsS(E,D,[E|L]),E\==D. /*(6)*/
subsS(and(C1,C2),D,L) :- Cinv=and(C2,C1), not(member(Cinv,L)), subsS(Cinv,D,[Cinv|L]). /*(7)*/

/* ? - subsS(chihuahua,and(mammifere,some(aMaitre))).
true .*/
/* ?- subsS(and(chien,some(aMaitre)),pet).
true .*/
/* ?-subsS(chihuahua,and(pet,chien)).
true .
Ce test en particulier aurait fonctionné avant l'ajout des règles, 
car Prolog aurait su le lire tel quel dans la liste de faits. */

/* Question 2 : explication du choix des règles ---------------------------------------------------------------*/

/* subsS(C,and(D1,D2),L) :- D1\=D2, subsS(C,D1,L), subsS(C,D2,L). (1)
Si je peux subsumer C par le premier et par le deuxième de deux concepts, alors C est subsumé par l'intersection 
des deux : typiquement, si un chihuahua est un chien, et séparément un animal de compagnie, 
alors c'est bien un chien... de compagnie. 
Comme on a déjà fait le choix de décrire chihuahua par une intersection dans la T-Box, voici un autre exemple : 
grâce à cette règle, subsS(lion,and(mammifere,carnivoreExc)) >>> true. */

/* subsS(C,D,L) :- subs(and(D1,D2),D), E=and(D1,D2), not(member(E,L)), subsS(C,E,[E|L]), E\==C. (2)
Si D subsume deux concepts D1 et D2 qui subsument déjà C (=dont l'intersection subsume déjà C),
alors D subsume aussi C. Intuitivement, D est un concept placé un ou plusieurs grades "au-dessus". 
C'est une forme de transitivité.
A supposer qu'un cheshireCat (=C) soit un chat (=D1) et aussi un esprit (=D2), 
et qu'on sache que subs((chat,esprit),etreVivant) (=D),
grâce à cette règle, on peut dériver que subsS(cheshireCat,etreVivant) >>> true. */

/* subsS(and(C,C),D,L) :- nonvar(C),subsS(C,D,[C|L]). (3)
Si C est subsumé par D, alors l'intersection de C et C (=C) est subsumée par D.
On précise que C n'est pas une variable pour éviter les ambiguités. 
C'est une sorte de cas de base qui permet de tirer une forme conjonctive à partir de chaque concept.
Grâce à cette règle, subsS(and(chien,chien),canide) >>> true. */

/* subsS(and(C1,C2),D,L) :- C1\=C2, subsS(C1,D,[C1|L]). (4)
   subsS(and(C1,C2),D,L) :- C1\=C2, subsS(C2,D,[C2|L]). (5)
Du fait qu'un membre d'une intersection soit subsumé par un concept, je dérive le fait que l'intersection entière 
est aussi subsumée par ledit concept.
Mettons qu'il existe quelque chose qui est un félin, mais aussi un schmilblick (objet qui n'est pas dans la base). 
On sait déjà que felin est subsumé par animal. Or, le fait d'être un félin suffit pour être un animal, et ce 
quelle que soit l'autre caractéristique de notre hybride (!).
Grâce à cette règle, on a subsS(and(felin,*schmilblick*),animal) >>> true. */

/* subsS(and(C1,C2),D,L) :- subs(C1,E1), E=and(E1,C2), not(member(E,L)), subsS(E,D,[E|L]),E\==D. (6)
Si D subsume l'intersection de deux concepts, alors il subsume aussi 
[l'intersection de [n'importe quel concept qui est sous l'un] avec [l'autre]].
Typiquement, on sait seulement que pet subsume l'intersection de deux classes, animal et some(aMaitre). 
On souhaite maintenant montrer que pet subsume aussi les chiens (qui sont des animaux) qui ont un maître.
Grâce à cette règle, on a subsS(and(chien,some(aMaitre)),pet) >>> true. */

/* subsS(and(C1,C2),D,L) :- Cinv=and(C2,C1), not(member(Cinv,L)), subsS(Cinv,D,[Cinv|L]). (7)
Cette règle énonce la commutativité de l'intersection, et même si elle n'a pas la même forme que la règle 
précédente, elle permet de dériver sa symétrique.
Elle nous permettrait d'ailleurs de supprimer l'une ou l'autre des règles 4 et 5, puisqu'il s'agit là 
aussi d'une question de symétrie.
Grâce à elle, je peux m'appuyer sur le fait que subs(and(animal, plante), nothing) 
(et donc subsS(and(animal, plante),nothing)) et dériver subsS(and(plante,animal),nothing).*/

/* Question 3 : réflexion -------------------------------------------------------------------------------------*/
/* Il a déjà été établi que ce programme permettait de gérer toute requête impliquant des concepts atomiques. 
Les règles concernant l'intersection ayant été écrites en supplément, on a cependant la déception de constater 
qu'il en manque au moins une, celle qui correspondrait à la règle (3) pour le membre de droite. 
Pour l'instant (mais est-ce vraiment passionnant), il est impossible de dériver que 
subsS(chien,and(canide,canide)). */ 

/* ============================================================================================================*/

/* Exercice 4 : Gestion des rôles =============================================================================*/

/* Question 1 : quantificateur universel, gestion des rôles qualifiés -----------------------------------------*/

/* subsS(all(R,C),all(R,D),L) :- subsS(C,D,L).
On s'est longtemps demandé.e pourquoi cette règle ne fonctionnait pas.
La solution consiste à l'ajouter plutôt au niveau factuel (donc de s'orienter vers le prédicat subs). 
On remercie pour cela les échanges avec d'autres binômes, et en particulier celui d'Ariana et Dorian.

Pour le comprendre, voyons ce que faisait subsS avant d'ajouter cette règle. 
Comme on l'a vu, il lui fallait, au bout de sa récursion, une subsomption factuelle comme cas de base sur lequel 
s'appuyer. Or, dans certains cas, subsS ne parvient jamais à se rerouter vers une subsomption factuelle qui 
corresponde à ce qu'on cherche : en particulier, si aucun concept ne subsume all(R,C), on n'a aucune chance.
Utiliser subs au lieu de subsS permet de définir la règle comme une "traduction syntaxique" directe,
un peu comme on l'a fait avec l'équivalence. */

:-discontiguous subs/2.
subs(all(R,C), all(R,D)):-subs(C,D).

/* Question 2 : test des requêtes -----------------------------------------------------------------------------*/

/* ?- subsS(lion, all(mange, etreVivant)).
true . -- Aurait été gérable via subsS.*/

/* ?- subsS(all(mange, canari), carnivoreExc).
true . -- Nécessitait d'ajouter une règle au niveau factuel.*/

/* Question 3 : compléments -----------------------------------------------------------------------------------*/

/* A regarder les requêtes à tester, on se rend compte qu'il y a une grande nouveauté. 
L'idée est de faire comprendre à Prolog ce que c'est que ce nothing qui n'apparaît pour l'instant que dans
subs(and(animal, plante), nothing) - ce qui nous a aussi posé un sérieux problème.
Après avoir mille fois tenté de définir factuellement le concept nothing (qui n'est autorisé qu'en ALC !), 
on change de perspective.

On tente de développer une technique de réécriture des requêtes. 
Pour la première, le but est de montrer 
subsS(and(carnivoreExc,herbivoreExc),all(mange,nothing)),
donc, par définition de cExc et hExc, subsS(and(all(mange,animal),all(mange,plante)),all(mange,nothing)).

Pour ce faire, on doit déjà tirer de subs(and(animal, plante), nothing)
que subsS(all(mange, and(animal, plante)), all(mange, nothing)).
On voudrait bien aussi que and(carnivoreExc, herbivoreExc) (= and(all(mange,animal),all(mange,plante))
soit subsumé par all(mange, and(animal, plante)), 
ce qui avec la subsomption précédente doit permettre de déduire exactement ce qu'on veut.
D'où nos ajouts :*/

:- discontiguous subs/2.
subs(all(R,and(D1,D2)),all(R,E)) :- subs(and(D1,D2),E).
subs(and(all(R,D1),all(R,D2)),all(R,and(D1,D2))).

/* Ce qui donne
?- subsS(and(carnivoreExc,herbivoreExc),all(mange,nothing)).
true .*/
/* puis
?- subsS(and(and(carnivoreExc,herbivoreExc),animal),nothing).
true .*/

/* Accessoirement, on remarque que
?- subsS(and(and(carnivoreExc,animal),herbivoreExc),nothing).
false.
Dans la requête précédente, and(carnivoreExc,herbivoreExc) était subsumé par nothing. La contradiction était
"facile" à trouver, et il suffisait que nothing subsume cette contradiction pour subsumer toute l'intersection, 
c'est-à-dire and(and(carnivoreExc,herbivoreExc),animal).
Or dans celle-ci, il n'y a pas de contradiction dans les intersections exactement délimitées par les parenthèses. 
On peut écrire and(carnivoreExc, animal) sans souci, un animal peut très bien être carnivore.
Le problème est dans l'association d'un tel objet avec herbivoreExc.
Remarquons au passage qu'utiliser le complément de règles suivant, plutôt que le nôtre
:- discontiguous subsS/3.
subsS(C, all(R, and(D1, D2)), L) :- D1 \= D2, subsS(C, all(R, D1), L), subsS(C, all(R, D2), L).
subsS(C, all(R, D), L) :- subs(and(D1, D2), D), E = all(R, and(D1, D2)), not(member(E, L)), subsS(C, E, [E|L]), E\==C.
aurait permis à Prolog de retomber sur le fait subs((animal,plante),nothing)
en faisant jouer les treize règles qui constituent maintenant la définition de subsS, 
et d'en tirer qu'il y a bien contradiction, donc de renvoyer true.
Ce complément reprend le schéma utilisé pour le traitement des intersections. 
Il est donc plus général que le nôtre, qui est très ad hoc, mais un peu moins intuitif. */
	                    
/* Question 4 : quantificateur universel, gestion des instances -----------------------------------------------*/

subs(all(R, I), all(R, C)) :- inst(I, C).
/* permet de gérer les instances avec le même raisonnement que pour les concepts.*/

/* Question 5 : gestion des quantificateurs existentiels ------------------------------------------------------*/

/* Si Prolog a pu nous dire que les souris mangeaient quelque chose sans savoir vraiment ce que cela implique
(cf. 2.5) c'est qu'il est capable de considérer tout quantificateur existentiel de type some(R), 
où R est un rôle, comme un concept atomique. 
Un rôle quantifié par some() ne peut pas être qualifié en FL-, on ne peut donc avoir aucune variation syntaxique.
Tout ce qui implique some() sera de la forme some([R]). 
some() est donc déjà géré de la façon la plus appropriée par les règles sur la subsomption atomique. */

/* Question 6 : tests avec variables --------------------------------------------------------------------------*/

/* Récapitulons : ce programme sait maintenant gérer des concepts atomiques, et entre eux des subsomptions et des 
équivalences ; il a la possibilité de considérer des intersections et des quantificateurs universels, et d'en 
dériver même pour répondre à une requête qui n'en contient pas. */

/* La requête subsS(lion,X) va donner lion, felin, mammifere, animal, etreVivant, 
de par sa classification de Linné (...),
mais encore carnivoreExc, predateur, vu ce qu'on a dit du régime alimentaire du lion dans les faits,
some(mange), car tous les animaux mangent selon les faits,
all(mange,some(mange)), car tout ce qui mange mange quelque chose selon les faits,
puis finalement all(mange,animal) par équivalence avec le régime carnivore, 
et par suite all(mange,etreVivant) par subsomption entre animal et etreVivant.
Sans tenir compte de l'ordre, tout concorde:
?- subsS(lion, X).
X = lion ;
X = felin ;
X = carnivoreExc ;
X = mammifere ;
X = animal ;
X = etreVivant ;
X = some(mange) ;
X = predateur ;
X = all(mange, animal) ;
X = all(mange, etreVivant) ;
X = all(mange, some(mange)) ;
false.*/

/* La requête subsS(X,predateur) va déjà donner predateur, carnivoreExc.
Elle renvoie aussi lion, car le lion est défini comme carnivoreExc,
puis all(mange,animal) par équivalence avec carnivoreExc,
puis la série all(mange,mammifere), all(mange,felin), all(mange,canide), all(mange,chien), all(mange, chat), 
all(mange, souris), all(mange, canari), all(mange, lion), qui correspond à tout ce qu'on peut subsumer par animal,
puis toute une liste d'intersections possibles dans et hors du all (de par les règles fraîchement définies en 4.3). 
?- subsS(X,predateur).
X = predateur ;
X = carnivoreExc ;
X = lion ;
X = all(mange, animal) ;
X = all(mange, chat) ;
X = all(mange, lion) ;
X = all(mange, chien) ;
X = all(mange, souris) ;
X = all(mange, felin) ;
X = all(mange, canide) ;
X = all(mange, mammifere) ;
X = all(mange, canari) ;
puis un temps d'arrêt : il y a une infinité d'intersections disponibles !
Quelle que soit l'intersection fixée and(C,D), je pourrai toujours par exemple l'augmenter d'un all.
Prolog boucle indéfiniment jusqu'à ce qu'on lui demande de s'arrêter. */

/* ============================================================================================================*/

/* Exercice 5 : Complétude de l'ensemble de règles ============================================================*/

/* L'incomplétude de cet ensemble a été constatée plus haut, lorsque la requête subsS(chien,(canide,canide)) 
a renvoyé false (là où la subsomption était en fait correcte). 
A supposer que personne n'ait remarqué ce détail, 
on a ici appris à gérer les subsomptions de concepts atomiques,
puis les équivalences, 
puis les intersections, 
puis les quantificateurs universels sous leurs deux formes (all(rôle, concept) et all(rôle, instance)),
avant de décider qu'il était inutile de se mêler des quantificateurs existentiels 
(pour la bonne raison qu'ils ressemblent syntaxiquement à des concepts atomiques, FL- interdisant d'écrire des 
intersections, négations, ou quoi que ce soit d'autre qu'un rôle atomique sous le quantificateur some()).
Les cinq cas connus de la grammaire de FL- ont donc été couverts.
En outre, le programme est probablement adéquat - selon nos tests et notre intuition,
il semble bien que toute chose qu'il reconnaît comme vraie le soit. */

/* ============================================================================================================*/
/* Ce second TME présente un autre environnement de travail, le logiciel 
Prolog, qui permet de résoudre une formule dans un contexte de règles donné.
De la logique propositionnelle, on passe ici à la logique des prédicats 
du premier ordre.

A partir d'une base de connaissances, Prolog se montre capable de vérifier 
ou d'invalider des affirmations, et, si elles comportent des variables, 
de trouver les valeurs qui les satisfont. La base de connaissances se 
redivise en deux parties:
> Les règles de définition et de réécriture des prédicats sont instantiables, 
car définies pour des variables libres. Grâce à elles, Prolog passe d'une 
écriture à la suivante en unifiant entre la requête et le terme de gauche 
d'une règle - il en infère alors le terme de droite. Il tente ainsi de 
ramener la requête à une forme comparable à une liste de faits donnés.
> La liste de faits ne peut pas être simplifiée. Elle constitue un cas de 
base pour ce qui n'est finalement qu'une opération récursive...

Note: il y a équivalence entre une formule et l'ensemble de ses versions 
unifiées. Si au moins une version unifiée est vraie, elle l'est aussi.

Expressions avec constantes:
S'il existe un chemin, une suite d'unifications, tel que la requête mène 
à un fait connu (on remonte l'implication fait->requête), Prolog la valide.
S'il n'y a plus de réécritures possibles et qu'aucun fait ne correspond, 
il renvoie false.

Présence de variables:
Prolog teste les substitutions possibles au cours de ses manoeuvres 
d'unification et renvoie les noms des constantes qui satisfont la formule 
évaluée. Si aucune substitution ne donne un fait connu, il renvoie false. 

Les objets manipulés sont des prédicats d'arité n. Un prédicat p concernant 
une ou plusieurs valeurs (X,Y...) est vrai seulement s'il existe :
- un fait explicite tel que p(X,Y...) OU
- une relation entre des prédicats qui permet d'inférer que p(X,Y,...)

***************************************************************************
************************************************************************ */

/* conflits possibles: mettre les règles de l'exercice 1 XOR de l'exercice 2 
en commentaire s'il faut utiliser ce fichier sous Prolog */

/* Exercice 1 - premières traces avec Prolog

r(a,b). /*(1)*/
r(f(X),X) :- p(X,Y). /*(2)*/
p(f(X),Y) :- r(X,Y). /*(3)*/

Etant donnés les faits et règles précédents, chargés dans un fichier .pl,
on soumet à Prolog une assertion: ------------ r(f(f(a)),b). --------------

En activant le mode trace, on obtient:
[trace] 1 ?- r(f(f(a)),b). ------------------------------------------------
   Call: (8) r(f(f(a)), b) ? creep ----------------------------------------
   Call: (9) p(f(a), b) ? creep -------------------------------------------
   Call: (10) r(a, b) ? creep ---------------------------------------------
   Exit: (10) r(a, b) ? creep ---------------------------------------------
   Exit: (9) p(f(a), b) ? creep -------------------------------------------
   Exit: (8) r(f(f(a)), b) ? creep ----------------------------------------
true. ---------------------------------------------------------------------

----------------------------------------------- r(f(f(a)),b) --------------
> est de la forme r(f(X),Y) avec X=f(a), Y=b.
  déjà, y a-t-il un tel fait ? non. mais:
> selon (2), dire cela, c'est dire que p(f(a),b).
  y a-t-il un tel fait ? non. 
  continuer les unifications en suivant les règles.
> p(f(a),b) est de la forme p(f(X),Y) avec X=a, Y=b
  et selon (3), dire cela, c'est dire que r(a,b).
> il n'existe plus aucune règle disponible pour simplifier,
  c'est donc notre dernière chance : existe-t-il un fait tel que r(a,b)? 
  (en d'autres termes, avais-je en fait raison d'affirmer r(f(f(a)),b), 
  qui est vrai si r(a,b)?)
  oui: c'est (1), le seul fait disponible.
> on remonte pas à pas.
> true.

Sur une autre trace: ----------------------- p(f(a),b). -------------------
[trace] 2 ?- p(f(a),b). ---------------------------------------------------
   Call: (8) p(f(a), b) ? creep -------------------------------------------
   Call: (9) r(a, b) ? creep ----------------------------------------------
   Exit: (9) r(a, b) ? creep ----------------------------------------------
   Exit: (8) p(f(a), b) ? creep -------------------------------------------
true. ---------------------------------------------------------------------

-------------------------------------------- p(f(a),b) --------------------
> est de la forme p(f(X),Y) avec X=f(a)
  il n'existe pas un tel fait, mais on sait que 
> selon (2), dire cela, c'est dire que r(a,b).
> il n'y a plus aucune règle disponible pour simplifier.
  existe-t-il un fait tel que r(a,b)?   
  oui, c'est (1)
> on remonte les étapes précédentes.
> true.

***************************************************************************
************************************************************************ */

r(a,b). /*(1)*/
q(X,X). /*(2)*/
q(X,Z) :- r(X,Y),q(Y,Z). /*(3)*/

/* Exercice 2 - requêtes avec variables

Cette fois, les requêtes soumises à Prolog contiennent des variables non 
instanciées. Prolog doit donc décider s'il existe des constantes telles 
que la formule citée peut être satisfaite, et si oui, en donner la liste.

Prolog offre la trace suivante en réponse à la requête ------- q(X,b). ----

[trace] 3 ?- q(X,b). ------------------------------------------------------
   Call: (8) q(_14320, b) ? creep -----------------------------------------
   Exit: (8) q(b, b) ? creep ----------------------------------------------
X = b ; -------------------------------------------------------------------
   Redo: (8) q(_14320, b) ? creep -----------------------------------------
   Call: (9) r(_14320, _14538) ? creep ------------------------------------
   Exit: (9) r(a, b) ? creep ----------------------------------------------
   Call: (9) q(b, b) ? creep ----------------------------------------------
   Exit: (9) q(b, b) ? creep ----------------------------------------------
   Exit: (8) q(a, b) ? creep ----------------------------------------------
X = a ; -------------------------------------------------------------------
   Redo: (9) q(b, b) ? creep ----------------------------------------------
   Call: (10) r(b, _14538) ? creep ----------------------------------------
   Fail: (10) r(b, _14538) ? creep ----------------------------------------
   Fail: (9) q(b, b) ? creep ----------------------------------------------
   Fail: (8) q(_14320, b) ? creep -----------------------------------------
false. --------------------------------------------------------------------

------------------------------------------------------------ q(X,b). ------
Prolog va ici considérer plusieurs cas pour satisfaire ce qui peut l'être.
> existe-t-il directement un fait de la forme q(X,b) ?
  (2) donne que q(X,X) est vrai pour tout X 
  c'est en particulier le cas sous la substitution X/b.
> d'où l'affichage X = b.
Y a-t-il d'autres cas ? La requête est aussi de la forme q(X,Z) avec Z=b.
> selon (3), dire cela, c'est dire que r(X,Y) et que q(Y,b), Y quelconque.
  il y a effectivement un fait du type r(X,Y) et q(Y,b), 
  à savoir r(a,b) et q(b,b) comme précédemment.
  on remonte jusqu'à la formule originale en substituant a à X, b à Y,
> donc a fonctionne aussi, d'où l'affichage X = a.
Encore d'autres cas ? On reprend à la dernière formule non résolue:
> on n'a pas exploré l'embranchement q(b,b) avec la règle (3).
  Prolog s'en charge avant de conclure qu'il n'y a pas de troisième cas 
  (car aucun fait du type r(b,T)).
L'affichage final sera donc X = b, X = a.

Sur une dernière trace: ----------------------------------- q(b,X). -------
[trace] 4 ?- q(b,X). ------------------------------------------------------
   Call: (15) q(b, _16184) ? creep ----------------------------------------
   Exit: (15) q(b, b) ? creep ---------------------------------------------
X = b ; -------------------------------------------------------------------
   Redo: (15) q(b, _16184) ? creep ----------------------------------------
   Call: (16) r(b, _16400) ? creep ----------------------------------------
   Fail: (16) r(b, _16400) ? creep ----------------------------------------
   Fail: (15) q(b, _16184) ? creep ----------------------------------------
false. --------------------------------------------------------------------

----------------------------------------------------------- q(b,X) --------
> y a-t-il un fait tel que q(b,X)?
  q(X,X) est vrai pour tout X, et en particulier sous X/b
> d'où l'affichage X = b.
D'autres cas ? On reprend à la dernière formule non résolue:
> q(b,X) est de la forme q(X,Z) avec X/b, Z/X
  ce qui selon (3) donne r(b,T) et q(T,X)
  existe-t-il un fait de la forme r(b,T) et q(T,X) ?
  non (fail)
> d'où l'affichage false.
L'affichage total est donc X = b; false, où le false final indique qu'il 
n'y a pas d'autre possibilité.

***************************************************************************
************************************************************************ */

pere(ilya, sacha).
pere(ilya, yusef).
pere(sacha, dragomir).
pere(yusef, clementine).
pere(yusef, mustafa).

pere(kant, kleist).
pere(kant, hegel).
pere(hegel, frege).
pere(frege, lrc).

mere(gaia,ilya).
mere(julnar, dragomir).
mere(lorelei, sacha).
mere(azar, yusef).
mere(citronnelle, clementine).
mere(citronnelle, mustafa).

mere(michele, lechat).

parent(X,Y) :- mere(X,Y).
parent(X,Y) :- pere(X,Y).
parents(X,Y,Z) :- pere(X,Z), mere(Y,Z).

grandPere(X,Y) :- parent(Z,Y), pere(X,Z).
frereouSoeur(X,Y) :- parent(Z,X), parent(Z,Y), X\==Y.

ancetre(X,Y) :- parent(X,Y).
ancetre(X,Y) :- parent(X,Z),ancetre(Z,Y). 
ancetre(gaia,kant).

/* Exercice 4 - Liens de parenté

Test des prédicats père et mère. ------------------------------------------

?- pere(ilya, dragomir).
false.
Ilya est le grand-père de Dragomir.

mere(julnar, dragomir).
true.

?- mere(X,Y).
X = gaia, Y = ilya ;
X = julnar, Y = dragomir ;
X = lorelei, Y = sacha ;
X = azar, Y = yusef ;
X = citronnelle, Y = clementine ;
X = citronnelle, Y = mustafa ;
X = michele, Y = lechat.
Tous les couples mère-enfant de la base.

Test du prédicat parent/2. ------------------------------------------------

?- parent(X,lechat).
X = michele.
On sait retrouver un inconnu,

?- parent(citronnelle,X).
X = clementine ;
X = mustafa.
et les enfants d'une mère,

?- parent(ilya,X).
X = sacha ;
X = yusef.
et les enfants d'un père.

?- parent(X,Y). 
X = gaia, Y = ilya ;
X = julnar, Y = dragomir ;
X = lorelei, Y = sacha ;
X = azar, Y = yusef ;
X = citronnelle, Y = clementine ;
X = citronnelle, Y = mustafa ;
X = michele, Y = lechat ;
X = ilya, Y = sacha ;
X = ilya, Y = yusef ;
X = sacha, Y = dragomir ;
X = yusef, Y = clementine ;
X = yusef, Y = mustafa ;
X = kant, Y = kleist ;
X = kant, Y = hegel ; 
X = hegel, Y = frege ;
X = frege, Y = lrc.
Tous les couples parent-enfant existants.

Test du prédicat parents/3. -----------------------------------------------

?- parents(citronnelle, yusef, clementine).
false.
?- parents(yusef, citronnelle, clementine).
true.
Prêter attention à l'ordre dans lequel on indique les parents.

?- parents(lorelei, sacha, X).
false.

?- parents(X, Y, yusef).
X = ilya, Y = azar.

?- parents(X, Y, Z).
X = ilya, Y = lorelei, Z = sacha ;
X = ilya, Y = azar, Z = yusef ;
X = sacha, Y = julnar, Z = dragomir ;
X = yusef, Y = citronnelle, Z = clementine ;
X = yusef, Y = citronnelle, Z = mustafa ;
false.
Tous les triplets (parents)-enfant.
On ne compte pas ici les parents célibataires, il faut avoir absolument un 
X ET un Y qui vérifient la relation.

Test du prédicat grandPere. -----------------------------------------------

?- grandPere(X, frege).
X = kant.

?- grandPere(X, lrc).
X = hegel.

?- grandPere(ilya, X).
X = dragomir ;
X = clementine ;
X = mustafa ;
false.

Test du prédicat frereOuSoeur. --------------------------------------------

?- frereouSoeur(yusef,X).
X = sacha ;
false.

?- frereouSoeur(X,Y).
X = clementine, Y = mustafa ;
X = mustafa, Y = clementine ;
X = sacha, Y = yusef ;
X = yusef, Y = sacha ;
X = clementine, Y = mustafa ;
X = mustafa, Y = clementine ;
X = kleist, Y = hegel ;
X = hegel, Y = kleist ;
false.
On considère ici les demi-frères et soeurs, seul cas pour lequel un Kleist 
peut être le frère d'un Hegel - vrai seulement si le père commun est Kant.
Ce n'est plus d'actualité si on définit frereouSoeur avec parent/3.
On notera aussi que chaque paire peut être représentée deux fois, si on 
cherche d'abord du côté de la mère, puis du père... ce qui renvoie, en tout, 
quatre fois le lien de fraternité entre les deux objets concernés.
Ici, typiquement, Clémentine et Mustafa.

Test du prédicat ancetre. -------------------------------------------------

?- ancetre(X,lrc).
X = frege ;
X = kant ;
X = hegel ;
false.
Filiation ascendante.
Malheureusement, Gaia n'est pas considérée comme un ancêtre de LRC, puisque 
Gaia n'est pas un parent direct de son dernier ancêtre (Kant).

?- ancetre(azar,X).
X = yusef ;
X = clementine ;
X = mustafa ;
false.
La filiation déroulée dans ce sens est descendante.

6 ?- ancetre(gaia,X).
X = ilya ;
X = sacha ;
X = yusef ;
X = dragomir ;
X = clementine ;
X = mustafa ;
X = kant.
La descendance de Gaia est de nouveau coupée à Kant et ne va pas plus loin. 
La parenté entre Gaia et Kant n'étant pas l'objet d'une filiation détaillée,
le lien ne peut pas être obtenu à partir de la définition d'ancetre : 
ladite définition est récursive avec un pas de 1 et ne sait pas gérer les 
"sauts" au cours des générations.

***************************************************************************
************************************************************************ */

et(0,0,0).
et(0,1,0).
et(1,0,0).
et(1,1,1).

ou(0,0,0).
ou(1,0,1).
ou(0,1,1).
ou(1,1,1).

non(1,0).
non(0,1).

circuit(1,1,1).
circuit(0,1,1).
circuit(0,0,1).
circuit(1,0,0).

/* Exercice 5 - Circuit logique

Tests des prédicats de base. -----------------------------------------------

?- et(X,Y,1).
X = Y, Y = 1.

?- et(0,0,R).
R = 0 ;
false.

?- et(X,Y,R).
X = Y, Y = R, R = 0 ;
X = R, R = 0, Y = 1 ;
X = 1, Y = R, R = 0 ;
X = Y, Y = R, R = 1.

?- ou(X,1,0).
false.
Aucune solution.

?- non(X,R).
X = 1, R = 0 ;
X = 0, R = 1.

Table de vérité du circuit. ------------------------------------------------

?- circuit(X,Y,R).
X = Y, Y = R, R = 1 ;
X = 0, Y = R, R = 1 ;
X = Y, Y = 0, R = 1 ;
X = 1, Y = R, R = 0.
Cette table de vérité est bien celle de l'implication.
Ex falso quodlibet, mais le vrai ne peut pas impliquer le faux.

Essais sur le circuit. -----------------------------------------------------

?- circuit(X,0,R).
X = 0, R = 1 ;
X = 1, R = 0.
Si le deuxième terme est faux, R=neg(X).

?- circuit(X,1,1).
X = 1 ;
X = 0.
Si le deuxième terme est vrai, le circuit rend vrai quel que soit 
le premier. (Quand j'implique, je peux trouver le vrai aussi bien à partir 
du faux qu'à partir du vrai.)

?- circuit(1,Y,R).
Y = R, R = 1 ;
Y = R, R = 0.
Si le premier terme est vrai, R est égal au deuxième.

?- circuit(X,Y,0).
X = 1, Y = 0.
L'unique possibilité.

***************************************************************************
************************************************************************ */
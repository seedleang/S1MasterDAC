/* Ce troisième TME sert d'introduction à un autre pan de fonctionnalités de Prolog,
qui est donc aussi capable de gérer des listes que des variables simples.
Ce fut l'occasion d'essayer des constructions récursives plus complexes.
Les listes peuvent être construites par l'outil |, et soumises à des prédicats 
identiques à ceux qu'on utilise sur des variables simples.
| réunit les éléments de deux arguments qu'il prend en entrée pour les placer 
ensemble dans un même objet. L'ordre est conservé.
L'accès aux listes est restreint à leur premier élément, la tête, H. On peut ainsi 
diviser une liste en deux parties en la notant L = [H|T]. Il n'y a cependant aucune 
possibilité de parcours direct, à moins d'utiliser des prédicats récursifs qui se 
fondent sur cette séparabilité entre la tête et le corps de liste. Cela dit, les 
possibilités de prédicats concernant les listes sous Prolog ne font l'objet d'aucune 
limitation concrète pour peu que l'on sache correctement appliquer cette récursion. 
De même des opérations liées.
Le dernier exercice du TME montre ainsi que Prolog, un langage déclaratif, est 
aussi capable de résoudre le classique problème des palindromes que n'importe quel 
langage fonctionnel. */






/* Exercice 1 - Familiarisation avec les listes ==================================

Etant données les requêtes 
[a, [b, c], d] = [X]. ------------------------------------------------------------
[a, [b, c], d] = [X, Y, Z]. ------------------------------------------------------
[a, [b, c], d] = [a | L]. --------------------------------------------------------
[a, [b, c], d] = [X, Y]. ---------------------------------------------------------
[a, [b, c], d] = [X | Y]. --------------------------------------------------------
[a, [b, c], d] = [a, b | L]. -----------------------------------------------------
[a, b, [c, d]] = [a, b | L]. -----------------------------------------------------
[a, b, c, d | L1] = [a, b | L2]. -------------------------------------------------

Prolog renvoie les résultats suivants :
?- [a, [b, c], d] = [X]. ---------------------------------------------------------
false. 

?- [a, [b, c], d] = [X, Y, Z]. ---------------------------------------------------
X = a, Y = [b, c], Z = d. 

Prolog ne sait pas unifier un élément (comme [X]) avec une liste, mais peut en 
revanche affecter une liste à une variable, comme il le fait ensuite avec Y (sans 
crochets).

?- [a, [b, c], d] = [a | L]. -----------------------------------------------------
L = [[b, c], d].

?- [a, [b, c], d] = [X, Y]. ------------------------------------------------------
false. 

Il est impossible de parcourir les éléments d'une liste de listes "à plat", 
c'est-à-dire en itérant la lecture comme s'ils faisaient partie du même objet. 
Les niveaux d'imbrication sont séparés.
C'est pourquoi il n'est pas permis de découper une liste de trois sous-listes
en deux éléments.

?- [a, [b, c], d] = [X | Y]. -----------------------------------------------------
X = a, Y = [[b, c], d]. 

C'est l'occasion de parler du constructeur |, à ne pas confondre avec la virgule. 
[X,Y] est la liste composée de X et de Y, accolés mais bien séparés.
Le constructeur dans [X | Y] permet de créer une nouvelle liste, 
composée des ELEMENTS de X suivis des ELEMENTS de Y. 

?- [a, [b, c], d] = [a, b | L]. --------------------------------------------------
false. 

?- [a, b, [c, d]] = [a, b | L]. --------------------------------------------------
L = [[c, d]]. 

?- [a, b, c, d | L1] = [a, b | L2]. ----------------------------------------------
L2 = [c, d|L1]. 

Une liste est une boîte dans laquelle je peux aussi mettre des constructeurs.

=============================================================================== */






/* Exercice 2 - Construction de prédicats ===================================== */

concatene([],Y,Y).
concatene([T|LX],Y,[T|LZ]) :- concatene(LX,Y,LZ).

/* La liste X = [T|LX] doit constituer la première partie du résultat Z = [T|LZ]. 
On le vérifie en retirant le premier élément de X et celui de Z. Si ces éléments
sont égaux (s'il est possible d'unifier la requête avec le terme de gauche),
la récursivité continue et descend jusqu'au cas de base (défini comme un fait) 
où X est vide et Z = Y. */

inverse([],[]).
inverse([T|L],Z) :- inverse(L,R),concatene(R,[T],Z).

/* Une fois la queue de liste inversée, la tête doit être en dernière position. */

supprime([],_,[]). /* _ empêche Prolog de crier au singleton */
supprime([H|X], Y, [H|Z]) :- (H \= Y), supprime(X, Y, Z).
supprime([H|X], Y, Z) :- supprime(X, Y, Z), H = Y.

/* La suppression s'applique à la liste privée de sa tête, avec deux cas, 
en fonction de la comparaison entre ladite tête et l'élément indésirable. 
A noter que dans le second, la liste résultat (Z) ne doit pas contenir la tête. */

/* alternative	supprime([A|B], A, D) :- supprime(B, A, D). ! <-- opérateur cut
				supprime([A|B], C, [A|D]) :- supprime(B, C, D). */
				
filtre(L1,L1,[]).
filtre(L1,[],L1).
filtre(L1,[H2|T2],L3) :- supprime(L1, H2, Y), filtre(Y, T2, L3).

/* Ce filtre épure la première liste en s'appliquant séparément à chaque élément 
cité dans la seconde. */


/* Vérification des prédicats ---------------------------------------------------

?- concatene([a,b,c],[d],L2). ---------------------------------------------------
L2 = [a, b, c, d].

concatene/3 permet aussi la décomposition en sous-listes du dernier argument:
?- concatene(X,Y,[a,b,c,d]). ----------------------------------------------------
X = [], Y = [a, b, c, d] ;
X = [a], Y = [b, c, d] ;
X = [a, b], Y = [c, d] ;
X = [a, b, c], Y = [d] ;
X = [a, b, c, d], Y = [] ;
false.

?- inverse([a,b,c,d],L2). --------------------------------------------------------
L2 = [d, c, b, a].

?- supprime([a,b,a,c],a,L). ------------------------------------------------------
L = [b, c] ;
false.

?- filtre([1,2,3,4,2,3,4,2,4,1],[2,4],L). ----------------------------------------
L = [1, 3, 3, 1] ;
false.

------------------------------------------------------- Tout se passe comme prévu.

=============================================================================== */






/* Exercice 3 - Traitement des palindromes =======================================

En utilisant le prédicat magique, défini à l'exercice précédent: */

palindrome(X) :- inverse(X,X).

/* Il suffit que le mot X soit sa propre image dans un miroir. */

/* En évitant l'usage de l'inverse,
et en se fondant sur la définition suivante:
Sur un alphabet A,
- un mot vide est un palindrome,
- un mot d'une lettre a in A est un palindrome,
- un mot ewe avec e in A, w in A^[len(w)] est un palindrome */

palindrome2([]).
palindrome2([_]).
palindrome2([H|T]) :- concatene(X,[H],T),palindrome2(X).

/* Une liste est un palindrome si la suite de liste privée de sa toute fin (X),
laquelle fin doit être égale à la tête de liste (H), est aussi un palindrome.
Chaque fois que la fin qu'on vient d'isoler n'est pas égale à la tête de liste,
Prolog peut renvoyer false et terminer le calcul. */

/* Vérification des prédicats ----------------------------------------------------

?- palindrome([l,a,v,a,l]). ------------------------------------------------------
true.

?- palindrome([n,a,v,a,l]). ------------------------------------------------------
false.

?- palindrome2([l,a,v,a,l]). -----------------------------------------------------
true ;
false.

?- palindrome2([n,a,v,a,l]). -----------------------------------------------------
false.

Et pour essayer un palindrome "pair":
?- palindrome2([e,l,u,p,a,r,c,e,t,t,e,c,r,a,p,u,l,e]). ---------------------------
true ;
false.

------------------------------------------------------- Tout se passe comme prévu.

Il est bon de remarquer la façon dont Prolog traite ici la différence de casse:
il lance une tentative d'unification entre la minuscule et la majuscule.
?- palindrome2([E,s,o,p,e,r,e,s,t,e,i,c,i,e,t,s,e,r,e,p,o,s,e]). -----------------
E = e ;
false.
?- palindrome2([e,s,o,p,e,r,e,s,t,e,i,c,i,e,t,s,e,r,e,p,o,s,e]). -----------------
true ;
false.

=============================================================================== */
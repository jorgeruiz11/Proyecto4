/** Programa para el cálcuo de secuentes. **/

% 1150 es el "código" de prolog para poder definir las funciones que queremos.
:- op(1150,xfy,or). % Definimos la disyunción como operación binaria y la llamaremos con "or".
:- op(1150,fx,neg). % Definimos la negación como operación unaria y la llamaremos con "neg".
:- op(1150,xfy,and). % Definimos la conjunción como operación binaria y la llamaremos con "and".
:- op(1150,xfy,impl). % Definimos la implicación como operación binaria y la llamaremos con "impl".
:- op(1150,xfy,iff). % Definimos la doble implicación como operación binaria y la llamaremos con "iff".


/**
  dnf representa una forma normal en la lógica. La llamamos forma normal disyuntiva.
  Lo que quiere decir con esto es que al devoler un resultado este no contará con -> ni <->, sino
  que vendrá en función de ¬ (neg) y V (or) ayudandonos de las equivalencias.
*/


            /****** DNF (Forma normal Disyuntiva) ******/


% A,B,C son fórmulas de la lógica.

% Si A es una fórmula atómica, entonces la dnf de A es ella misma.
dnf(A,A) :- atom(A).
% Si la dnf de A es C, entonces la dnf de la negación de A será la negación de C.
dnf(neg A,neg C) :- dnf(A,C).
% Si la dnf de A es C y la dnf de B es D, entonces la dnf de A o B será C o D, respectivamente.
dnf(A or B,C or D) :- dnf(A,C),dnf(B,D).
/**
  Si la dnf de A es C y la dnf de B es D, entonces la dnf de  A y B "(A ∧ B)" será
  la negación de, la negación de C o la negación de D "¬(¬C v ¬D)". Como podemos ver
  ésta es una equivalencia lógica, ya que: (φ ∧ ψ) ≡ ¬(¬φ ∨ ¬ψ)
*/
dnf(A and B,neg((neg C) or (neg D))) :- dnf(A,C),dnf(B,D).
/**
  Si la dnf de A es C y la dnf de B es D, entonces la dnf de A implica B (A → B)
  será la negación de C o D (¬ C v D). Notemos que ésta también es una equivalencia lógica
  ya que: (φ → ψ) ≡ (¬φ ∨ ψ)
*/
dnf(A impl B,(neg C) or D) :- dnf(A,C),dnf(B,D).
% Si la dnf de A syss B "(A ↔ B)" es C entonces la dnf de ((A → B) ∧ (B → A)) será C
dnf(A iff B,C) :- dnf((A impl B) and (B impl A),C).



/**
  Usaremos dnfL para poder hacer las llamadas recursivas, de manera específica,
  dnfL trabaja con listas de formulas.
*/

% la dnf de la lista vacía es la lista vacía.
dnfL([],[]).
/**
  Si la dnf de F es G, entonces la dnf de cada elemento del resto de la lista donde
  se encuentra F será cada elemento del resto de la lista donde se encuentra G.
  Es decir, si la dnf de F es G, entonces la dnf de F_1 será G_1, ..., la dnf de F_n será G_n.
*/
dnfL([F|Fs],[G|Gs]) :- dnf(F,G),dnfL(Fs,Gs).



            /****  CÁCULO DE SECUENTES  ****/


% I's,D's,F's son fórmulas de la lógica o listas de fórmulas.

% Cada vez que mencionemos que B es el sc de A, lo relacionaremos con A ⊢ B.

/**
  El predicado intersection(S1,S2,S3) es verdadero si S3 se unifica con la intersección
  de S1 y S2.
  Si la intersección de I y D no es vacía "Si (vars(I) ∩ vars(D)) ≠ ∅, entonces I ⊢ D",
  es decir, si existe un unificador para I y D, entonces D será en cálcuo de secuentes (se infiere)
  de I.
*/
sc(I,D) :- not(intersection(I,D,[])).
%  Si de I se infieren "⊢" F,D, entonces de I u {¬ F} ⊢ D.      -- I u {¬ F} = {I, ¬F}
sc([(neg F)|I],D) :- sc_aux(I,[F|D]).
% Si de F,I ⊢ D entonces de I ⊢ {¬ F} u D.
sc(I,[(neg F)|D]) :- sc_aux([F|I],D).
% Si D1 = {F1, F2, D} y si I ⊢ D1, entonces I ⊢ {(F1 v F2), D}
sc(I,[(F1 or F2)|D]) :- union([F1,F2],D,D1),sc_aux(I,D1).
% Si de {F1, I} ⊢ D y de {F2, I} ⊢ D, entonces {(F1 v F2), I} ⊢ D.
% Notemos que con que cumpla uno, este será válido, pero puede cumplir las dos.
sc([(F1 or F2)|I],D) :- sc_aux([F1|I],D),sc_aux([F2|I],D).


/**
  Usaremos sc_aux para poder hacer las llamdas recursivas.
  El predicado permutation(X,Y) es verdadero cuando X es una permutación de Y. "permutation(?Xs, ?Ys)
                                                                                True when Xs is a permutation of Ys"
  Si I es una permutación de I1 y D es una permutación de D1, entonces D1 es el cálculo
  de secuentes de I1, si todo esto es verdadero, entonces D será el cálculo de secuentes de I.
  Es decir, si en cada permutación (a la par) D1 es el sc de I1, entonces finalmente D será el sc de I.
*/
sc_aux(I,D) :- permutation(I,I1),permutation(D,D1),sc(I1,D1).


/** Si I,D son listas de fórmulas y I1 es la dnfL de I (haciendo la dnf elemento por elemento)
  y D1 es la dnfL de D (el mismo caso que el anterior) y para cada I1 si D1 es su respectivo
  sc, entonces la lista D será el scl (cálculo de secuentes) de I.
*/
sc1(I,D) :- dnfL(I,I1),dnfL(D,D1),sc(I1,D1).

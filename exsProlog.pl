%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% Notació:
%%   * "donat N" significa que l'argument N estarà instanciat inicialmente.
%%   * "ha de ser capaç de generar totes les respostes possibles" significa que
%%     si hi ha backtracking ha de poder generar la següent resposta, com el
%%     member(E,L) que per una llista L "donada" pot generar tots els elements E.
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% En LI adapterem la "Notation of Predicate Descriptions" de SWI-Prolog per
%% descriure els predicats, prefixant cada argument amb un d'aquests 3 símbols:
%%   '+' quan l'argument ha d'estar necessàriament instanciat (no pot ser una
%%       variable sense instanciar). Pot ser ground (f(a) o 34)" o no (X+1 o g(a,Y)).
%%       Quan parlem de "donada L", llavors especficarem +L en la *descripció*.
%%       Per exemple, l'argument de +L del predicat esta_ordenada(+L).
%%   '-' quan l'argument ha de ser necessàriament una variable que quedarà
%%       instanciada, al satisfer-se el predicat, amb un cert terme que podem
%%       veure com un "resultat".
%%       Per exemple, l'argument -F en el predicat fact(+N,-F) que per un N donat,
%%       se satisfà fent que F sigui el valor N!.
%%   '?' quan s'accepta que l'argument pugui estar instanciat o no.
%%       Es tracta dels casos en que es diu "ha de poder generar la S i també
%%       comprovar una S donada". Llavors especificarem ?S en la *descripció*.
%%       Per exemple, l'argument ?S de suma(+L,?S).
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% En aquests exercicis feu servir els predicats propis de SWI Prolog:
%%   * member(E,L)         en lloc de  pert(E,L)
%%   * append(L1,L2,L3)    en lloc de  conc(L1,L2,L3)
%%   * select(E,L,R)       en lloc de  pert_amb_resta(E,L,R)
%%   * permutation(L,P)    en lloc de  permutacio(L,P)
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%



% PROB. A =========================================================
% Escriu un predicat
% prod(+L,?P)  que signifiqui: P és el producte dels
% elements de la llista de enters donada L. Ha de poder generar la
% P i també comprovar una P donada

prod([], 0)  :- !.
prod([A],A)  :- !.
prod([X|L], P) :- prod(L, R) , not(R = 0) , P is X * R.


% PROB. B =========================================================
% Escriu un predicat
% pescalar(+L1,+L2,?P) que signifiqui: P és el producte escalar dels
% vectors L1 i L2, on els vectors es representen com llistes
% d'enters. El predicat ha de fallar si els dos vectors
% tenen longituds diferents.

pescalar([],[],0) :- !.
pescalar([X|L1],[Y|L2],P) :- pescalar(L1,L2,R), P is X*Y+R.


% PROB. C =========================================================
% Representant conjunts com llistes sense repeticions, escriu
% predicats per les operacions d'intersecció i unió de conjunts donats

% interseccio(+L1,+L2,?L3)

interseccio([], _ ,[]) :- !.
interseccio([X|L1], L2, L3) :- not(member(X,L2)), interseccio(L1,L2,L3).
interseccio([X|L1], L2, [X|L3]) :- member(X,L2), interseccio(L1,L2,L3).


% unio(+L1,+L2,?L3)
% este se ejecuta completo

% casos base
unio([],[],[]) :- !.
unio([],[],_) :- !.

% añadimos X a L3 si no esta en L2, sino continuamos
unio([X|L1],L2,[X|L3]) :- not(member(X,L2)), unio(L1,L2,L3).
unio([X|L1],L2,L3) :- member(X,L2), unio(L1,L2,L3).

% una vez L1 es vacia añadimos todos los elementos  de L2 ya que no estaran en L3
unio([],[X|L2],[X|L3]) :- unio([],L2,L3).

% PROB. D =========================================================
% Usant append/3, escriu un predicat per calcular l'últim 
% element d'una llista donada, i un altre per calcular la llista
% inversa d'una llista donada.

% ultim(+L,?E)

ultim(L,E) :- append(_,[X],L), E=X.


% inversa(+L1,?L2)
inversa([],[]).
inversa([X|L1], R) :- inversa(L1,R2), append(R2,[X],R).




% PROB. E =========================================================
% Escriu un predicat
% fib(+N,?F) que signifiqui: F és l'N-éssim nombre de Fibonacci
% per a la N donada. Aquests nombres es defineixen així:
% fib(1) = 1, fib(2) = 1, i si N > 2 llavors
% fib(N) = fib(N-1) + fib(N-2)
fib(1,1):-!.
fib(2,1):-!.
fib(N,F):- N > 2, N1 is N-1, fib(N1,F1), N2 is N-2, fib(N2,F2), F is F1+F2.




% PROB. F =========================================================
% Escriu un predicat
% dados(+P,+N,-L) que signifiqui: la llista L expressa una forma de
% sumar P punts llançant N daus. Per exemple: si P és 5, i
% N és 2, una solució seria [1,4] (noteu que la longitud de L és N.
% Tant P com N venen instanciats. El predicat deu ser capaç de
% generar totes les solucions possibles,

dado(1).
dado(2).
dado(3).
dado(4).
dado(5).
dado(6).

dados_2(0,0,[]).
dados_2(P,N,[X|L]):- N > 0, dado(X), P >= X, P2 is P-X ,N2 is N-1, dados_2(P2,N2,L).

dados(P,N,L) :- dados_2(P,N,L), write(L), nl, fail.


% PROB. G =========================================================
% Escriu un predicat
% suma_la_resta(+L) que, donada una llista d'enters L, es satisfà si
% existeix algun element en L que és igual a la suma de la resta
% d'elements de L, i que altrament falla.
% Escriu abans un predicat
% suma(+L,?S) que, donada una llista d'enters L, se satisfà si S
% és la suma dels elements d'L.

% suma(+L,?S)

suma([],0).
suma([X|L],S):- suma(L,S2), R is X+S2, S=R.


% suma_la_resta(+L)


suma_la_resta(L) :- select(X,L,R) , suma(R,S) , X =:= S, !.


% PROB. H =========================================================
% Escriu un predicat
% card(+L) que, donada una llista d'enters L, escriba la llista
% que, para cada element d'L, diu quantes vegades surt aquest
% element en L.
% Per exemple, si fem la consulta
% card( [1,2,1,5,1,3,3,7] )  l'intèrpret escriurà:
% [[1,3],[2,1],[5,1],[3,2],[7,1]].


% ESTE PA CONTAR
count_ocurrences([],_,0).
count_ocurrences([Y|L],X,N):- not(X==Y) ,count_ocurrences(L,X,N1), N is N1.
count_ocurrences([Y|L],X,N):- X==Y,count_ocurrences(L,X,N1), N is N1+1.

% ESTA PARA PASR DE LISTA  A SET
create_set([], []).
create_set([X|L1], [X|L2]) :- not(member(X,L1)),create_set(L1,L2).
create_set([_|L1], L2) :- create_set(L1,L2).

% PARA CADA ELEMENTO DEL SET VEO CUANTOS HAY EN LA ORIGINAL,
do_work_card(L1, [X|L2], [Y|L3]) :- count_ocurrences(L1,X,N), Y=[X,N], do_work_card(L1,L2,L3).
do_work_card(_,[],[]).

% IMRPIRMO POR PANTALLA
card(L) :- create_set(L,L1) , do_work_card(L,L1,R), !,write(R), nl.



% PROB. I ========================================================
% Escriu un predicat
% esta_ordenada(+L) que signifiqui: la llista L de nombres enters
% està ordenada de menor a major.
% Per exemple, a la consulta:
% ?- esta_ordenada([3,45,67,83]).
% l'intèrpret respon yes, i a la consulta:
% ?- esta_ordenada([3,67,45]).
% respon no.

esta_ordenada([]).
esta_ordenada([_]).
esta_ordenada([X,Y|L]) :- X =< Y, esta_ordenada([Y|L]).





% PROB. J ========================================================
% Escriu un predicat
% palíndroms(+L) que, donada una llista de lletres L escrigui
% totes les permutacions dels seus elements que siguin palíndroms
% (capicues). Per exemple, amb la consulta palindrom([a,a,c,c])
% s'escriu [a,c,c,a] i [c,a,a,c]
% (possiblement diverses vegades, no cal que eviteu les repeticions).


% caso baso, palabra vacia y palabra suelta
is_palindrom([]).
is_palindrom([_]).
is_palindrom([X|L]) :- append(LR,[Y],L),X==Y , is_palindrom(LR).

palindroms(L) :- permutation(L,R), is_palindrom(R) , write(R), nl, fail .




% PROB. K ========================================================
% Volem obtenir en Prolog un predicat
% dom(+L) que, donada una llista L de fitxes de dominó (en el format
% indicat abaix), escrigui una cadena de dominófent servir *totes*
% les fitxes de L, o escrigui "no hi ha cadena" si no és possible.
% Per exemple,
% ?- dom( [ f(3,4), f(2,3), f(1,6), f(2,2), f(4,2), f(2,1) ] ).
% escriu la cadena correcta:
% [ f(2,3), f(3,4), f(4,2), f(2,2), f(2,1), f(1,6) ].
%
% També podem "girar" alguna fitxa como f(N,M), reemplaçant-la
% per f(M,N). Així, per:
% ?- dom( [ f(4,3), f(2,3), f(1,6), f(2,2), f(2,4), f(2,1) ] ).
% només hi ha cadena si es gira alguna fitxa (per exemple, hi ha
% mateixa cadena d'abans).
%
% El següent programa Prolog encara no té implementat els possibles
% girs de fitxes, ni té implementat el predicat ok(P), que
% significa: P és una cadena de dominó correcta (tal qual,
% sense necessitat de girar cap fitxa):

p([],[]).
p(L,[X|P]) :- select(X,L,R), p(R,P).

dom(L) :- p(L,P), ok(P), write(P), nl.
dom(_) :- write('no hi ha cadena'), nl.

% a) Escriu el predicat ok(+P) que falta.

ok([_]).
ok([[_,X],[Y,Z]|R]) :- X == Y, ok([[Y,Z]|R]).


% b) Estén el predicat p/2 per a que el programa també pugui
%    fer cadenes girant alguna de les fitxes de l'entrada.







% PROB. L ========================================================
% Write in Prolog a predicate aplanada(+L,?F) that ``flattens''
% (cat.: ``aplana'') the list F as in the example:
% ?- aplanada( [a,b,[c,[d],e,[]],f,[g,h]], F ).
% F = [a,b,c,d,e,f,g,h]







% PROB. M ========================================================
% Consider two groups of 10 people each. In the first group,
% as expected, the percentage of people with lung cancer among smokers
% is higher than among non-smokers.
% In the second group, the same is the case.
% But if we consider the 20 people of the two groups together, then
% the situation is the opposite: the proportion of people with
% lung cancer is higher among non-smokers than among smokers!
% Can this be true? Write a little Prolog program to find it out.

%% Descomenteu i completeu les linies de codi que veieu a continuació:
%% main :-
%%     between(0,4,SC1),    % SC1:   "no.    smokers with    cancer group 1"
%%     between(0,4,SNC1),   % SNC1:  "no.    smokers with no cancer group 1"
%%     between(0,4,NSC1),   % NSC1:  "no. no smokers with    cancer group 1"
%%     between(0,4,NSNC1),  % NSNC1: "no. no smokers with no cancer group 1"
%%     10 is SC1+SNC1+NSC1+NSNC1,  
%%     ...

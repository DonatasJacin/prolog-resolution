
/* My solution shown here for converting propositional formulae into conjunctive normal form
 and then resolving is highly based on the solution provided in Section 2.9 of Fitting's book */

/* Begin by initialising operators and their precedence */ 

?-op(140, fy, neg).
?-op(160, xfy, [and, or, imp, revimp, uparrow, downarrow, notimp, notrevimp, equiv, notequiv]).

/* member(Item, List) :- Item occurs in list */

/* if X is the head... */
member(X, [X|_]).
/* else if X is not the head */
member(X, [_|Tail]) :- member(X,Tail).


/* remove(Item, List, Newlist) :-
        Newlist is the result of removing all occurences of Item from List
*/

/* if list is empty... */
remove(_, [], []).
/* else if X is the head ... */
remove(X, [X|Tail], Newtail) :-
    remove(X, Tail, Newtail).
/* else ... */
remove(X, [Head|Tail], (Head|Newtail)) :-
    remove(X, Tail, Newtail).

/* conjunctive(X) :- X is an alpha formula */

conjunctive(_ and _).
conjunctive(neg(_ or _)).
conjunctive(neg(_ imp _)).
conjunctive(neg(_ revimp _)).
conjunctive(neg(_ uparrow _)).
conjunctive(_ downarrow _).
conjunctive(_ notimp _).
conjunctive(_ notrevimp _).

/* disjunctive(X) :- X is a beta formula */

disjunctive(neg(_ and _)).
disjunctive(_ or _).
disjunctive(_ imp _).
disjunctive(_ revimp _).
disjunctive(_ uparrow _).
disjunctive(neg(_ downarrow _)).
disjunctive(neg(_ notimp _)).
disjunctive(neg(_ notrevimp _)).

/* unary(X) :- X is a double negation, or a negated constant */

unary(neg neg _).
unary(neg true).
unary(neg false).

/* equivalent(X) :- X is composed of equivalence operators */
equivalent(_ equiv _).
equivalent(neg(_ equiv _)).
equivalent(_ notequiv _).
equivalent(neg(_ notequiv _)).

/* components(X, Y, Z) :- Y and Z are the components of the formula X, as defined
 in the alpha and beta table */

components(X and Y, X, Y).
components(neg(X and Y), neg X, neg Y).
components(X or Y, X, Y).
components(neg(X or Y), neg X, neg Y).
components(X imp Y, neg X, Y).
components(neg(X imp Y), X, neg Y). 
components(X revimp Y, X, neg Y).
components(neg(X revimp Y), neg X, Y).
components(X uparrow Y, neg X, neg Y).
components(neg(X uparrow Y), X, Y).
components(X downarrow Y, neg X, neg Y).
components(neg(X downarrow Y), X, Y).
components(X notimp Y, X, neg Y).
components(neg(X notimp Y), neg X, Y).
components(X notrevimp Y, neg X, Y).
components(neg(X notrevimp Y), X, neg Y).

/* component(X, Y) :- Y is the component of the unary formula X. */

component(neg neg X, X).
component(neg true, false).
component(neg false, true).

/* extension to component for equivalence formulas */

component(X equiv Y, (neg X or Y) and (X or neg Y)).
component(neg(X equiv Y), (neg X or neg Y) and (X or Y)).
component(X notequiv Y, neg(X or neg Y) and (X or Y)).
component(neg(X notequiv Y), (neg X or Y) and (X or neg Y)).

/* singlestep(Old, New) :- New is the result of applying a single step of the expansion process to Old, which is a conjunction of disjunctions. */

/* I have modified the algorithm provided in Section 2.9 from disjunctive normal form to
 conjunctive normal form below*/ 

/* singlestep for equivalence formulas */
singlestep([Disjunction | Rest], New) :-
    member(Formula, Disjunction),
    equivalent(Formula),
    component(Formula, Newformula),
    removeAllElements(Formula, Disjunction, Temporary),
    joinLists([Newformula], Temporary, Newdisjunction),
    New = [Newdisjunction | Rest].

/* singlestep for alpha formulas */
singlestep([Disjunction | Rest], New) :-
    member(Alpha, Disjunction),
    conjunctive(Alpha),
    components(Alpha, Alphaone, Alphatwo),
    removeAllElements(Alpha, Disjunction, Temporary),
    Newdisjunctionone = [Alphaone | Temporary],
    joinLists([Alphaone], Temporary, Newdisjunctionone),
    joinLists([Alphatwo], Temporary, Newdisjunctiontwo),
    New = [Newdisjunctionone, Newdisjunctiontwo | Rest].

/* singlestep for beta formulas */
singlestep([Disjunction | Rest], New) :-
    member(Beta, Disjunction),
    disjunctive(Beta),
    components(Beta, Betaone, Betatwo), 
    removeAllElements(Beta, Disjunction, Temporary),
    Newdisjunction = [Betaone, Betatwo | Temporary],
    New = [Newdisjunction | Rest].

/* singlestep for unary operators */
singlestep([Disjunction | Rest], New) :-
    member(Formula, Disjunction),
    unary(Formula),
    component(Formula, Newformula),
    removeAllElements(Formula, Disjunction, Temporary),
    joinLists([Newformula], Temporary, Newdisjunction),
    New = [Newdisjunction | Rest].

singlestep([Disjunction | Rest], New) :-
    singlestep(Rest, Newrest),
    joinLists([Disjunction], Newrest, New).


/* joinLists(List1,List2,List3) :- List3 is the result of joining List1 and List2*/
/* This method of joining or appending two lists was found online, specifically at:
https://stackoverflow.com/questions/11539203/how-do-i-append-lists-in-prolog */
joinLists([X | Y], Z, [X | W]) :-
    joinLists(Y, Z, W).
joinLists([], X, X).

/* findList(Element, List, Location) :- returns list Location where Element exists */

findList(Element, [_ | Rest], Location) :-
    findList(Element, Rest, Location).
findList(Element, [List | _], Location) :-
    member(Element, List),
    Location = List.

/* removeElement(Element, List, Newlist) :- returns Newlist with Element removed from List*/

removeElement(_, [], []):- 
    !.
removeElement(Element, [Element | Rest], Newlist) :-
    !,
    Newlist = Rest.
removeElement(Element, [Head | Rest], Newlist) :-
    !,
    removeElement(Element, Rest, Newerlist),
    joinLists([Head], Newerlist, Newlist).

/* removeAllElements(Element, List, Newlist) :- returns Newlist with all Element removed from List */

removeAllElements(_, [], []):- 
    !.
removeAllElements(Element, [Element | Rest], Newlist) :-
    !,
    removeAllElements(Element, Rest, Newlist).
removeAllElements(Element, [Head | Rest], Newlist) :-
    !,
    removeAllElements(Element, Rest, Newerlist),
    joinLists([Head], Newerlist, Newlist).

/* simplify(List, Newlist, Output) :- returns Output with all elements appearing only once from List */

/* when original list is empty... 
just output Newlist */
simplify([], Newlist, Newlist).
/* if head is not already in Newlist ... */
simplify([Head | Rest], Newlist, Output) :-
    not(member(Head, Newlist)),
    /* add to Newlist */
    simplify(Rest, [Head | Newlist], Output).
/* else if head is already in Newlist... */
simplify([Head | Rest], Newlist, Output) :-
    member(Head, Newlist),
    /* don't add to Newlist */
    simplify(Rest, Newlist, Output).

/* simplifyAll(List, Newlist, Output) :- returns Output with all sublists simplified */

simplifyAll([], Newlist, Newlist).
simplifyAll([Head | Rest], Newlist, Output):-
    simplify(Head, [], Newhead),
    simplifyAll(Rest, [Newhead | Newlist], Output).

/* as specified in coursework document, we define resolution to deal with resolution rules */

resolution(Disjunction, Disjunction) :-
    member([], Disjunction).
resolution(Disjunction, Output) :-
    resolutionstep(Disjunction, Temporary),
    resolution(Temporary, Output).

/* now define resolutionstep to apply resolution rules to disjunctions */

/* Simply removes all false occurances in disjunction */
resolutionstep([Disjunction | Rest], New) :-
    member(false, Disjunction),
    removeAllElements(false, Disjunction, Newdisjunction),
    New = [Newdisjunction, Rest].

/* for negated */
resolutionstep([Disjunction | Rest], New) :-
    member(neg Atomic, Disjunction),
    findList(Atomic, Rest, OppDisjunction),
    removeAllElements(neg Atomic, Disjunction, Temporary),
    removeAllElements(Atomic, OppDisjunction, OppTemporary),
    joinLists(Temporary, OppTemporary, Newdisjunction),
    simplify(Newdisjunction, [], Newerdisjunction),
    removeElement(OppDisjunction, Rest, Newrest),
    joinLists([Newerdisjunction], Newrest, New).

/* for not negated */
resolutionstep([Disjunction | Rest], New) :-
    member(Atomic, Disjunction),
    findList(neg Atomic, Rest, OppDisjunction),
    removeAllElements(Atomic, Disjunction, Temporary),
    removeAllElements(neg Atomic, OppDisjunction, OppTemporary),
    joinLists(Temporary, OppTemporary, Newdisjunction),
    simplify(Newdisjunction, [], Newerdisjunction),
    removeElement(OppDisjunction, Rest, Newrest),
    joinLists([Newerdisjunction], Newrest, New).

resolutionstep([Disjunction | Rest], New) :-
    resolutionstep(Rest, Newrest),
    joinLists([Disjunction], Newrest, New).

/* expand_and_close(Tableau) :- some expansion of Tableau closes. */

expand_and_close(Tableau, Output) :-
    simplifyAll(Tableau, [], NewTableau),
    resolution(NewTableau, Output).

expand_and_close(Tableau, Output) :-
    singlestep(Tableau, NewTableau),
    !,
    expand_and_close(NewTableau, Output).

/* expand(Old, New) :- New is the result of applying singlestep as many times as possible, starting with Old. */

expand(Dis, Newdis) :-
    singlestep(Dis, Temp),
    !,
    expand(Temp, Newdis).
expand(Dis, Newdis) :-
    simplifyAll(Dis, [], Tempdis),
    resolution(Tempdis, Newdis).

/* clauseform(X, Y) :- Y is the clause form of X. */

clauseform(X, Y) :- expand([[X]], Y).

/* closed(Tableau) :- every branch of Tableau contains a contradiction. */

closed([Branch | Rest]) :-
    member(false, Branch),
    closed(Rest).

closed([Branch | Rest]) :-
    member(X, Branch),
    member(neg X, Branch),
    closed(Rest).

closed([]).

/* test(X) :- create a complete Tableau expansion for neg X, and see if it is closed.*/

test(X) :-
    if_then_else(expand_and_close([[neg X]], _), yes, no).

yes :-
    write(yes).

no :-
    write(no).

/* if_then_else(P, Q, R) :- either P and Q, or not P and not R. */

if_then_else(P, Q, _) :- 
    P,
    !,
    Q.

if_then_else(_, _, R) :-
    R.

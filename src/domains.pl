
:- module(domains, [
         translate/3
  ]).


:- use_module(parser).
:- use_module(utils).

:- discontiguous domains:translate/3.
:- discontiguous domains:translate/4.

remove_type(typestr(V), V, typestr).
remove_type(typenum(V), V, typenum).

gen_values([], L, Lout) :-
            append(L, [newline, '}'], Lout).

gen_values([H|T], L, Lout) :-
       remove_type(H, Hv, Type),
       (Type = typestr -> append(L, [newline, '\'', Hv, '\'', space, : , space, "True"], L1) ; append(L, [newline, Hv,  space, : , space, "True"], L1)),
       (T \= [] -> append(L1, [','], L2) ;  L2 = L1),
       gen_values(T, L2, Lout).

translate(domains, Domains, Lout) :-
       translate(domains, Domains, [], Lout).

translate(domains, [], L, L).

translate(domains, [H|T], L, Lout) :- 
           H = (Domain, Values),
           atom_chars(Domain, Chars),
           append(Namechars, ['_',_], Chars),
           atom_chars(_, Namechars),
           append(L, [newline, Domain, space, =, space, '{' ], L1),
           gen_values(Values, L1, L2),
           translate(domains, T, L2, Lout).

inverse_format_arg(typestr(X), X).
inverse_format_arg(typenum(X), X).


translate(inputs, Inputvalues, L) :-
     translate(inputs, Inputvalues, [newline, input, space, =, '{'], L).

translate(inputs, [], L, Lout) :-
            append(L, [newline, '}'], Lout).


translate(inputs, [H|T], L, Lout) :-
        H =.. [Name|Args],
        maplist(inverse_format_arg, Args, Args1),
        H1 =.. [Name|Args1],
        (T = [] -> append(L, [newline, '\'', H1, '\'', space, :, space, "True"], L1) 
                ;  append(L, [newline, '\'', H1, '\'', space, :, space, "True", ','], L1)),
        translate(inputs, T, L1, Lout).

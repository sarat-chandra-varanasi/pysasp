:- module(parser, [
                      neg_name/2,
                      neg_functor/2,
                      typeof/2,
                      gen_intermediate_prog/11,
                      or/3,
                      and/3,
                      subexprs/2
                  ]).


:- use_module(main).
:- use_module(io).
:- use_module(common).
:- use_module(main).
:- dynamic domain/1.
:- dynamic main_pred/1.        

:- discontiguous parser:domains/3.
:- discontiguous parser:drop_domains/3.
:- discontiguous parser:drop_domains/4.
:- discontiguous parser:domains_for/3.
:- discontiguous parser:domains_for/4.
:- discontiguous parser:is_primitive/1.
:- discontiguous parser:add_edges/3.
:- discontiguous parser:add_edges/4.
:- discontiguous parser:add_dataflow/4.
:- discontiguous parser:disjunctive_rules/6.
:- discontiguous parser:infer_types/2.
:- discontiguous parser:infer_types/3.

domains(S) :- setof(X, main:domain(X), S).

domains(S, Domains) :- domains(S, [], Domains).
domains([], L, L).

domains([domain_1(Domterm)-[] | T], L, Domains) :- 
            !, split_functor(Domterm, Namechars, _), 
            atom_chars(Name, Namechars), 
            append(L, [Name], L1),
            assert(domain(Name)),
            domains(T, L1, Domains).

domain(xyz).


domains([_|T], L, Domains) :- domains(T, L, Domains).

main_pred([main_1(Predterm)-[]|_], Main) :- 
                  !, split_functor(Predterm, Namechars, _),
                  atom_chars(Main, Namechars), 
                  assert(main_pred(Main)).

main_pred([_|T], Main) :- main_pred(T,Main).

main_pred_arity(Main, [H|_], Arity) :- 
              H = Head-_,
              Head =.. [Main_n|_],
              split_functor(Main, Mainchars, -1),
              split_functor(Main_n, Mainchars, Arity).

main_pred_arity(Main, [H|T], Arity) :-
              H = Head-_,
              Head =.. [Main_n|_],
              split_functor(Main, Mainchars, -1),
              split_functor(Main_n, Chars, _),
              Mainchars \= Chars,
              main_pred_arity(Main, T, Arity).

inputs(S, Inputs) :-
       inputs(S, [], Inputs).

inputs([], I, I).

inputs([input_1(Inputterm)-[] |T], I, Inputs) :-
            split_functor(Inputterm, Namechars, _),
            atom_chars(Name, Namechars),
            append(I, [Name], I1),
            inputs(T, I1, Inputs).


inputs([_|T], I, Inputs) :-
          inputs(T, I, Inputs).

get_body(_-Body, Body).
           
func_arity(Functor, Statements, Functor_n) :-
            maplist(get_body, Statements, L),
            reduce(lst_union, L, L1),
            functor_arity(Functor, L1, Functor_n).

functor_arity(Functor, [H|_], Functor_n) :- 
              H =.. [Functor_n|_],
              split_functor(Functor, Functorchars, -1),
              split_functor(Functor_n, Functorchars, Arity),
              Arity > -1, !.

functor_arity(Functor, [H|T], Functor_n1) :-
              H =.. [Functor_n|_],
              split_functor(Functor, Functorchars, -1),
              split_functor(Functor_n, Chars, _),
              Functorchars \= Chars,
              functor_arity(Functor, T, Functor_n1).


functor_arities(Functors, Statements, Functor_ns) :-
         functor_arities(Functors, Statements, [], Functor_ns).

functor_arities([], _, F, F).
functor_arities([H|T], Statements, F, Functor_ns) :-
          func_arity(H, Statements, F_n),
          append(F, [F_n], F1),
          functor_arities(T, Statements, F1, Functor_ns).

is_domain(Domains, Functor) :-
            Functor =.. [Name, _],
            member(Name, Domains).

format_arg(X+Y,X1+Y1) :- format_arg(X,X1), format_arg(Y,Y1).
format_arg(X-Y,X1-Y1) :- format_arg(X,X1), format_arg(Y,Y1).

format_arg(A, A) :- A = typenum(_).

format_arg(A, A) :- A = typestr(_).

format_arg(A, Afmt) :-
        atom_chars(A, [H|_]),
        char_type(H, upper),
        string_lower(A, A1),
        atom_string(Afmt, A1).

format_arg(A_n, typestr(Afmt)) :-
        atom_chars(A_n, [H|_]),
        char_type(H, lower),
        split_functor(A_n, Chars, _),
        atom_chars(Afmt, Chars).
        

format_args(Args,Args1) :-
     format_args(Args, [], Args1).

format_args([H|T], A, Args1) :-
        format_arg(H, H1),
        append(A, [H1], A1),
        format_args(T, A1, Args1).

format_args([], A, A).

format_functor((Domains, Functor1), Functor2) :-
              is_domain(Domains, Functor1),
              Functor1 =.. [Functor1_n|Args],
              format_args(Args, Args1),
              Functor2 =.. [Functor1_n|Args1].

format_functor((Domains, Functor1), Functor2) :-
         Functor1 \= not(_),
         not(is_primitive(Functor1)),
         not(is_domain(Domains,Functor1)),
         Functor1 =.. [Functor1_n|Args],
         %split_functor(Functor1_n,Functor1chars,_),
         %atom_chars(Functorname, Functor1chars),
         format_args(Args, Args1),
         %Functor2 =.. [Functorname|Args1],
         Functor2 =.. [Functor1_n|Args1].

format_functor((Domains, Functor1), Functor3) :-
         Functor1 \= not(_),
         is_primitive(Functor1),
         not(is_domain(Domains,Functor1)),
         id(Id),
         retract(id(Id)),
         Id1 is Id + 1,
         assert(id(Id1)),
         Functor1 =.. [Functor1_n|Args],
         %split_functor(Functor1_n,Functor1chars,_),
         %atom_chars(Functorname, Functor1chars),
         format_args(Args, Args1),
         atom_string(primitive_, P),
         atom_string(Id1, Ids),
         string_concat(P, Ids, Prim),
         atom_string(Primitive, Prim),
         %Functor2 =.. [Functorname|Args1],
         Functor2 =.. [Functor1_n|Args1],
         Functor3 =.. [Primitive,Functor2].

format_functor((_, Functor1), Functor2) :-
         Functor1 = not(F1),
         not(is_primitive(F1)),
         F1 =.. [Functor1_n|Args],
         %split_functor(Functor1_n,Functor1chars,_),
         format_args(Args, Args1),
         atom_chars(Functor1_n, Chars),
         %Functor1chars1 = [n, o, t, '_' | Functor1chars],
         Chars1 = [n, o, t, '_' | Chars],
         flatten(Chars1, Chars2),
         atom_chars(Functorname, Chars2),
         %atom_chars(Functorname, Functor1chars1),
         %Functor2 =.. [Functorname|Args1],
         Functor2 =.. [Functorname|Args1].

format_functor((_, Functor1), Functor3) :-
         Functor1 = not(F1),
         F1 =.. [Functor1_n|Args],
         is_primitive(F1),
         id(Id),
         retract(id(Id)),
         Id1 is Id + 1,
         assert(id(Id1)),
         %split_functor(Functor1_n,Functor1chars,_),
         format_args(Args, Args1),
         atom_chars(Functor1_n, Chars),
         %Functor1chars1 = [n, o, t, '_' | Functor1chars],
         Chars1 = [n, o, t, '_' | Chars],
         flatten(Chars1, Chars2),
         atom_chars(Functorname, Chars2),
         %atom_chars(Functorname, Functor1chars1),
         %Functor2 =.. [Functorname|Args1],
         Functor2 =.. [Functorname|Args1],
         atom_string(primitive_, P),
         atom_string(Id1, Ids),
         string_concat(P, Ids, Primitive),
         atom_string(Primitive, _),
         Functor3 =.. [Primitive,Functor2].

format_head(Headterm-[], Headfunctor) :- 
         format_functor(Headterm, Headfunctor).

match_rule(Head-Body, Head, Body).
match_rule(Head-[], Head, []).

lst_union([],L,L).
lst_union([H|T],L,L1) :- member(H, L), lst_union(T,L,L1).
lst_union([H|T],L,[H|L1]) :- not(member(H,L)), lst_union(T,L,L1).


lst_intersect([],_,[]).
lst_intersect([H|T], L, [H|L1]) :- member(H, L), lst_intersect(T, L,  L1).
lst_intersect([H|T], L, L1) :- not(member(H, L)), lst_intersect(T, L, L1).


lst_difference([], _, []).
lst_difference([H|T],L,[H|L1]) :- not(member(H,L)), lst_difference(T, L, L1).
lst_difference([H|T],L,L1) :- member(H, L), lst_difference(T, L,  L1).


is_var(X) :- X \= typestr(_), X \= typenum(_).
    
filter(Property, L, L1) :-
         filter(Property, L, [], L1).
filter(Property, [H|T], L, L2) :-
         call(Property, H),
         append(L, [H], L1),
         filter(Property, T, L1, L2).
filter(Property, [H|T], L, L1) :-
         not(call(Property, H)),
         filter(Property, T, L, L1).
filter(_, [], L, L).

functor_vars(F, V3) :- 
      F =.. [Name|V], 
      atom_chars(Name, [p,r,i,m,i,t,i,v,e|_]), !,
      V = [V1],
      V1 =.. [_|V2],
      filter(is_var, V2, V3). 
functor_vars(F, V3) :- 
      F =.. [Name|V], 
      atom_chars(Name, [n,o,t,'_',p,r,i,m,i,t,i,v,e|_]), !,
      V = [V1],
      V1 =.. [_|V2],
      filter(is_var, V2, V3). 

functor_vars(F, V1) :-
     F =.. [_|V],
     filter(is_var, V, V1).


all_variables(Rule, Vs) :- 
          match_rule(Rule, Head, Body),
          maplist(format_functor,[Head|Body],Rulefmt),
          maplist(functor_vars,Rulefmt,Vs1),
          reduce(lst_union,Vs1,Vs).

vars_domain((Domains, Term), Functor) :- Term =.. [Name,V], member(Name, Domains), Functor =.. [V, Name]. 
vars_domain((Domains, Term), nil) :- Term =.. [Name|_], not(member(Name, Domains)).

%domain_info(Rule, Domains) :-
%           match_rule(Rule, _, Body), 
%           maplist(format_functor,Body,Bodyfmt),
%           maplist(vars_domain,Bodyfmt,Doms),
%           lst_difference(Doms,[nil],Domains). 

domain_info(Domains, Lst, Doms) :-
          cross(Domains, Lst, Lst1),
          maplist( vars_domain,Lst1, Doms1), 
          lst_difference(Doms1, [nil], Doms).

foldr(_,X,[],X).
foldr(F,X,[H|T],R2) :- foldr(F,X,T,R1), call(F,H,R1,R2).        

reduce(F,[H|T],L1) :- foldr(F,H,T,L1).
reduce(_,[],[]).

:- dynamic rule_ident/2.

rule_id(Domains, Inputs, Rule, Id) :- 
         match_rule(Rule, Head, _),
         Head =.. [Id|_],
         or(member(Id, Inputs), member(Id, Domains), true).

rule_id(Domains, Inputs, Rule, Id) :- 
            match_rule(Rule, Head, _),
            Head =.. [Id|_],
            not(member(Id, Inputs)),
            not(member(Id, Domains)),
            not(rule_ident(Id, _)),
            assert(rule_ident(Id,1)).
            
rule_id(Domains, Inputs, Rule, Id) :- 
            match_rule(Rule, Head, _),
            Head =.. [Name_n|_],
            not(member(Name_n, Inputs)),
            not(member(Name_n, Domains)),
            rule_ident(Name_n, Count),
            atom_chars(Name_n, Chars),
            append(Name, ['_',Arity], Chars),
            Count1 is Count + 1,
            retract(rule_ident(Name_n, Count)),
            assert(rule_ident(Name_n, Count1)),
            number_chars(Count1, Chars1),
            append(Name, Chars1, Chars2),
            append(Chars2,['_',Arity],Chars3),
            atom_chars(Id, Chars3).


rule_id_fmt((Id,_,_,_,_), Id).

drop_domains(_,[], L, L).
drop_domains(Domains, L, L1) :- drop_domains(Domains, L, [], L1).
drop_domains(Domains,[H|T], L, L1) :- H =.. [Name | _], member(Name, Domains), drop_domains(Domains, T, L, L1).
drop_domains(Domains,[H|T], L, L2) :- H =.. [Name | _], not(member(Name, Domains)), append(L, [H], L1), drop_domains(Domains,T, L1, L2).



classify_rule(Main, Rule, main) :- Rule = (_,Head,_,_,_,_,_), rule_head_name(Head, Main).
classify_rule(Main, Rule, abstraction) :- Rule = (_,Head,_,_,_,_,_), rule_head_name(Head, Name), Main \= Name, atom_chars(Main, Mainchars),
                                          atom_chars(Name, Namechars), Namechars \= [n, o, t, '_' | Mainchars].
classify_rule(Main, Rule, dual) :- Rule = (_,Head,_,_,_,_,_), rule_head_name(Head, Name), Main \= Name, atom_chars(Main, Mainchars),
                                          atom_chars(Name, Namechars), Namechars = [n, o, t, '_' | Mainchars].                                          

name(Functor, Name) :- Functor =.. [Name | _].

check_reachable(Main, [Goal|_], Graph) :-
              reach(Main, Goal, Graph).

check_reachable(Main, [Goal|T], Graph) :-
              not(reach(Main, Goal, Graph)),
              check_reachable(Main, T, Graph).

has_main_call(Main, and(Body), Graph) :- maplist(parser:name, Body, Names), check_reachable(Main, Names, Graph), !. 
has_main_call(Main, or(Body), Graph) :- maplist(parser:name, Body, Names), check_reachable(Main, Names, Graph), !.

calls_main(Main, Rule, Property, Graph) :- Rule  = (_,_,Body,_,_,_,_), (has_main_call(Main,Body,Graph) -> Property = callmain ; Property = notcallmain).

domains_for(_, [], B, B).
domains_for(V, Domains, B) :-
            domains_for(V, Domains, [], B).
domains_for(V, [H|T], B, B2) :-
             H =.. [V1, _],
             member(V1, V),
             append(B, [H], B1),
             domains_for(V, T, B1, B2).

domains_for(V, [H|T], B, B1) :-
              H =.. [V1, _],
              not(member(V1, V)),
              domains_for(V, T, B, B1).

pair(Element1, Element2, (Element1, Element2)).

cross(Element, L, L1) :- 
         cross(Element, L, [], L1).

cross(_, [], L, L).

cross(Element, [H|T], L, L2) :-
            append(L, [(Element, H)], L1),
            cross(Element, T, L1, L2).


all_domains(Domains, Alldomains) :-
          maplist(dual_dom, Domains, Duals),
          lst_union(Domains, Duals, Alldomains).

bodyvar_doms(Bodyvars, Doms, Bdoms) :-
         bodyvar_doms(Bodyvars, Doms, [], Bdoms).

bodyvar_doms([], _, B, B).

bodyvar_doms([H|T], [A|T1], B, Bdoms) :-
          A =.. [H|_],
          append(B, [A], B1),
          bodyvar_doms(T, T1, B1, Bdoms).

bodyvar_doms([H|T], [A|T1], B, Bdoms) :-
          not(A =.. [H|_]),
          bodyvar_doms(T, T1, B, Bdoms).


%domains are complete here
format_rule(((Domains,Inputs),Rule), Rulefmt) :- 
                     rule_id(Domains, Inputs, Rule, Id),
                     match_rule(Rule,Head,Body),
                     format_functor((Domains, Head),Headfmt),
                     Headfmt =.. [_|Args],
                     Headfmt1 =.. [Id|Args],
                     cross(Domains, Body, Body1),
                     maplist(format_functor,Body1,Bodyfmt),
                     domain_info(Domains,Bodyfmt,Doms),
                     all_domains(Domains, _),
                     drop_domains(Domains, Bodyfmt,Bodyfmt1),
                     functor_vars(Headfmt,Hvs),
                     maplist(functor_vars,Bodyfmt,Bvs),
                     reduce(lst_union,Bvs,Bvs1),
                     lst_difference(Bvs1, Hvs, Bodyvars), 
                     bodyvar_doms(Bodyvars, Doms, Bdoms),
                     domains_for(Bodyvars, Doms, Backtracking),
                     Rulefmt = (Id,Headfmt1,and(Bodyfmt1),Bdoms,Doms,Backtracking,[]). 

is_primitive((_<_)).
is_primitive((_>_)).
is_primitive(_\=_).
is_primitive((_=_)).
is_primitive((_+_)).
is_primitive((_-_)).
is_primitive((_>=_)).
is_primitive((_=<_)).


or(X, _, true) :- X, !.
or(_, Y, true) :- Y, !.
or(_, _, false). 

and(X, Y, true) :- X, Y, !.
and(_, _, false).

is_primitive(not(X)) :- is_primitive(X). 

is_prim(Functor) :-
             Functor =.. [Name|_],
             atom_chars(Name, [p,r,i,m,i,t,i,v,e|_]).

is_prim(Functor) :-
             Functor =.. [Name|_],
             atom_chars(Name, [n,o,t,'_',p,r,i,m,i,t,i,v,e|_]).             

match_rule_fmt((_,Head, and(Body),_,_,_,_), Head, Body).
match_rule_fmt((_,Head, or(Body),_,_,_,_), Head, Body).

exclude_primitives(Goals,Goals1) :-
             exclude_primitives(Goals, [], Goals1).
exclude_primitives([], G, G).
exclude_primitives([H|T], G, Goals) :- 
              is_prim(H),
              exclude_primitives(T, G, Goals). 
exclude_primitives([H|T], G, Goals) :-
              not(is_prim(H)),
              append(G, [H], G1),
              exclude_primitives(T, G1, Goals).


dual_dom(Name, Dual) :-
         atom_chars(Name, Chars),
         append([n,o,t,'_'], Chars, Chars1),
         atom_chars(Dual, Chars1).

exclude_domains(Domains, Goals, Goals1) :-
             %maplist(dual_dom, Domains, Duals),
             %append(Domains, Duals, Domains1),
             exclude_domains(Domains, Goals, [], Goals1).

exclude_domains(_, [], G, G).

exclude_domains(Domains, [H|T], G, Goals1) :-
              parser:name(H, Name),
              member(Name, Domains),
              exclude_domains(Domains, T, G, Goals1).

exclude_domains(Domains, [H|T], G, Goals1) :-
              parser:name(H, Name),
              not(member(Name, Domains)),
              append(G, [H], G1),
              exclude_domains(Domains, T, G1, Goals1).


create_edge(Head, Body, edge(Head, Body)).

:- dynamic id/1.

id(0).


add_edges(_, [], E, E).
add_edges(Head, Body, Edges) :- 
         add_edges(Head, Body, [], Edges).
add_edges(Head, [H|T], E, Edges) :-
           create_edge(Head, H, Edge),
           append(E, [Edge], E1),
           add_edges(Head, T, E1, Edges).




construct_call_graph(Rules, Domains, Graph) :-
        construct_call_graph(Rules, Domains, [], Graph).

construct_call_graph([], _, Graph, Graph).


construct_call_graph([H|T], Domains, G, Graph) :-
            match_rule_fmt(H, Head, Body),
            exclude_domains(Domains, Body, Body1), 
            %rule_id_fmt(H, Headname),
            parser:name(Head, Headname),
            maplist(name, Body1, Bodynames), 
            add_edges(Headname, Bodynames, G1),
            append(G,G1,G2),     
            construct_call_graph(T, Domains, G2, Graph).

rule_id_by_functor(Functor, Id) :-
                  Functor =.. [Name | Args],
                  length(Args, Arity),
                  atom_chars(Name, Namechars),
                  number_chars(Arity,[Aritychar]),
                  append(Namechars, ['_', Aritychar], Chars),
                  atom_chars(Id, Chars).

delete_vertex(V, Graph, Graph1) :-
           delete_vertex(V, Graph, [], Graph1).
delete_vertex(V, [edge(V, _)|T], G, Graph) :-
             delete_vertex(V, T, G, Graph).
delete_vertex(V, [edge(_, V)|T], G, Graph) :-
             delete_vertex(V, T, G, Graph).
delete_vertex(_, [], G, G).
delete_vertex(V, [edge(X, Y) | T], G, Graph) :-
                X \= V, Y \= V, 
                append(G, [edge(X, Y)], G1),
                delete_vertex(V, T, G1, Graph). 


%reach(X, Y, Graph) :- member(edge(Y, X), Graph).
reach(X, Y, Graph) :-
            reach(X, Y, Graph, []).
reach(X, Y, Graph, Visited) :- 
              member(edge(Z, X), Graph),
              (Z = Y ;  not(member(Z, Visited)),reach(Z, Y, Graph, [Z|Visited])).

cycle(Graph) :- reach(X, Y, Graph), reach(Y, X, Graph).

invalid(Graph) :- member(edge(X, Y), Graph), member(edge(Y, X), Graph).






not_cycle(Graph) :- not(cycle(Graph)).

is_annotatedfmt(Domains, Termfmt) :-
            Termfmt =.. [Name|_],
            member(Name, Domains).


neg_functor((Domains,Termfmt), Termfmt) :-
         is_annotatedfmt(Domains, Termfmt).

neg_functor((_,Termfmt), Dualfmt) :-
           is_primitive(Termfmt),
            Dualfmt = not(Termfmt). 

neg_functor((Domains, Termfmt), Dualfmt) :-
           not(is_primitive(Termfmt)),
           not(is_annotatedfmt(Domains,Termfmt)),
           Termfmt =.. [Name | Args],
           atom_chars(Name, Namechars),
           Namechars \= [n, o, t, '_'|_],
           Dualchars = [n, o, t, '_'| Namechars],
           atom_chars(Dualname, Dualchars),
           Dualfmt =.. [Dualname | Args].

neg_functor((Domains,Termfmt), Dualfmt) :-
           not(is_primitive(Termfmt)),
           not(is_annotatedfmt(Domains, Termfmt)),
           Termfmt =.. [Name | Args],
           atom_chars(Name, Namechars),
           Namechars = [n, o, t, '_'| Dualchars],
           atom_chars(Dualname, Dualchars),
           Dualfmt =.. [Dualname | Args].

gen_dual((_, (Id,Headfmt,Body,Bodyvars,Doms,Backtracking,Foralls)),Dual) :-
                    or(Body = and([]),Body = or([]), true),
                    Dual = (Id,Headfmt,Body,Bodyvars,Doms,Backtracking,Foralls).


gen_dual((Domains, (Id,Headfmt,and(Bodyfmt),Bodyvars,Doms,Backtracking,Foralls)),Dual) :-
             not(member(Id, Domains)),
             neg_functor((Domains, Headfmt), Dualheadfmt),
             cross(Domains, Bodyfmt, Bodyfmt1),
             maplist(neg_functor, Bodyfmt1, Bodyfmt2),
             atom_chars(Id, Chars),
             atom_chars(Dualid, [n,o,t,'_'|Chars]),
             (Backtracking = [] -> Foralls1 = Foralls ; Foralls1 = Backtracking),
             Dual = (Dualid, Dualheadfmt, or(Bodyfmt2),Bodyvars,Doms,[],Foralls1).

gen_dual((Domains, (Id,Headfmt,or(Bodyfmt),Bodyvars,Doms,Backtracking,Foralls)),Dual) :-
             not(member(Id, Domains)),
             neg_functor((Domains, Headfmt), Dualheadfmt),
             cross(Domains, Bodyfmt, Bodyfmt1),
             maplist(neg_functor, Bodyfmt1, Bodyfmt2),
             atom_chars(Id, Chars),
             atom_chars(Dualid, [n,o,t,'_'|Chars]),
             (Backtracking = [] -> Foralls1 = Foralls ; Foralls1 = Backtracking),
             Dual = (Dualid, Dualheadfmt, and(Bodyfmt2),Bodyvars,Doms,[],Foralls1).


add_class_tuples((Main, _, Graph, R), R1) :- 
         calls_main(Main, R, Callmain, Graph), classify_rule(Main, R, Class),
         R = (Id, Head, Body, Bodyvars, Domains1, Backtracking, Foralls),
         R1  = pred(Class,Callmain,Id, Head, Body, Bodyvars, Domains1, Backtracking, Foralls).

is_annotated(domain_1(_)-[]).
is_annotated(main_1(_)-[]).
is_annotated(input_1(_)-[]).

annotations([input_1,domain_1,main_1]).


remove_annotations([], L, L).
remove_annotations([H|T], L, L2) :- 
        is_annotated(H) -> remove_annotations(T, L, L2) ; append(L, [H], L1), remove_annotations(T, L1, L2).

rule_head_name(Headfmt, Name) :-
             Headfmt =.. [Name | _].


affix_tuple(_, _, _, [], L, L).
affix_tuple(Main, Domains, Graph, [H|T], L, L2) :-
            append(L, [(Main, Domains, Graph, H)], L1), 
            affix_tuple(Main, Domains, Graph, T, L1, L2).

format_rules(Rules, R) :-
         format_rules(Rules, [], R).

%format_rules([], R, R).
%format_rules([H|T], R, Rules) :-
%          format_rule(H, Rule), 
%          append(R, [Rule], R1),
%          format_rules(T, R1, Rules).

neg_name(Name, Neg) :-
         atom_chars(Name, Namechars),
         (Namechars = [n, o, t, '_'| Negchars] -> atom_chars(Neg, Negchars) 
         ; Negchars = [n, o, t, '_' | Namechars], atom_chars(Neg, Negchars)).


%assign argflow only to predicates which callmain 
assign_argflow(Rule, _, _, Rule) :-
          Rule = pred(_,notcallmain,_,_,_,_,_).

get_rule_by_id(_, [], nil).


get_rule_by_id(Id, Rules, Rule) :-
            Rules = [Rule|_],
            Rule = (Id,_,_,_,_,_,_), !.    

get_rule_by_id(Id, Rules, Rule) :-
            Rules = [H|T],
            H = (Id1,_,_,_,_,_,_),
            Id1 \= Id, !,
            get_rule_by_id(Id, T, Rule).


expand_frontier(Vertex, Graph, Frontier) :-
                expand_frontier(Vertex, Graph, [], Frontier).

expand_frontier(Vertex, [H|T], F, Frontier) :-
                H = edge(Vertex, V1),
                append(F, [V1], F1), 
                expand_frontier(Vertex, T, F1, Frontier).

expand_frontier(Vertex, [edge(V1, _)|T], F, Frontier) :-
                Vertex \= V1,
                expand_frontier(Vertex, T, F, Frontier).

expand_frontier(_, [], F, F).

index_of(Element, List, Index) :-
        index_of(Element, List, 0, Index).

index_of(Element, [H|_], I, I1) :-
             Element = H, 
             I1 is I + 1.

index_of(Element, [H|T], I, I2) :-
              Element \= H, 
              I1 is I + 1,
              index_of(Element, T, I1, I2).

index_of_var(Functor, Var, Index) :-
             Functor =.. [_|Args],
             index_of(Var, Args, Index).

rename(Var, Var2) :-
           atom_chars(Var, Chars),
           Chars1 = [Chars|['_', '1']],
           flatten(Chars1, Chars2),
           atom_chars(Var2, Chars2).


index_tuple(Var, Functor, (Var, Var1, Index)) :-
               index_of_var(Var, Functor, Index), 
               rename(Var, Var1).


remove(H, L, L1) :-
          remove(H, L, [], L1).
remove(H, [X|Y], L, L1) :-
        H = X,
        remove(H, Y, L, L1).
remove(H, [X|Y], L, L2) :-
        H \= X, 
        append(L, [X], L1),
        remove(H, Y, L1, L2).
remove(_, [], L, L).


remove_duplicates([], []).
remove_duplicates([H|T], T3) :-
             remove(H, T, T1),
             remove_duplicates(T1,T2),
             append([H], T2, T3).
             
assign_flow(Vertex, Rules, Flow) :-
         assign_flow(Vertex, Rules, [], Flow).

assign_flow_init(Main, Rules, Flow, Flowout) :-
        get_rule_by_id(Main, Rules, Rule),
        match_rule_fmt(Rule, Head, Body),
        map_flow_init(Head, Body, Flow, Flowout). 
       

init_flow([], F, F).

init_flow([H|T], F, Flowout) :-
         H = ((Goalid, I), (_, J)),
         append(F, [(Goalid, I, J)], F1),
         init_flow(T, F1, Flowout).


map_flow_init(_, [], Flow, Flow).



map_flow_init(Head, [Goal|T], Flow, Flowout) :-
          map_vars(Head, Goal, Varmap),
          init_flow(Varmap, Flow, Flow1),
          map_flow_init(Head, T, Flow1, Flowout).


add_order(_,[],_,_,Flow, Flow). 

assign_flow(Vertex, Rules, Flow, Flow) :-
          get_rule_by_id(Vertex, Rules, nil).

assign_flow(Vertex, Rules, F, Flow) :-
          get_rule_by_id(Vertex, Rules, Rule),
          Rule \= nil,
          match_rule_fmt(Rule, Head, Body),
          map_flow(Head, Body, F, Flow).


calculate_flow(Main, Rules, Graph, Graph1, Flow) :-
          calculate_flow(Main, Rules, Graph, Graph1, [], Flow).

flow_helper([], _, _, Flow, Flow).
flow_helper([H|T],Rules, Graph, F, Flowout) :-
          assign_flow(H, Rules, F, F1),
          expand_frontier(H, Graph, Frontier),
          append(Frontier, T, Frontier1),
          flow_helper(Frontier1, Rules, Graph, F1, Flowout).




calculate_flow(Main, Rules, Graph, Graph1, F, Flowout) :-
         assign_flow_init(Main, Rules, F, F1),
         expand_frontier(Main, Graph, Frontier),
         flow_helper(Frontier, Rules, Graph1, F1, Flowout).

occurence(Var, Functor, Index) :-
         is_prim(Functor), !,
         Functor =.. [_,V],
         V =.. [_|Args],
         index_of(Var, Args, Index).

occurence(Var, Functor, Index) :-
         Functor =.. [_|Args],
         index_of(Var, Args, Index).

flow_of(Ruleid, Flow, Order, Order1) :-
      member((Ruleid, Order, Order1), Flow).

flow_of(Ruleid, Flow, Order, nil) :-
       not(member(Ruleid, Order, _), Flow).

map_vars(Head, Goal, Varmap) :-
        functor_vars(Head, Hv),
        functor_vars(Goal, Gv),
        lst_intersect(Hv, Gv, Common),
        map_vars_helper(Head, Goal, Common, Varmap).

map_vars_helper(Head, Goal, Common, Varmap) :-
          map_vars_helper(Head, Goal, Common, [], Varmap).

map_vars_helper(_, _, [], V, V).

map_vars_helper(Head, Goal, [H|T], V, Varmap) :-
             occurence(H, Head, Hi),
             occurence(H, Goal, Gi),
             id_functor(Headid, Head),
             id_functor(Goalid, Goal),
             append(V, [((Goalid, Gi), (Headid, Hi))], V1),
             map_vars_helper(Head, Goal, T, V1, Varmap).

map_flow(_, [], Flow, Flow).

map_flow(Head, [Goal | T], Flow, Flowout) :- 
          map_vars(Head, Goal, Varmap),
          map_flow_helper(Varmap, Flow, Flow1),
          map_flow(Head, T, Flow1, Flowout).

map_flow_helper([], Flow, Flow).

map_flow_helper([H|T], Flow, Flowout) :-
           H = ((Goalid, I),(Parent, J)),
           member((Parent, J, Index), Flow),
           append(Flow, [(Goalid, I, Index)], Flow1),
           map_flow_helper(T, Flow1, Flowout).

map_flow_helper([H|T], Flow, Flowout) :-
           H = ((_, _),(Parent, J)),
           not(member((Parent, J, _), Flow)),
           map_flow_helper(T, Flow, Flowout).

id_functor(Id, Functor) :-
               Functor =.. [Id|_].

add_dataflow(Rules, Flow, Rulesfinal) :-
         add_dataflow(Rules, Flow, [], Rulesfinal).


add_dataflow([], _, R, R).

add_dataflow([H|T], Flow, R, Rulesfinal) :-
         H = pred(X, notcallmain, A, B, C, D, E, F, G), 
         append(R, [pred(X,notcallmain, A, B, C, D, E, F, G,[])], R1),
         add_dataflow(T, Flow, R1, Rulesfinal).


value_at_index(List, Index, Value) :-
       value_at_index(List, 0, Index, Value).

value_at_index([H|_], I, Index, H) :-
          Index is I + 1.

value_at_index([_|T], I, Index, V) :- 
         Index > I + 1, 
         I1 is I + 1,
         value_at_index(T, I1, Index, V).
 

var_at_index(Functor, Index, Var) :-
            is_prim(Functor), !,
            Functor =.. [_|V], 
            V = [V1],
            V1 =.. [_|Args],
            var_at_index(Index, Args, Var).

var_at_index(Functor, Index, Var) :-
           Functor =.. [_|Args],
           value_at_index(Args, Index, Var).

vars_indices(Vars, Functor, Indices) :-
             vars_indices(Vars, [], Functor, Indices).

vars_indices(Vars, Vars, _, []).

vars_indices(Vars, V, Functor, [H|T]) :-
         var_at_index(Functor, H, Var),
         append(V, [(Var,Var1,H)], V1),
         rename(Var, Var1),
         vars_indices(Vars, V1, Functor, T).

flow_var_renamed(Head, Functor, Flow, Renamed) :-
              Functor =.. [Goalid|_],
              findall(Flowindex, member((Goalid, _, Flowindex), Flow), Flowindices),
              vars_indices(Renamed, Head, Flowindices).
        
flow_info(Head, Goals, Flow, Renamed) :-
         flow_info(Head, Goals, Flow, [], Renamed).

flow_info(_, [], _, R, R).

flow_info(Head, [H|T], Flow, R, Renamed) :-
          flow_var_renamed(Head, H, Flow, R1),
          lst_union(R, R1, R2),
          flow_info(Head, T, Flow, R2, Renamed).


add_dataflow([], _, R, R).

add_dataflow([H|T], Flow, R, Rulesfinal) :-
        H = pred(X, callmain, Id, Head, Body, A, B, C, D),
        body_of(Body, Body1), 
        flow_info(Head, Body1, Flow, Renamed),
        remove_duplicates(Renamed, Renamed1),
        append(R, [pred(X, callmain, Id, Head, Body, A, B, C, D, Renamed1)], R1),
        add_dataflow(T, Flow, R1, Rulesfinal).


body_of(and(Body), Body).
body_of(or(Body) , Body).


extract_domain_values(Domains, Domain, Rules, Doms) :-
       extract_domain_values(Domains, Domain, Rules, [], Doms).


extract_domain_values(_,_, [], D, D).

extract_domain_values(Domains, Domain, [H|T], D, Doms) :-
       H = pred(_,_,_,Head,and([]),[],[],[],[]),
       is_domain(Domains, Head), 
       Head =.. [Domain,Value],
       append(D, [Value], D1),
       extract_domain_values(Domains, Domain, T, D1, Doms).

extract_domain_values(Domains, Domain, [H|T], D, Doms) :-
       not(H =.. [Domain,_]),
       extract_domain_values(Domains, Domain, T, D, Doms).

domain_values(Domains, Rules, Values) :-
         domain_values(Domains, Domains, Rules, [], Values).

domain_values(_, [], _, V, V).

domain_values(Domains, [H|T], Rules, V, Values) :-  
          extract_domain_values(Domains, H, Rules, Vals),
          append(V, [(H,Vals)], V1),
          domain_values(Domains, T, Rules, V1, Values), !.

remove_facts(Domains, Rules, Rules1) :-
       remove_facts(Domains, Rules, [], Rules1).

remove_facts(Domains, [H|T], R, Rules) :-
          H = pred(_,_,_,_,and([]),[],[],[],[],[]),
          remove_facts(Domains, T, R, Rules).

remove_facts(_, [], R, R).

remove_facts(Domains, [H|T], R, Rules) :-
          append(R, [H], R1),
          remove_facts(Domains, T, R1, Rules).

input_values(Inputs, Rules, Values) :-
         input_values(Inputs, Rules, [], Values).

input_values(_, [], V, V).

input_values(Inputs, [H|T], V, Values) :-
         H = pred(abstraction,notcallmain,Id,Head,and([]),[],[],[],[]),
         member(Id, Inputs),
         append(V, [Head], V1),
         input_values(Inputs, T, V1, Values).

input_values(Inputs, [_|T], V, Values) :-
         input_values(Inputs, T, V, Values).

functor_name(S-[_], Name) :-
          S =.. [Name | _].
    
names(S, Names) :-
      names(S, [], Names).

names([], N, N).

names([H|T], N, Names) :-
     match_rule(H, Head, _),
     Head =..[Name|_],
     lst_union(N, [Name], N1),
     names(T, N1, Names).

rules_count(Name, Count, Rules) :- 
          rules_count(Name, Count, [], Rules).

rules_count(Name, 1, R, Rules) :-
       append(R, [Name], Rules).

rules_count(Name, Count, R, Rules) :-
         number_chars(Count, Chars),
         atom_chars(Name, Namechars),
         append(Prefix, ['_', Arity], Namechars),
         append(Prefix, Chars, Chars1),
         append(Chars1, ['_', Arity], Chars2),
         atom_chars(Rule, Chars2),
         append(R, [Rule], R1),
         Count1 is Count - 1,
         rules_count(Name, Count1, R1, Rules).


get_rules_by_ids(Ids, Rulesfmt, Rules) :-
       get_rules_by_ids(Ids, Rulesfmt, [], Rules).

get_rules_by_ids([], _, R, R).
get_rules_by_ids([H|T], Rulesfmt, R, Rules) :-
          get_rule_by_id(H, Rulesfmt, Rule),
          append(R, [Rule], R1),
          get_rules_by_ids(T, Rulesfmt, R1, Rules).


disjunctive_rules(Domains, Inputs, Rulesfmt, Names, Disjuncts) :-
       disjunctive_rules(Domains, Inputs, Names, Rulesfmt, [], Disjuncts).

disjunctive_rules(_, _, [],_,D, D).


rule_head_fmt((_,Head,_,_,_,_,_),Head).

:- dynamic has_disjunct/1.


disjunctive_rules(Domains, Inputs, [H|T], Rulesfmt, D, Disjuncts) :-
          rule_ident(H, Count),
          get_rule_by_id(H,Rulesfmt,(H,Head,_,_,_,_,_)),
          Count > 1,
          not(member(H, Inputs)),
          not(member(H, Domains)),
          rules_count(H, Count, Rulenames),
          get_rules_by_ids(Rulenames, Rulesfmt, Rules),
          maplist(rule_head_fmt, Rules, Ruleheads),
          Head =.. [Name|Args],
          atom_chars(Name, Namechars),
          append(Prefix, ['_',Arity],Namechars),
          append(Prefix,[d,i,s,j,u,n,c,t],Prefix1),
          append(Prefix1,['_',Arity],Idchars),
          atom_chars(Id, Idchars),
          Head1 =.. [Id|Args],
          neg_name(H, Hneg),
          neg_name(Id,Idneg),
          (not(has_disjunct(H)) -> assert(has_disjunct(H)), assert(disjunct(H,Id)), assert(disjunct(Hneg,Idneg)),
                                   assert(is_disjunct(Id)), assert(is_disjunct(Idneg))
                                    ; true), 
          Rule = (Id, Head1, or(Ruleheads),[],[],[],[]),
          append(D, [Rule], D1),
          disjunctive_rules(Domains, Inputs, T, Rulesfmt, D1, Disjuncts).

disjunctive_rules(Domains, Inputs, [H|T], Rulesfmt, D, Disjuncts) :-
          rule_ident(H, Count),
          get_rule_by_id(H,Rulesfmt,(H,_,_,_,_,_,_)),
          not(member(H, Inputs)),
          not(member(H, Domains)),
          Count = 1,
          disjunctive_rules(Domains, Inputs, T, Rulesfmt, D, Disjuncts).

disjunctive_rules(Domains, Inputs, [H|T], Rulesfmt, D, Disjuncts) :-
          annotations(A),
          reduce(or, [member(H, Inputs), member(H, Domains), member(H, A)], true),
          disjunctive_rules(Domains, Inputs, T, Rulesfmt, D, Disjuncts).

:- dynamic typeof/2.
:- dynamic disjunct/2.
:- dynamic is_disjunct/1.

infer_types(Rulesfinal, Types) :-
          infer_types(Rulesfinal, [], Types).


remove_head([_|T], T).

has_arithop(_+_).
has_arithop(_-_).
has_arithop(_<_).
has_arithop(_>_).
has_arithop(_>=_).
has_arithop(_=<_).
       
has_arithop([H|_]) :-
         has_arithop(H).

has_arithop([_|T]) :-
         has_arithop(T).

subexprs(X, [X]) :-  and(X\=(_=_), X\=(_\=_), true).

subexprs(X=Y, E) :- 
      subexprs(X, E1),
      subexprs(Y, E2),
      append(E1, E2, E).
subexprs(X\=Y, E) :- 
      subexprs(X, E1),
      subexprs(Y, E2),
      append(E1, E2, E).

is_arithmetic(Expr) :-
          has_arithop(Expr).

is_arithmetic(Expr) :-
        subexprs(Expr, Exprs),
        has_arithop(Exprs).        
           
arithmetic_vars(Goals, Avars2) :-
        filter(is_prim, Goals, Primitives),
        maplist(=.., Primitives, Primitives1),
        maplist(remove_head, Primitives1, Exprs),
        flatten(Exprs, Exprs1),
        filter(is_arithmetic, Exprs1, Aexprs),
        maplist(functor_vars, Aexprs, Avars),
        flatten(Avars, Avars1), 
        remove_duplicates(Avars1, Avars2).

infer_types(Rules, Types) :-
       infer_types(Rules, [], Types).

infer_types([], Ty, Ty).

assign_types(_, [], Ty, Ty).

assign_types(Flow, [H|T], Ty, Ty2) :-
        member((H,_,I),Flow),
        not(typeof(I,_)),
        assert(typeof(I,typenum)),
        append(Ty, [(I,typenum)], Ty1),
        assign_types(Flow, T, Ty1, Ty2).

assign_types(Flow, [H|T], Ty, Ty1) :-
        or(not(member((H,_,_),Flow)),(member((H,_,I),Flow),typeof(I,_)),true),
        assign_types(Flow, T, Ty, Ty1).


infer_types([H|T], Ty, Types) :-
          H = pred(_, _, _, _, Goals, _, _, _, _, Flow),
          or(Goals = and(Body), Goals = or(Body), true),
          arithmetic_vars(Body,Vars),
          assign_types(Flow, Vars, Ty, Ty1),
          infer_types(T, Ty1, Types).

gen_intermediate_prog(Source, Rulesfmt, Domains, Main, Inputs_n, Graph, Graph1, Flow1, Rulesfinal3, Values, Inputvalues) :-   
       io:load_source_files([Source], [], S, 0, _), 
       domains(S, Domains),
       inputs(S, Inputs),
       names(S, Names),
       main_pred(S, Main),
       main_pred_arity(Main, S, Arity),
       functor_arities(Domains, S, Domains_n),
       functor_arities(Inputs, S, Inputs_n),
       atom_string(Main, Mainstr),
       atom_string(Arity, Aritystr),
       string_concat(Mainstr, "_", Mainstr1),
       string_concat(Mainstr1, Aritystr, Idstr),
       atom_string(Mainid, Idstr),
       remove_annotations(S, [], S1),
       %maplist(dual_dom, Domains_n, Dualdomains),
       cross((Domains_n,Inputs_n), S1, S2),
       maplist(format_rule, S2, R),
       disjunctive_rules(Domains_n, Inputs_n, R, Names, Disjuncts),
       append(R, Disjuncts, R1),
       cross(Domains_n, R1, R2),
       maplist(gen_dual, R2, Duals), 
       lst_union(R1, Duals, Rulesfmt),
       construct_call_graph(Rulesfmt, Domains_n, Graph),
       affix_tuple(Mainid, Domains, Graph, Rulesfmt, [], Rulesfmt1), 
       maplist(add_class_tuples, Rulesfmt1, Rules), !, 
       delete_vertex(Mainid, Graph, Graph1),
       neg_name(Main, _),
       %delete_vertex(Negmain, Graph1, Graph2),
       (invalid(Graph1) -> write('One abstraction calls another abstraction. Invalid program\n'), abort ; true), !,
       calculate_flow(Mainid, Rulesfmt, Graph, Graph1, Flow), !,
       remove_duplicates(Flow, Flow1),
       add_dataflow(Rules, Flow, Rulesfinal),
       %write(Rulesfinal),
       domain_values(Domains_n, Rules, Values),
       input_values(Inputs_n, Rules, Inputvalues),
       remove_facts(Domains_n, Rulesfinal, Rulesfinal1),
       remove_facts(Inputs_n, Rulesfinal1, Rulesfinal2),
       infer_types(Rulesfinal2,_),
       maplist(rewrite_disjunct, Rulesfinal2, Rulesfinal3).

    
cleanup :- retractall(main_pred(_)), retractall(domain(_)), retractall(id(_)), retractall(rule_ident(_)).


connective_of(and(_), and).
connective_of(or(_), or).

substitute_disjuncts(Body, Bodyout) :-
          substitute_disjuncts(Body, [], Bodyout).

substitute_disjuncts([], B, B).

substitute_disjuncts([H|T], B, Bout) :-
      H =.. [Id|Args],
      (disjunct(Id, Disjunct) -> H1 =.. [Disjunct|Args] ; H1 = H),
      append(B, [H1], B1),
      substitute_disjuncts(T, B1, Bout).

rewrite_disjunct(Rule, Rule) :-
    Rule = pred(_,_,Id,_,_,_,_,_,_,_),
    is_disjunct(Id).

rewrite_disjunct(Rule, Ruleout) :-
    Rule = pred(A,B,Id,Head,Goals,C,D,E,F,G),
    not(is_disjunct(Id)),
    body_of(Goals, Body), 
    connective_of(Goals, Connective),
    substitute_disjuncts(Body, Body1),
    Functor =.. [Connective,Body1],
    Ruleout = pred(A, B, Id, Head, Functor,C, D, E, F, G).



:- module(utils,[
          replace_vars/3,
          add_backtracking/5,
          add_foralls/5,
          format/1,
          preamble/3,
          ctx_term/2,
          getarg_stmts/3

	]).

:- use_module(parser).
:- discontiguous utils:format/1.
:- discontiguous utils:translate_body/6.
:- use_module(main).

format([newline|T]) :- write('\n'), !,format(T).
format([tab(X)|T]) :- format(tab, X), !, format(T).
format(tab, 0).
format(tab, X) :- X > 0, write('\t'), X1 is X - 1, format(tab, X1).
format([tab|T]) :- write('\t'), !, format(T).
format([space|T]) :- write(' '), !, format(T).
format([X|T]) :-  write(X), format(T).
format([]).
 
ctx_string(0, "ctx"). 
ctx_string(Num, String) :- atom_string(Num,S), string_concat("ctx",S, String). 
ctx_term(Num, Term) :- ctx_string(Num, String), atom_string(Term, String).

preamble(Head,L1,Lout) :- 
       Head =.. [Name|Args], append(L1, [newline, tab, if, space, computation, "('", Name, "',", Args, ")", space, in, space, ctx, :, newline, tab(2), "return {'success': True, 'context'	: ctx}",
	                                newline, tab, ctx, "[computation('",Name, "',", Args, ")] = True"],L2),
       (optimize(true) -> append(L2, [newline, tab, "if str(ctx) in nogood:", newline, tab(2), "return {'success': False, 'context': ctx}"], Lout) ; Lout = L2).
 
add_backtracking([],Indent,Indent,L,L). 
add_backtracking([H|T], Indent, Indent2, L ,L2) :- H =.. [Name,Dom], Indent1 is Indent + 1, append(L, [newline, tab(Indent),for,space, Name,space, in,space, Dom, :], L1), 
                                                           add_backtracking(T, Indent1, Indent2, L1, L2). 
add_foralls([],Indent,Indent,L,L).
add_foralls([H|T], Indent, Indent2, L ,L2) :- H =.. [Name,Dom], Indent1 is Indent + 1, append(L, [newline, tab(Indent),for,space, Name,space, in,space, Dom, :], L1),
                                                  add_foralls(T, Indent1, Indent2, L1, L2).       

add_dataflow(_,L,L).

split_functor(X, Name, Args) :- X =.. [Name, Args]. 


getarg_stmts([],_,L,L).

getarg_stmts([H|T],Indent,L1,L3) :-  
          H = (_,NewVar,Pos), 
          (typeof(Pos,typenum) -> append(L1,[newline,tab(Indent),NewVar, " = int(getarg(term, ", Pos, "))"],L2) ; 
                            append(L1,[newline,tab(Indent),NewVar, " = getarg(term, ", Pos, ")"],L2)),
          getarg_stmts(T,Indent,L2,L3).

getarg_stmts(Flow,Indent,L) :- 
            getarg_stmts(Flow,Indent,[],L).

replace(Lin,Dataflow,Lout) :-  replace(Lin,Dataflow,[],Lout). 
replace([],_,Lin,Lin).
replace([H|T],Dataflow,Lin,Lout) :- member((H,H1,_),Dataflow), append(Lin,[H1],L2), replace(T,Dataflow,L2,Lout).
replace([H|T],Dataflow,Lin,Lout) :- not(member((H,_,_),Dataflow)), append(Lin,[H],L2), replace(T,Dataflow,L2,Lout).
replace_vars(Goals,Dataflow,L) :- replace_vars(Goals,Dataflow,[],L).
replace_vars([],_,Lin,Lin).
replace_vars([H|T],Dataflow,Lin, Lout) :- 
            H = Call, 
            Call =.. [Name|Args],
            parser:not(is_prim(Name)),
            replace(Args,Dataflow,Args1), Call1 =.. [Name|Args1], append(Lin,[Call1],L1),
            replace_vars(T,Dataflow,L1, Lout).

replace_vars([H|T],Dataflow,Lin, Lout) :- 
            H = Call, 
            Call =.. [Name|[Expr]],
            parser:is_prim(Name),
            Expr =.. [Op|Args],
            replace(Args,Dataflow,Args1), Call1 =.. [Op|Args1],
             Call2 =.. [Name|[Call1]],
             append(Lin,[Call2],L1),
            replace_vars(T,Dataflow,L1, Lout).



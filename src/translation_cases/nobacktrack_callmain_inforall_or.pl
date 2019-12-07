


translate_body_nobacktrack(callmain, or, inforall, Head, Body, Forall, Headargs, Body1, CtxNum, Indent, Indent1, L, Lout) :-
                 translate_body_nobacktrack_helper(callmain, or, inforall, Head, Body, Forall, Headargs, Body1, CtxNum, Indent, Indent1, L, L1),
                 translate_body_nobacktrack_final(callmain, or, inforall, [],_,Indent,Indent1,L1, Lout).

translate_body_nobacktrack_helper(callmain, or, inforall,_,_,_, _, [], _,_,_,L, L).

translate_body_nobacktrack_helper(callmain, or, inforall, Head, Body, Forall, Headargs, [H|T],CtxNum,Indent,Indent1,L,Lout) :- 
                    ctx_term(CtxNum,_),
                    H = Call, CtxNum1 is CtxNum + 1, ctx_term(CtxNum, _), ctx_term(CtxNum1, CtxNew),
                    %append(L, [newline, tab(Indent1), CtxNew, space, =, space, Call1], L1),
                    gen_call(Call, ctx, CtxNew, Indent1, L, L1),
                    Indent2 is Indent1 + 1, 
                    append(L1, [newline, tab(Indent1), if, space, CtxNew,"['success']",:, newline, tab(Indent2), ctx, space, =, space, CtxNew, "['context']"], L2),
                    append(L2, [newline, tab(Indent2), size, space, =, space, sizeof(ctx)], L3),
                    append(L3, [newline, tab(Indent1), else, :], L4),
                    (optimize(true), !, callsdual(H), ! -> 
                                 vars_replacedvars(Headargs, Headargs1),
                                 args_string(Headargs, Headargsstring),
                                 args_string(Headargs1, Headargsstring1),
                                 H =.. [_|Dualargs],
                                 args_string(Dualargs, Dualsargsstring),
                                 Head =.. [Name |_], 
                                 neg_name(Name, Property),
                                 append(L4, [newline, tab(Indent2), "inconsistent[atom(", Headargsstring1, "), atom(", Dualsargsstring, "),\"", Property, "\"] = True"], L5),
                                 append(L5, [newline, tab(Indent2), "inconsistent[atom(", Dualsargsstring, "), atom(", Headargsstring1, "),\"", Property, "\"] = True"], L6)
                                 ; 
                                 L6 = L4
                    ),
                    (T \= [] -> translate_body_nobacktrack_helper(callmain, or, inforall, Head, Body, Forall, Headargs, T, CtxNum1,Indent,Indent2,L6,Lout) ;  
                                optimize(true) -> 
                                 dual_call_functors(Body, Functors),
                                 maplist(functor_args, Functors, Functorsargs),
                                 maplist(args_string, Functorsargs, Argsstrings),
                                 gen_inconsistent_tuples(Head, Headargsstring, Argsstrings, Forall, Indent2, L7),
                                 append(L6, L7, L8),
                                 append(L8,[newline, tab(Indent2), "nogood[str(ctx)] = True"],L9),
                                 vars_replacedvars(Headargs, Headargs1),
                                 args_string(Headargs, Headargsstring),
                                 args_string(Headargs1, Headargsstring1),
                                 append(L9, [newline, tab(Indent2), "inconsistent[atom(", Headargsstring, "), atom(", Headargsstring1, "), str(ctx)] = True"], L10),
                                 append(L10, [newline, tab(Indent2), "inconsistent[atom(", Headargsstring1, "), atom(", Headargsstring, "), str(ctx)] = True"], L11),
                                 append(L11,[newline, tab(Indent2), "return {'success': False, 'context' : ", CtxNew, "}"],Lout)
                                 ; append(L6,[newline, tab(Indent2), "return {'success': False, 'context' : ", CtxNew, "}"],Lout)). 
                    

translate_body_nobacktrack_final(callmain , or, inforall, [],_,Indent,_, L, Lout) :- 
           Indent2 is Indent + 1, 
           append(L, [newline, tab(Indent2), "count = count + 1"], Lout).


translate_nobacktrack_final(callmain, or, inforall, _, _, _, L, Lout) :-
                      append(L, [newline, tab, "return {'success': True, 'context' : ctx}"], Lout).


dual_call_functors(Body, Functors) :-
            main_pred_id(Main),
            neg_name(Main, Dual),
            dual_call_functors(Dual,Body, [], Functors).

dual_call_functors(_, [], F, F).

dual_call_functors(Dual, [H|T], F, Functors) :-
              (H =.. [Dual|_] -> append(F, [H], F1) ; F1 = F), 
              dual_call_functors(Dual, T, F1, Functors).

callsdual(Functor) :-
          main_pred_id(Main),
          neg_name(Main, Dual),
          Functor =.. [Dual|_].

translate(Rule, callmain, or, inforall, Lout) :- 
              Rule =  pred(abstraction, callmain, _, Head, or(Body), _, _, Domains, Forall, Dataflow), Head =.. [Name| Args], append(Args,[ctx], Args1), Headcall =.. [Name|Args1], L1 = [def, space, Headcall, :],
               Domains = [],
               Indent = 1,
               add_backtracking(Domains,Indent,Indent1,L1,L2),
               add_foralls(Forall,Indent1,Indent2,L2,L3),
               Indent3 is Indent2 + 1, 
               Indent4 is Indent3 + 1, 
               Indent5 is Indent4 + 1, 
               getarg_stmts(Dataflow,Indent3,DL),
               append(L3,[newline, tab(Indent2), "count = 0", newline, tab(Indent2), "size = sizeof(ctx)", newline, tab(Indent2), "covered = {}",  newline, tab(Indent2),
                                "while count < size:", newline, tab(Indent3), "for term in ctx:", newline, tab(Indent4), "if not term in covered:", newline, tab(Indent5), 
                                   "covered[term] = True", newline, tab(Indent5), break], L4), 
               append(L4, DL, L5),
               replace_vars(Body,Dataflow,Body1), 
               translate_body_nobacktrack(callmain, or, inforall, Head, Body, Forall, Args, Body1, 0, Indent2, Indent3, L5, L6), 
               translate_nobacktrack_final(callmain, or, inforall, 1, _,Indent3, L6, Lout).


concat_str((Str, Instr), Outstr) :-
        string_concat(Instr, Str, Outstr).

string_term(X, Y) :-
        term_string(Y, X).

vars_replacedvars(Vars, Varsout) :-
  maplist(term_string, Vars, Varss),
  cross("_1", Varss, Varss1),
  maplist(concat_str, Varss1, Varss2),
  maplist(string_term, Varss2, Varsout).
     

functor_args(Functor, Args) :-
      Functor =.. [_|Args].


gen_inconsistent_tuples(Head, Headargsstring, Argsstrings, Forall, Indent, Lout) :-
      gen_inconsistent_tuples(Head, Headargsstring, Argsstrings, Forall, Indent, [], Lout).


gen_inconsistent_tuples(Head, Headargsstring, Argsstrings, [], Indent, L, Lout) :-
          Head =.. [Name |_], 
          neg_name(Name, Property),
          Indent1 is Indent + 1,
          gen_if_checks(Indent, Headargsstring, Argsstrings, L, L1),
          gen_inconsistent_tuples_helper(Property, Headargsstring, Argsstrings, Indent1, L1, Lout).

gen_inconsistent_tuples_helper(_, _, [], _,  L, L).

gen_inconsistent_tuples_helper(Property, Headargsstring, [H|T], Indent, L, Lout) :-
          append(L, [newline, tab(Indent), "inconsistent[atom(", Headargsstring, "),atom(", H, "),\"", Property, "\"] = True"], L1),
          append(L1, [newline, tab(Indent), "inconsistent[atom(", H, "),atom(", Headargsstring, "),\"", Property, "\"] = True"], L2),
          gen_inconsistent_tuples_helper(Property, Headargsstring, T, Indent, L2, Lout).

gen_inconsistent_tuples(Head, Headargsstring, Argsstrings, [H|T], Indent, L, Lout) :-
          H =.. [Var, Domain], 
          append(L, [newline, tab(Indent), for, space, Var, space,  in, space, Domain, :], L1),
          Indent1 is Indent + 1,
          gen_inconsistent_tuples(Head, Headargsstring, Argsstrings, T, Indent1, L1, Lout).



gen_if_checks(_, _, [], L, L).


gen_if_checks(Indent, Headargsstring, [H|T], L, Lout) :-
           append(L, [newline, tab(Indent), if, space, "atom(", Headargsstring, ") != atom(", H, "):"], L1),
           (T = [] -> Lout = L1 ; append(L1, [space, and, space], L2), gen_if_checks(Indent, Headargsstring, T, L2, Lout)).

      
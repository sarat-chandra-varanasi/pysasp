

translate_body_backtrack(notcallmain, and, notinforall, Headcall, [H|T],CtxNum,Indent,Indent1,L,Lout) :- 
                   ctx_term(CtxNum,_),
                   H = Call, CtxNum1 is CtxNum + 1, ctx_term(CtxNum, _), ctx_term(CtxNum1, CtxNew),
                   (optimize(true),!, dual_calls(Headcall),!, main_pred_call(Call)  -> 
                       Headcall =.. [Name|_],
                       neg_name(Name, Property),
                       gen_call_opt(Property, Call, ctx_copy, CtxNew, Indent1, L, L1) ; 
                       gen_call(Call, ctx_copy, CtxNew, Indent1, L, L1)),
                   Indent2 is Indent1 + 1, 
                   append(L1, [newline, tab(Indent1), if, space, CtxNew,"['success']",:, newline, tab(Indent2), ctx_copy, space, =, space, CtxNew, "['context']"], L2),
                   (T \= [] -> translate_body_backtrack(notcallmain, and, notinforall, Headcall, T, CtxNum1,Indent, Indent2, L2 ,L3) ; append(L2,[newline, tab(Indent2),"return {'success': True, 'context' : ctx_copy}"],L3)),
                   append(L3, [newline, tab(Indent1), else, :], L4),
                   (optimize(true),!, dual_calls(Headcall),!, main_pred_call(Call)  -> 
                         Indent3 is Indent2 + 1,
                          append(L4, [newline, tab(Indent2), "if 'trivial' not in ", CtxNew, :,
                                     newline, tab(Indent3), "nogood[str(", CtxNew, "['context'])] = True"], L5)                       
                        ; L5 = L4
                    ),
                   append(L5, [newline, tab(Indent2), "ctx_copy = copy(ctx)", newline, tab(Indent2), continue],Lout).

translate_final(notcallmain, and, notinforall, Indent, L, Lout) :-
                      append(L, [newline, tab(Indent), "return {'success' : False, 'context' : ctx}"], Lout).


translate(Rule, notcallmain, and, notinforall, Lout) :- 
                Rule = pred(abstraction, notcallmain, _, Head, and(Body), _, _, Domains, _, _), Head =.. [Name| Args], append(Args,[ctx], Args1), Headcall =.. [Name|Args1], L1 = [def, space, Headcall, :],
                Domains = [_|_],
				        Indent = 1,
                append(L1,[newline, tab(Indent),ctx_copy,space,=,copy(ctx)],L2),
				        add_backtracking(Domains,Indent,Indent1,L2,L3),
                translate_body_backtrack(notcallmain, and, notinforall, Head,Body,0,Indent,Indent1,L3,L4),
                translate_final(notcallmain, and, notinforall, 1,L4, Lout). 

calltype1(main).
calltype1(abstraction).

dual_calls(Call) :-
   main_pred_id(Main),
   neg_name(Main, Dual),
   callgraph(G),
   Call =.. [Name|_],
   member(edge(Dual,Name),G).


main_pred_call(Call) :-
    main_pred_id(Main),
    id_arity(Main, Arity),
    Call =.. [Main|Args],
    length(Args,Arity).



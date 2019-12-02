


translate_body_nobacktrack(notcallmain, or, inforall, Body, CtxNum, Indent, Indent1, L, Lout) :-
                 translate_body_nobacktrack_helper(notcallmain, or, inforall, Body, CtxNum, Indent, Indent1, L, Lout).
                 
translate_body_nobacktrack_helper(notcallmain, or, inforall, [], _,_,_,L, L).

translate_body_nobacktrack_helper(notcallmain, or, inforall, [H|T],CtxNum,Indent,Indent1,L,Lout) :- 
                    ctx_term(CtxNum,_),
                    H = Call, CtxNum1 is CtxNum + 1, ctx_term(CtxNum, _), ctx_term(CtxNum1, CtxNew),
                    %Call =.. [Name|Args], append(Args, [ctx], Args1), Call1 =.. [Name|Args1], 
                    %append(L, [newline, tab(Indent1), CtxNew, space, =, space, Call1], L1),
                    gen_call(Call, ctx, CtxNew, Indent1, L, L1),
                    Indent2 is Indent1 + 1, 
                    append(L1, [newline, tab(Indent1), if, space, CtxNew,"['success']",:, newline, tab(Indent2), ctx, space, =, space, CtxNew, "['context']"], L2),
                    append(L2, [newline, tab(Indent1), else, :], L3),
                    (T \= [] -> translate_body_nobacktrack_helper(notcallmain, or, inforall,T,CtxNum1,Indent,Indent2,L3,Lout) ; 
                            optimize(true) -> append(L3,[newline, tab(Indent2), "nogood[str(ctx)] = True", newline, tab(Indent2), "return {'success': False, 'context' : ctx}"],Lout) ;
                             append(L3,[newline, tab(Indent2), "return {'success': False, 'context' : ctx}"],Lout)). 
                    

translate_nobacktrack_final(notcallmain, or, inforall, _, _, _, L, Lout) :-
                      append(L, [newline, tab, "return {'success': True, 'context' : ctx}"], Lout).


translate(Rule, notcallmain, or, inforall, Lout) :- 
              Rule =  pred(abstraction, notcallmain, _, Head, or(Body), _, _, Domains, Forall, Dataflow), Head =.. [Name| Args], append(Args,[ctx], Args1), Headcall =.. [Name|Args1], L1 = [def, space, Headcall, :],
               Domains = [],
               Forall \= [],
               Indent = 1,
               add_backtracking(Domains,Indent,Indent1,L1,L2),
               add_foralls(Forall,Indent1,Indent2,L2,L3),
               replace_vars(Body,Dataflow,Body1), 
               translate_body_nobacktrack(notcallmain, or, inforall, Body1,0,Indent1,Indent2,L3,L4), 
               translate_nobacktrack_final(notcallmain, or, inforall, 1, _,Indent2, L4, Lout).



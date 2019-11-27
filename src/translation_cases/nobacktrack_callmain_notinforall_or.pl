

translate_body_nobacktrack(callmain, or, notinforall, Body, CtxNum, Indent, Indent1, L, Lout) :-
                 translate_body_nobacktrack_helper(callmain, or, notinforall, Body, CtxNum, Indent, Indent1, L, L1),
                 translate_body_nobacktrack_final(callmain, or, notinforall, [],_,Indent,Indent1,L1, Lout).

translate_body_nobacktrack_helper(callmain, or, notinforall, [], _,_,_,L, L).

translate_body_nobacktrack_helper(callmain, or, notinforall, [H|T],CtxNum,Indent,Indent1,L,Lout) :- 
                    ctx_term(CtxNum,_),
                    H = Call, CtxNum1 is CtxNum + 1, ctx_term(CtxNum, _), ctx_term(CtxNum1, CtxNew),
                    Call =.. [Name|Args], append(Args, [ctx], Args1), Call1 =.. [Name|Args1], 
                    gen_call(Call, ctx, CtxNew, Indent1, L, L1),
                    append(L, [newline, tab(Indent1), CtxNew, space, =, space, Call1], L1),
                    Indent2 is Indent1 + 1, 
                    append(L1, [newline, tab(Indent1), if, space, CtxNew,"['success']",:, newline, tab(Indent2), ctx, space, =, space, CtxNew, "['context']"], L2),
                    append(L2, [newline, tab(Indent2), size, space, =, space, sizeof(ctx)], L3),
                    append(L3, [newline, tab(Indent1), else, :], L4),
                    (T \= [] -> translate_body_nobacktrack_helper(callmain, or, notinforall,T,CtxNum1,Indent,Indent2,L4,Lout) ;  append(L4,[newline, tab(Indent2), "return {'success': False, 'context' : ctx}"],Lout)). 
                    

translate_body_nobacktrack_final(callmain, or, notinforall, [],_,Indent, _, L, Lout) :- 
           Indent1 is Indent + 1, 
           append(L, [newline, tab(Indent1), "count = count + 1"], Lout).


translate_nobacktrack_final(callmain, or, notinforall, Indent, L, Lout) :-
                      append(L,[newline, tab(Indent), "return {'success': True, 'context' : ctx}"], Lout).


translate(Rule, callmain, or, notinforall, Lout) :- 
             Rule =  pred(abstraction, callmain, _, Head, or(Body), _, _, Domains, Forall, Dataflow), Head =.. [Name| Args], append(Args,[ctx], Args1), Headcall =.. [Name|Args1], L1 = [def, space, Headcall, :],
               Domains = [],
               Forall = [],
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
               append(L4,DL,L5),
               replace_vars(Body,Dataflow,Body1), 
               translate_body_nobacktrack(callmain, or, notinforall, Body1,0,Indent1,Indent3,L5,L6), 
               translate_nobacktrack_final(callmain, or, notinforall, 1, L6, Lout).




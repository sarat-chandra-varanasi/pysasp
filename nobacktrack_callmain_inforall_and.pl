

translate(Rule, callmain, and, inforall, Lout) :- 
                    Rule = pred(abstraction, callmain, _, Head, and(Body), _, _, Domains, Forall, Dataflow), Head =.. [Name| Args], append(Args,[ctx], Args1), Headcall =.. [Name|Args1], L1 = [def, space, Headcall, :],
					Domains = [],
					add_foralls(Forall,1,Indent1,L1,L2),
                    add_dataflow(Dataflow, L2, L3),
                    Indent2 is Indent1 + 1, 
                    Indent3 is Indent2 + 1, 
                    Indent4 is Indent3 + 1, 
                    getarg_stmts(Dataflow,Indent2,DL),
                    append(L3,[newline, tab(Indent1), "count = 0", newline, tab(Indent1), "size = sizeof(ctx)", newline, tab(Indent1), "covered = {}",  newline, tab(Indent1),
                        	    "while count < size:", newline, tab(Indent2), "for term in ctx:", newline, tab(Indent3), "if not term in covered:", newline, tab(Indent4), 
                         	     "covered[term] = True", newline, tab(Indent4), break], L4), 
                    append(L4, DL, L5),
                    replace_vars(Body,Dataflow,Body1), 
                    translate_body_nobacktrack(callmain, and, inforall, Body1,0,Indent2,L5,L6), 
                    translate_body_nobacktrack_final(callmain, and, inforall, Indent2, L6, Lout).

translate_body_nobacktrack_final(callmain, and, inforall, _, L, Lout) :-
                   append(L, [newline, tab, "return {'success' : True, 'context' : ctx}"], Lout).
 
translate_body_nobacktrack(callmain, and, inforall, [],_,_,L,L).
                   
translate_body_nobacktrack(callmain, and, inforall, [H|T],CtxNum,Indent,L,Lout) :- H = Call, CtxNum1 is CtxNum + 1, ctx_term(CtxNum, _), ctx_term(CtxNum1, CtxNew),
                     gen_call(Call, ctx, CtxNew, Indent, L, L1),
                     Indent1 is Indent + 1,
                     append(L1, [newline, tab(Indent), if, space, CtxNew,"['success']",:, newline, tab(Indent1), ctx, space, =, space, CtxNew, "['context']",
                                 newline, tab(Indent1), "size = sizeof(ctx)"], L2),
                     translate_body_nobacktrack(callmain, and, inforall, T,CtxNum1,Indent1,L2,L3),
                     (optimize(true) -> 
                        append(L3, [newline, tab(Indent), else, :, newline, tab(Indent1), "nogood[str(ctx)] = True", newline, tab(Indent1), "return {'success' : False, 'context' : ctx['context']}"],L4)
                      ; append(L3, [newline, tab(Indent), else, :, newline, tab(Indent1), "return {'success' : False, 'context' : ctx['context']}"],L4)),
                     append(L4, [newline, tab(Indent), "count = count + 1"], Lout).


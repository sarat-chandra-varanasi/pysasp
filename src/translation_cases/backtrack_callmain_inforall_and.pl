

translate_body_backtrack_final(callmain, and, inforall, [],Indent, Nesting, L, Lout) :- 
           Indent1 is Indent + Nesting + 1, 
           Indent2 is Indent + Nesting,
           append(L, [newline, tab(Indent1), "count = count + 1"], L1),
           append(L1, [newline, tab(Indent2), "if b_fail_callmain == False:", newline, tab(Indent1), "return {'success' : True, 'context' : ctx_copy}"], L2),
           append(L2, [newline, tab(Indent2), "else:", newline, tab(Indent1), "ctx_copy = copy(ctx)", newline, tab(Indent1), break],L3),
           add_breakout(Indent2,Nesting,L3,Lout).


add_breakout(_,1,L,L).
add_breakout(IndentNest,Nesting,L,Lout) :-
                 IndentNest1 is IndentNest - 1, 
                 append(L, [newline, tab(IndentNest1), "if b_fail_callmain:", newline, tab(IndentNest), break],L1),
                 Nesting1 is Nesting - 1,
                 add_breakout(IndentNest1, Nesting1,L1,Lout).

translate_body_backtrack_helper(callmain, and, inforall, [H|T],CtxNum,Indent,Indent1,L,Lout) :- 
           ctx_term(CtxNum,_),
           L1 = L,
           H = Call, CtxNum1 is CtxNum + 1, ctx_term(CtxNum, _), ctx_term(CtxNum1, CtxNew),
           %Call =.. [Name|Args], append(Args, [ctx_copy], Args1), Call1 =.. [Name|Args1], 
           %append(L1, [newline, tab(Indent1), CtxNew, space, =, space, Call1], L2),
           gen_call(Call, ctx_copy, CtxNew, Indent1, L1, L2),
           Indent2 is Indent1 + 1, 
           append(L2, [newline, tab(Indent1), if, space, CtxNew,"['success']",:,  
                       newline, tab(Indent2), ctx_copy, space, =, space, CtxNew, "['context']"], L3),
           append(L3, [newline, tab(Indent2), size, space, =, space, sizeof(ctx_copy)], L4),
           (T \= [] -> translate_body_backtrack_helper(callmain, and, inforall, T, CtxNum1,Indent, Indent2, L4 ,L5) ; append(L3,[newline, tab(Indent2), "size = sizeof(ctx_copy)"],L5)),
           append(L5, [newline, tab(Indent1), else, :, newline, tab(Indent2), "b_fail_callmain = True", newline, tab(Indent2), break],Lout).

translate_final(callmain, and, inforall, Indent, L, Lout) :-
                          append(L, [newline, tab(Indent), "return {'success' : False, 'context': ctx}"],Lout).

translate_body_backtrack(callmain, and, inforall, [H|T],CtxNum,Indent,Indent1,Nesting,L,Lout) :- 
                                     translate_body_backtrack_helper(callmain, and, inforall, [H|T],CtxNum,Indent,Indent1,L,L1),
                                    translate_body_backtrack_final(callmain, and, inforall, [],Indent,Nesting,L1,Lout). 

translate(Rule, callmain, and, inforall, Lout) :- 
               Rule = pred(abstraction, callmain, _, Head, and(Body), _, _, Domains, Forall, Dataflow), Head =.. [Name| Args], append(Args,[ctx], Args1), Headcall =.. [Name|Args1], L1 = [def, space, Headcall, :],
               Domains = [_|_],
               (Forall = [_|_] -> ForallState = inforall ; ForallState = not_inforall),
               Indent = 1,
               append(L1,[newline, tab(Indent),ctx_copy,space,=,copy(ctx)],L2),
               add_backtracking(Domains,Indent,Indent1,L2,L3),
               add_foralls(Forall,Indent1,Indent2,L3,L4),
               length(Forall, Nesting),
               add_dataflow(Dataflow, L5, L6),
               Indent3 is Indent2 + 1, 
               Indent4 is Indent3 + 1, 
               Indent5 is Indent4 + 1, 
               getarg_stmts(Dataflow,Indent3,DL),
               append(L4,[newline, tab(Indent2), "b_fail_callmain = False", newline, tab(Indent2), "count = 0", newline, tab(Indent2), "size = sizeof(ctx_copy)", newline, tab(Indent2), "covered = {}",  newline, tab(Indent2),
                                "while count < size:", newline, tab(Indent3), "for term in ctx_copy:", newline, tab(Indent4), "if not term in covered:", newline, tab(Indent5), 
                                   "covered[term] = True", newline, tab(Indent5), break], L5), 
               append(L6, DL, L7),
               replace_vars(Body,Dataflow,Body1), 
               translate_body_backtrack(callmain, and, ForallState, Body1,0,Indent1,Indent3,Nesting,L7,L8), 
               translate_final(callmain, and, inforall, 1, L8, Lout).


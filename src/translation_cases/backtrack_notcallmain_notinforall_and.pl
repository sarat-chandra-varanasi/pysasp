

translate_body_backtrack(notcallmain, and, notinforall, [H|T],CtxNum,Indent,Indent1,L,Lout) :- 
                            ctx_term(CtxNum,_),
                            H = Call, CtxNum1 is CtxNum + 1, ctx_term(CtxNum, _), ctx_term(CtxNum1, CtxNew),
                            %Call =.. [Name|Args], append(Args, [ctx_copy], Args1), Call1 =.. [Name|Args1], 
                            gen_call(Call, ctx_copy, CtxNew, Indent1, L, L1),
                            %append(L1, [newline, tab(Indent1), CtxNew, space, =, space, Call1], L2),
                            Indent2 is Indent1 + 1, 
                            append(L1, [newline, tab(Indent1), if, space, CtxNew,"['success']",:, newline, tab(Indent2), ctx_copy, space, =, space, CtxNew, "['context']"], L2),
                            (T \= [] -> translate_body_backtrack(notcallmain, and, notinforall, T, CtxNum1,Indent, Indent2, L2 ,L3) ; append(L2,[newline, tab(Indent2),"return {'success': True, 'context' : ctx_copy}"],L3)),
                            append(L3, [newline, tab(Indent1), else, :, newline, tab(Indent2), "ctx_copy = copy(ctx)", newline, tab(Indent2), continue],Lout).

translate_final(notcallmain, and, notinforall, Indent, L, Lout) :-
                      append(L, [newline, tab(Indent), "return {'success' : False, 'context' : ctx}"], Lout).



translate(Rule, notcallmain, and, notinforall, Lout) :- 
                calltype1(X),
                Rule = pred(X, notcallmain, _, Head, and(Body), _, _, Domains, _, _), Head =.. [Name| Args], append(Args,[ctx], Args1), Headcall =.. [Name|Args1], L1 = [def, space, Headcall, :],
                (X = main -> preamble(Head,L1,L2) ; L2 = L1),
				 Domains = [_|_],
				Indent = 1,
				append(L2,[newline, tab(Indent),ctx_copy,space,=,copy(ctx)],L3),
				add_backtracking(Domains,Indent,Indent1,L3,L4),
                translate_body_backtrack(notcallmain, and, notinforall,Body,0,Indent,Indent1,L4,L5),
                translate_final(notcallmain, and, notinforall, 1,L5, Lout). 

calltype1(main).
calltype1(abstraction).


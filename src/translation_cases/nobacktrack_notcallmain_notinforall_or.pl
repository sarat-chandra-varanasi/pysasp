
translate_body_nobacktrack(notcallmain, or, notinforall, [],_,Indent,L,Lout) :-  
          append(L, [newline, tab(Indent), "return {'success': False, 'context' : ctx}"], Lout).

translate_body_nobacktrack(notcallmain, or, notinforall, [H|T],CtxNum,Indent,L,Lout) :- 
                        H = Call, CtxNum1 is CtxNum + 1, ctx_term(CtxNum, _), ctx_term(CtxNum1, CtxNew),
                        gen_call(Call, ctx, CtxNew, Indent, L, L1), 
                        %append(L, [newline, tab(Indent), CtxNew, space, =, space, Call1], L1),
                        Indent1 is Indent + 1,
                        append(L1, [newline, tab(Indent), if, space, CtxNew,"['success']",:, newline, tab(Indent1), ctx, space, =, space, CtxNew, "['context']"], L2),
                        append(L2, [newline, tab(Indent1), "return {'success' : True, 'context' : ctx }"], L3),
                        append(L3, [newline, tab(Indent), else,  :], L4),
                        translate_body_nobacktrack(notcallmain, or, notinforall, T, CtxNum1,Indent1,L4,Lout).

translate(Rule, notcallmain, or, notinforall, Lout) :-
                        calltype(X),
                        Rule = pred(X, notcallmain, _, Head, or(Body), _, _, Domains, Forall, _), Head =.. [Name| Args], append(Args,[ctx], Args1), Headcall =.. [Name|Args1], L1 = [def, space, Headcall, :],
				Domains = [],
                        add_foralls(Forall,L1, L2,1,Indent1),
                        translate_body_nobacktrack(notcallmain, or, notinforall, Body,0,Indent1,L2,Lout).


calltype(dual).
calltype(abstraction).


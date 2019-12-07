

translate(Rule, Callmain, and, notinforall, L) :-
    Rule = pred(main, _, A, Head, Body, B, C, Domains, _, Dataflow),
    Rulemod = pred(main, notcallmain, A, Head, Body, B, C, Domains, [], Dataflow),
    (Domains \= [] -> translate_main_backtrack(Rulemod, L) ; translate_main_nobacktrack(Rulemod, L)).


translate_main_body_backtrack([H|T],CtxNum,Indent,Indent1,L,Lout) :- 
         ctx_term(CtxNum,_),
         H = Call, CtxNum1 is CtxNum + 1, ctx_term(CtxNum, _), ctx_term(CtxNum1, CtxNew),
         gen_call(Call, ctx_copy, CtxNew, Indent1, L, L1),
         Indent2 is Indent1 + 1, 
         append(L1, [newline, tab(Indent1), if, space, CtxNew,"['success']",:, newline, tab(Indent2), ctx_copy, space, =, space, CtxNew, "['context']"], L2),
         (T \= [] -> translate_main_body_backtrack(T, CtxNum1,Indent, Indent2, L2 ,L3) ; append(L2,[newline, tab(Indent2),"return {'success': True, 'context' : ctx_copy}"],L3)),
         append(L3, [newline, tab(Indent1), else, :, newline, tab(Indent2), "ctx_copy = copy(ctx)", newline, tab(Indent2), continue],Lout).

translate_final(notcallmain, and, notinforall, Indent, L, Lout) :-
         append(L, [newline, tab(Indent), "return {'success' : False, 'context' : ctx}"], Lout).


translate_main_backtrack(Rule, Lout) :- 
        Rule = pred(main, notcallmain, _, Head, and(Body), _, _, Domains, _, _), Head =.. [Name| Args], append(Args,[ctx], Args1), Headcall =.. [Name|Args1], L1 = [def, space, Headcall, :],
        preamble(Head,L1,L2),
				Domains = [_|_],
				Indent = 1,
				append(L2,[newline, tab(Indent),ctx_copy,space,=,copy(ctx)],L3),
				add_backtracking(Domains,Indent,Indent1,L3,L4),
        translate_main_body_backtrack(Body,0,Indent,Indent1,L4,L5),
        translate_main_backtrack_final(1,L5, Lout). 


translate_main_nobacktrack(Rule, Lout) :- 
          Rule =  pred(main, notcallmain, _, Head, and(Body), _, _, Domains, Forall, _), Head =.. [Name| Args], append(Args,[ctx], Args1), Headcall =.. [Name|Args1], L1 = [def, space, Headcall, :],
          preamble(Head,L1, L2), 
		      Domains = [],
		      Forall = [], 
          add_foralls(Forall,L2, L3,1,Indent1),
          translate_main_body_nobacktrack(Body,0,Indent1, L3, Lout).


translate_main_body_nobacktrack([],_,Indent1,L,Lout) :-
                    append(L, [newline, tab(Indent1), "return {'success' : True, 'context' : ctx}"], Lout).

translate_main_body_nobacktrack([H|T],CtxNum,Indent,L,Lout) :- H = Call, CtxNum1 is CtxNum + 1, ctx_term(CtxNum, _  ), ctx_term(CtxNum1, CtxNew),
                     gen_call(Call, ctx, CtxNew, Indent, L, L1),
                     Indent1 is Indent + 1,
                     append(L1, [newline, tab(Indent), if, space, CtxNew,"['success']",:, newline, tab(Indent1), ctx, space, =, space, CtxNew, "['context']"], L2),
                     translate_main_body_nobacktrack(T,CtxNum1,Indent1,L2,L3),
                     append(L3, [newline, tab(Indent), else, :], L4), 
                     (optimize(true),not(is_prim(Call)) -> append(L4, [newline, tab(Indent1), "nogood[str(", CtxNew, "['context'])] = True"], L5),
                                                           append(L5, [newline, tab(Indent1), "nogood[str(ctx)] = True"], L6)
                                                         ; L6 = L4),
                     append(L6, [newline, tab(Indent1), "return {'success' : False, 'context' : ctx}"],Lout).



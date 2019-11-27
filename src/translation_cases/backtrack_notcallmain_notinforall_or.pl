

translate(Rule, notcallmain, or, notinforall, Lout) :- 
        Rule = pred(abstraction, notcallmain,_, Head, or(Body), _, _, Domains, Forall, _), Head =.. [Name| Args], append(Args,[ctx], Args1), Headcall =.. [Name|Args1], L1 = [def, space, Headcall, :],
				Domains = [_|_],
				(Forall = [] -> ForallState = notinforall ; ForallState = inforall),
				Indent = 1,
				append(L1,[newline, tab(Indent),ctx_copy,space,=,copy(ctx)],L2),
				add_backtracking(Domains,Indent,Indent1,L2,L3),
        add_foralls(Forall,Indent1,Indent2, L3, L4),
        translate_body_backtrack(notcallmain, Connective,ForallState,Body,0,Indent1,Indent2,L4,L5), 
        translate_body_backtrack_final(notcallmain, Connective, ForallState,[],Indent1, Indent2, L5, Lout).


translate_body_backtrack_final(notcallmain, or, inforall, [],Indent,_,L,Lout) :- 
                                 Indent1 is Indent + 1,
                                 append(L, [newline, tab(Indent), "if break_out:", newline, tab(Indent1), "break_out = False", newline, tab(Indent), continue], L1),
                                 append(L1, [newline, tab, "return {'success': False, 'context' : ctx}"],Lout).


translate_body_backtrack(or, notinforall, [],_,_,Indent,L,Lout) :- append(L, [newline, tab(Indent), "ctx_copy = copy(ctx)", newline, tab(Indent),continue],Lout).


translate_body_backtrack(notcallmain, or, notinforall, [H|T],CtxNum,Indent,Indent1,L,Lout) :- 
                      ctx_term(CtxNum,_),
                      L1 = L,
                      H = Call, CtxNum1 is CtxNum + 1, ctx_term(CtxNum, _), ctx_term(CtxNum1, CtxNew),
                      %append(L1, [newline, tab(Indent1), CtxNew, space, =, space, Call1], L2),
                      gen_call(Call, ctx_copy, CtxNew, Indent1, L1, L2),
                      Indent2 is Indent1 + 1, 
                      append(L2, [newline, tab(Indent1), if, space, CtxNew,"['success']",:, newline, tab(Indent2), ctx_copy, space, =, space, CtxNew, "['context']"], L3),
                      append(L3, [newline, tab(Indent2), "return {'success' : True, 'context': ctx_copy}"], L4), 
                      append(L4, [newline, tab(Indent1), else, :],L5), 
                      translate_body_backtrack(notcallmain, or,notinforall,T,CtxNum1,Indent,Indent2,L5,Lout).
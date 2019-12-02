

%assuming that dual has no forall
translate(Rule, _, or, notinforall, Lout) :-
     Rule = pred(dual, _, _, Head,  or(Body),_, _,_, Forall, _), 
      Forall = [],
      Head =.. [Name| Args], append(Args,[ctx], Args1), Headcall =.. [Name|Args1], L1 = [def, space, Headcall, :],
      parser:neg_name(Name, Negname),
      append(L1, [newline, tab, if, space, "computation('", Negname, "',", Args, ')',  space, in, space, ctx, :,
      	          newline, tab(2), "return {'success' : False, 'context' : ctx}" ], L2),
      args_string(Args, Argsstring),
      (optimize(true) -> append(L2,[newline, tab, "ctx_check = copy(ctx)", newline, tab, "ctx_check[dualatom_2(", Argsstring, ")] = True",
                                   newline, tab, "if str(ctx_check) in nogooddual:",
                                   newline, tab, tab, "return {'success' : False, 'context' : ctx}",
                                   newline, tab, "if str(ctx) in nogood:",
                                   newline, tab, tab, "return {'success': False, 'context' : ctx}"], L3) ; L3 = L2),
      translate_body_nobacktrack(dual, Args, Body, 0, 1, L3, Lout).
      
translate_body_nobacktrack(dual, Headargs, [],_,Indent,L,Lout) :-  
           args_string(Headargs, Headargsstring),
          (optimize(true) -> append(L, [newline, tab(Indent), "ctx_dual = copy(ctx)", 
                                       newline, tab(Indent), "ctx_dual[dualatom_2(", Headargsstring, ")] = True",
                                       newline, tab(Indent), "nogooddual[str(ctx_dual)] = True"], L1) ; L1 = L),
          append(L1, [newline, tab(Indent), "return {'success': False, 'context' : ctx}"], Lout).

translate_body_nobacktrack(dual, Headargs, [H|T],CtxNum,Indent,L,Lout) :- 
                        H = Call, CtxNum1 is CtxNum + 1, ctx_term(CtxNum, _), ctx_term(CtxNum1, CtxNew),
                        gen_call(Call, ctx, CtxNew, Indent, L, L1), 
                        Indent1 is Indent + 1,
                        append(L1, [newline, tab(Indent), if, space, CtxNew,"['success']",:, newline, tab(Indent1), ctx, space, =, space, CtxNew, "['context']"], L2),
                        append(L2, [newline, tab(Indent1), "return {'success' : True, 'context' : ctx }"], L3),
                        append(L3, [newline, tab(Indent), else,  :], L4),
                        translate_body_nobacktrack(dual, Headargs, T, CtxNum1,Indent1,L4,Lout).


gen_call_opt(Call, Ctx, Ctxnew, Indent, L, Lout) :-
      parser:is_prim(Call),
      Call =.. [Name|[Primitive]],
      (is_pos(Name) -> process_operator(pos, Primitive, Primitive1) ; process_operator(neg, Primitive, Primitive1)),
      append(L, [newline, tab(Indent), Ctxnew, space, =, "{'success': True, 'context': ", Ctx, "}", 
             space, if, space, Primitive1, space, else, space, "{'success': False, 'context': ", Ctx , "}"], Lout).
      
gen_call_opt(Property, Call, Ctx, Ctxnew, Indent, L, Lout) :-
     parser:not(is_prim(Call)), 
     main_pred_id(Main),
     id_arity(Main, _),
     Call =.. [Name|Args], 
     append(Args, [copy(Ctx)], Args1), Call1 =.. [Name|Args1],
     args_string(Args, Argsstring),
     neg_name(Property, Propertyneg),
     append(L, [newline, tab(Indent), Ctxnew, space, =, space, "{'success' : False, 'context' : ctx, 'trivial' : True} if is_inconsistent_property(atom_2(", Argsstring, "), ctx,\"", Propertyneg, "\") else ", Call1], Lout). 
     
args_string(Args, String) :-
      args_string(Args, "", String).

args_string([], S, S).

args_string([H|T], S, String) :-
         term_string(H, Hs),
         string_concat(S, Hs, S1),
         (T = [] -> S2 = S1 ; string_concat(S1, ",", S2)),
         args_string(T, S2, String).
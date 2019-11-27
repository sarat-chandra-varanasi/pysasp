

%assuming that dual has no forall
translate(Rule, _, or, notinforall, Lout) :-
     Rule = pred(dual, _, _, Head,  or(Body),_, _,_, Forall, _), 
      Forall = [],
      Head =.. [Name| Args], append(Args,[ctx], Args1), Headcall =.. [Name|Args1], L1 = [def, space, Headcall, :],
      parser:neg_name(Name, Negname),
      append(L1, [newline, tab, if, space, "computation('", Negname, "',", Args, ')',  space, in, space, ctx, :,
      	          newline, tab(2), "return {'success' : False, 'context' : ctx}" ], L2),
      translate_body_nobacktrack(notcallmain, or, notinforall, Body, 0, 1, L2, Lout).
      

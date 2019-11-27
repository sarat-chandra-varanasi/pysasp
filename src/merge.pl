
:- module(backtrack_callmain_inforall_and,[
            translate/5
     ]).

:- use_module(utils).


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
           ctx_term(CtxNum,CtxTerm),
           L1 = L,
           H = Call, CtxNum1 is CtxNum + 1, ctx_term(CtxNum, CtxOld), ctx_term(CtxNum1, CtxNew),
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
               translate_body_backtrack(callmain, Connective, ForallState, Body1,0,Indent1,Indent3,Nesting,L7,L8), 
               translate_final(callmain, and, inforall, 1, L8, Lout).


:- module(backtrack_notcallmain_notinforall_and,[
                   translate/5
    ]).

:- use_module(utils).

translate_body_backtrack(notcallmain, and, notinforall, [H|T],CtxNum,Indent,Indent1,L,Lout) :- 
                            ctx_term(CtxNum,CtxTerm),
                            H = Call, CtxNum1 is CtxNum + 1, ctx_term(CtxNum, CtxOld), ctx_term(CtxNum1, CtxNew),
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
                Rule = pred(X, notcallmain, _, Head, and(Body), _, _, Domains, Forall, Dataflow), Head =.. [Name| Args], append(Args,[ctx], Args1), Headcall =.. [Name|Args1], L1 = [def, space, Headcall, :],
                (X = main -> preamble(Head,L1,L2) ; L2 = L1),
							  Domains = [_|_],
							 (Forall = [] -> ForallState = notinforall ; ForallState = inforall),
							 Indent = 1,
							 append(L2,[newline, tab(Indent),ctx_copy,space,=,copy(ctx)],L3),
							 add_backtracking(Domains,Indent,Indent1,L3,L4),
               translate_body_backtrack(notcallmain, and, notinforall,Body,0,Indent,Indent1,L4,L5),
               translate_final(notcallmain, and, notinforall, 1,L5, Lout). 

calltype1(main).
calltype1(abstraction).


:- module(backtrack_notcallmain_notinforall_or,[
                   translate/5
  
  ]).

:- use_module(utils).

translate(Rule, notcallmain, or, notinforall, Lout) :- 
        Rule = pred(abstraction, notcallmain,_, Head, or(Body), _, _, Domains, Forall, Dataflow), Head =.. [Name| Args], append(Args,[ctx], Args1), Headcall =.. [Name|Args1], L1 = [def, space, Headcall, :],
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
                      ctx_term(CtxNum,CtxTerm),
                      L1 = L,
                      H = Call, CtxNum1 is CtxNum + 1, ctx_term(CtxNum, CtxOld), ctx_term(CtxNum1, CtxNew),
                      Call =.. [Name|Args], append(Args, [ctx_copy], Args1), Call1 =.. [Name|Args1], 
                      %append(L1, [newline, tab(Indent1), CtxNew, space, =, space, Call1], L2),
                      gen_call(Call, ctx_copy, CtxNew, Indent1, L1, L2),
                      Indent2 is Indent1 + 1, 
                      append(L2, [newline, tab(Indent1), if, space, CtxNew,"['success']",:, newline, tab(Indent2), ctx_copy, space, =, space, CtxNew, "['context']"], L3),
                      append(L3, [newline, tab(Indent2), "return {'success' : True, 'context': ctx_copy}"], L4), 
                      append(L4, [newline, tab(Indent1), else, :],L5), 
                      translate_body_backtrack(notcallmain, or,notinforall,T,CtxNum1,Indent,Indent2,L5,Lout).
:- module(domains, [
         translate/4
  ]).


:- use_module(parser).
:- use_module(utils).

remove_type(typestr(V), V, typestr).
remove_type(typenum(V), V, typenum).

gen_values([], L, Lout) :-
            append(L, [newline, '}'], Lout).

gen_values([H|T], L, Lout) :-
       remove_type(H, Hv, Type),
       (Type = typestr -> append(L, [newline, '\'', Hv, '\'', space, : , space, "True"], L1) ; append(L, [newline, Hv,  space, : , space, "True"], L1)),
       (T \= [] -> append(L1, [','], L2) ;  L2 = L1),
       gen_values(T, L2, Lout).

translate(domains, Domains, Lout) :-
       translate(domains, Domains, [], Lout).

translate(domains, [], L, L).

translate(domains, [H|T], L, Lout) :- 
           H = (Domain, Values),
           atom_chars(Domain, Chars),
           append(Namechars, ['_',_], Chars),
           atom_chars(Name, Namechars),
           append(L, [newline, Domain, space, =, space, '{' ], L1),
           gen_values(Values, L1, L2),
           translate(domains, T, L2, Lout).

inverse_format_arg(typestr(X), X).
inverse_format_arg(typenum(X), X).


translate(inputs, Inputvalues, L) :-
     translate(inputs, Inputvalues, [newline, input, space, =, '{'], L).

translate(inputs, [], L, Lout) :-
            append(L, [newline, '}'], Lout).


translate(inputs, [H|T], L, Lout) :-
        H =.. [Name|Args],
        maplist(inverse_format_arg, Args, Args1),
        H1 =.. [Name|Args1],
        (T = [] -> append(L, [newline, '\'', H1, '\'', space, :, space, "True"], L1) 
                ;  append(L, [newline, '\'', H1, '\'', space, :, space, "True", ','], L1)),
        translate(inputs, T, L1, Lout).
:- module(dual, [
        translate/5
	])

:- use_module(parser).

%assuming that dual has no forall
translate(Rule, _, or, notinforall, Lout) :-
     Rule = pred(dual, _, _, Head,  or(Body),_, _,Domains, Forall, Dataflow), 
      Forall = [],
      Head =.. [Name| Args], append(Args,[ctx], Args1), Headcall =.. [Name|Args1], L1 = [def, space, Headcall, :],
      parser:neg_name(Name, Negname),
      append(L1, [newline, tab, if, space, "computation('", Negname, "',", Args, ')',  space, in, space, ctx, :,
      	          newline, tab(2), "return {'success' : False, 'context' : ctx}" ], L2),
      translate_body_nobacktrack(notcallmain, or, notinforall, Body, 0, 1, L2, Lout).
      

:- module(maincall,[
          translate/5
	]).



translate(Rule, callmain, and, notinforall, L) :-
    Rule = pred(main, _, A, Head, Body, B, C, Domains, Forall, Dataflow),
    Rulemod = pred(main, notcallmain, A, Head, Body, B, C, Domains, [], Dataflow),
    translate(Rulemod, notcallmain, and, notinforall, L).

:- module(nobacktrack_callmain_inforall_and,[
         translate/5
    ]).

:- use_module(utils).


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

translate_body_nobacktrack_final(callmain, and, inforall, Indent, L, Lout) :-
                   append(L, [newline, tab, "return {'success' : True, 'context' : ctx}"], Lout).
 
translate_body_nobacktrack(callmain, and, inforall, [],Indent,_,L,L).
                   
translate_body_nobacktrack(callmain, and, inforall, [H|T],CtxNum,Indent,L,Lout) :- H = Call, CtxNum1 is CtxNum + 1, ctx_term(CtxNum, CtxOld), ctx_term(CtxNum1, CtxNew),
                     Call =.. [Name|Args], append(Args, [ctx], Args1), Call1 =.. [Name|Args1], 
                     %append(L, [newline, tab(Indent), CtxNew, space, =, space, Call1], L1),
                     gen_call(Call, ctx, CtxNew, Indent, L, L1),
                     Indent1 is Indent + 1,
                     append(L1, [newline, tab(Indent), if, space, CtxNew,"['success']",:, newline, tab(Indent1), ctx, space, =, space, CtxNew, "['context']",
                                 newline, tab(Indent1), "size = sizeof(ctx)"], L2),
                     translate_body_nobacktrack(callmain, and, inforall, T,CtxNum1,Indent1,L2,L3),
                     append(L3, [newline, tab(Indent), else, :, newline, tab(Indent1), "return {'success' : False, 'context' : ctx['context']}"],L4),
                     append(L4, [newline, tab(Indent), "count = count + 1"], Lout).


:- module(nobacktrack_calmain_inforall_or,[
            translate/5
     ]).


:- use_module(utils).

translate_body_nobacktrack(callmain, or, inforall, Body, CtxNum, Indent, Indent1, L, Lout) :-
                 translate_body_nobacktrack_helper(callmain, or, inforall, Body, CtxNum, Indent, Indent1, L, L1),
                 translate_body_nobacktrack_final(callmain, or, inforall, [],_,Indent,Indent1,L1, Lout).

translate_body_nobacktrack_helper(callmain, or, inforall, [], _,_,_,L, L).

translate_body_nobacktrack_helper(callmain, or, inforall, [H|T],CtxNum,Indent,Indent1,L,Lout) :- 
                    ctx_term(CtxNum,CtxTerm),
                    H = Call, CtxNum1 is CtxNum + 1, ctx_term(CtxNum, CtxOld), ctx_term(CtxNum1, CtxNew),
                    Call =.. [Name|Args], append(Args, [ctx], Args1), Call1 =.. [Name|Args1], 
                    %append(L, [newline, tab(Indent1), CtxNew, space, =, space, Call1], L1),
                    gen_call(Call, ctx, CtxNew, Indent1, L, L1),
                    Indent2 is Indent1 + 1, 
                    append(L1, [newline, tab(Indent1), if, space, CtxNew,"['success']",:, newline, tab(Indent2), ctx, space, =, space, CtxNew, "['context']"], L2),
                    append(L2, [newline, tab(Indent2), size, space, =, space, sizeof(ctx)], L3),
                    append(L3, [newline, tab(Indent1), else, :], L4),
                    (T \= [] -> translate_body_nobacktrack_helper(callmain, or, inforall,T,CtxNum1,Indent,Indent2,L4,Lout) ;  append(L4,[newline, tab(Indent2), "return {'success': False, 'context' : ctx}"],Lout)). 
                    

translate_body_nobacktrack_final(callmain, or, inforall, [],_,Indent,Indent1, L, Lout) :- 
           Indent2 is Indent + 1, 
           append(L, [newline, tab(Indent2), "count = count + 1"], Lout).


translate_nobacktrack_final(callmain, or, inforall, _, Indent, Indent1, L, Lout) :-
                      append(L, [newline, tab, "return {'success': True, 'context' : ctx}"], Lout).


translate(Rule, callmain, or, inforall, Lout) :- 
              Rule =  pred(abstraction, callmain, _, Head, or(Body), _, _, Domains, Forall, Dataflow), Head =.. [Name| Args], append(Args,[ctx], Args1), Headcall =.. [Name|Args1], L1 = [def, space, Headcall, :],
               Domains = [],
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
               append(L4, DL, L5),
               replace_vars(Body,Dataflow,Body1), 
               translate_body_nobacktrack(callmain, or, inforall, Body1,0,Indent2,Indent3,L5,L6), 
               translate_nobacktrack_final(callmain, or, inforall, 1, _,Indent3, L6, Lout).



:- module(nobacktrack_callmain_notinforall_or,[
               translate/5
    ]).

:- use_module(utils).

translate_body_nobacktrack(callmain, or, notinforall, Body, CtxNum, Indent, Indent1, L, Lout) :-
                 translate_body_nobacktrack_helper(callmain, or, notinforall, Body, CtxNum, Indent, Indent1, L, L1),
                 translate_body_nobacktrack_final(callmain, or, notinforall, [],_,Indent,Indent1,L1, Lout).

translate_body_nobacktrack_helper(callmain, or, notinforall, [], _,_,_,L, L).

translate_body_nobacktrack_helper(callmain, or, notinforall, [H|T],CtxNum,Indent,Indent1,L,Lout) :- 
                    ctx_term(CtxNum,CtxTerm),
                    H = Call, CtxNum1 is CtxNum + 1, ctx_term(CtxNum, CtxOld), ctx_term(CtxNum1, CtxNew),
                    %Call =.. [Name|Args], append(Args, [ctx], Args1), Call1 =.. [Name|Args1], 
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
               replace_vars(Body,Dataflow,Body1), 
               translate_body_nobacktrack(callmain, or, notinforall, Body1,0,Indent1,Indent3,L4,L5), 
               translate_nobacktrack_final(callmain, or, notinforall, 1, L5, Lout).




:- module(nobacktrack_notcallmain_notinforall_and,[
          translate/5
  ]).


:- use_module(utils).

translate(Rule, notcallmain, and, notinforall, Lout) :- 
          calltype2(X),
          Rule =  pred(X, notcallmain, _, Head, and(Body), _, _, Domains, Forall, Dataflow), Head =.. [Name| Args], append(Args,[ctx], Args1), Headcall =.. [Name|Args1], L1 = [def, space, Headcall, :],
          (X = main -> preamble(Head,L1, L2) ; L2 = L1), 
			    Domains = [],
			    Forall = [], 
              add_foralls(Forall,L2, L3,1,Indent1),
              translate_body_nobacktrack(notcallmain, and, notinforall,  Body,0,Indent1, L3, Lout).


translate_body_nobacktrack(notcallmain, and, notinforall, [],_,Indent1,L,Lout) :-
                    append(L, [newline, tab(Indent1), "return {'success' : True, 'context' : ctx}"], Lout).

translate_body_nobacktrack(notcallmain, and, notinforall, [H|T],CtxNum,Indent,L,Lout) :- H = Call, CtxNum1 is CtxNum + 1, ctx_term(CtxNum, CtxOld), ctx_term(CtxNum1, CtxNew),
                     Call =.. [Name|Args], append(Args, [ctx], Args1), Call1 =.. [Name|Args1], 
                     %append(L, [newline, tab(Indent), CtxNew, space, =, space, Call1], L1),
                     gen_call(Call, ctx, CtxNew, Indent, L, L1),
                     Indent1 is Indent + 1,
                     append(L1, [newline, tab(Indent), if, space, CtxNew,"['success']",:, newline, tab(Indent1), ctx, space, =, space, CtxNew, "['context']"], L2),
                     translate_body_nobacktrack(notcallmain, and, notinforall, T,CtxNum1,Indent1,L2,L3),
                     append(L3, [newline, tab(Indent), else, :, newline, tab(Indent1), "return {'success' : False, 'context' : ctx}"],Lout).

calltype2(main).
calltype2(abstraction).

gen_call(Call, Ctx, Ctxnew, Indent, L, Lout) :-
      parser:is_prim(Call),
      Call =.. [Name|[Primitive]],
      (is_pos(Name) -> process_operator(pos, Primitive, Primitive1) ; process_operator(neg, Primitive, Primitive1)),
      append(L, [newline, tab(Indent), Ctxnew, space, =, "{'success': True, 'context': ", Ctx, "}", 
             space, if, space, Primitive1, space, else, space, "{'success': False, 'context': ", Ctx , "}"], Lout).
      
gen_call(Call, Ctx, Ctxnew, Indent, L, Lout) :-
     parser:not(is_prim(Call)),
     Call =.. [Name|Args], append(Args, [Ctx], Args1), Call1 =.. [Name|Args1],
     append(L, [newline, tab(Indent), Ctxnew, space, =, space, Call1], Lout).

map_op("\\=", "!=").
map_op("<", "<").
map_op(">", ">").
map_op("=", "==").
map_op("=<", "<=").
map_op(">=", ">=").

map_negop("\\=", "==").
map_negop("<", ">=").
map_negop(">", "<=").
map_negop("=", "!=").
map_negop("=<", ">").
map_negop(">=", "<").

is_pos(Primitive) :-
     atom_chars(Primitive, [p,r,i,m,i,t,i,v,e|_]).

is_neg(Primitive) :-
     atom_chars(Primitive, [n,o,t,p,r,i,m,i,t,i,v,e|_]).



process_operator(pos, Functor, Result) :-
      Functor =.. [Op, A, B],
      atom_string(Op, Ops),
      map_op(Ops, Ops1),
      atom_string(A, As),
      atom_string(B, Bs),
      string_concat(As, Ops1, Partial),
      string_concat(Partial, Bs, Result).


process_operator(neg, Functor, Result) :-
      Functor =.. [Op, A, B],
      atom_string(Op, Ops),
      map_negop(Ops, Ops1),
      atom_string(A, As),
      atom_string(B, Bs),
      string_concat(As, Ops1, Partial),
      string_concat(Partial, Bs, Result).




:- module(bobacktrack_notcallmain_notinforall_or,[
            translate/5
      ]).


translate_body_nobacktrack(notcallmain, or, notinforall, [],_,Indent,L,Lout) :-  
          append(L, [newline, tab(Indent), "return {'success': False, 'context' : ctx}"], Lout).

translate_body_nobacktrack(notcallmain, or, notinforall, [H|T],CtxNum,Indent,L,Lout) :- 
                        H = Call, CtxNum1 is CtxNum + 1, ctx_term(CtxNum, CtxOld), ctx_term(CtxNum1, CtxNew),
                        %Call =.. [Name|Args], append(Args, [ctx], Args1), Call1 =.. [Name|Args1],
                        gen_call(Call, ctx, CtxNew, Indent, L, L1), 
                        append(L, [newline, tab(Indent), CtxNew, space, =, space, Call1], L1),
                        Indent1 is Indent + 1,
                        append(L1, [newline, tab(Indent), if, space, CtxNew,"['success']",:, newline, tab(Indent1), ctx, space, =, space, CtxNew, "['context']"], L2),
                        append(L2, [newline, tab(Indent1), "return {'success' : True, 'context' : ctx }"], L3),
                        append(L3, [newline, tab(Indent), else,  :], L4),
                        translate_body_nobacktrack(notcallmain, or, notinforall, T, CtxNum1,Indent1,L4,Lout).

translate(Rule, notcallmain, or, notinforall, Lout) :-
                        calltype(X),
                        Rule = pred(X, notcallmain, _, Head, or(Body), _, _, Domains, Forall, Dataflow), Head =.. [Name| Args], append(Args,[ctx], Args1), Headcall =.. [Name|Args1], L1 = [def, space, Headcall, :],
				Domains = [],
                        add_foralls(Forall,L1, L2,1,Indent1),
                        translate_body_nobacktrack(notcallmain, or, notinforall, Body,0,Indent1,L2,Lout).


calltype(dual).
calltype(abstraction).


:- module(preamble,[
            init/1
  ]).

init(L) :-
  L =[newline, "import copy",
  	      newline, "copy = copy.deepcopy",
  	      newline, "def sizeof(dict):",
  	      newline, tab, "return len(dict)",
          newline, "def getarg(term, argnum):",
          newline, tab, "index = term.find('(')",
          newline, tab, "sArg = term[index+1:len(term)-1]",
          newline, tab, "return sArg.split(',')[argnum-1]",
          newline, "def computation(predicate, args):",
          newline, tab, "s = predicate + '('",
          newline, tab, "i = 0",
          newline, tab, "while i < len(args) - 1:",
          newline, tab(2), "s += str(args[i]) + ','",
          newline, tab(2), "i += 1",
          newline, tab, "s += str(args[i]) + ')'",
          newline, tab, "return s"].
  	      
:- module(translate, [
            translate/2

  ]).

:- use_module(parser).
:- use_module(utils).
:- use_module(preamble).
:- use_module(domains).
:- use_module(maincall).
:- use_module(dual).
:- use_module(backtrack_callmain_inforall_and).
:- use_module(backtrack_notcallmain_notinforall_and).
:- use_module(backtrack_notcallmain_notinforall_or).
:- use_module(nobacktrack_callmain_inforall_and).
:- use_module(nobacktrack_callmain_inforall_or).
:- use_module(nobacktrack_callmain_notinforall_or).
:- use_module(nobacktrack_notcallmain_notinforall_and).
:- use_module(nobacktrack_notcallmain_notinforall_or).

translate(Source,Dest) :-
     %open(Dest, write, Out), set_output(Out),
     parser:gen_intermediate_prog(Source, Rulesfmt, Domains, Main, Inputs, Graph, Graph1, Flow1, Rulesfinal1, Values,Inputvalues),
     init(L), format(L),
     translate(domains, Values, L1), format(L1), 
     translate(inputs, Inputvalues, L2), format(L2),
     gen_input_calls(Inputs, L3), format(L3),
     Rulesfinal1 = [A|T],
     format([newline]),
     mod_rules(Rulesfinal1, Mod), 
     translate_rules(Mod). 
     

translate_rules([]).


mod_rules(Rules, Mod) :-
     mod_rules(Rules, [], Mod).

mod_rules([], M, M).

mod_rules([H|T], M, Mod) :-
           H = pred(Type, Callmain, A, Head, Connective, B, C, Domains, Forall, Dataflow),
           ((Callmain = callmain, Connective = and(_), Domains = [_|_]) ->
             Hmod = pred(Type, notcallmain, A, Head, Connective, B, C, Domains, [], Dataflow) ;
             Hmod = H),
           append(M, [Hmod], M1),
           mod_rules(T, M1, Mod).
      

translate_rules([H|T]) :-
        H = pred(Type, Callmain, A, Head, Connective, B, C, Domains, Forall, Dataflow),  
        Forall = [],
        Connective =.. [Op, Body],
        translate(H, Callmain, Op, notinforall, L), format(L), !,
        format([newline]),
        translate_rules(T).

translate_rules([H|T]) :-
        H = pred(Type, Callmain, A, Head, Connective, B, C, Domains, Forall, Dataflow),
        Forall = [_|_],
        Connective =.. [Op, Body],
        translate(H, Callmain, Op, inforall, L), format(L), !,
        format([newline]),
        translate_rules(T).


get_vars(Arity, Vars) :-
      get_vars(Arity, [], Vars).

get_vars(0, V, V).

get_vars(Arity, V, Vars) :-
       var_id(Id),
       Id1 is Id + 1,
       retract(var_id(Id)),
       assert(var_id(Id1)),
       number_chars(Id, Idchars),
       append([x,'_'],Idchars, Varchars),
       atom_chars(Var, Varchars),
       append(V, [Var], V1),
       Arity1 is Arity - 1,
       get_vars(Arity1, V1, Vars).        

:- dynamic var_id/1.

var_id(1).

gen_input_calls(Inputs, Lout) :- 
      gen_input_calls(Inputs, [], Lout).

gen_input_calls([], L, L).

gen_input_calls([H|T], L, Lout) :- 
      atom_chars(H,Chars),
      append(Namechars, ['_',Aritychar],Chars),
      atom_chars(Name, Namechars),
      number_chars(Arity, [Aritychar]),
      get_vars(Arity, Vars),
      append(Vars, [ctx], Vars1),
      Call =.. [H|Vars1],
      append(L, [newline, def, space, Call, :, 
      	         newline, tab, if, space, "computation('", H, "',", Vars, ")", space, in, space, input, :,
      	         newline, tab, tab, "return {'success' : True, 'context': ctx}",
      	         newline, tab, else,:,
      	         newline, tab, tab, "return {'success': False, 'context' : ctx}"], L1),
      parser:neg_name(H, Dualname),
      Dual =.. [Dualname|Vars1],
      append(L1, [newline, def, space, Dual, :, 
      	         newline, tab, if, space, "computation('", H, "',", Vars, ")", space, in, space, input, :,
      	         newline, tab, tab, "return {'success' : False, 'context': ctx}",
      	         newline, tab, else,:,
      	         newline, tab, tab, "return {'success': True, 'context' : ctx}"], L2),
      gen_input_calls(T, L2, Lout).


:- module(utils,[
          replace_vars/3,
          add_backtracking/5,
          add_foralls/5

	]).

format([newline|T]) :- write('\n'), !,format(T).
format([tab(X)|T]) :- format(tab, X), !, format(T).
format(tab, 0).
format(tab, X) :- X > 0, write('\t'), X1 is X - 1, format(tab, X1).
format([tab|T]) :- write('\t'), !, format(T).
format([space|T]) :- write(' '), !, format(T).
format([X|T]) :-  write(X), format(T).
format([]).
 
ctx_string(0, "ctx"). 
ctx_string(Num, String) :- atom_string(Num,S), string_concat("ctx",S, String). 
ctx_term(Num, Term) :- ctx_string(Num, String), atom_string(Term, String).

preamble(Head,L1,L2) :- Head =.. [Name|Args], append(L1, [newline, tab, if, space, computation, "('", Name, "',", Args, ")", space, in, space, ctx, :, newline, tab(2), "return {'success': True, 'context'	: ctx}",
	                                newline, tab, ctx, "[computation('",Name, "',", Args, ")] = True"],L2).


translate_body_nobacktrack(and, [],_,_,L,L).

translate_body_nobacktrack(and, [H|T],CtxNum,Indent,L,Lout) :- H = Call, CtxNum1 is CtxNum + 1, ctx_term(CtxNum, CtxOld), ctx_term(CtxNum1, CtxNew),
                                                      Call =.. [Name|Args], append(Args, [ctx], Args1), Call1 =.. [Name|Args1], 
                                                      append(L, [newline, tab(Indent), CtxNew, space, =, space, Call1], L1),
                                                      Indent1 is Indent + 1,
                                                      append(L1, [newline, tab(Indent), if, space, CtxNew,"['success']",:, newline, tab(Indent1), ctx, space, =, space, CtxNew, "['context']"], L2),
                                                      translate_body_nobacktrack(and, T,CtxNum1,Indent1,L2,L3),
                                                      append(L3, [newline, tab(Indent), else, :, newline, tab(Indent1), "return {'success' : False, 'context' : ctx['context']}"],Lout).

translate_body_nobacktrack(or, [],_,Indent,L,Lout) :-  
          append(L, [newline, tab(Indent), "return {'success': False, 'context' : ctx}"], Lout).

translate_body_nobacktrack(or, [H|T],CtxNum,Indent,L,Lout) :- 
                        H = Call, CtxNum1 is CtxNum + 1, ctx_term(CtxNum, CtxOld), ctx_term(CtxNum1, CtxNew),
                        Call =.. [Name|Args], append(Args, [ctx], Args1), Call1 =.. [Name|Args1], 
                        append(L, [newline, tab(Indent), CtxNew, space, =, space, Call1], L1),
                        Indent1 is Indent + 1,
                        append(L1, [newline, tab(Indent), if, space, CtxNew,"['success']",:, newline, tab(Indent1), ctx, space, =, space, CtxNew, "['context']"], L2),
                        append(L2, [newline, tab(Indent1), "return {'success' : True, 'context' : ctx }"], L3),
                        append(L3, [newline, tab(Indent), else,  :], L4),
                        translate_body_nobacktrack(notcallmain, or, notinforall, T, CtxNum1,Indent1,L4,Lout).
                                           


translate_body(Body,[],CtxNum,Indent,L,L1) :- 
                   translate_body_nobacktrack(and, Body,CtxNum,Indent,L,L1).
                  


translate_body_backtrack(notcallmain, and, notinforall, [H|T],CtxNum,Indent,Indent1,L,Lout) :- 
                                                       ctx_term(CtxNum,CtxTerm),
                                                       L1 = L,
                                                       H = Call, CtxNum1 is CtxNum + 1, ctx_term(CtxNum, CtxOld), ctx_term(CtxNum1, CtxNew),
                                                       Call =.. [Name|Args], append(Args, [ctx_copy], Args1), Call1 =.. [Name|Args1], 
                                                       append(L1, [newline, tab(Indent1), CtxNew, space, =, space, Call1], L2),
                                                       Indent2 is Indent1 + 1, 
                                                       append(L2, [newline, tab(Indent1), if, space, CtxNew,"['success']",:, newline, tab(Indent2), ctx_copy, space, =, space, CtxNew, "['context']"], L3),
                                                       (T \= [] -> translate_body_backtrack(notcallmain, and, notinforall, T, CtxNum1,Indent, Indent2, L3 ,L4) ; append(L3,[newline, tab(Indent2),"return {'success': True, 'context' : ctx_copy}"],L4)),
                                                       append(L4, [newline, tab(Indent1), else, :, newline, tab(Indent2), "ctx_copy = copy(ctx)", newline, tab(Indent2), continue],Lout).
                        
translate_body_backtrack(notcallmain, or, notinforall, [], Ctxnum, Indent, Indent1, L, Lout) :- 
                               Indent2 is Indent1 + 1,
                               append(L, [newline, tab(Indent2), "ctx_copy = copy(ctx)", newline,  tab(Indent2), continue], Lout).


translate_body_backtrack_final(notcallmain, or, notinforall, [], [], Ctxnum, Indent, Indent1, L, Lout) :-
                              append(L, [newline, tab, "return {'success': False, 'context' : ctx"], Lout).                                                      
                                                       
                                                     
translate_body_backtrack_final(callmain, or, inforall, [],Indent,_,L,Lout) :- 
                                 Indent1 is Indent + 1,
                                 append(L, [newline, tab(Indent), "if break_out:", newline, tab(Indent1), "break_out = False"], L1),
                                 append(L1, [newline, tab(Indent), "ctx_copy = copy(ctx)", newline, tab(Indent), continue], L2),
                                 append(L2, [newline, tab, "return {'success': False, 'context' : ctx}"],Lout).

%assumption: goals with body vars reordered at the time of parsing to the right
translate_body(Body,Domains,CtxNum,Indent,L,Lout) :-
									    append(L,[newline, tab(Indent),ctx_copy,space,=,copy(ctx)],L1),
											add_backtracking(Domains,Indent,Indent1,L1,L2),
											translate_body_backtrack(Body,CtxNum,Indent,Indent1,L2,Lout	).
                      
 
add_backtracking([],Indent,Indent,L,L). 
add_backtracking([H|T], Indent, Indent2, L ,L2) :- H =.. [Name,Dom], Indent1 is Indent + 1, append(L, [newline, tab(Indent),for,space, Name,space, in,space, Dom, :], L1), 
                                                           add_backtracking(T, Indent1, Indent2, L1, L2). 
add_foralls([],Indent,Indent,L,L).
add_foralls([H|T], Indent, Indent2, L ,L2) :- H =.. [Name,Dom], Indent1 is Indent + 1, append(L, [newline, tab(Indent),for,space, Name,space, in,space, Dom, :], L1),
                                                  add_foralls(T, Indent1, Indent2, L1, L2).       

add_dataflow(_,L,L).

split_functor(X, Name, Args) :- X =.. [Name, Args]. 


getarg_stmts([],Indent,L,L).

getarg_stmts([H|T],Indent,L1,L3) :-  
          H = (OldVar,NewVar,Pos), 
          (typeof(Pos,typenum) -> append(L1,[newline,tab(Indent),NewVar, " = int(getarg(term, ", Pos, "))"],L2) ; 
                            append(L1,[newline,tab(Indent),NewVar, " = getarg(term, ", Pos, ")"],L2)),
          getarg_stmts(T,Indent,L2,L3).

getarg_stmts(Flow,Indent,L) :- 
            getarg_stmts(Flow,Indent,[],L).

replace(Lin,Dataflow,Lout) :-  replace(Lin,Dataflow,[],Lout). 
replace([],Dataflow,Lin,Lin).
replace([H|T],Dataflow,Lin,Lout) :- member((H,H1,_),Dataflow), append(Lin,[H1],L2), replace(T,Dataflow,L2,Lout).
replace([H|T],Dataflow,Lin,Lout) :- not(member((H,H1,_),Dataflow)), append(Lin,[H],L2), replace(T,Dataflow,L2,Lout).
replace_vars(Goals,Dataflow,L) :- replace_vars(Goals,Dataflow,[],L).
replace_vars([],Dataflow,Lin,Lin).
replace_vars([H|T],Dataflow,Lin, Lout) :- 
            H = Call, 
            Call =.. [Name|Args],
            parser:not(is_prim(Name)),
            replace(Args,Dataflow,Args1), Call1 =.. [Name|Args1], append(Lin,[Call1],L1),
            replace_vars(T,Dataflow,L1, Lout).

replace_vars([H|T],Dataflow,Lin, Lout) :- 
            H = Call, 
            Call =.. [Name|[Expr]],
            parser:is_prim(Name),
            Expr =.. [Op|Args],
            replace(Args,Dataflow,Args1), Call1 =.. [Op|Args1],
             Call2 =.. [Name|[Call1]],
             append(Lin,[Call2],L1),
            replace_vars(T,Dataflow,L1, Lout).



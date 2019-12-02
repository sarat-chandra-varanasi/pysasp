

translate(Rule, notcallmain, and, notinforall, Lout) :- 
          Rule =  pred(abstraction, notcallmain, _, Head, and(Body), _, _, Domains, Forall, _), Head =.. [Name| Args], append(Args,[ctx], Args1), Headcall =.. [Name|Args1], L1 = [def, space, Headcall, :],
          Domains = [],
			    Forall = [], 
          add_foralls(Forall,L2, L3,1,Indent1),
          translate_body_nobacktrack(notcallmain, and, notinforall,  Body,0,Indent1, L3, Lout).


translate_body_nobacktrack(notcallmain, and, notinforall, [],_,Indent1,L,Lout) :-
                    append(L, [newline, tab(Indent1), "return {'success' : True, 'context' : ctx}"], Lout).

translate_body_nobacktrack(notcallmain, and, notinforall, [H|T],CtxNum,Indent,L,Lout) :- H = Call, CtxNum1 is CtxNum + 1, ctx_term(CtxNum, _  ), ctx_term(CtxNum1, CtxNew),
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
     Call =.. [Name|Args], append(Args, [copy(Ctx)], Args1), Call1 =.. [Name|Args1],
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



not_has_subexprs(Functor) :-
      Functor =.. [_, A, B],
      and(A =.. [A], B =..[B], true).

has_subexprs(Functor) :-
       not(not_has_subexprs(Functor)).

process_operator(pos, Functor, Result) :-
      has_subexprs(Functor),
      Functor =.. [Op|_],
      subexprs(Functor, [A,B]),
      term_string(Op, Ops),
      map_op(Ops, Ops1),
      maplist(term_string, [A,B],[A1,B1]),
      string_concat(A1, Ops1, Partial),
      string_concat(Partial, B1, Result).

process_operator(neg, Functor, Result) :-
      has_subexprs(Functor),
      Functor =.. [Op|_],
      subexprs(Functor, [A,B]),
      term_string(Op, Ops),
      map_negop(Ops, Ops1),
      maplist(term_string, [A,B],[A1,B1]),
      string_concat(A1, Ops1, Partial),
      string_concat(Partial, B1, Result).


process_operator(pos, Functor, Result) :-
      not_has_subexprs(Functor),
      Functor =.. [Op, A, B],
      atom_string(Op, Ops),
      map_op(Ops, Ops1),
      atom_string(A, As),
      atom_string(B, Bs),
      string_concat(As, Ops1, Partial),
      string_concat(Partial, Bs, Result).


process_operator(neg, Functor, Result) :-
      not_has_subexprs(Functor),
      Functor =.. [Op, A, B],
      atom_string(Op, Ops),
      map_negop(Ops, Ops1),
      atom_string(A, As),
      atom_string(B, Bs),
      string_concat(As, Ops1, Partial),
      string_concat(Partial, Bs, Result).





:- module(translate, [
            translate/2,
            args_string/2

  ]).

:- use_module(parser).
:- use_module(utils).
:- use_module(preamble).
:- use_module(domains).
:- use_module(main).

:- discontiguous translate:translate/1.
:- discontiguous translate:translate_rules/1.
:- discontiguous translate:translate_final/6.
:- discontiguous translate:translate/5.
:- discontiguous translate:translate_body_backtrack_final/8.
:- discontiguous translate:translate_body_backtrack/9.
:- discontiguous translate:translate_body_nobacktrack/9.
:- discontiguous translate:translate_body_nobacktrack_helper/9.
:- discontiguous translate:translate_body_nobacktrack_final/9.
:- discontiguous translate:translate_body_nobacktrack/8.
:- discontiguous translate:translate_nobacktrack_final/8.

translate(Source, _) :-
     %open(Dest, write, Out), set_output(Out),
     gen_intermediate_prog(Source, _, _, Mainid, Inputs, _, _, _, Rulesfinal1, Values,Inputvalues),
     init(L), format(L),
     (optimize(true) -> gen_atom_call(Mainid, L1), format(L1) ; true),
     translate(domains, Values, L2), format(L2), 
     translate(inputs, Inputvalues, L3), format(L3),
     gen_input_calls(Inputs, L4), format(L4),
     format([newline]),
     mod_rules(Rulesfinal1, Mod), 
     translate_rules(Mod). 
     

translate_rules([]).


mod_rules(Rules, Mod) :-
     mod_rules(Rules, [], Mod).

mod_rules([], M, M).

mod_rules([H|T], M, Mod) :-
           H = pred(Type, Callmain, A, Head, Connective, B, C, Domains, _, Dataflow),
           ((Callmain = callmain, Connective = and(_), Domains = [_|_]) ->
             Hmod = pred(Type, notcallmain, A, Head, Connective, B, C, Domains, [], Dataflow) ;
             Hmod = H),
           append(M, [Hmod], M1),
           mod_rules(T, M1, Mod).
      

translate_rules([H|T]) :-
        H = pred(_, Callmain, _, _, Connective, _, _, _, Forall, _),  
        Forall = [],
        Connective =.. [Op, _],
        translate(H, Callmain, Op, notinforall, L), format(L), !,
        format([newline]),
        translate_rules(T).

translate_rules([H|T]) :-
        H = pred(_, Callmain, _, _, Connective, _, _, _, Forall, _),
        Forall = [_|_],
        Connective =.. [Op, _],
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
      atom_chars(_, Namechars),
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

gen_atom_call(Mainid, L) :-
     atom_chars(Mainid, Chars),
     append(Namechars, ['_', Aritychar], Chars),
     number_chars(Arity, [Aritychar]),
     get_vars(Arity, Vars),
     term_string(atom_, Atomstr),
     string_concat(Atomstr, Aritychar, Atomcall),
     term_string(Atom, Atomcall),
     Functor =.. [Atom|Vars],
     L1 = [newline, def, space, Functor, :, 
           newline, tab, "return computation('", Mainid, "',", Vars, ")"],
     term_string(dualatom_, Dualatomstr),
     string_concat(Dualatomstr, Aritychar, Dualatomcall),
     term_string(Dualatom, Dualatomcall),
     Functorneg =.. [Dualatom|Vars],
     neg_name(Mainid, Negid),
     L2 = [newline, def, space, Functorneg, :, 
           newline, tab, "return computation('", Negid, "',", Vars, ")"],
     append(L1, L2, L).
     
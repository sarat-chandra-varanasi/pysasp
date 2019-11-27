

translate(Rule, callmain, and, notinforall, L) :-
    Rule = pred(main, _, A, Head, Body, B, C, Domains, _, Dataflow),
    Rulemod = pred(main, notcallmain, A, Head, Body, B, C, Domains, [], Dataflow),
    translate(Rulemod, notcallmain, and, notinforall, L).


:- module(preamble,[
            init/1
  ]).

:- use_module(main).

init(Lout) :-
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
          newline, tab, "return s"],
  (optimize(true) -> opt_init(L1), append(L, L1, Lout) ; Lout = L).
  	      

opt_init([newline, "nogood = {}", newline, "inconsistent = {}", newline, "nogooddual = {}", 
          newline, "def is_inconsistent_property(atom, ctx, property):",
          newline, tab, "for term in ctx:",
          newline, tab, tab, "if (atom,term,property) in inconsistent:",
          newline, tab, tab, tab, "return True",
          newline, tab, "return False",
          newline, "def is_inconsistent(atom, ctx):",
          newline, tab, "for term in ctx:",
          newline, tab, tab, "if (atom, term, str(ctx)) in inconsistent:",
          newline, tab, tab, tab, "return True",
          newline, tab, "return False"]).
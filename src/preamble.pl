
:- module(preamble,[
            init/1
  ]).

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
  (optimize(true) -> append(L, [newline, "nogood = {}"], Lout) ; Lout = L).
  	      
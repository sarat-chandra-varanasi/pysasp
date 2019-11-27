
index(1).
index(2).
%index(3).

num(3).
num(1).
%num(2).

domain(num).
domain(index).
main(output).

output(X, I) :- num(X), index(I), not dominated(X, I), not blocked(X, I), not other(X, I).
dominated(X, I) :- num(Y), index(J), num(X), index(I), I \= J, X \= Y, output(Y, J), J < I, Y > X.
other(X, I) :- num(X), index(I), index(J), I \= J, output(X, J).
blocked(X, I) :- num(X), index(I), num(Y), X \= Y, output(X, I), output(Y, I).
 



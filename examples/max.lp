num(1).
num(3).
num(5).
num(7).

domain(num).
main(max).


dominated(X) :- num(X), num(Y), Y > X.

max(X) :- num(X), not dominated(X).
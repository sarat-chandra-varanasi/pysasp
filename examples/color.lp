domain(node).
domain(col).
main(color).

col(green).
col(red).
col(blue).

node(c).
node(a).
node(b).


input(edge).

edge(a, b).
edge(b, a).
edge(b, c).
edge(c, b).
edge(a, c).
edge(c, a).

color(X, C) :- node(X), col(C), not othercolor(X, C), not conflict(X, C).
othercolor(X, C) :- node(X), col(C), col(C1), C \= C1, color(X, C1).
conflict(X, C) :- node(X), col(C), node(Y), X \= Y, edge(X, Y), color(X, C), color(Y, C).	
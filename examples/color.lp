%domains are annotated with using domain/1
domain(node).
domain(col).

%color/2 is the main predicate from where the computation starts
main(color).

col(green).
col(red).
col(blue).

node(c).
node(a).
node(b).

%edge/2 represents the input graph
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
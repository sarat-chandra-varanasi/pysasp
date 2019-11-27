queen(1).
queen(2).

dom(-2).
dom(-1).
dom(0).
dom(1).
dom(2).

row(1).
row(2).
col(1).
col(2).

domain(queen).
domain(dom).
domain(row).
domain(col).

main(place).

%place the queen Q at board position I, J
place(Q, I, J) :- queen(Q), row(I), col(J), not other_place(Q, I, J), not conflict(Q, I, J), not blocked(Q, I, J).

%Q is placed in a position other than I, J
other_place(Q, I, J) :- queen(Q), row(I), col(J), row(I1), col(J1), different(I, J, I1, J1),  place(Q, I1, J1).
different(I1, J1, I2, J2) :- row(I1), row(I2), col(J1), col(J2), I1 \= I2.
different(I1, J1, I2, J2) :- row(I1), row(I2), col(J1), col(J2), J1 \= J2.

%Q1 is placed in an position conflicting (attacking) with Q, I, J
conflict(Q, I, J) :- queen(Q), queen(Q1), Q = Q1, row(I), col(J), row(I1), col(J1), conflict_position(I, J, I1, J1), place(Q, I, J), place(Q1, I1, J1).
conflict_position(I1, J1, I2, J2) :- row(I1), row(I2), col(J1), col(J2), J1 \= J2, I1 = I2.
conflict_position(I1, J1, I2, J2) :- row(I1), row(I2), col(J1), col(J2), I1 \= I2, J1 = J2.	
conflict_position(I1, J1, I2, J2) :-  row(I1), col(J1), row(I2), col(J2), dom(D1), I1 \= I2, J1 \= J2, diff(I1, I2, D1), diff(J1, J2, D1).

%Q1 is placed in the same position as Q
blocked(Q, I, J) :- queen(Q), row(I), col(J), queen(Q1), Q1 \= Q, place(Q1, I, J).

diff(I1, I2, D1) :- dom(I1), dom(I2), dom(D1), I1 >= I2, D1 = I1 - I2.
diff(I1, I2, D1) :- dom(I1), dom(I2), dom(D1), I1 < I2, D1 = I2 - I1.


n = 5-1
R = QQ[x,y,b_2..b_n,u_0..u_n]
bb = {0,1} | for i from 2 to n list b_i

C = transpose matrix for i from 0 to n list {1/(x+bb_i), 1/(x+bb_i)^2, 1/(y+bb_i), 1/(y+bb_i)^2}



factor det A4

A3 = submatrix(A4,{0,1,2},{0,1,2})
factor det A3
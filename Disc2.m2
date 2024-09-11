l = 4;
d = 2;
R = matrix {{0, 1, 0}, {0, 0, 1}, {1, 1, 1}, {1, 0, 0}}

-- Random l x (d+1) matrix:
-- R = random(QQ^l,QQ^(d+1));
-- The random matrix R that I got was the following:
-- R = matrix {{1, 1, 0}, {0, 1, 0}, {0, 0, 1}, {0, 7, 5}}
-- R = matrix {{1, 1, 0}, {0, 1, 0}, {0, 0, 1}, {0, 7, 5}, {-17, 8, 12}}; This matrix for l=5, d=2 does *not* give rise to the uniform matroid and yields a (prime over QQ) ML discriminant of degree 8 while Simon's degree equals 2*d*(l-2 choose d) = 12 here.

-- This matrix for l=5, d=2 gives an MLDiscriminant which has codimension 2! One component is ideal(u_2+u_3+u_4,u_1+u_5) and the other one is ideal(u_3,u_4)...
-- R = matrix {{2, 2, 0}, {0, 1, 0}, {0, 0, 1}, {0, 2, 1}, {1, 1, 0}};
-- R = matrix {{1, 1, 2}, {1, 2, 1}, {2, 3, 3}, {1, 0, 1}, {1, 0, 1}};
-- R = matrix {{1, 1, 0}, {2, 1, 0}, {1, 2, 0}, {0, 2, 1}, {0, 1, 2}, {0, 1, 1}}

Rhat = submatrix'(R,{},{0})

P = QQ[u_1..u_l,y_1..y_l,x_1..x_d];

Scatt = (transpose Rhat) * diagonalMatrix(toList(u_1..u_l)) * (transpose matrix {toList(y_1..y_l)});

lsHess = {};
for i from 1 to l do (
lsHess = append(lsHess,u_i*y_i^2);
);

Hess = det((transpose Rhat)*diagonalMatrix(lsHess)*Rhat);

-- Ramification locus:
Ram = ideal(Scatt) + ideal(Hess);

-- Impose conditions for the x_i's to lie in the hyperplane arrangement complement (in particular avoiding the hyperplane at infinity x_0 = 0):
for i from 1 to l do (
Ram = Ram + ideal(y_i * (R * (transpose matrix {join({sub(1,P)},toList(x_1..x_d))}) )_(i-1,0) - 1);
);

MLDisc = eliminate(Ram, join( toList(y_1..y_l), toList(x_1..x_d) ) )




--

loadPackage "Resultants";

N = gens kernel (transpose R);

A = QQ[y_1..y_l];

N = sub(N,frac(A));

lsInv = {};
for i from 1 to l do (
lsInv = append(lsInv,1/y_i);
);

I = ideal( sub( product(toList(y_1..y_l)) * (transpose N) * (transpose matrix {lsInv}), A) );

I = saturate(I,toList(y_1..y_l))

Hu = hurwitzForm(I);

AU = QQ[ gens ring ideal ring Hu, u_1..u_l]

Hu = sub(Hu,AU);

lsInvU = {};
for i from 1 to l do (
lsInvU = append(lsInvU,1/u_i);
);

M = transpose gens kernel (transpose Rhat);
Mu = sub(M * diagonalMatrix(lsInvU), frac(AU));
Mu = transpose Mu;

lsSubst = { y_(0,1,2) => det(submatrix(Mu,{0,1,2},)), y_(0,1,3) => det(submatrix(Mu,{0,1,3},)), y_(0,1,4) => det(submatrix(Mu,{0,1,4},)), y_(0,2,3) => det(submatrix(Mu,{0,2,3},)), y_(0,2,4) => det(submatrix(Mu,{0,2,4},)), y_(0,3,4) => det(submatrix(Mu,{0,3,4},)), y_(1,2,3) => det(submatrix(Mu,{1,2,3},)), y_(1,2,4) => det(submatrix(Mu,{1,2,4},)), y_(1,3,4) => det(submatrix(Mu,{1,3,4},)), y_(2,3,4) => det(submatrix(Mu,{2,3,4},)) };

HuDisc = sub(Hu,lsSubst)


--
N2 = gens kernel (transpose Rhat);

N2 = sub(N2,frac(A));

I2 = ideal( sub( product(toList(y_1..y_l)) * (transpose N2) * (transpose matrix {lsInv}), A) );

I2 = saturate(I2,toList(y_1..y_l))

Hu2 = hurwitzForm(I2);


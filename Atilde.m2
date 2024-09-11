d=2; n=d+2;
R = QQ[a_(d+2,1)..a_(n,d),b_(d+2)..b_n][x_0..x_d]; -- , Degrees=>{(d*(n-d-1)):0, (n-d-1):0, (d+1):1}
--R = QQ[a_(d+1,1)..a_(n,d),b_(d+1)..b_n,x_0..x_d, Degrees=>{(d*(n-d)):0, (n-d):0, (d+1):1}]; -- , Degrees=>{(d*(n-d-1)):0, (n-d-1):0, (d+1):1}
S = R[v_1..v_n];

A  = id_(S^d) | matrix toList(d:{1}) | genericMatrix(coefficientRing R,a_(d+2,1),d,n-d-1) -- To be understood as \tilde{A}^T
bA = matrix{toList(d:0) | {1} | toList(b_(d+2)..b_n)} || A
--A  = id_(S^d) | genericMatrix(R,a_(d+1,1),d,n-d) -- To be understood as \tilde{A}^T
--bA = matrix{toList(d:0) | toList(b_(d+1)..b_n)} || A


xx = id_(R^1) || (genericMatrix(R, x_1, d, 1))
l  = i -> ( (transpose bA)^{i-1} * xx)_0_0
dl = i -> (A^{i-1} * genericMatrix(S, v_1, n, 1))_0_0

complInN = A -> toList(set(0..n-1) - set(A))

h = sum(subsets(n,d), I -> product(I,i->v_(i+1))*det(A_I)^2*product(complInN I, i->l(i+1)))
htilde = sub(sub(h, for i from 1 to d list v_i=>(v_i - dl(i))), R[v_(d+1)..v_n])

--

needsPackage "Resultants";
di = discriminant htilde

dih = homogenize(di, x_0)

mons = genericMatrix(R,x_0,d+1,1)*genericMatrix(R,x_0,1,d+1)
Q = diff(mons, dih/2 )

J = radical minors(2,Q)

decompose J





















-------------

needs "splitForms.m2"
(I, mons) = idealOfSplitForms 2

htilde' = sub(htilde, QQ[a_(d+1,1)..a_(n,d),b_(d+1)..b_n][x_0..x_d,v_(d+1),v_(d+2)])
coefs = apply(mons, m->coefficient(sub(m,{x_0=>1}), htilde'))

phi = map(coefficientRing ring htilde', ring I, coefs)
decompose radical phi I
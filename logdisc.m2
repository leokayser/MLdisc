-----------------------------------
-- Convention:
-- (n+1) affine hyperplanes in AA^d
-- \ell(x_1..x_d) = Ax + b
-----------------------------------

needsPackage "Resultants";

essentialGenericArrangement = method();
essentialGenericArrangement (ZZ,ZZ) := (d,n) -> (
    R  := QQ[a_(d,1)..a_(n,d),b_(d)..b_n];
    A  := id_(R^d) || transpose genericMatrix(R,a_(d,1),d,n+1-d);
    bA := matrix( toList(d:{0}) | apply(toList(d..n), i->{b_i}) ) | A;
    return bA;
);

-- Convention for naming the minors:
-- (1 1  1 ... 1  1 0)
-- (1 x1 x2    xd 0 1)
--  0 1  2     d
-- This leads to the variable names
-- s_1=x1,...,s_d=xd,s_(0,1)=1-x1,...,s_(1,2)=x1-x2,...,s_(d-1,d)=x(d-1)-xd
M0nArrangement = method(Options => {Localize => false});
M0nArrangement (ZZ) := o -> m -> (
    d := m-3;
    constantMatrix := (r,c,x) -> matrix for i from 0 to r-1 list for j from 0 to c-1 list x;

    Mlower := fold( (A,B)->A||B, for i from 1 to d-1 list (k := d-i; constantMatrix(k,i,0) | constantMatrix(k,1,1) | -id_(QQ^k)) );
    M := (constantMatrix(d,1,0) | id_(QQ^d)) || (constantMatrix(d,1,-1) | id_(QQ^d)) || Mlower;

    n := numRows M - 1;

    return (M,QQ[s_1..s_d, flatten for i from 0 to d list for j from i+1 to d list s_(i,j), if o.Localize then y_0..y_n, x_1..x_d]);
);

--termTable = method(Options => {Factor => true});
termTable = f -> (
    coeff := coefficients f;
    return netList transpose ({flatten entries first coeff} | {flatten entries last coeff / factor});
);

likeRam = method(Options => {PolyRing => null, Localize => true, Substitute => false});
likeRam (Matrix) := o -> bA -> (
    R := if ring bA === ZZ then QQ else ring bA;
    A := submatrix'(bA,{},{0});
    d := numColumns(bA) - 1;
    n := numRows(bA) - 1;

    paramVar := if o.Substitute then v else u;
    S := if o.Localize then R[paramVar_0..paramVar_n,x_1..x_d,y_0..y_n] else R[paramVar_0..paramVar_n,x_1..x_d]; 
    paramVar = value(paramVar);

    xx := id_(S^1) || (genericMatrix(S, x_1, d, 1));
    linForms := flatten entries (bA * xx);
    uv := genericMatrix(S, paramVar_0, n+1, 1);

    likeEqs := if o.Substitute then (
        ideal( transpose A * uv )
    ) else if o.Localize then (
        ideal( transpose A * diagonalMatrix(toList(y_0..y_n)) * uv )
    ) else (
        ideal apply(flatten entries (transpose A * diagonalMatrix(apply(linForms, ell->1/ell)) * uv), numerator)
    );

    if o.Localize then likeEqs = likeEqs + ideal( for j from 0 to n list y_j * (linForms#j) - 1 );

    linFormExp := if o.Substitute then 1 else 2;
    hess := if o.Localize then (
        ideal sum( subsets(n+1,d), I -> det(A^I)^2 * product(I, j -> paramVar_j*y_j^linFormExp) )
    ) else (
        ideal sum( subsets(n+1,d), I -> det(A^I)^2 * product(I, j -> paramVar_j) * product(toList(set(0..n)-set(I)), j->(linForms#j)^linFormExp) )
    );

    ram := likeEqs + hess;

    return if instance(o.PolyRing,Nothing) then 
        ram
    else
        sub(ram, vars o.PolyRing)
    ;
);

logDisc = method(Options => {PolyRing => null});
logDisc (Matrix) := o -> bA -> (
    n := numRows(bA) - 1;
    d := numColumns(bA) - 1;
    ram := likeRam(bA, Substitute=>false, Localize=>true, PolyRing=>o.PolyRing);
    use ring ram;
    return eliminate(ram, join( toList(y_0..y_n), toList(x_1..x_d) ) );
);

-- Assumes bA starts with the linear forms x_1,...,x_d (i.e. starts as (0|Id_d))
htilde = method(Options => {PolyRing => null}); -- TODO? Homogenization not yet implemented.
htilde (Matrix) := o -> bA -> (
    n := numRows(bA) - 1;
    d := numColumns(bA) - 1;
    pols := flatten entries gens likeRam(bA, Substitute=>true, Localize=>false, PolyRing=>o.PolyRing);
    h := pols#d;
    g := gens ring h;
    S' := (coefficientRing ring h)[g_{(n+1)..(n+d)}][g_{d..n}];
    return sub( sub(h, for i from 0 to d-1 list g_i=>(g_i - pols#i)), S');
);

recLinSpace = method();
recLinSpace (Matrix) := B -> (
    n := numRows(B) - 1;
    R := QQ[y_0..y_n];
    N := gens ker transpose B;
    lsInv := matrix for i from 0 to n list {product(toList(set(0..n)-set({i})), j->y_j)};
    I := ideal( (transpose N) * lsInv);
    return saturate(I, toList(y_0..y_n));
)

end
hurwitzDisc = method();
hurwitzDisc (Matrix) := bA -> (
    bA := matrix(QQ,{{0,1,0},{0,0,1},{1,1,1},{1,2,3}})
    n := numRows(bA) - 1;
    I := recLinSpace bA;
    hu := hurwitzForm I;
    
    
    AU := QQ[ gens ring ideal ring hu, u_0..u_n];

    Hu = sub(hu,AU);

    lsInvU := for j from 0 to n list 1/u_j;

    M = transpose gens ker (transpose submatrix'(bA,{},{0}));
    Mu = sub(M * diagonalMatrix(lsInvU), frac(AU));
    Mu = transpose Mu;

    lsSubst = { y_(0,1,2) => det(submatrix(Mu,{0,1,2},)), y_(0,1,3) => det(submatrix(Mu,{0,1,3},)), y_(0,1,4) => det(submatrix(Mu,{0,1,4},)), y_(0,2,3) => det(submatrix(Mu,{0,2,3},)), y_(0,2,4) => det(submatrix(Mu,{0,2,4},)), y_(0,3,4) => det(submatrix(Mu,{0,3,4},)), y_(1,2,3) => det(submatrix(Mu,{1,2,3},)), y_(1,2,4) => det(submatrix(Mu,{1,2,4},)), y_(1,3,4) => det(submatrix(Mu,{1,3,4},)), y_(2,3,4) => det(submatrix(Mu,{2,3,4},)) };

    HuDisc = sub(Hu,lsSubst)

    return hu;
)

end
restart
load "logdisc.m2"

bA = matrix(QQ,{{0,1,0},{0,0,1},{0,1,-1},{-1,1,0},{-3,0,1},{1,2,-1}})
gbTrace = 1
I = logDisc bA

(M,S) = M0nArrangement(5, Localize=>true)
nabla = (logDisc(M, PolyRing=>S))_0

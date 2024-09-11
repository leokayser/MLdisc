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

M0nArrangement = method();
M0nArrangement (ZZ) := n -> (
    constantMatrix := (r,c,x) -> matrix for i from 0 to r-1 list for j from 0 to c-1 list x;
    M := fold( (A,B)->A||B, for i from 0 to n-4 list (k := n-i-3; constantMatrix(k,i,0) | constantMatrix(k,1,1) | -id_(QQ^k)) );
    return (constantMatrix(n-3,1,0) | id_(QQ^(n-3))) || M;
);

--termTable = method(Options => {Factor => true});
termTable = f -> (
    coeff := coefficients f;
    return netList transpose ({flatten entries first coeff} | {flatten entries last coeff / factor});
);

likeRam = method(Options => {Localize => true, Substitute => false});
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
    
    return (likeEqs + hess);
);

logDisc = method();
logDisc (Matrix) := bA -> (
    n := numRows(bA) - 1;
    d := numColumns(bA) - 1;
    ram := likeRam(bA, Substitute=>false, Localize=>true);
    return eliminate(ram, join( toList(y_0..y_n), toList(x_1..x_d) ) );
);

-- Assumes bA starts with the linear forms x_1,...,x_d (i.e. starts as (0|Id_d))
htilde = method(); -- TODO? Homogenization not yet implemented.
htilde (Matrix) := bA -> (
    n := numRows(bA) - 1;
    d := numColumns(bA) - 1;
    pols := flatten entries gens likeRam(bA, Substitute=>true, Localize=>false);
    h := pols#d;
    S':= (coefficientRing ring h)[x_1..x_d][v_d..v_n];
    return sub( sub(h, for i from 0 to d-1 list v_i=>(v_i - pols#i)), S' );
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

bA = M0nArrangement 7
termTable htilde bA

netList transpose ({flatten entries first coefficients h} | {flatten entries last coefficients h / factor})

netList {flatten entries (bA * ( matrix{{1}} || (genericMatrix(coefficientRing ring h, x_1, 3, 1)) ))}
    linForms := flatten entries (bA * xx);

nabla = logDisc bA

f = sub(nabla, QQ[u_0..u_4, Weights=>{1,0,1,0,0}])
inF = (leadTerm(1,f))_0_0





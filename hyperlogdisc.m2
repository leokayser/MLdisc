needsPackage "Polyhedra"

--randInh = d -> sub(random(d,ZZ[t_0..t_n]), matrix{{1} | toList(x_1..x_n)})
--randH = d -> sub(random(d,ZZ[t_1..t_n]), matrix{toList(x_1..x_n)})

logDisc = method()
logDisc (RingElement) := g -> (
    --ell = {f} | (for i from 1 to n list x_i);
    R := ring g;
    n := numgens R;
    Rbig := (coefficientRing R)[gens R, u_0..u_n,y_0..y_n];
    f := sub(g,Rbig);

    ell := {f,x_1,x_2};

    likeCor := ideal for i from 1 to n list sum(n+1, j -> u_j*diff(x_i,ell#j)*y_j);
    loc := ideal for j from 0 to n list ell#j * y_j - 1;

    loghess := diagonalMatrix(for i from 1 to n list -u_i/x_i^2) + matrix for i from 1 to n list for k from 1 to n list u_0*(diff(x_k,diff(x_i,f))*f - diff(x_i,f)*diff(x_k,f))/(f^2);
    h := numerator det loghess;
    uRing := (coefficientRing R)[(gens Rbig)_(toList(n..(2*n)))]; print uRing;
    return sub(eliminate(likeCor + loc + ideal(h), toList(y_0..y_n) | toList(x_1..x_n)), uRing);
)

fromListForm = method()
fromListForm (Ring,List) := (R,l) -> (
    xx := gens R;
    return sum(l, (expv,coef) -> coef * product(xx,expv, (x,e) -> x^e));
)

randomPolynomialWithSupport = method(Options=>{Height=>10})
randomPolynomialWithSupport (Ring,Polyhedron) := o -> (R,P) -> (
    exps := (flatten@@entries) \ latticePoints P;
    C := coefficientRing R;
    lf := apply(exps, expv -> (expv, random(C, Height=>o.Height) ));
    return fromListForm(R,lf);
)

end
restart
n = 2;
R = ZZ/101[x_1..x_n];
load "hyperlogdisc.m2"

P = newtonPolytope(x_1+x_2+x_1^2+x_2^2); latticePoints P
f = randomPolynomialWithSupport(R,P)
logDisc f


fromListForm(R, listForm f)

-------
f = (x_1+x_2+1)*(-x_1+x_2-2) + z
nabla = logDisc f
nabla0 = logDisc(sub(f,{z=>0}))
I = ideal(sub(nabla_0, {z=>0}) // u_0^2)
tex oo
I == nabla0

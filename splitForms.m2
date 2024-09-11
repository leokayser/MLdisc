
idealOfSplitForms = (d,d2) -> (
    S := QQ[a_(0,0)..a_(d-1,d),b_0..b_1, Degrees=>{(d*(d+1)+2):0}][x_0..x_d,v_(d+1),v_(d+2), Degrees=>{(d+1):{1,0}, 2:{0,1}}];
    
    genForm := sum(0..(d-1), i->sum(0..d, j->a_(i,j)*x_j) * v_(d+1)^(d-1-i)*v_(d+2)^i);

    genSplit := genForm * (b_0*v_(d+1) + b_1*v_(d+2));

    monbasis := flatten entries basis({1,d},S);

    R := QQ[t_0..t_(#monbasis-1)];

    phi := map(coefficientRing S, R, for i from 0 to #monbasis - 1 list coefficient(monbasis#i, genSplit));

    return (ideal mingens ker phi, monbasis);
)
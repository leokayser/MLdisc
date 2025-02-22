stuff = f -> (
    R := QQ[gens ring f, y, u];
    I := ideal(sub(f,R), y^2, u^3+42);
    J := eliminate({R_0, y}, I);
    return sub(J, QQ[u]);
)

S = QQ[x]
f = x^2+1
stuff f
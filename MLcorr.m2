R = QQ[p_(0,0)..p_(1,1),u_(0,0)..u_(1,1), Degrees=>toList(4:{1,0}) | toList(4:{0,1})]
pplus = sum((gens R)_{0..3})
uplus = sum((gens R)_{4..7})
H = ideal(product((gens R)_{0..3})*pplus)

X = ideal(det genericMatrix(R,2,2))
dlog = ideal(apply((0,0)..(1,1), i -> H_0*u_i//p_i - H_0*uplus//pplus))
LX = saturate(X + dlog, H)

U = matrix{
    {0,               -u_(1,0)-u_(1,1), 0,                u_(0,0)+u_(0,1)},
    {u_(1,1)+u_(0,1), -u_(0,0)-u_(1,0), 0,                0              },
    {u_(1,1)+u_(1,0), 0,                -u_(0,1)-u_(0,0), 0              },
    {0,               0,                -u_(0,1)-u_(1,1), u_(0,0)+u_(1,0)}
}
bernd = ideal(U * transpose matrix{{p_(0,0), p_(0,1), p_(1,0), p_(1,1)}})
isSubset(bernd, LX)
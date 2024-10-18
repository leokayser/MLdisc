n = 3
KK = frac (QQ[b_2..b_n])
S = KK[u_0..u_n,y_0..y_n,x]
c = {0,1} | apply(toList(2..n), i->b_i)
R = matrix for i to n list {c_i,1}
ell = for i to n list R_(i,1)*x + R_(i,0)

dlog = sum(1..n, i->u_i*y_i)
hess = sum(1..n, i->u_i*y_i^2)
locl = ideal(for i from 1 to n list y_i*ell_(i-1)-1)
--locb =  ideal(e*product(subsets(0..n,2), T -> c_(T_1)-c_(T_0))-1)

likeCorRam = ideal(dlog, hess) + locl
IDisc = eliminate({x} | toList(y_1..y_n), likeCorRam)
Disc = (entries mingens IDisc)#0#0
S' = KK[u_1..u_n]
Disc = sub(Disc, S')
loadPackage "Resultants"
discriminant Disc


coef = flatten entries (coefficients Disc)#1
mons = flatten entries (coefficients Disc)#0
netList( {mons} | {coef} )
# factor Disc
ideal diff(transpose vars S', Disc)
--Universal discriminant!
-- n < 4: Empty.
-- n = 4:
   (b-1)² * u0^2
+ 2b(b-1) * u0u1
+      b² * u1^2
-  2(b-1) * u0u2
+      2b * u1u2
+       1 * u2^2
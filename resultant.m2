n = 2
B = QQ[b_2..b_n]
use B[u_0..u_n][x]
c = {0,1} | apply(toList(2..n), i->b_i)

ind = toList(0..n)
g = e -> sum(ind, i -> u_i * product( toList(set(ind) - {i}), j ->  (x - c_j)^e));

s = resultant(g(1),g(2),x);
T = factor s


--f1 = sum(ind, i -> u_i * product( toList(set(ind) - {i}), j ->  x - b_j));   
--f2 = sum(ind, i -> u_i * product( toList(set(ind) - {i}), j -> (x - b_j)^2));
--r = resultant(f1,f2,x); factor r
--sub(r, {b_0=>0, b_1=>1}) == s
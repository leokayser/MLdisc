n = 2
R = QQ[z,u_0..u_n,x_1..x_n,y_0..y_n]

randInh = d -> sub(random(d,ZZ[t_0..t_n]), matrix{{1} | toList(x_1..x_n)})
randH = d -> sub(random(d,ZZ[t_1..t_n]), matrix{toList(x_1..x_n)})

logDisc = f -> (
    ell = {f} | (for i from 1 to n list x_i);

    likeCor = ideal for i from 1 to n list sum(n+1, j -> u_j*diff(x_i,ell#j)*y_j);
    loc = ideal for j from 0 to n list ell#j * y_j - 1;

    loghess = diagonalMatrix(for i from 1 to n list -u_i/x_i^2) + matrix for i from 1 to n list for k from 1 to n list u_0*(diff(x_k,diff(x_i,f))*f - diff(x_i,f)*diff(x_k,f))/(f^2);

    h = numerator det loghess;

    return eliminate(likeCor + loc + ideal(h), toList(y_0..y_n) | toList(x_1..x_n));
)


end
restart
load "hyperlogdisc.m2"

f = (x_1+x_2+1)*(2*x_1-3*x_2+5) + z
nabla = logDisc f
nabla0 = logDisc(sub(f,{z=>0}))
I = ideal(sub(nabla_0, {z=>0}) // u_0^2)
I == nabla0
logDisc randInh()
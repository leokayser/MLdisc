using HomotopyContinuation
using Oscar

d = 2
l = 4

K = QQ
RR, vrs = polynomial_ring(K,vcat(["x$i" for i = 1:d+1], ["y$i" for i = 1:l]))
x,y = vrs[1:d+1],vrs[d+2:d+1+l]

R = rand(-10:10,l,d+1)
r = R*x

X_R_inc = ideal([r[i]*y[i] - 1 for i in eachindex(y)])

X_R = eliminate(X_R_inc, x)



@var t[1:2,1:2]
#@var v[1:2]
#F= [Rec; [X[1];X[2]]+t*[X[3];X[4]]]
#J = differentiate(F,X)[:,1:3]
#K = GF(1993)
nsamples = 550
samples = []
samples_XR = []
for i = 1:nsamples
    aux = K.(R*(rand(1:50,3).//rand(1:10,3)))
    if sum(aux.==zero(K)) > 0
        i = i-1
        continue
    end
    push!(samples_XR, 1 .// aux)
end
samples_XR

function HC_to_oscar_Q(f,vars,HC_vars,K)
    E,C = exponents_coefficients(f,HC_vars)
    sum([K(C[i])*prod(vars.^E[:,i]) for i = 1:length(C)])
end

RR, x = polynomial_ring(K,["x$i" for i = 1:4])
Rec = HC_to_oscar_Q(Rec[1],x,X,K)

for s in samples_XR
    v = K.([Oscar.evaluate(derivative(Rec,x[i]),s) for i = 1:4])
    k = K.([v[2] -v[1] 0 0; 0 v[3] -v[2] 0; 0 0 v[4] -v[3]])
    t_mtx = matrix_space(K,2,4)([transpose(s);rand(-10:10,1,3)*k])
    #u_mtx = transpose(nullspace(t_mtx)[2])
    u_mtx = t_mtx
    try 
        u_mtx = inv(u_mtx[:,1:2])*u_mtx
        push!(samples,[u_mtx[1,3];u_mtx[2,3];u_mtx[1,4];u_mtx[2,4]])
        #push!(samples,minors(u_mtx,2))
    catch 
    end
end


deg = 8
#@var p[1:6]
#E, C = exponents_coefficients((sum(p))^deg, p[:])
E, C = exponents_coefficients((1+sum(t))^deg, t[:])
Vdm = transpose(hcat([[prod(s.^E[:,i]) for i = 1:size(E,2)] for s in samples]...))
#using LinearAlgebra
MS = matrix_space(K,size(Vdm)...);
Vdm_osc = MS(Vdm);
ns = nullspace(Vdm_osc)[2]


Rt, t = polynomial_ring(K,["t$i" for i = 1:4])
mons = [prod(t[:].^E[:,i]) for i = 1:size(E,2)];
Hu_t = dot(mons,ns)
Rp, p = graded_polynomial_ring(K,["p12";"p13";"p14";"p23";"p24";"p34"])
p12,p13,p14,p23,p24,p34 = p
Kp = fraction_field(Rp)
Hu_p = Oscar.evaluate(Hu_t,[-p23//p12;p13//p12;-p24//p12;p14//p12])
I = ideal([numerator(Hu_p),p12*p34 - p13*p24 + p14*p23])
E = saturation(I, ideal([p12]))
Hu = minimal_generating_set(E)[2]



J = ideal([p23,p24,p34])^2

is_subset(ideal([Hu]),J)


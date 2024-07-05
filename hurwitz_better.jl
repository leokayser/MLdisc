using Oscar
using LinearAlgebra

d, l = 3, 5
range = -10:10
A = rand(range,l,d+1)


function ϕ(x)
    1 .// (A*[1;x])
end

function J(x)
    -diagm(ϕ(x).^2)*A
end

function ψ(x,v,N)
    transpose( [ϕ(x) J(x)*v N] )
end

nsamples = 1000

mtcs = []
for i in 1:nsamples
    x = []
    while true
        x = rand(range,d)
        if prod(A*[1;x]) != 0
            break
        end
    end
    push!(mtcs, ψ(x,rand(range,d+1),rand(range,l,l-d-2)))
end



degree_hur = 2*binomial(l-1,d-1)*(l-1-d)

# Compute a basis for K[ϕ]_d, the degree d part of the algebra K[ϕ].
# The first output is the basis, the second the vector with the leading exponents of the elements in the basis
function get_basis(ϕ,d,K,vars,leadexps)
    vars_t = ["t$i" for i = 1:length(ϕ)]
    S, t = PolynomialRing(K, vars_t)
    allmons = collect(Oscar.monomials(sum(t)^d)) #all monomials in t of degree d
    allexps = collect(Oscar.exponents(sum(t)^d)) #all exponents of monomials in t of degree d
    latticepoint = [ allexps[i]'*leadexps    for i=1:length(allexps)  ] #all d-sum of elements in leadexps
    mons_in_dP = [prod(vars.^lp) for lp in latticepoint]  #monomials with exponent in latticepoint
    mons_in_dP_unique = unique(mons_in_dP)
    leadmons = [prod(vars.^e) for e in leadexps]
    aux = [findfirst(mon-> Oscar.evaluate(mon,leadmons) == mymon, allmons) for mymon in mons_in_dP_unique]
    return allexps[aux] #allexps[aux][i]:= allexps[aux[i]]
end

# It returns the plucker relations of the Grassmannian Gr(k,m),
# i.e. kxk minors of matrix with identity on the left and variables on the right( I_k | t_i )
function plückercoordinates(k,m,K)
    n=k*(m-k)
    varstring = ["t$i" for i =1:n];
    R, t = PolynomialRing(K, varstring)
    vrs = t
    MS = MatrixSpace(R,k,m)
    M = Int64.(diagm(ones(k))).+0*t[1]
    M = R.(hcat(M, reshape(t,k,m-k)))
    M = MS(M)
    ϕ = minors(M,k);
    return R,ϕ,vrs,M
end

# Compute the leading exponent of f with respect to the weight vector w.
function leadexp(f,w)
    exps = collect(exponents(f))
    weights = [dot(w,e) for e in exps]
    lm = argmin(weights)
    exps[lm]
end

R,p,vrs,M = plückercoordinates(l-d,l,QQ)
w = [-1 for i=1:length(vrs)];
leadexps = [leadexp(hh,w) for hh in p]
HF_Gr(l-d,l,degree_hur)
B = get_basis(p,degree_hur,QQ,vrs,leadexps)

# Hilbert function of Grassmannian Gr(k,m)
function HF_Gr(k,m,t)
    prefac=prod([factorial(i) for i=1:k-1])//(prod([factorial(m-i) for i=1:k]))
    return Int(prefac*(prod([prod([t+i+l for l=0:m-k-1]) for i=1:k])))
end

varstring = []
indsvec = subsets(l,l-d)
for i = eachindex(indsvec)
    ind = indsvec[findfirst(k->det(M[:,k])==p[i],indsvec)]
    push!(varstring,"p$(ind)")
end
varstring = convert(Vector{String},varstring)
Gr, pluck = polynomial_ring(QQ,varstring)

mons = [prod(pluck.^b) for b in B]

MS = matrix_space(QQ,l-d,l)
samples = [minors(MS(mtx),l-d) for mtx in mtcs]

Vdm = transpose(hcat([[evaluate(m,s) for m in mons] for s in samples]...))
ns = nullspace(matrix_space(QQ,size(Vdm)...)(Vdm))[2]

Hu = (transpose(ns)*mons)[1]


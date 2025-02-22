# Authors: Leonie Kayser, Andreas Kretschmer, Simon Telen
# Date: October 11, 2024
# Description: 
#   This code accompanies the paper "Logarithmic discriminants of hyperplane arrangements". 
#   A demo of the functionality is included at the bottom of the file. 
#   The runs in Julia v1.11 and uses the following packages: 
#       HomotopyContinuation v2.9.5
#       IterTools v1.10.0

using HomotopyContinuation
using LinearAlgebra
using IterTools

# Generate the matrix L associated to the hyperplane arrangement whose complement is M_{0,m}.
# Input: m 
# Output: L
function get_L_M0m(m)
    inds = collect(IterTools.subsets(1:m-2,2))
    L = zeros(Int,m-2,m-3+length(inds))
    L[2:end,1:m-3] = diagm(ones(Int,m-3))
    for i = 1:length(inds)
        L[inds[i],m-3+i] = [-1;1]
    end
    return L
end

# Compute equations for (a dense subset of) the Ramification locus of the projection of the
# likelihood correspondence to parameter space. 
# Input: L
# Output: Ram - the desired equations
#         u, x, y, v - all HomotopyContinuation variables used in Ram 
function get_Ramification(L)
    A = L[2:end,:]
    d, n = size(L).-(1,1)
    @var u[1:n+1] x[1:d] y[1:n+1] v[1:d]
    ℓ = [1 transpose(x)]*L
    LE = [[y[i]*ℓ[i]-1 for i =1:n+1];A*diagm(u)*y] # likelihood equations    
    Hess = A*diagm(-u.*(y.^2))*transpose(A) # Hessian matrix
    # The ramification locus is defined by LE and Hess*v = 0, where the latter encodes 
    # that the Hessian determinant has determinant zero. 
    return [LE;Hess*v; dot(randn(ComplexF64,d),v)-1], u, x, y, v
end


# Compute the degree of the logarithmic discriminant of L (assuming it is a hypersurface).
# Input: L
# Output: The number of intersections of the logarithmic discriminant with a generic line. 
#         This intersection is computed using numerical homotopy continuation. 
function get_deg_DeltaLog(L)
    d, n = size(L).-(1,1)
    Ram, u, x, y, v = get_Ramification(L)
    @var t
    myc = randn(ComplexF64,n+1)
    myd = randn(ComplexF64,n+1)
    param =  myc + t.*myd # a random parametric line
    R = HomotopyContinuation.solve(System(subs(Ram,u=>param), variables = [t;v;x;y]))
    uvals = [HomotopyContinuation.evaluate(System(param),[sol[1]]) for sol in solutions(R)]
    return length(unique_points(uvals)) 
end

# Attempts to compute the logarithmic discriminant of the matrix L. 
# Input: L
# Output: The logarithmic discriminant polynomial of L. 
function get_DeltaLog(L)
    d, n = size(L).-(1,1)
    Ram, u, x, y, v = get_Ramification(L)
    @var t
    myc = randn(ComplexF64,n+1)
    myd = randn(ComplexF64,n+1)
    param =  myc + t.*myd # a random parametric line
    R = HomotopyContinuation.solve(System(subs(Ram,u=>param), variables = [t;v;x;y]))
    uvals = [HomotopyContinuation.evaluate(System(param),[sol[1]]) for sol in solutions(R)]
    deg = length(unique_points(uvals))
    nsamples = Int(round(binomial(n + deg, deg)*1.3))
    @var c[1:n+1] dd[1:n+1]
    F = System(subs(Ram,u=> c + t.*dd), parameters = [c;dd])
    paramSys = System(c+t.*dd, variables = [t;c;dd])
    samples = uvals
    while length(samples) < nsamples
        newc = randn(ComplexF64,(n+1))
        newd = randn(ComplexF64,(n+1))
        newR = HomotopyContinuation.solve(F,solutions(R); start_parameters = [myc;myd], target_parameters = [newc;newd])
        newuvals = [HomotopyContinuation.evaluate(paramSys,[sol[1];newc;newd]) for sol in solutions(newR)]
        push!(samples,unique_points(newuvals)...)
    end
    E, C = exponents_coefficients(sum(u)^deg,u)
    mons = [prod(u.^E[:,i]) for i = 1:size(E,2)]
    Vdmrows = [[prod(s.^E[:,i]) for i = 1:size(E,2)] for s in samples]
    Vdmrows = [v/norm(v) for v in Vdmrows]
    Vdm = transpose(hcat(Vdmrows...))
    ns = nullspace(Vdm)
    real_ns = real.(ns/ns[argmax(abs.(ns))])
    real_error = norm(real.(ns/ns[argmax(abs.(ns))])-ns/ns[argmax(abs.(ns))])
    rat_ns = rationalize.(real_ns,tol=1e-10)
    rat_error = norm(rat_ns-real_ns)
    LCM = lcm(denominator.(rat_ns))
    int_ns = Int.(LCM*rat_ns)
    disc = dot(int_ns,mons)
end




# Here is a short demo of the functionality. 
L = get_L_M0m(7) # the matrix of M07
deg = get_deg_DeltaLog(L) # 208

L = get_L_M0m(5) # the matrix of M05
Δ = get_DeltaLog(L) # the discriminant in Example 1.1

L = [-1 0 1;
      1 1 1] # The arrangement in Example 3.3
deg = get_deg_DeltaLog(L) # 4 - the degree of the codimension-one part of ∇
Δ = get_DeltaLog(L) # the discriminant in Example 3.3
module NCImpls
export NCImpl,BearerMultiset, bearers, isempty, testy, subpart

using StaticArrays
using StructEquality, Combinatorics

abstract type PairWrapper{N,T} end
getvalue(i::PairWrapper{N,T}) where {N,T} = (i.prem, i.conc)

⊂(x,y) = x != y && x ⊆ y

"""
A BearerMultiset is a fixed-length vector representing the number of times
each bearer in the language appears in a given claim. E.g. if L = [a,b,c] 
thenthe multiset set {a,a,c} is represented by [2,0,1].
"""
@struct_hash_equal struct BearerMultiset{N}
    value::SVector{N, Int}
    BearerMultiset{N}(v::SVector{N,Int}=SVector{N, Int}) where {N} = new{N}(v)
end

"""Empty multiset is the zero vector"""
BearerMultiset(N::Int) = BearerMultiset{N}(SVector{N,Int}(zeros(Int, N)...))


"""Give the vector directly"""
function BearerMultiset(v::Vector{Int})
    N = length(v)
    BearerMultiset{N}(SVector{N,Int}(v...))
end

Base.getindex(bm::BearerMultiset{N}, idx::Integer) where {N} = bm.value[idx]

# index-wise comparison: true if i[k] <= j[k] for all positions
function Base.isless(i::BearerMultiset{N}, j::BearerMultiset{N}) where N
    return all(i[k] <= j[k] for k in 1:N)
end

Base.isempty(i::BearerMultiset{N}) where N = all(i[k] == 0 for k in 1:N)

function Base.show(io::IO, ::MIME"text/plain", i::BearerMultiset{N}) where N
    if isempty(i)
        print(io, "∅")
    else
        letters = [Char('a' + k - 1) for k in 1:N]
        syms = [string(letters[k]) for k in 1:N for _ in 1:i.value[k]]
        print(io, join(syms, ","))
    end
end

Base.string(i::BearerMultiset) = sprint(show, "text/plain", i)

"""
An implication is a pair of BearerMultisets of L, represented as fixed-length 
vectors of integers. If |L| = n, then the length of each vector component of 
an implication i is n. The first vector, i.prem, consists of the positive 
(premisory) claimables.The second vector, i.conc, consists of the negative 
(conclusory) claimables. E.g. if L = [a,b], then a,b,b ⊢ a,a is the pair 
([1,2],[2,0]).
"""
@struct_hash_equal struct NCImpl{N} # <: PairWrapper{N, Int}
    prem::BearerMultiset{N}
    conc::BearerMultiset{N}
    NCImpl{N}(p::BearerMultiset{N}=BearerMultiset{N}(), q::BearerMultiset{N}=BearerMultiset{N}()) where {N} = new{N}(p,q)
end

"""Give the implication as two vectors"""
function NCImpl(p::Vector{Int}, q::Vector{Int})
    N = length(p)
    length(q) == N || error("prem and conc must have same length, got $(length(p)) and $(length(q))")
    NCImpl{N}(BearerMultiset(p), BearerMultiset(q))
end

 
"""Give the implication as two multisets"""
function NCImpl(p::BearerMultiset{N}, q::BearerMultiset{M}) where {N,M}
    M == N || error("prem and conc must have same length, got $(N) and $(M)")
    NCImpl{N}(p, q)
end

"""The empty implicaiton is two empty BearerMultisets"""
NCImpl(N::Int) = NCImpl{N}(BearerMultiset(N),BearerMultiset(N))

# info about implications
Base.isempty(i::NCImpl{N}) where N = all(i[k] == 0 for k in 1:N)

"""Gives the number of bearers"""
bearers(::NCImpl{N}) where N = N

function Base.show(io::IO, ::MIME"text/plain", i::NCImpl{N}) where N
    letters = [Char('a' + k - 1) for k in 1:N]
    if isempty(i.prem)
        prem_syms = "∅"
    else
        prem_syms = [string(letters[k]) for k in 1:N for _ in 1:i.prem[k]]
    end
    if isempty(i.conc)
        conc_syms = "∅"
    else
        conc_syms = [string(letters[k]) for k in 1:N for _ in 1:i.conc[k]]
    end
    print(io, join(prem_syms, ","), " ⊢ ", join(conc_syms, ","))
end

Base.string(i::NCImpl) = sprint(show, "text/plain", i)

subpart(i1::NCImpl, i2::NCImpl) = i1.prem ≤ i2.prem && i1.conc ≤ i2.conc


function Base.union(impls::Vector{NCImpl{N}}) where N
    isempty(impls) && return NCImpl{N}()
    prems = map(impl -> impl.prem.value, impls)
    concs = map(impl -> impl.conc.value, impls)
    sum_prem = reduce(+, prems)
    sum_conc = reduce(+, concs)
    NCImpl{N}(BearerMultiset{N}(sum_prem), BearerMultiset{N}(sum_conc))
end

Base.union(i::NCImpl{N}...) where N = union(collect(i))

end # module    

module Impls 
export Impl, bearers, prem, conc, has_prem, has_conc, impl_dict, impl_vec, ⊂,
       getvalue

using StructEquality, Combinatorics
import GATlab: getvalue 


const Maybe{T} = Union{Nothing, T}

"""Many types in ROLE.jl are just simple wrappers around a BitSet"""
abstract type BitSetWrapper end 
getvalue(i::BitSetWrapper) = i.value
Base.length(i::BitSetWrapper) = length(getvalue(i))
Base.push!(i::BitSetWrapper, x::Int) = push!(getvalue(i), x)
Base.filter(f, i::BitSetWrapper) = filter(f, getvalue(i))
Base.iterate(i::BitSetWrapper, x...) = iterate(getvalue(i), x...)
Base.in(i::Int, r::BitSetWrapper) = i ∈ getvalue(r)
Base.issubset(i1::BitSetWrapper, i2::BitSetWrapper) = 
  issubset(getvalue(i1), getvalue(i2))

⊂(x,y) = x != y && x ⊆ y # strict subset relation

# Implications (and incompatibilities)
######################################

"""
An implication is a subset of L+L, where the first half are the positive 
(premisory) claimables and the second are negative (conclusory) claimables.

E.g. if L+L = [1=a⁺,2=a⁻,3=b⁺,4=b⁻], then  a,b ⊢ b is the bitset 1011

The number of bearers is in the type parameter because at times we want the 
maximal value of the type (e.g. the unit for intersection). 
"""
@struct_hash_equal struct Impl{N} <: BitSetWrapper
  value::BitSet
  Impl{N}(b::BitSet=BitSet()) where N = new{N}(b)
end

bearers(::Impl{N}) where N = N

"""Empty implication on N bearers"""
Impl(N::Int) = Impl{N}(BitSet())

"""Give bitset directly, number of bearers as an argument"""
Impl(p1::AbstractVector, N::Maybe{Int}=nothing) = 
  Impl{isnothing(N) ? div(max(0, p1...),2,RoundUp) : N}(BitSet(Vector{Int}(p1)))

"""
Specify an implication by giving the premises and conclusions explicitly.
"""
function Impl(p1::AbstractVector, p2::AbstractVector, N::Maybe{Int}=nothing) 
  Impl([[x*2-1 for x in p1]; [x*2 for x in p2]], N)
end

"""Which bearers are premises"""
prem(i::Impl{N}) where N = [j for j in 1:N if j*2-1 ∈ i]

"""Which bearers are conclusions"""
conc(i::Impl{N}) where N = [j for j in 1:N if j*2 ∈ i]

has_prem(i::Impl, x::Int) = x*2-1 ∈ i

has_conc(i::Impl, x::Int) = x*2 ∈ i

overlap(i::Impl) = !isempty(prem(i) ∩ conc(i))

function Base.show(io::IO, ::MIME"text/plain", i::Impl{N}) where N
  print(io, "$(join(prem(i),",")) ⊢ $(join(conc(i),","))")
end

Base.isless(i₁::Impl, i₂::Impl) = getvalue(i₁) ≤ getvalue(i₂)

Base.string(i::Impl) = sprint(show, "text/plain", i)

Base.isempty(i::Impl) = isempty(getvalue(i))

Base.union(i::Vector{Impl{N}}) where N = 
  isempty(i) ? Impl{N}() : Impl{N}(union(getvalue.(i)...))

Base.union(i::Impl{N}...) where N = union(collect(i))

Base.union!(i::Impl{N}, j::Impl{N}...) where N = 
  union!(getvalue(i), getvalue.(j)...)

function Base.replace(i::Impl{N}, p::Pair{Int,Int})::Impl{N} where N
  Impl(replace(prem(i), p), replace(conc(i), p), N)
end

# Caching a linear order of implications
########################################

"""Cache, for a given L, the bidirectional mapping of 𝒫(L+L) to implications"""
const ImpDict = Dict{Int, Pair{Vector{Impl}, Dict{Impl, Int}}}()

"""Cache which implications are implied to be good by containment"""
const CONTAINMENT = Dict{Int, BitSet}()

""" 
Get the i'th implication in the ordered set of all possible implications, 𝒫(L+L)
"""
@inline impl_vec(i::Int) = ImpDict[i][1]

"""
Get the (linear) index of a particular implication in the ordered set 𝒫(L+L)
"""
@inline impl_dict(i::Int) = ImpDict[i][2]

"""
Compute an order on the set of possible implications on `i` bearers.
"""
function compute_impldict!(i::Int)::Pair{Vector{Impl}, Dict{Impl, Int}}
  imps = Impl{i}.(BitSet.(Vector{Int}.(powerset(1:2*i))))
  CONTAINMENT[i] = BitSet([i for (i,j) in enumerate(imps) if overlap(j)])
  ImpDict[i] = imps => Dict(j=>i for (i,j) in enumerate(imps))
end

end # module

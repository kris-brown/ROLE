"""
We assume that all reason relations satisfy containment and that all explicit
Implication instances are *not* implications which have intersection between
premises and conclusions.
"""
module ImpFrames
export ImpFrame, rsr

using Combinatorics, PrettyTables, Random
using StatsBase: sample

const imap = Iterators.map
const ifilter = Iterators.filter
const iflatten = Iterators.flatten

using ..Impls, ..ImplSets
using ..Impls: BitSetWrapper, Maybe, ImpDict, compute_impldict!, CONTAINMENT
import ..Impls: prem, conc, bearers


# Implication frames
####################
function compute_rolelattice end # will be implemented in Roles.jl 

""" 
Most basic representation of an implication frame on a set of bearers 1:N 

The distinguished subset of good implications (incoherent sets of acceptances 
and rejections) 𝕀 is stored in the `value` field.
"""
struct ImpFrame{N} <: BitSetWrapper
  value::ImplSet{N}
  names::Vector{Symbol}

  function ImpFrame{N}(I, names::Maybe{Vector{Symbol}}=nothing) where N
    iframe = new{N}(I, isnothing(names) ? Symbol.(string.(1:N)) : names)
    haskey(ImpDict, N) || compute_impldict!(N) # compute this and cache
    compute_rolelattice(iframe) # compute this automatically and cache
    iframe
  end
end

Base.:(==)(i::ImpFrame{N}, j::ImpFrame{N}) where N = getvalue(i) == getvalue(j)
Base.hash(i::ImpFrame) = hash(getvalue(i))

"""
Give an implication frame via a list of sequents.

We assume the empty sequent is in this set.

Optionally specify the size of L
"""
function ImpFrame(xs::AbstractVector{<:Pair}, N::Int; names=nothing, containment=false)
  haskey(ImpDict, N) || compute_impldict!(N) # compute this and cache
  id = impl_dict(N)
  I = BitSet([id[Impl(x...,N)] for x in xs])
  containment && union!(I, CONTAINMENT[N])
  push!(I, 1) # assume empty sequent
  ImpFrame{N}(ImplSet{N}(I), names)
end


function ImpFrame(xs::AbstractVector{<:Pair}, names::AbstractVector{Symbol}; containment=false)
  dic = Dict(k=>v for (v, k) in enumerate(names))
  xs′ = map(xs) do (p, c)
    getindex.(Ref(dic), p) => getindex.(Ref(dic), c)
  end
  ImpFrame(xs′, length(names); names, containment)
end

bearers(::ImpFrame{N}) where N = N

function Base.show(io::IO, ::MIME"text/plain", r::ImpFrame{N}) where N 
  names = [join(string.(r.names[x]), ",") for x in powerset(1:N)]
  println(io, pretty_table(String, reduce(hcat, map(powerset(1:N)) do Δ
    map(powerset(1:N)) do Γ
      Impl(Γ, Δ, N) ∈ r ? "✓" : "×"
    end
  end); header=names, row_labels=names, tf=tf_markdown))
end

Base.string(i::ImpFrame) = sprint(show, "text/plain", i)

function ImpFrame(B::Int, names=nothing; random=false)
  I = if random
    N = length(impl_vec(B))
    sample(1:N, rand(0:N), replace = false)
  else 
    Int[]
  end
  push!(I, 1)
  ImpFrame{B}(ImplSet{B}(BitSet(I)), names)
end

Base.in(i::Impl, r::ImpFrame) = impl_dict(bearers(r))[i] ∈ r

Base.push!(r::ImpFrame, i::Impl) = push!(r, impl_dict(bearers(r))[i])

Impl(p::Union{Vector{Any},AbstractVector{Int}}, 
     c::Union{Vector{Any},AbstractVector{Int}}, 
     ::ImpFrame{N}) where N = Impl(p, c, N)

Impl(p::Union{Vector{Any},AbstractVector{Symbol}}, 
     c::Union{Vector{Any},AbstractVector{Symbol}}, 
     i::ImpFrame{N}) where N = Impl(i.(p), i.(c), N)

"""Convert a symbol to an integer via lookup in the names vector"""
(i::ImpFrame)(s::Symbol)::Int = findfirst(==(s), i.names)

"""
The RSR of an implication is the set of implications which, when unioned 
with it, make it into a good one.
"""
function rsr(frame::ImpFrame{N}, x::Impl{N})::ImplSet{N} where N
  ImplSet{N}(BitSet([i for (i,j) in enumerate(impl_vec(N)) if x ∪ j ∈ frame]))
end

function rsr(frame::ImpFrame, xs::ImplSet{N})::ImplSet{N} where N
  intersect(rsr.(Ref(frame), impl_vec(N)[collect(xs)]))
end



end #module

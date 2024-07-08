"""
We assume that all reason relations satisfy containment and that all explicit
Implication instances are *not* implications which have intersection between
premises and conclusions.
"""
module RRels 
export RRel, RRelRSR, Implication

using StructEquality, Combinatorics, PrettyTables, Random

# Implications (and incompatibilities)
######################################

"""
Note, there is a way of representing implications which exclude the possibility
of representing implications which satisfy containment by construction:

E.g. if bearers are {a,b,c,d,e} and we want to represent: a,b ⊢ d,e

We encode this with two subsets.  Bᵧ ⊆ Bᵢ ⊆ B, where |B| = N

The first subset picks out the bearers that feature anywhere in the implication
The second subset picks out which elements of that first subset are premises.
The complement of the second subset are the bearers in the conclusion.

However, this subset of implications is not closed under union. Furthermore,
it is less straightforward to assess "is bearer #2 in the premises of this?".
"""

"""E.g. a,b,c ⊢ d,e,f"""
@struct_hash_equal struct Implication
  prem::BitSet
  conc::BitSet
end

Implication(p1::AbstractVector, p2::AbstractVector) = 
  Implication(BitSet(Vector{Int}(p1)), BitSet(Vector{Int}(p2)))

Implication(p::Pair) = Implication(p...)

function Base.show(io::IO, ::MIME"text/plain", i::Implication) 
  print(io, join(string.(i.prem),",")," ⊢ ",join(string.(i.conc),","))
end

Base.isless(i₁::Implication, i₂::Implication) = 
  (i₁.prem, i₁.conc) ≤ (i₂.prem, i₂.conc)

Base.string(i::Implication) = sprint(show,"text/plain",i)

Base.isempty(i::Implication) = isempty(i.prem) && isempty(i.conc)

Base.:(+)(i::Implication, j::Implication) = 
  Implication(i.prem ∪ j.prem, i.conc ∪ j.conc)

""" Is the implication one which is required by containment? """
contain(i::Implication)::Bool = intersects(i.prem, i.conc)

""" Check if a bearer is mentioned at all """
Base.in(i::Int, imp::Implication) = i ∈ imp.prem || i ∈ imp.conc

swap(i::Implication) = Implication(i.conc, i.prem)

# Reason relations
##################

""" Most basic representation of a reason relation on a set of bearers 1:N """
@struct_hash_equal struct RRel
  N::Int
  I::Vector{Implication}
  RRel(N, I) = unique(I) == I ? new(N, I) : error("Non unique I: $I")
end

function Base.show(io::IO, ::MIME"text/plain", r::RRel) 
  names = [join(string.(x), ",") for x in powerset(1:r.N)]
  println(io, pretty_table(String, reduce(hcat, map(powerset(1:r.N)) do Δ
    map(powerset(1:r.N)) do Γ
      isempty(Γ∩Δ) || return "⊞"
      return Implication(Γ, Δ) ∈ r ? "✓" : "×"
    end
  end); header=names, row_labels=names, tf=tf_markdown))
end

Base.length(r::RRel) = r.N

RRel(B::Int, I::Vector{<:Pair}) = RRel(B, sort(Implication.(I)))

function RRel(B::Int; random=false)
  I = if random
    all_Is = shuffle(collect(all_implications(B)))
    all_Is[1:rand(0:length(all_Is))]
  else 
    Pair[]
  end
  return RRel(B, I)
end

Base.in(i::Implication, r::RRel) = i ∈ r.I

"""Iterator for all possible implications on a set of `n` bearers"""
function all_implications(n::Int)
  it = Iterators.map(x->BitSet(x), powerset(1:n))
  Iterators.map(((Γ,Δ),) -> Implication(Γ,Δ), Iterators.product(it, it))
end

"""
Either all implications except those which satisfy containment (default) or 
just the ones which satisfy containment
"""
containment(n::Int, exclude=true) = Iterators.filter(all_implications(n)) do i 
  (exclude ? (!) : identity)(contain(i))
end

# BitSets do not know the maximum possible value, so pass this in
complement(b::BitSet, n::Int) = BitSet(setdiff(1:n, b))

intersects(X, Y)::Bool = if length(Y) > length(X) 
  any(x -> x ∈ Y, X)
else 
  any(y -> y ∈ X, Y)
end

"""Check if the result of merging two implications will satisfy containment"""
intersect_add(ΓΔ::Implication, XY::Implication) = 
  intersects(ΓΔ.prem, XY.conc) || intersects(ΓΔ.conc, XY.prem) 

"""
A reason relation with lots of precomputed, cached info (including RSRs)

The RSR of an implication that satisfies containment is all of 𝒫(B)² 
"""
@struct_hash_equal struct RRelRSR
  rrel::RRel
  implications::Vector{Implication}
  inv_implication::Dict{Implication,Int} # reverse map for `implications`
  I::BitSet # indices of the good implications
  Iinv::Dict{Int,Int} # implication index -> good implementation index
  lattice::Vector{BitSet} # For each (Γ,Δ): which implications are supersets?
  prem::Vector{BitSet} # a ∈ Γ
  conc::Vector{BitSet} # a ∈ Δ
  goodprem::Vector{BitSet} # a ∈ Γ && (Γ,Δ) ∈ I
  goodconc::Vector{BitSet} # a ∈ Δ && (Γ,Δ) ∈ I
  RSR::Vector{BitSet} # what is in RSR(Γ,Δ)
  RSR′::Vector{BitSet} # what RSRs is (Γ,Δ) in?
  function RRelRSR(r::RRel)  
    implications = collect(containment(r.N))
    PN = length(implications) # |P(B)²| minus the containment ones
    inv_implication = Dict(v=>i for (i,v) in enumerate(implications))
    I = BitSet(getindex.(Ref(inv_implication), r.I))
    Iinv = Dict(v => i for (i,v) in enumerate(I))
    lattice = [BitSet([j for j in i:PN if i ⊆ j]) for i in 1:PN]
    prem = map(1:r.N) do i 
      BitSet(j for (j, x) in enumerate(implications) if i ∈ x.prem)
    end
    conc = map(1:r.N) do i 
      BitSet(j for (j, x) in enumerate(implications) if i ∈ x.conc)
    end
    RSR = map(implications) do ΓΔ
      BitSet(Iterators.map(first, Iterators.filter(enumerate(implications)) do (i, XY)
        intersect_add(ΓΔ, XY) || ΓΔ+XY ∈ r.I
      end))
    end
    RSR′ = [BitSet(j for j in 1:PN if i ∈ RSR[j]) for i in 1:PN]
    goodprem = [p ∩ RSR[1] for p in prem]
    goodconc = [p ∩ RSR[1] for p in conc]
    new(r, implications, inv_implication, I, Iinv, lattice, prem, conc, 
        goodprem, goodconc, RSR, RSR′)
  end
end

# Idea: a |B|x|B| matrix of BitSets that indexes implications by premise and 
# conclusion length

Base.getindex(rr::RRelRSR, i::Int) = rr.implications[i]

Base.getindex(rr::RRelRSR, i::Implication) = rr.inv_implication[i]

Base.getindex(rr::RRelRSR, Γ::AbstractVector, Δ::AbstractVector) = 
  rr.inv_implication[Implication(Γ, Δ)]

Base.length(r::RRelRSR) = length(r.rrel)

end #module

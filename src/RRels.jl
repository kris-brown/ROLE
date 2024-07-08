"""
We assume that all reason relations satisfy containment and that all explicit
Implication instances are *not* implications which have intersection between
premises and conclusions.
"""
module RRels 
export RRel, RRelRSR, Implication, RSR, Role, ⊔, ⊓

using StructEquality, Combinatorics, PrettyTables, Random

const imap = Iterators.map
const ifilter = Iterators.filter
const iproduct = Iterators.product

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

prem(i::Implication) = i.prem
conc(i::Implication) = i.conc

Base.length(::Implication) = 2

const ΓΔ₀ = Implication([],[])

Implication(p1::AbstractVector, p2::AbstractVector) = 
  Implication(BitSet(Vector{Int}(p1)), BitSet(Vector{Int}(p2)))

Implication(p::Pair) = Implication(p...)

Base.show(io::IO, ::MIME"text/plain", i::Implication) =
  let (Γ, Δ) = join.(i, ","); print(io, Γ, " ⊢ ", Δ) end

Base.iterate(i::Implication, x...) = iterate((prem(i), conc(i)), x...)

Base.isless(i₁::Implication, i₂::Implication) = let (Γ, Δ) = i₁, (X, Y) = i₂;
  (Γ, Δ) ≤ (X, Y)
end

Base.string(i::Implication) = sprint(show, "text/plain", i)

Base.isempty(i::Implication) = all(isempty, i)

Base.:(+)(i::Implication, j::Implication) = let (Γ, Δ) = i, (X, Y) = j;
  Implication(Γ ∪ X, Δ ∪ Y)
end

""" Is the implication one which is required by containment? """
contain(i::Implication)::Bool = intersects(i...)

""" Check if a bearer is mentioned at all """
Base.in(i::Int, imp::Implication) = i ∈ prem(imp) || i ∈ conc(imp)

swap(i::Implication) = Implication(conc(i), prem(i))

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
  it = imap(x -> BitSet(x), powerset(1:n))
  imap(((Γ,Δ),) -> Implication(Γ,Δ), iproduct(it, it))
end

"""
Either all implications except those which satisfy containment (default) or 
just the ones which satisfy containment
"""
containment(n::Int, exclude=true) = ifilter(all_implications(n)) do i 
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
intersect_add(i::Implication, j::Implication) = let (Γ, Δ) = i, (X, Y) = j;
  intersects(Γ, Y) || intersects(Δ, X) 
end

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
    pre = map(1:r.N) do i 
      BitSet(j for (j, x) in enumerate(implications) if i ∈ prem(x))
    end
    con = map(1:r.N) do i 
      BitSet(j for (j, x) in enumerate(implications) if i ∈ conc(x))
    end
    RSR = map(implications) do ΓΔ
      BitSet(imap(first, ifilter(enumerate(implications)) do (i, XY)
        intersect_add(ΓΔ, XY) || ΓΔ+XY ∈ r.I
      end))
    end
    RSR′ = [BitSet(j for j in 1:PN if i ∈ RSR[j]) for i in 1:PN]
    goodprem = [p ∩ RSR[1] for p in pre]
    goodconc = [p ∩ RSR[1] for p in con]
    new(r, implications, inv_implication, I, Iinv, lattice, pre, con, 
        goodprem, goodconc, RSR, RSR′)
  end
end

# Idea: a |B|x|B| matrix of BitSets that indexes implications by premise and 
# conclusion length

Base.getindex(rr::RRelRSR, i::Int) = rr.implications[i]

Base.getindex(rr::RRelRSR, i::Implication) = rr.inv_implication[i]
Base.haskey(rr::RRelRSR, i::Implication) = haskey(rr.inv_implication, i)

Base.getindex(rr::RRelRSR, Γ::AbstractVector, Δ::AbstractVector) = 
  rr.inv_implication[Implication(Γ, Δ)]

Base.length(r::RRelRSR) = length(r.rrel)

""" RSR of an implication """
RSR(rr::RRelRSR, i::Int)::BitSet = rr.RSR[i]

""" RSR of a set of implications """
RSR(rr::RRelRSR, is::BitSet)::BitSet = begin
  res = BitSet(1:length(rr.implications))
  for i in is 
    intersect!(res, rr.RSR[i])
  end
  return res
end

""" 

Addition of implications via their indices, returning the index of the result. 
When implications added together produces an implication that is guaranteed by 
containment (ones for which we have no index), return 0.

"""
add(rr::RRelRSR, is::Int...) = let idx = sum(rr[i] for i in is; init=ΓΔ₀);
  haskey(rr, idx) ? rr[idx] : 0
end

# Conceptual roles 
##################
abstract type AbsRole end

# the role of a trivial implication, i.e. one true by containment
@struct_hash_equal struct TrivialRole <: AbsRole end

role(::TrivialRole) = TrivialRole()

""" 
A conceptual role is represented by a set of implications - the role itself 
is the equivalence class of sets of implications that have the same RSR.
"""
@struct_hash_equal struct Role <: AbsRole 
  role::BitSet
end 

Role(r::Role) = r

Role(x::AbstractVector) = Role(BitSet(x))

role(r::Role) = r.role

RSR(rr::RRelRSR, r::Role) = RSR(rr, role(r))

""" The adjunction of a set of implicational roles """
⊔(rr::RRelRSR, is::AbstractVector{Role}) = ⊔(rr, is)
⊔(rr::RRelRSR, xs...) = ⊔(rr, Role.(xs)...)

function⊔(rr::RRelRSR, xs::Role...) 
  Role(BitSet(ifilter(>(0), [add(rr, combo...) for combo in iproduct(role.(xs)...)])))
end


""" The symjunction of """
⊓(is::AbstractVector{Role}) = ⊓(is...)
⊓(xs...) = ⊓(Role.(xs)...)

⊓(xs::Role...) = Role(∪(role.(xs)...))

end #module

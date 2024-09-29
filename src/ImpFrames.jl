"""
We assume that all reason relations satisfy containment and that all explicit
Implication instances are *not* implications which have intersection between
premises and conclusions.
"""
module ImpFrames
export ImpFrame, Impl, bearers, prem, conc, has_prem, has_conc, ImplSet, 
       RoleLattice ,getvalue, rsr, Content, contents, getcontent, Role,
       ⊗, ⊔, ⊓, ¬, →, ∨, ∧, ⪯, ⊩, impl_dict, impl_vec

using StructEquality, Combinatorics, PrettyTables, Random
using StatsBase: sample

const imap = Iterators.map
const ifilter = Iterators.filter
const iproduct = Iterators.product
const iflatten = Iterators.flatten
const Maybe{T} = Union{Nothing, T}

"""Many types in this file are just simple wrappers around a BitSet"""
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


# Sets of implications 
######################

"""
A set of implications, e.g. {(a,b ⊢ b), (b ⊢ a)}.

Given an index for each implication in the space of possible implications for 
some number of bearers, N, this data is captured by a BitSet. 
"""
@struct_hash_equal struct ImplSet{N} <: BitSetWrapper
  value::BitSet
  ImplSet{N}(v::BitSet=BitSet()) where N = new{N}(v)
end 

ImplSet(v::AbstractVector{Int}, N::Int) = ImplSet{N}(BitSet(v))

ImplSet(v::AbstractVector{Impl{N}}) where N = 
  ImplSet{N}(BitSet(getindex.(Ref(impl_dict(N)), v)))

ImplSet(i::Impl{N}) where N = ImplSet([i])

bearers(::ImplSet{N}) where N = N

is_top(i::ImplSet{N}) where N = length(i) == 2^(2*N)

top(i::Int) = ImplSet{i}(BitSet(1:2^(2*i)))

top(::Type{ImplSet{N}}) where N = top(N)

Base.union(i::Vector{ImplSet{N}}) where N = 
  ImplSet{N}(isempty(i) ? BitSet() : union(getvalue.(i)...))

Base.intersect(i::Vector{ImplSet{N}}) where N = 
  isempty(i) ? top(N) : ImplSet{N}(intersect(getvalue.(i)...))

function Base.show(io::IO, ::MIME"text/plain", i::ImplSet{N}) where N
  str = ["($(string(impl_vec(N)[x])))" for x in getvalue(i)]
  print(io, "{$(join(str,","))}")
end

Base.string(i::ImplSet) = sprint(show, "text/plain", i)

"""
Quantale monoidal operation for 𝒫(S) where (S, 0, ∪) is a monoid.
"""
function ⊗(xs::Vector{ImplSet{N}})::ImplSet{N} where N
  isempty(xs) && return ImplSet([Impl{N}()]) # unit of the ⊗ operation
  v = impl_vec(N)
  map(collect.(iproduct(xs...))) do imp_tuple # iterate over cartesian product
    i = Impl{N}()
    for it in imp_tuple 
      union!(i, v[it])
    end
    i 
  end |> vec |> Vector{Impl{N}} |> ImplSet
end

⊗(xs::ImplSet{N}...) where N = ⊗(collect(xs))

# Implication frames
####################

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
    RoleLattice(iframe) # compute this automatically and cache
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
  N = isnothing(N) ? max(collect(iflatten(iflatten(xs)))...) : N # default to max
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


# Implicational roles
#####################

"""
An implicational role is a Range of Subjunctive Robustness for some set of 
candidate implications. However, we can always express it as an intersection 
of some set of atomic roles (which are ImplSets in some linear order, stored in 
a `RoleLattice`).

The indices in the Role only makes sense w/r/t a role lattice of some 
particular implication frame, given as a type parameter.
"""
@struct_hash_equal struct Role{F} <: BitSetWrapper
  value::BitSet
  Role{F}(v::BitSet) where F = new{F}(v)
end

ImplSet(atoms::Vector{<:ImplSet}, r::Role) = intersect(atoms[collect(r)])

ImplSet(r::Role{F}) where F =  ImplSet(get_lattice(F).atoms, r)

rsr(r::Role{F}) where F = rsr(get_frame(F), ImplSet(r))

# Role Lattices
###############

"""
An lattice of roles associated with some implication frame (ℒ,𝕀). There is a 
special set of roles which forms a basis for the lattice (any element is an
intersection of some subset of this basis.) This basis is not a set of atoms,
however (the way a power set lattice has a basis of atomic elements), some of 
the atoms are subsets of each other. If B₁ ⊆ B₂, then it doesn't make sense to 
express some element as the intersection ∩{B₁,B₂,...} (putting B₂ in there in 
the first place is completely redundnant). Thus, we store the inclusion poset
among the basis elements in order to make it easy to filter out redundant info
and have a more normal form for expressing elements of the lattice as joins of
basis elements.

Type parameters are N (an integer) for the number of bearers

We only store the atoms (they are put in a fixed order so that they can be 
referred to be integers). Roles are identified with sets of atoms.

We cache a forward map: S → Role and an inverse map: AtomRole → 𝒫(S).
"""
@struct_hash_equal struct RoleLattice{N,F}
  atoms::Vector{ImplSet{N}}
  atomdict::Dict{ImplSet{N}, Int}
  subset::Vector{BitSet}
  role::Vector{Role{F}}

  function RoleLattice(f::ImpFrame{N}) where N
    # Check if we've computed this before
    key = hash(f)
    haskey(RoleDict, key) && return get_lattice(key)
    # Compute roles of all candidate implications
    all_rsrs = rsr.(Ref(f), impl_vec(N))
  
    # Isolate unique roles
    unique_roles = sort(filter!(r->!is_top(r), unique(all_rsrs)), 
                        by=length)
    atomdict = Dict(v=>i for (i,v) in enumerate(unique_roles))
    # Get matrix of subsets
    subsets = [BitSet([i for (x, i) in atomdict if u ⊂ x]) for u in unique_roles]
  
    # Cache the role of every candidate implication
    roles = factor.(key, Ref(unique_roles), Ref(subsets), all_rsrs)
    
    # Put together
    lat = new{N, key}(unique_roles, atomdict, subsets, roles)
    RoleDict[key] = f => lat # cache the result
    lat
  end
end

"""Caching roles of an implication frame"""
const RoleDict = Dict{UInt64, Pair{ImpFrame, RoleLattice}}()

get_frame(u::UInt64) = RoleDict[u][1]

get_lattice(u::UInt64) = RoleDict[u][2]

function get_lattice(i::ImpFrame) 
  h = hash(i)
  if haskey(RoleDict, h) 
    get_lattice(h)
  else 
    RoleLattice(i)
  end
end

""" Compute the role lattice """
Base.length(rl::RoleLattice{T}) where T = length(rl.atoms)

"""Is an implication contained in the role"""
Base.in(i::Impl{N}, rl::Role) where N = impl_dict(N)[i] ∈ ImplSet(rl)

"""
Factor an arbitrary role ImplSet into a finite intersection of roles

Note: this may throw an error if the ImplSet is not in the image of `rsr`.
"""
function factor(F::UInt64, atoms::Vector{ImplSet{T}}, subsets::Vector{BitSet}, 
                role::ImplSet{T}, ; check=true)::Role{F} where {T}
  is_top(role) && return Role{F}(BitSet()) # simple case
  forbidden, res = BitSet(), BitSet()
  for (i, a) in enumerate(atoms)
    i ∈ forbidden && continue # we've already ruled this one out
    if role ⊆ a 
      push!(res, i) # we need to intersect with atom `a` to get `role` 
      union!(forbidden, subsets[i]) # any basis roles strictly larger than a
    end 
  end
  
  setdiff!(res, forbidden) # remove redundant basis elements
  result = Role{F}(res)

  if check # confirm that the input is the join of the result atoms
    role′ = ImplSet(atoms, result)
    role == role′|| error("HERE: $role\n $(role′)")
  end

  return result
end

function factor(rlat::RoleLattice{T,F}, role::ImplSet{T}; check=true)::Role where {T,F}
  factor(F, rlat.atoms, rlat.subset, role; check)
end

(rlat::RoleLattice)(iset::ImplSet; check=true) = factor(rlat, iset; check)

(rlat::RoleLattice)(i::Impl; check=true) = factor(rlat, ImplSet(i); check)


prem_role(i::ImpFrame{N}, a::Int) where N = let rlat = get_lattice(i);
  rlat(rsr(i, Impl([a], Int[], N)))
end

conc_role(i::ImpFrame{N}, a::Int) where N = let rlat = get_lattice(i);
  rlat(rsr(i, Impl(Int[], [a], N)))
end

# Operations on roles
#--------------------

# "Symjunction" i.e. intersection
⊓(r1::Role{F}, r2::Role{F}) where F = ⊓([r1,r2])

# Intersecting the sets is unioning the generators which are implicitly 
# intersected to obtain the implicit implication set
⊓(rs::AbstractVector{Role{F}}) where F = Role{F}(∪(getvalue.(rs)...))


# "Adjunction" i.e. monoidal product dual to rsr²(- ⊗ -)
⊔(r1::Role{F}, r2::Role{F}) where F = ⊔([r1,r2])

function ⊔(rs::AbstractVector{Role{F}})::Role{F} where F
  f = get_frame(F)
  N = bearers(f)
  get_lattice(F)(rsr(get_frame(F), ⊗(ImplSet{N}[rsr.(rs)...])))
end

# Implicational role inclusion
function ⪯(r1::Role{F}, r2::Role{F})::Bool where F 
  ImplSet(r1) ⊆ ImplSet(r2)
end

function ⪯(r1::AbstractVector{Role{F}}, r2::AbstractVector{Role{F}})::Bool where F 
  intersect(ImplSet.(r1)) ⊆ ⊔(ImplSet.(r2))
end

# Conceptual contents 
#####################


@struct_hash_equal struct Content{F}
  prem::Role{F}
  conc::Role{F}
end

"""Accessor function"""
function prem(c::Content{F})::Role{F} where F 
  c.prem 
end

"""Accessor function"""
function conc(c::Content{F})::Role{F} where F 
  c.conc
end

getcontent(i::ImpFrame, a::Int) = Content(prem_role(i, a), conc_role(i, a))

contents(i::ImpFrame{N}) where N = [getcontent(i, a) for a in 1:N]

Base.iterate(c::Content, i...) = iterate((prem(c), conc(c)), i...)

¬(c::Content{F}) where F = Content{F}(conc(c), prem(c))

function →(a::Content{F}, b::Content{F}) where F  
  ((a⁺, a⁻), (b⁺, b⁻)) = (a, b)
  Content{F}(a⁻ ⊓ b⁺ ⊓ (a⁻ ⊔ b⁺) , a⁺ ⊔ b⁻) 
end

function ∧(a::Content{F}, b::Content{F}) where F  
  ((a⁺, a⁻), (b⁺, b⁻)) = (a, b)
  Content{F}(a⁺ ⊔ b⁺,  a⁻ ⊓ b⁻ ⊓ (a⁻ ⊔ b⁻)) 
end

function ∨(a::Content{F}, b::Content{F}) where F  
  ((a⁺, a⁻), (b⁺, b⁻)) = (a, b)
  Content{F}(a⁺ ⊓ b⁺ ⊓ (a⁺ ⊔ b⁺), a⁻ ⊔ b⁻) 
end

"""
Content entailment for lists of conceptual contents Γ and Δ

⟦Γ⟧ ⊩ ⟦Δ⟧ := ⟦Γ⟧⁺ ⊔ ⟦Δ⟧⁻ ⊆ 𝕀
"""
function ⊩(x::AbstractVector{Content{F}}, y::AbstractVector{Content{F}}) where {F}
  f = get_frame(F)
  v = ⊔(Role{F}[prem.(x)..., conc.(y)...])
  rsr(f,ImplSet(v)) ⊆ getvalue(f)
end

⊩(x::Content{F}, y::Content{F}) where F = [x] ⊩ [y]


end #module

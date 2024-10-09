module Roles 
export RoleLattice, Role, ⊔, ⊓, get_frame

using StructEquality

using ..Impls, ..ImplSets, ..ImpFrames
using ..Impls: BitSetWrapper
import ..ImplSets: ImplSet, is_top
import ..ImpFrames: compute_rolelattice, rsr

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
A lattice of roles associated with some implication frame (ℒ,𝕀). There is a 
special set of roles which forms a basis for the lattice (any element is an
intersection of some subset of this basis.) This basis is not a set of atoms,
however (the way a power set lattice has a basis of atomic elements), some of 
the atoms are subsets of each other. If B₁ ⊆ B₂, then it doesn't make sense to 
express some element as the intersection ∩{B₁,B₂,...} (putting B₂ in there in 
the first place is completely redundant). Thus, we store the inclusion poset
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

get_lattice(i::ImpFrame) = get_lattice(hash(i))

Base.length(rl::RoleLattice{T}) where T = length(rl.atoms)

compute_rolelattice(i::ImpFrame) = RoleLattice(i)

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


end # module

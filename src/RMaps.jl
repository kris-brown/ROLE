"""
Various notions of maps between reason relations and algorithms for 
finding them / verifying the naturality of purported maps.
"""
module RMaps 
export RRelMap, is_natural, homomorphisms, homomorphism, RRelC, RRelC′, Interp

using StructEquality
using MLStyle: @match, @data

using GATlab

using ..RRels
using ..RRels: intersects, contain, AbsRole, all_implications, role, containment

const Maybe{T} = Union{T, Nothing}
const ifilter = Iterators.filter
const imap = Iterators.map

"""
A function on bearers. Should send good implications to good ones.
"""
@struct_hash_equal struct RRelMap 
  fB::Vector{Int}
end

Base.length(r::RRelMap) = length(r.fB)
Base.iterate(r::RRelMap, i...) = iterate(r.fB, i...)

(f::RRelMap)(i::BitSet) = f(collect(i))
(f::RRelMap)(i::Union{Vector{Int},Int}) = f.fB[i]
(f::RRelMap)(i::Implication) = Implication(f(i.prem), f(i.conc))

""" 
Is it the case that the action of the map sends all good inferences to good ones
"""
is_natural(f, dom::RRel, codom::RRel, m::Model) =
  isempty(naturality_failures(m, f, dom, codom))

"""
A map sending bearers to conceptual roles (i.e. RSRs of a subset of 
*candidate* implications). We need not mention implications which satisfy 
contraction because their RSR is the entire set of implications, such that 
intersecting with them is a no-op.

E.g. for a map X → Y, we specify a function X → 𝒫(𝒫(Y)²)
"""
@struct_hash_equal struct RoleMap
  fB::Vector{<:AbsRole}
end

RoleMap(xs::Vector{Any}) = RoleMap(Role.(xs))

(f::RoleMap)(i::BitSet) = f(collect(i))
(f::RoleMap)(i::Union{Int, AbstractVector{Int}}) = f.fB[i]

"""
Pair of interpretation functions, sending bearers to their premisory role
and their conclusory role. This is the data of a function X → 𝒫(𝒫(Y)²)²
"""
@struct_hash_equal struct Interp 
  prem::RoleMap
  conc::RoleMap
end

Interp(a,b) = Interp(RoleMap(a), RoleMap(b))

Interp(prem::AbstractVector{<:AbstractVector{Int}},
       conc::AbstractVector{<:AbstractVector{Int}}
      ) = Interp(RoleMap(prem), RoleMap(conc))

""" 
The interpretation of the domain lexicon into the codomain induces a reason
relation.
"""
function ideal(i::Interp, codom::RRelRSR)::RRel
  i⁺, i⁻ = i.prem, i.conc
  N = length(i⁺.fB)
  I = ifilter(containment(N)) do (Γ, Δ)
    # println("Γ $(string(Γ)), Δ $(string(Δ))")
    # println("\ti⁺(Γ) $(role.(i⁺(Γ)))")
    # println("\ti⁻(Δ) $(role.(i⁻(Δ)))")
    # println("\trole(⊔...)) $(role(⊔(codom, i⁺(Γ)..., i⁻(Δ)...)))")
    RSR(codom, ⊔(codom, i⁺(Γ)..., i⁻(Δ)...)) ⊆ codom.I
  end |> collect
  RRel(N, I)
end

# Categories
############
struct RRelC <: Model{Tuple{RRel, RRelMap}} end

@instance ThCategory{RRel, RRelMap} [model::RRelC] begin
  Hom(f::RRelMap, d::RRel, c::RRel; model) =
    is_natural(model, f, d, c) ? f : @fail join(
      naturality_failures(model, f, d, c), "\n")

  id(rr::RRel) = RRelMap(collect(1:rr.N))
  compose(f::RRelMap, g::RRelMap) = 
    RRelMap(ThCategory.compose[FinSetC()](f.fB, g.fB))
end

struct RRelC′ <: Model{Tuple{RRel, RRelMap}} end

@instance ThCategory{RRel, Interp} [model::RRelC′] begin
  Hom(f::Interp, d::RRel, c::RRel; model) =
    is_natural(model, f, d, c) ? f : @fail join(
      naturality_failures(model, f, d, c), "\n")

  id(rr::RRel) = Interp(collect(1:rr.N))
  compose(f::Interp, g::Interp) = error("TODO")
end

# Naturality 
############

"""
Find examples where Γ⊢Δ but f(Γ)⊬f(Δ)
"""
function naturality_failures(::RRelC, r::RRelMap, dom::RRel, codom::RRel)
  # Error if map is syntactically malformed
  length(r) == length(dom) || error("Bad map length")
  all(>(0), r.fB) || error("Out of bounds")
  maximum(r; init=0) ≤ length(codom) || error("out of bounds")
  # Find naturality failures
  res = String[]
  for ΓΔ in dom.I
    rΓΔ = r(ΓΔ) 
    if !(contain(rΓΔ) || rΓΔ ∈ codom.I)
      push!(res, "Dom: " * string(ΓΔ) * " Codom: " * replace(string(rΓΔ), "⊢" => "⊬"))
    end
  end
  return res
end


"""
Find examples where  ⟦Γ⟧ ⊢ ⟦Δ⟧ but Γ⊬Δ
"""
function naturality_failures(::RRelC′, r::RRelMap, dom::RRel, codom::RRel)
  error("TODO")
end

# Homomorphism search
#####################
abstract type BacktrackingState end 

function homomorphism(X::RRelRSR, Y::RRelRSR; cat=RRelC(), kw...)
  result = nothing
  backtracking_search(cat, X, Y; kw...) do α
    result = α; return true
  end
  return result
end

function homomorphisms(X::RRelRSR, Y::RRelRSR; 
                       cat::Model{Tuple{RRel,Hom}}=RRelC(), kw...)  where {Hom}
  results = Hom[]
  backtracking_search(cat, X, Y; kw...) do α
    push!(results, deepcopy(α)); return false
  end
  return results
end

""" Main loop of backtracking search """
function backtracking_search(f, cat::Model, state::BacktrackingState, depth::Int) 
  # Choose the next unassigned element.
  mrv, x, options = find_mrv_elem(cat, state, depth)
  if isnothing(x)
    return f(RRelMap(state.assignment))
  elseif mrv == 0
    return false # No allowable assignment, so we must backtrack.
  end
  # Attempt all assignments of the chosen element.
  for y in options
    (assign_elem!(cat, state, depth, x, y) 
    && backtracking_search(f, cat, state, depth + 1)) && return true
    unassign_elem!(cat, state, depth, x)
  end
  return false
end

""" Find the most constrained element """
function find_mrv_elem(cat::Model, state::BacktrackingState, depth::Int 
                      )::Tuple{Number, Maybe{Int},Maybe{Vector{Int}}}
  Ny = length(state.codom)
  mrv, mrv_elem, options = Inf, nothing, nothing
  for x in 1:length(state.dom)
    state.assignment[x] == 0 || continue
    x_opts = filter(y -> can_assign_elem(cat, state, depth, x, y), 1:Ny)
    if length(x_opts) < mrv
      mrv, mrv_elem, options = length(x_opts), x, x_opts
    end
  end
  return (mrv, mrv_elem, options)
end

# Nonmutating overall, but we temporarily mutate the backtracking state.
function can_assign_elem(cat::Model, state::BacktrackingState, depth::Int, 
                         x::Int, y::Int)::Bool
  ok = assign_elem!(cat, state, depth, x, y)
  unassign_elem!(cat, state, depth, x)
  return ok
end

# RRelC-specific
#---------------

"""
assignment: the partially-specified mapping of bearers (0 = unspecified)
possibilities: assigning for each good inference in the domain what good 
               (non-containment) inferences in the codomain could be mapped to, 
               given the current assignment.
"""
struct RRelBacktrackingState <: BacktrackingState
  dom::RRelRSR
  codom::RRelRSR
  assignment::Vector{Int}
  assignment_depth::Vector{Int}
  # possibilities::Vector{BitSet}
end 

(s::BacktrackingState)(i::Int) = s.assignment[i]

"""
Search the space of functions Yˣ of functions from bearers of X to bearers of Y.
"""
function backtracking_search(f, cat::RRelC, X::RRelRSR, Y::RRelRSR; kw...)
  state = RRelBacktrackingState(X, Y, zeros(Int, length(X)), zeros(Int, length(X))
                           ) # init_possibilities(X, Y)
  backtracking_search(f, cat, state, 1)
end

""" Initialize `possibilities` for BacktrackingState """
function init_possibilities(X::RRelRSR, Y::RRelRSR)
  imap((X.I)) do i
    (Γ, Δ) = X[i]
    BitSet(imap(last, ifilter(pairs(Y.inv_implication)) do ((X,Y), j) 
      isempty(X) && !isempty(Γ) && return false
      isempty(Y) && !isempty(Δ) && return false
      length(Γ) ≥ length(X) && length(Δ) ≥ length(Y) 
    end))
  end
end

function assign_elem!(::RRelC, state::RRelBacktrackingState, depth::Int, 
                      x::Int, y::Int)::Bool
  y′ = state.assignment[x]
  y′ == y && return true  # If x is already assigned to y, return immediately.
  y′ == 0 || return false # Otherwise, x must be unassigned.

  # Make the assignment and recursively assign subparts.
  state.assignment[x] = y
  state.assignment_depth[x] = depth
  # every good (Γ⊢Δ) in X which x figures into is a constraint
  for i in state.dom.goodprem[x] ∪state.dom.goodconc[x]
    ΓΔ = state.dom[i]
    fΓ, fΔ = state.(ΓΔ.prem), state.(ΓΔ.conc)
    intersects(fΓ, fΔ) && continue # possible to satisfy containment
    # What are the possible good inferences this could be sent to?
    fΓzs, fΔzs = count.(==(0), [fΓ, fΔ])
    fΓnz, fΔnz = filter.(!=(0), [fΓ, fΔ])
    y_poss = ifilter(state.codom.I) do j
      XY = state.codom[j]
      !isempty(XY.prem) || isempty(ΓΔ.prem) || return false
      !isempty(XY.conc) || isempty(ΓΔ.conc) || return false
      fΓnz ⊆ XY.prem || return false
      fΔnz ⊆ XY.conc || return false
      length(setdiff(XY.prem, fΓnz)) ≤ fΓzs || return false
      length(setdiff(XY.conc, fΔnz)) ≤ fΔzs || return false
      return true
    end |> collect
    isempty(y_poss) && return false
  end
  return true
end

function unassign_elem!(::RRelC, state::RRelBacktrackingState, depth::Int, 
                        x::Int)::Nothing
  state.assignment[x] == 0 && return nothing
  assign_depth = state.assignment_depth[x]
  @assert assign_depth <= depth
  if assign_depth == depth
    state.assignment[x] = 0
    state.assignment_depth[x] = 0
  end
  return nothing
end

# Interpretation function search
#--------------------------------

"""
assignment: the partially-specified mapping of bearers (0 = unspecified)
"""
struct InterpBacktrackingState <: BacktrackingState
  dom::RRelRSR
  codom::RRelRSR
  assignment::Matrix{Bool}
  assignment_depth::Matrix{Int}
end 

"""
Search the space of functions Yˣ of functions from bearers of X to bearers of Y.
"""
function backtracking_search(cat::Interp, f, X::RRelRSR, Y::RRelRSR; kw...)
  state = InterpBacktrackingState(X, Y, zeros(Int, length(X)), zeros(Int, length(X)))
  backtracking_search(cat, f, state, 1)
end

function assign_elem!(::Interp, state::InterpBacktrackingState, depth::Int, 
                      x::Int, y::Int)::Bool
  error("TODO")
end

function unassign_elem!(::Interp, state::InterpBacktrackingState, depth::Int, 
                        x::Int)::Nothing
  error("TODO")
end

end # module

"""
Various notions of maps between reason relations and algorithms for 
finding them / verifying the naturality of purported maps.
"""
module RMaps 
export RRelMap, is_natural, homomorphisms, homomorphism

using StructEquality
using MLStyle: @match, @data

using ..RRels
using ..RRels: intersects, contain

const Maybe{T} = Union{T, Nothing}

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
is_natural(r::RRelMap, dom::RRel, codom::RRel) =
  isempty(naturality_failures(r, dom, codom))

"""
Find examples where Γ⊢Δ but f(Γ)⊬f(Δ)
"""
function naturality_failures(r::RRelMap, dom::RRel, codom::RRel)
  length(r) == length(dom) || error("Bad map length")
  all(>(0), r.fB) || error("Out of bounds")
  maximum(r; init=0) ≤ length(codom) || error("out of bounds")
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
An interpretation function on bearers. Sends bearers to sets of bearers (i.e.
a relation between the two bearer sets).
"""
@struct_hash_equal struct RRelRel
  fB::Vector{Vector{Int}}
end

"""
Pair of interpretation functions, sending bearers to their premisory role
and their conclusory role
"""
@struct_hash_equal struct RRelRel2
  prem::RRelRel
  conc::RRelRel
end

function is_natural(f::RRelRel2, dom::RRel, codom::RRel)
end


# Homomorphism search
#####################
"""
assignment: the partially-specified mapping of bearers (0 = unspecified)
possibilities: assigning for each good inference in the domain what good 
               inferences in the codomain could be mapped to, given the 
               current assignment. Only explicitly track non-containment ones.
"""
struct BacktrackingState
  dom::RRelRSR
  codom::RRelRSR
  assignment::Vector{Int}
  assignment_depth::Vector{Int}
  # possibilities::Vector{BitSet}
end 

(s::BacktrackingState)(i::Int) = s.assignment[i]

function homomorphism(X::RRelRSR, Y::RRelRSR; kw...)
  result = nothing
  backtracking_search(X, Y; kw...) do α
    result = α; return true
  end
  return result
end

function homomorphisms(X::RRelRSR, Y::RRelRSR; kw...) 
  results = []
  backtracking_search(X, Y; kw...) do α
    push!(results, deepcopy(α)); return false
  end
  return results
end

"""
Search the space of functions Yˣ of functions from bearers of X to bearers of Y.
"""
function backtracking_search(f, X::RRelRSR, Y::RRelRSR; kw...)
  state = BacktrackingState(X, Y, zeros(Int, length(X)), zeros(Int, length(X))
                           ) # init_possibilities(X, Y)
  backtracking_search(f, state, 1)
end

""" Initialize `possibilities` for BacktrackingState """
function init_possibilities(X::RRelRSR, Y::RRelRSR)
  Iterators.map((X.I)) do i
    ΓΔ = X[i]
    BitSet(Iterators.map(last, Iterators.filter(pairs(Y.inv_implication)) do (XY, j) 
      isempty(XY.prem) && !isempty(ΓΔ.prem) && return false
      isempty(XY.conc) && !isempty(ΓΔ.conc) && return false
      length(ΓΔ.prem) ≥ length(XY.prem) && length(ΓΔ.conc) ≥ length(XY.conc) 
    end))
  end
end

""" Main loop of backtracking search """
function backtracking_search(f, state::BacktrackingState, depth::Int) 
  # Choose the next unassigned element.
  println("DEPTH $depth Finding MRV")
  mrv, x, options = find_mrv_elem(state, depth)
  println("DEPTH $depth: Found MRV $x ↦ $options")
  if isnothing(x)
    println("\n*RESULT*\n")
    return f(RRelMap(state.assignment))
  elseif mrv == 0
    return false # No allowable assignment, so we must backtrack.
  end
  # Attempt all assignments of the chosen element.
  for y in options
    (assign_elem!(state, depth, x, y) 
    && backtracking_search(f, state, depth + 1)) && return true
    unassign_elem!(state, depth, x)
  end
  return false
end

""" Find the most constrained element """
function find_mrv_elem(state::BacktrackingState, depth::Int 
                      )::Tuple{Number, Maybe{Int},Maybe{Vector{Int}}}
  Ny = length(state.codom)
  mrv, mrv_elem, options = Inf, nothing, nothing
  for x in 1:length(state.dom)
    state.assignment[x] == 0 || continue
    x_opts = filter(y -> can_assign_elem(state, depth, x, y), 1:Ny)
    if length(x_opts) < mrv
      mrv, mrv_elem, options = length(x_opts), x, x_opts
    end
  end
  (mrv, mrv_elem, options)
end

# Nonmutating overall, but we temporarily mutate the backtracking state.
function can_assign_elem(state::BacktrackingState, depth::Int, x::Int, y::Int)::Bool
  ok = assign_elem!(state, depth, x, y)
  unassign_elem!(state, depth, x)
  return ok
end

function assign_elem!(state::BacktrackingState, depth::Int, x::Int, y::Int)::Bool
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
    y_poss = Iterators.filter(state.codom.I) do j
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

function unassign_elem!(state::BacktrackingState, depth::Int, x::Int)::Nothing
  state.assignment[x] == 0 && return nothing
  assign_depth = state.assignment_depth[x]
  @assert assign_depth <= depth
  if assign_depth == depth
    state.assignment[x] = 0
    state.assignment_depth[x] = 0
  end
  return nothing
end




end # module
module RMaps 

export FMap, Cont, ContC, Open, OpenC, is_natural, naturality_failures, 
       homomorphisms, preimage, terminal, initial, coproduct, product, 
       Interp, sound, soundness_failures, interps, sound_dom

using ..ImpFrames
using ..ImpFrames: impl_vec, get_frame
import ..ImpFrames: getvalue, prem, conc


using GATlab
using StructEquality
using Combinatorics
using StaticArrays


"""
Interpretation function: sends bearers to conceptual contents
"""
@struct_hash_equal struct Interp{N, Cod}
  value::SVector{N, Content{Cod}}
  Interp(v::AbstractVector{Content{C}}) where C = new{length(v), C}(SVector(v...))
end

getvalue(i::Interp) = i.value


function (f::Interp{N,Cod})(i::Int)::Content{Cod} where {N,Cod} 
  getvalue(f)[i] 
end

"""Compute the content entailment of an implication"""
function (f::Interp{N,Cod})(i::Impl{N}) where {N,Cod}
  f.(prem(i)) ⊩ f.(conc(i))
end

sound(f::Interp{N, Cod}, dom::ImpFrame{N}) where {N, Cod} = 
  isempty(soundness_failures(f, dom))


"""The domain of an interpretation, if it were sound"""
function sound_dom(f::Interp{N, Cod})::ImpFrame{N} where {N, Cod}
  ImpFrame{N}(BitSet([idx for (idx, i) in enumerate(impl_vec(N)) 
                      if f(i)]) |> ImplSet{N})
end

""" 
`first` means only return the first failure
"""
function soundness_failures(f::Interp{N, Cod}, dom::ImpFrame{N}; first=false) where {N, Cod}
  cod = get_frame(Cod)
  res = []
  for imp in impl_vec(N)
    # println("$(string(imp)) -> $(imp ∈ dom)")
    if (imp ∈ dom) != f(i) 
      first && return [imp]
      push!(res, imp)
    end
  end
  res
end

"""
Enumerate sound interpretation functions by brute force.
"""
function interps(dom::ImpFrame{N}, cod::ImpFrame) where N
  r = RoleLattice(cod)
  F = hash(cod)
  res = Interp[]
  badprem, badconc = Set(),Set()
  pset = Iterators.product(fill(powerset(eachindex(r.atoms)), 2)...)
  for ats in Iterators.product(fill(pset, N)...)
    @show ats
    f = Interp(map(ats) do (p, c)
      Content(Role{F}(BitSet(p)), Role{F}(BitSet(c)))
    end |> collect)
    fails = soundness_failures(f, dom; first=true)

    if isempty(fails)
      println("FOUND ONE!") && push!(res, f)
    else  # learn why it was wrong, prevent that same assignment
      fail = only(fails)
      push!(badprem, [p => ats[p][1] for p in prem(fail)])
      push!(badconc, [p => ats[p][1] for p in conc(fail)])
      @show string(fail)
      @show badprem 
      @show badconc 
      error("HERE")
    end
  end
  return res
end

# Finite functions
##################

"""Representation of a finite function"""
@struct_hash_equal struct FMap
  value::Vector{Int}
end

getvalue(f::FMap) = f.value

"""Apply the function to a bearer"""
(f::FMap)(i::Int) = getvalue(f)[i]

"""Map an implication forward using the image of the function"""
(f::FMap)(i::Impl{N}) where N = Impl(f.(prem(i)), f.(conc(i)), N)

"""Pull an implication backwards using the preimage of the function"""
function preimage(f::FMap, impl::Impl, N::Int)::Impl{N}
  Impl([i for i in 1:N if has_prem(impl, f(i))], 
       [i for i in 1:N if has_conc(impl, f(i))], N)
end


# Things generic to all categories of Implication Frames
########################################################
abstract type IFrameCat <: Model{Tuple{ImpFrame, FMap}} end
abstract type HomAlgorithm end 
struct BruteForce <: HomAlgorithm end

""" Special naturality_failures method for each category """
is_natural(m, f, d, c) = isempty(naturality_failures(m, f, d, c))

initial(::IFrameCat) = ImpFrame(0)

homomorphisms(X::IFrameCat, d::ImpFrame{N}, c::ImpFrame{M}, 
              alg=BruteForce()) where {N,M} = homomorphisms(X, alg, d, c)

"""Brute force algorithm"""
function homomorphisms(X::IFrameCat, ::BruteForce, d::ImpFrame{N}, 
                       c::ImpFrame{M}; monic=false, iso=false) where {N,M}
  res, iter = FMap[], []

  # Handle constraints
  iter = []
  if iso 
    M == N || return res
    iter = permutations(M)
  elseif monic 
    iter = combinations(1:M,N)
  else 
    iter = with_replacement_combinations(1:M,N)
  end

  for f in iter
    is_natural(X, FMap(f), d, c) && push!(res, FMap(f))
  end
  res
end

""" Get a coproduct without specifying the distinguished good implications """
function empty_coproduct(Xs::ImpFrame...)
  bs = bearers.(Xs)
  Σ = ImpFrame(sum(bs; init=0))
  ιs = [FMap(i:j) for (i,j) in zip(cumsum([1,bs...]), cumsum(bs))]
  return (Σ, ιs)
end

"""Map into terminal object"""
delete(c::IFrameCat, ::ImpFrame{N}) where N = (terminal(c), FMap(ones(Int, N)))

"""Map from initial object"""
create(c::IFrameCat, ::ImpFrame) = (initial(c), Fmap(Int[]))

# universal(i::IFrameCat, c::Coproduct, csp::Cospan)::FMap = error("undefined")


# Category of Implication Frames and Continuous Maps
####################################################

"""
A category where objects are implication frames and maps are functions 
f: ℒₘ → ℒₙ between bearer sets which are required to satisfy the following 
equation, for all good implications in 𝕀ₙ: f⁻¹(i) ∈ 𝕀ₘ
"""
struct Cont <: IFrameCat end
const ContC = Cont()

@instance ThCategory{ImpFrame, FMap} [model::Cont] begin
  Hom(f::FMap, d::ImpFrame, c::ImpFrame; model) =
    is_natural(model, f, d, c) ? f : @fail join(
      naturality_failures(model, f, d, c), "\n")

  id(rr::ImpFrame) = FMap(collect(1:bearers(rr)))
  compose(f::FMap, g::FMap) = 
    FMap(ThCategory.compose[FinSetC()](getvalue(f), getvalue(g)))
end

"""
Check if a purported map satisfies the continuity constraint
"""
naturality_failures(::Cont, f::FMap, d::ImpFrame{N}, c::ImpFrame{M}) where {N,M} = 
  filter(i -> preimage(f, impl_vec(M)[i], N) ∉ d, c) 

terminal(::Cont) = ImpFrame(Pair[], 1)

"""
x ∈ 𝕀 of coproduct if ∀ i, ιᵢ⁻¹(x) ∈ 𝕀ᵢ
"""
function coproduct(::Cont, Xs::ImpFrame...)
  Σ, ιs = empty_coproduct(Xs...)
  for (idx, i) in enumerate(impl_vec(bearers(Σ)))
    all(((ι, X),)-> preimage(ι, i, bearers(X)) ∈ X, zip(ιs, Xs)) && push!(Σ, idx)
  end
  return (Σ, ιs)
end 

# Category of Implication Frames and Open Maps
####################################################

"""
A category where objects are implication frames and maps are functions 
f: ℒₘ → ℒₙ between bearer sets which are required to satisfy the following 
equation, for all good implications in 𝕀ₘ: f(i) ∈ 𝕀ₙ
"""
struct Open <: IFrameCat end
const OpenC = Open()

@instance ThCategory{ImpFrame, FMap} [model::Open] begin
  Hom(f::FMap, d::ImpFrame, c::ImpFrame; model) =
    is_natural(model, f, d, c) ? f : @fail join(
      naturality_failures(model, f, d, c), "\n")

  id(rr::ImpFrame) = FMap(collect(1:bearers(rr)))
  compose(f::FMap, g::FMap) = 
    FMap(ThCategory.compose[FinSetC()](getvalue(f), getvalue(g)))
end

"""
Check if a purported map satisfies the continuity constraint
"""
naturality_failures(::Open, f::FMap, d::ImpFrame{N}, c::ImpFrame{M}) where {N,M} = 
  filter(i -> f(impl_vec(M)[i]) ∉ d, c)


terminal(::Open) = ImpFrame([[]=>[1],[1]=>[],[1]=>[1]], 1)

"""
𝕀 of coproduct is equal to ⋃ ιᵢ(𝕀ᵢ)
"""
function coproduct(::Open, Xs::ImpFrame...)
  Σ, ιs = empty_coproduct(Xs...)
  for (ι, X) in zip(ιs, Xs)
    for j ∈ X 
      push!(Σ, ι(impl_vec(bearers(X))[j]))
    end
  end
  return (Σ, ιs)
end 




end # module

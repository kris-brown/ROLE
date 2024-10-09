module LimitsFinC 

using DataStructures: IntDisjointSets, find_root!

using ..Limits, ..Diagrams, ..Functions,  ..FinSets
import ..Limits: limit, colimit, universal

# Terminal object
#################
limit(e::EmptyDiagram, m::FinC) =
  Limit(Diagram(e, m), Multispan(FinSet(1), FinFunction[]))

universal(::EmptyDiagram, ::FinC, ::Multispan, c::Multispan) =
  FinFunction(fill(1, length(apex(c))), 1)

# Initial object
################

colimit(e::EmptyDiagram, m::FinC) =
  Colimit(Diagram(e, m), Multicospan(FinSet(), FinFunction[]))

universal(::EmptyDiagram, ::FinC, ::Multicospan, x::Multicospan) =
  FinFunction(Int[], apex(x))
 
# Products
##########

function limit(Xs::DiscreteDiagram, m::FinC)
  ns = length.(Xs)
  indices = CartesianIndices(Tuple(ns))
  n = prod(ns)
  πs = map(1:length(ns)) do j 
    FinFunction([indices[i][j] for i in 1:n], ns[j]) 
  end
  Limit(Diagram(Xs, m), Multispan(FinSet(n), πs))
end

function universal(::DiscreteDiagram, ::FinC, res::Multispan, cone::Multispan)
  ns = length.(codom.(cone))
  indices = LinearIndices(Tuple(ns))
  v = map(apex(cone)) do i 
    indices[(f(i) for f in cone)...]
  end
  FinFunction(v, apex(res))
end

# Coproducts
############

function colimit(Xs::DiscreteDiagram, m::FinC)
  ns = length.(Xs)
  n = sum(ns)
  offsets = [0, cumsum(ns)...]
  ιs = map(1:length(ns)) do j 
    FinFunction((1:ns[j]) .+ offsets[j], n) 
  end
  Colimit(Diagram(Xs, m), Multicospan(FinSet(n), ιs))
end

function universal(::DiscreteDiagram, ::FinC, ::Multicospan, cocone::Multicospan)
  FinFunction(mapreduce(collect, vcat, cocone, init=Int[]), apex(cocone))
end

# Equalizers
############

function limit(para::ParallelMorphisms, c::FinC)
  @assert !isempty(para)
  f1, frest = para[1], para[2:end]
  m = length(dom(para))
  eq = FinFunction(filter(i -> all(f1(i) == f(i) for f in frest), 1:m), m)
  Limit(Diagram(para, c), Multispan(dom(eq), [eq]))
end

function universal(::ParallelMorphisms, ::FinC, res::Multispan, cone::Multispan)
  ι = collect(only(res))
  h = only(cone)
  FinFunction(Int[only(searchsorted(ι, h(i))) for i in dom(h)], length(ι))
end


# Coequalizers
##############
function colimit(para::ParallelMorphisms, c::FinC)
  @assert !isempty(para)
  f1, frest = para[1], para[2:end]
  m, n = length(dom(para)), length(codom(para))
  sets = IntDisjointSets(n)
  for i in 1:m
    for f in frest
      union!(sets, f1(i), f(i))
    end
  end
  q = quotient_projection(sets)
  Colimit(Diagram(para, c), Multicospan(dom(q), [q]))
end

function universal(::ParallelMorphisms, ::FinC, res::Multicospan, cocone::Multicospan)
  pass_to_quotient(only(res), only(cocone))
end

""" Create projection map π: X → X/∼ from partition of X.
"""
function quotient_projection(sets::IntDisjointSets)
  h = [ find_root!(sets, i) for i in 1:length(sets) ]
  roots = unique!(sort(h))
  FinFunction([ searchsortedfirst(roots, r) for r in h ], length(roots))
end

""" Given h: X → Y, pass to quotient q: X/~ → Y under projection π: X → X/~.
"""
function pass_to_quotient(π::FinFunction, h::FinFunction)
  @assert dom(π) == dom(h)
  q = zeros(Int, length(codom(π)))
  for i in dom(h)
    j = π(i)
    if q[j] == 0
      q[j] = h(i)
    else
      q[j] == h(i) || error("Quotient map of colimit is ill-defined")
    end
  end
  any(==(0), q) && error("Projection map is not surjective")
  FinFunction(q, codom(h))
end

function pass_to_quotient(π::FinFunction, h::FinDomFunction)
  @assert dom(π) == dom(h)
  q = Vector{Union{Some{eltype(codom(h))},Nothing}}(nothing, length(codom(π)))
  for i in dom(h)
    j = π(i)
    if isnothing(q[j])
      q[j] = Some(h(i))
    else
      something(q[j]) == h(i) || error("Quotient map of colimit is ill-defined")
    end
  end
  any(isnothing, q) && error("Projection map is not surjective")
  FinDomFunction(map(something, q), codom(h))
end


end # module

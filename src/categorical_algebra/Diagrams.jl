module Diagrams 

export Diagram, EmptyDiagram, DiscreteDiagram, Multispan, Multicospan,
       ParallelMorphisms, BipartiteFreeDiagram, apex, legs, Span, Cospan

using StructEquality

using GATlab
import ..Functions: dom, codom

using ..Functions

abstract type DiagramImpl{Ob,Hom} end 

@struct_hash_equal struct Diagram{Ob, Hom}
  impl::DiagramImpl{Ob,Hom}
  cat::Model{Tuple{Ob,Hom}}
  function Diagram(i, c::Model{Tuple{Ob,Hom}}) where {Ob, Hom} 
    implements(c, ThCategory) || error("Bad model")
    new{Ob,Hom}(i, c)
  end
end 

@struct_hash_equal struct EmptyDiagram{Ob,Hom} <: DiagramImpl{Ob,Hom} end

""" Default diagram, given just a model of `ThCategory` """
Diagram(m::Model{Tuple{Ob,Hom}}) where {Ob, Hom} = Diagram(EmptyDiagram{Ob,Hom}(), m)

@struct_hash_equal struct DiscreteDiagram{Ob,Hom} <: DiagramImpl{Ob,Hom}
  objects::AbstractVector{Ob}
end

Base.length(m::DiscreteDiagram) = length(m.objects) 
Base.iterate(m::DiscreteDiagram, x...) = iterate(m.objects, x...)


""" Fails if there is no default model of `ThCategory` for Ob """
Diagram(v::AbstractVector{Ob}) where {Ob} = 
  Diagram(DiscreteDiagram(v), default(ThCategory, Ob))


@struct_hash_equal struct Multispan{Ob, Hom} <: DiagramImpl{Ob,Hom}
  apex::Ob
  legs::AbstractVector{Hom}
end

function Span(f,g)
  dom(f) == dom(g) || error("Cannot make span from $f and $g") 
  Multispan(dom(f), [f,g])
end

Multispan{Ob, Hom}(a::Ob) where {Ob, Hom}= Multispan{Ob, Hom}(a, Hom[])
apex(m::Multispan) = m.apex
legs(m::Multispan) = m.legs
Base.length(m::Multispan) = length(legs(m)) 
Base.iterate(m::Multispan, x...) = iterate(m.legs, x...)

@struct_hash_equal struct Multicospan{Ob, Hom} <: DiagramImpl{Ob,Hom}
  apex::Ob
  legs::AbstractVector{Hom}
end

function Cospan(f,g)
  codom(f) == codom(g) || error("Cannot make cospan from $f and $g") 
  Multicospan(codom(f), [f,g])
end

Multicospan{Ob, Hom}(a::Ob) where {Ob, Hom}= Multicospan{Ob, Hom}(a, Hom[])
apex(m::Multicospan) = m.apex
legs(m::Multicospan) = m.legs
Base.length(m::Multicospan) = length(legs(m)) 
Base.iterate(m::Multicospan, x...) = iterate(m.legs, x...)

@struct_hash_equal struct ParallelMorphisms{Ob, Hom} <: DiagramImpl{Ob,Hom}
  dom::Ob
  codom::Ob
  homs::AbstractVector{Hom}
end

Base.length(m::ParallelMorphisms) = length(m.homs) 
Base.iterate(m::ParallelMorphisms, x...) = iterate(m.homs, x...)
Base.getindex(m::ParallelMorphisms, x) = m.homs[x]
Base.lastindex(m::ParallelMorphisms) = lastindex(m.homs)

dom(p::ParallelMorphisms) = p.dom
codom(p::ParallelMorphisms) = p.codom


function ParallelMorphisms{Ob,Hom}(xs::AbstractVector{Hom}) where {Ob, Hom}
  isempty(xs) && error("Parallel morphisms must be nonempty")
  allequal(dom.(xs)) || error("Parallel morphism must share domain")
  allequal(codom.(xs)) || error("Parallel morphism must share domain")
  ParallelMorphisms{Ob,Hom}(dom(first(xs)), codom(first(xs)), xs)
end

@struct_hash_equal struct BipartiteFreeDiagram{Ob, Hom} <: DiagramImpl{Ob,Hom}
  ob₁::AbstractVector{Ob}
  ob₂::AbstractVector{Ob}
  homs::AbstractVector{Tuple{Int,Int,Hom}}
end

end # module 

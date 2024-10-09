module Limits 

export Limit, Colimit, cone, cocone, terminal, initial, product, coproduct,
       limit, colimit, universal, create, delete, equalizer, coequalizer, proj,
       incl, factorize

using StructEquality
import AlgebraicInterfaces: ob

using GATlab 

using ..Diagrams, ..Functions
import ..Diagrams: apex, legs


const C{Ob,Hom} = Model{Tuple{Ob,Hom}}

@struct_hash_equal struct Limit{Ob, Hom}
  diag::Diagram{Ob,Hom}
  cone::Multispan{Ob, Hom}
end 

ob(lim::Limit) = apex(lim)
cone(lim::Limit) = lim.cone
apex(lim::Limit) = apex(cone(lim)) 
legs(lim::Limit) = legs(cone(lim))


@struct_hash_equal struct Colimit{Ob, Hom}
  diag::Diagram
  cocone::Multicospan{Ob, Hom}
end 

cocone(colim::Colimit) = colim.cocone
apex(colim::Colimit) = apex(cocone(colim))
ob(colim::Colimit) = apex(colim)
legs(colim::Colimit) = legs(cocone(colim))

# Generic (co)limits
####################
limit(d::Diagram) = limit(d.impl, d.cat)
colimit(d::Diagram) = colimit(d.impl, d.cat)

terminal(m::Model; kw...) = limit(Diagram(m); kw...)

initial(m::Model; kw...) = colimit(Diagram(m); kw...)

product(xs::AbstractVector, model::C{Ob,Hom}) where {Ob, Hom} = 
  limit(DiscreteDiagram{Ob,Hom}(xs), model)

coproduct(xs::AbstractVector, model::C{Ob,Hom}) where {Ob, Hom} = 
  colimit(DiscreteDiagram{Ob,Hom}(xs), model)

equalizer(xs::AbstractVector, model::C{Ob,Hom}) where {Ob, Hom} = 
  limit(ParallelMorphisms{Ob,Hom}(xs), model)

coequalizer(xs::AbstractVector, model::C{Ob,Hom}) where {Ob, Hom} = 
  colimit(ParallelMorphisms{Ob,Hom}(xs), model)


function universal(c::Limit{Ob,Hom}, x::Multispan{Ob,Hom})::Hom where {Ob,Hom} 
  universal(c.diag.impl, c.diag.cat, c.cone, x)
end

function universal(c::Colimit{Ob,Hom}, x::Multicospan{Ob,Hom})::Hom where {Ob,Hom} 
  universal(c.diag.impl, c.diag.cat, c.cocone, x)
end

function create(l::Colimit{Ob,Hom}, x::Ob) where {Ob,Hom} 
  l.diag.impl isa EmptyDiagram || error(
    "Can only call `create` on EmptyDiagram colimits")
  universal(l, Multicospan{Ob,Hom}(x))
end

function delete(l::Limit{Ob,Hom}, x::Ob) where {Ob,Hom} 
  l.diag.impl isa EmptyDiagram || error(
    "Can only call `delete` on EmptyDiagram limits")
  universal(l, Multispan{Ob,Hom}(x))
end


create(x::Ob, mod::C{Ob,Hom}) where {Ob,Hom} = create(initial(mod), x)
delete(x::Ob, mod::C{Ob,Hom}) where {Ob,Hom} = delete(terminal(mod), x)
proj(coeq::Colimit) = only(legs(coeq))
incl(eq::Limit) = only(legs(eq))

function factorize(lim::Limit{Ob,Hom}, h::Hom) where {Ob,Hom} 
  lim.diag.impl isa ParallelMorphisms || error(
    "Can only call `factorize` on ParallelMorphisms colimits")
  universal(lim, Multispan(dom(h), [h]))
end 
function factorize(colim::Colimit{Ob,Hom}, h::Hom) where {Ob,Hom} 
  colim.diag.impl isa ParallelMorphisms || error(
    "Can only call `factorize` on ParallelMorphisms colimits")
  universal(colim, Multicospan(dom(h), [h]))
end

end # module 

"""
This is very much a work in progress. An attempt to extract relevant ideas from 
Catlab.jl.
"""
module CategoricalAlgebra 

export dom, codom

function dom end 
function codom end 

struct Span{Ob, Hom}
  apex::Ob
  left::Hom
  right::Hom
end 

struct Copan{Ob, Hom}
  apex::Ob
  left::Hom
  right::Hom
end 


struct Multispan{Ob, Hom}
  apex::Ob
  homs::AbstractVector{Hom}
end 


struct Multicospan{Ob, Hom}
  apex::Ob
  homs::AbstractVector{Hom}
end 


struct Product{Ob, Hom}
  apex::Ob
  proj::Multispan{Ob, Hom}
end

struct Coproduct 
  apex::Ob
  inj::Multispan{Ob, Hom}
end

function universal(c::Coproduct{Ob,Hom}, csp::Multicospan)::Multicospan{Ob,Hom}
  
end


end # module
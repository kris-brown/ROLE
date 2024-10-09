module Theories 

using GATlab

@theory ThSet′ begin
  Bool′::TYPE
  Int′::TYPE
  Any′::TYPE
  Set′::TYPE
  in′(e::Any′, s::Set′)::Bool′
  eltype′(s::Set′)::Any′
end

@theory ThFinSet′ <: ThSet′ begin
  length′(s::Set′)::Int′
  iterate′(s::Set′)::Any′
  iterate′(s::Set′,a::Any′)::Any′
end

# """ Inclusion morphism """
# @theorymap ι(ThSet, ThSet) begin
#   Bool′ => Bool′
#   Any′ => Any′
#   Int′ => Int′
#   Set′ => Set′
#   in′(e,s) ⊣ [e::Any′, s::Set′] => in′(e,s)
# end




end # module

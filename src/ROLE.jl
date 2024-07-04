module ROLE

using Reexport

include("RRels.jl")
include("RMaps.jl")
@reexport using .RRels
@reexport using .RMaps

end # module
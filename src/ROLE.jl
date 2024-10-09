module ROLE

using Reexport

include("Impls.jl")
include("ImplSets.jl")
include("ImpFrames.jl")
include("Roles.jl")
include("Contents.jl")

include("categorical_algebra/module.jl")

include("RMaps.jl")

@reexport using .Impls
@reexport using .ImplSets
@reexport using .ImpFrames
@reexport using .Roles
@reexport using .Contents

@reexport using .CategoricalAlgebra

@reexport using .RMaps

end # module

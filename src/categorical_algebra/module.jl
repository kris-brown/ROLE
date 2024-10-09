
module CategoricalAlgebra

using Reexport

include("Theories.jl")
include("Sets.jl")
include("FinSets.jl")
include("Functions.jl")
include("Diagrams.jl")
include("Limits.jl")
include("LimitsFinC.jl")


@reexport using .FinSets
@reexport using .Sets
@reexport using .Functions
@reexport using .Diagrams
@reexport using .Limits

end # module

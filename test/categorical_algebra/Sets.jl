module TestSets

using Test,  ROLE.CategoricalAlgebra.Sets

@test 3 ∈ SetOb(Int)
@test :a ∈ SetOb(Symbol)
@test :a ∉ SetOb(Int)

@test :a ∈ SetOb(EitherSet(SetOb(Int), SetOb(Symbol)))
@test :a ∈ SetOb(EitherSet(SetOb(Symbol), SetOb(Symbol)))


end # module

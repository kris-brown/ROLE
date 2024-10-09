module TestFinSets

using GATlab, ROLE, Test

using .ThCategory


for s₁₂₃ in [FinSet(3), 
             FinSet(Set([1,2,3])),
             FinSet(EitherFinSet(FinSet(2), FinSet(Set([3]))))
             ]
  @test 2 ∈ s₁₂₃
  @test 4 ∉ s₁₂₃
  @test length(s₁₂₃) == 3
  @test sort(collect(s₁₂₃)) == Int[1,2,3]
end


struct NewFinSetType end
struct NewFinSetTypeModel <: Model{Tuple{Bool, Int, Any, NewFinSetType}} end
# Hasn't implemented *how* this thing is supposed to be treated as FinSet: error
@test_throws MethodError FinSet(NewFinSetType(), NewFinSetTypeModel())


2 ∈ SetOb(FinSet(3)) # coercion to SetOb from FinSet


end # module
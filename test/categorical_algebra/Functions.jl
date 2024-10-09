module TestFunctions 

using Test, ROLE, GATlab

using .ThCategory

# FinFunctions
##############

ab = FinSet(Set([:a,:b]))
s₁₂₃ = FinSet(3)
f = FinFunction(Dict(:a=>2, :b=>3), FinSet(3))
g = FinFunction([3,2,1], FinSet(3))
x =  FinFunction(Dict(:a=>2, :b=>1), FinSet(3))


@withmodel FinC() (id, ⋅) begin 
  @test id(ab) ⋅ f ⋅ g == x
end

# FinDomFunctions
#################

f′ = FinDomFunction(f)
g′ = FinDomFunction(FinSet(3), SetOb(String), FinFunctionVector(["3","2","1"]))
x′ =  FinDomFunction(FinSet(Set([:a,:b])), SetOb(String), FinFunctionDict(Dict(:a=>"2", :b=>"1")))

@withmodel FinDomC() (id, ⋅) begin 
  @test id(ab) ⋅ f′ ⋅ g′ == x′
end

# VarFunctions
##############
T(x::SetOb) = SetOb(EitherSet(x, SetOb(AttrVal{Symbol})))
T(x::FinSet) = T(SetOb(x))

f′′ = VarFunction{Symbol}(Dict(:a=>AttrVal{Symbol}(:X), :b=>3), T(FinSet(3)))
g′′ = VarFunction{Symbol}(FinSet(3), T(SetOb(String)), FinFunctionVector(["3","2","1"]))
x′′ =  VarFunction{Symbol}(FinSet(Set([:a,:b])), T(SetOb(String)), FinFunctionDict(Dict(:a=>AttrVal{Symbol}(:X), :b=>"1")))

z = @withmodel AttrC{Symbol}() (id, ⋅) begin 
  @test id(ab) ⋅ f′′ ⋅ g′′ == x′′
end

end # module
module Sets 

export SetOb, TypeSet, EitherSet

using StructEquality

using GATlab

using ..Theories: ThSet′

# Shorthand 
const M{T} = Model{Tuple{Bool, Int, Any, T}}

# Sets
######

@struct_hash_equal struct SetOb
  impl::Any
  mod::Any
  SetOb(i::T, m::M{T}) where {T} = 
    implements(m, ThSet′) ? new(i, m) : throw(MethodError("Bad model $i $m"))
end

Base.in(e, f::SetOb) = ThSet′.in′[f.mod](e, f.impl)
Base.eltype(s::SetOb) = eltype(s.impl)

# Implementations

""" Raw Julia type """
@struct_hash_equal struct TypeSet{T} end

@struct_hash_equal struct TypeSetImpl{T} <: M{TypeSet{T}} end

@instance ThSet′{Bool, Int, Any, TypeSet{T}} [model::TypeSetImpl{T}] where T begin
  in′(i::Any, s::TypeSet{T})::Bool = i isa T
  eltype′(s::TypeSet{T})::Any = T
end

""" Default model for a Set made out of a Julia `Type` """
SetOb(T::Type) = SetOb(TypeSet{T}(), TypeSetImpl{T}())

""" Sum type """
@struct_hash_equal struct EitherSet
  left::SetOb
  right::SetOb
end

@struct_hash_equal struct EitherSetImpl <: M{EitherSet} end

@instance ThSet′{Bool, Int, Any, EitherSet} [model::EitherSetImpl] begin
  in′(i::Any, s::EitherSet)::Bool = i ∈ s.left || i ∈ s.right
  eltype′(s::EitherSet)::Any = Union{eltype(s.left), eltype(s.right)}
end

SetOb(s::EitherSet) = SetOb(s, EitherSetImpl())

end # module

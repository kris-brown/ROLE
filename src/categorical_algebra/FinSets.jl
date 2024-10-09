module FinSets
export FinSet, FinSetInt, FinSetHash, EitherFinSet

using StructEquality

using GATlab
import GATlab: getvalue

using ..Theories: ThFinSet′
using ..Sets
using ..Sets: M
import ..Sets: SetOb


"""
A type of finite sets which implements the ThFinSet interface.
"""
@struct_hash_equal struct FinSet
  impl::Any
  mod::Any
  FinSet(i::T, m::M{T}) where {T} = 
    implements(m, ThFinSet′) ? new(i, m) : throw(MethodError("Bad model $i $m"))
end

Base.in(e, f::FinSet) = ThFinSet′.in′[f.mod](e, f.impl)
Base.length(f::FinSet) = ThFinSet′.length′[f.mod](f.impl)
Base.iterate(f::FinSet, args...) = ThFinSet′.iterate′[f.mod](f.impl, args...)
Base.eltype(s::FinSet) = eltype(s.impl)

# Normally we would have to migrate the model, but because the sorts are the 
# same between the two theories, this is unnecessary.
""" Explicitly cast FinSet as SetOb. This will always succeed. """
SetOb(f::FinSet) = SetOb(f.impl, f.mod) # migrate_model(ι, f.mod)) 

""" Attempt to case SetOb to FinSet ... this can throw runtime error."""
FinSet(s::SetOb) = FinSet(s.impl, s.mod) 

# Implementations
#----------------

"""
A set {1,2,...,n} represented by a single `Int`
"""
@struct_hash_equal struct FinSetInt
  n::Int
end 

@struct_hash_equal struct FinSetIntImpl <: M{FinSetInt} end

@instance ThFinSet′{Bool, Int, Any, FinSetInt} [model::FinSetIntImpl] begin
  in′(i::Any, s::FinSetInt)::Bool = 0 < i ≤ s.n
  eltype′(s::FinSetInt)::Any = Int
  length′(s::FinSetInt)::Int = s.n
  iterate′(s::FinSetInt)::Any = iterate(1:s.n)
  iterate′(s::FinSetInt, x::Any)::Any = iterate(1:s.n, x)
end

""" Default model for a finset made out of a Julia `Int` """
FinSet(i::Int) = FinSet(FinSetInt(i), FinSetIntImpl())

""" Default FinSet with no parameters """
FinSet() = FinSet(0)

"""
A Julia finite set.
"""
@struct_hash_equal struct FinSetHash{T}
  set::Set{T}
end 

@struct_hash_equal struct FinSetHashImpl{T} <: M{FinSetHash{T}} end

@instance ThFinSet′{Bool, Int, Any, FinSetHash{T}
                  } [model::FinSetHashImpl{T}] where T begin
  in′(i::Any, s::FinSetHash{T})::Bool = i ∈ s.set
  eltype′(s::FinSetHash{T}) = T
  length′(s::FinSetHash{T})::Int = length(s.set)
  iterate′(s::FinSetHash{T})::Any = iterate(s.set)
  iterate′(s::FinSetHash{T}, x::Any)::Any = iterate(s.set, x)
end

""" Default model for a finset made out of a Julia `Set` """
FinSet(s::Set{T}) where T = FinSet(FinSetHash(s), FinSetHashImpl{T}())

""" Sum type """
@struct_hash_equal struct EitherFinSet
  left::FinSet
  right::FinSet
end

@struct_hash_equal struct EitherFinSetImpl  <: M{EitherFinSet} end

@instance ThFinSet′{Bool, Int, Any, EitherFinSet} [model::EitherFinSetImpl] begin
  in′(i::Any, s::EitherFinSet)::Bool = i ∈ s.left || i ∈ s.right
  eltype′(f::EitherFinSet)::Any = Union{eltype(s.left), eltype(s.right)}
  length′(s::EitherFinSet)::Int = length(s.left) + length(s.right)
  iterate′(s::EitherFinSet)::Any = iterate([s.left...,s.right...])
  iterate′(s::EitherFinSet, x::Any)::Any = iterate([s.left...,s.right...], x)
end

""" Default model for an eitherset """
FinSet(s::EitherFinSet) = FinSet(s, EitherFinSetImpl())


end # module 

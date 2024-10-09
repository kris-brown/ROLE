module ImplSets 
export ImplSet, ⊗

using StructEquality

using ..Impls 
using ..Impls: BitSetWrapper, ImpDict, compute_impldict!
import ..Impls: bearers

const iproduct = Iterators.product

"""
A set of implications, e.g. {(a,b ⊢ b), (b ⊢ a)}.

Given an index for each implication in the space of possible implications for 
some number of bearers, N, this data is captured by a BitSet. 
"""
@struct_hash_equal struct ImplSet{N} <: BitSetWrapper
  value::BitSet
  ImplSet{N}(v::BitSet=BitSet()) where N = new{N}(v)
end 

ImplSet(v::AbstractVector{Int}, N::Int) = ImplSet{N}(BitSet(v))

function ImplSet(v::AbstractVector{Impl{N}}) where N
  haskey(ImpDict, N) || compute_impldict!(N) # compute this and cache
  ImplSet{N}(BitSet(getindex.(Ref(impl_dict(N)), v)))
end

ImplSet(i::Impl{N}) where N = ImplSet([i])

bearers(::ImplSet{N}) where N = N

is_top(i::ImplSet{N}) where N = length(i) == 2^(2*N)

top(i::Int) = ImplSet{i}(BitSet(1:2^(2*i)))

top(::Type{ImplSet{N}}) where N = top(N)

Base.union(i::Vector{ImplSet{N}}) where N = 
  ImplSet{N}(isempty(i) ? BitSet() : union(getvalue.(i)...))

Base.intersect(i::Vector{ImplSet{N}}) where N = 
  isempty(i) ? top(N) : ImplSet{N}(intersect(getvalue.(i)...))

function Base.show(io::IO, ::MIME"text/plain", i::ImplSet{N}) where N
  str = ["($(string(impl_vec(N)[x])))" for x in getvalue(i)]
  print(io, "{$(join(str,","))}")
end

Base.string(i::ImplSet) = sprint(show, "text/plain", i)

"""
Quantale monoidal operation for 𝒫(S) where (S, 0, ∪) is a monoid.
"""
function ⊗(xs::Vector{ImplSet{N}})::ImplSet{N} where N
  isempty(xs) && return ImplSet([Impl{N}()]) # unit of the ⊗ operation
  v = impl_vec(N)
  map(collect.(iproduct(xs...))) do imp_tuple # iterate over cartesian product
    i = Impl{N}()
    for it in imp_tuple 
      union!(i, v[it])
    end
    i 
  end |> vec |> Vector{Impl{N}} |> ImplSet
end

⊗(xs::ImplSet{N}...) where N = ⊗(collect(xs))

end # module

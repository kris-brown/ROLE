module Functions 

export FinFunction, FinFunctionDict, FinFunctionVector, FinDomFunction,
       VarFunction, FinC, FinDomC, AttrC, AttrVal, dom, codom, force

import AlgebraicInterfaces: dom, codom

using GATlab

using StructEquality

using ..Sets, ..FinSets

# Fin(Dom)Functions
###################

""" 
We *don't* go through the GATlab process for function impls. The only interface 
they must satisfy is that calling `impl` on an element of `dom` gives an element 
of `codom` and `postcompose` with another FinFunction yields another impl.
"""
abstract type AbsFun end 

"""
A FinFunction has a finite set as domain and as codomain.
"""
@struct_hash_equal struct FinFunction <: AbsFun
  dom::FinSet
  codom::FinSet
  impl::Any
  function FinFunction(dom, codom, impl; check=true) 
    if check 
      for x in dom 
        impl(x) ∈ codom || error("Bad function f($x) = $(impl(x)) ∉ $codom")
      end
    end
    new(dom, codom, impl)
  end
end

dom(f::FinFunction) = f.dom
codom(f::FinFunction) = f.codom
(f::FinFunction)(i) = f.impl(i)
Base.collect(f::FinFunction) = [f(x) for x in dom(f)]
force(f::FinFunction) = FinFunction(f.dom, f.codom, 
                                    FinFunctionVector([f(x) for x in f.dom]))


@struct_hash_equal struct FinC <: Model{Tuple{FinSet,FinFunction}} end 
 
@instance ThCategory{FinSet,FinFunction} [model::FinC] begin
  id(s::FinSet)::FinFunction = FinFunction(s)
  function compose(f::FinFunction, g::FinFunction)::FinFunction 
    FinFunction(dom(f), codom(g), postcompose(f.impl, g))
  end
end

"""
Domain must be a FinSet, codom must be a SetOb
"""
@struct_hash_equal struct FinDomFunction <: AbsFun
  dom::FinSet
  codom::SetOb
  impl::Any
  function FinDomFunction(dom, codom, impl; check=false) 
    if check 
      for x in dom 
        impl(x) ∈ codom || error("Bad function f($x) = $(impl(x)) ∉ $codom")
      end
    end
    new(dom, codom, impl)
  end
end

dom(f::FinDomFunction)::FinSet = f.dom
codom(f::FinDomFunction)::SetOb = f.codom
(f::FinDomFunction)(i) = f.impl(i)

""" Cast a FinFunction to a FinDomFunction """
FinDomFunction(f::FinFunction) = FinDomFunction(f.dom, SetOb(f.codom), f.impl)

""" Category of FinDomFunctions """
@struct_hash_equal struct FinDomC <: Model{Tuple{FinSet,FinDomFunction}} end 
 
@instance ThCategory{FinSet,FinDomFunction} [model::FinDomC] begin
  id(s::FinSet)::FinDomFunction = FinDomFunction(s)
  function compose(f::FinDomFunction, g::FinDomFunction)::FinDomFunction 
    FinDomFunction(dom(f), codom(g), postcompose(f.impl, g))
  end
end



# Implementations
#----------------
""" 
Valid function when domain is indexed by positive integers less than the 
vector length.
"""
@struct_hash_equal struct FinFunctionVector
  val::Vector
end

(f::FinFunctionVector)(i::Int) = f.val[i]

postcompose(f::FinFunctionVector, g::AbsFun) = 
  FinFunctionVector([g(x) for x in f.val])

""" 
Default `FinFunction` from a `AbstractVector` and codom
Assumes the domain is a `FinSetInt`
"""
FinFunction(f::AbstractVector, cod::FinSet) = 
  FinFunction(FinSet(length(f)), cod, FinFunctionVector(f))

""" Default `FinFunction` between `FinSetInt`s. """
FinFunction(f::AbstractVector, cod::Int) = FinFunction(f, FinSet(cod))

FinDomFunction(f::AbstractVector, cod::FinSet) = FinDomFunction(FinFunction(f, cod))
FinDomFunction(f::AbstractVector, cod::SetOb) = 
  FinFunction(FinSet(length(f)), cod, FinFunctionVector(f))

@struct_hash_equal struct IdentityFunction end

(::IdentityFunction)(x) = x
postcompose(::IdentityFunction, g::AbsFun) = g.impl

""" Default `FinFunction` from a `FinSet`"""
FinFunction(s::FinSet) = FinFunction(s, s, IdentityFunction())
FinDomFunction(s::FinSet) = FinDomFunction(FinFunction(s))

""" 
Valid function when domain is indexed by positive integers less than the 
vector length.
"""
@struct_hash_equal struct FinFunctionDict
  val::Dict
end

(d::FinFunctionDict)(k) = d.val[k]
postcompose(f::FinFunctionDict, g::AbsFun) = 
  FinFunctionDict(Dict(k => g(v) for (k,v) in f.val))

""" Default `FinFunction` from a `AbstractVector` and codom"""
FinFunction(f::AbstractDict, cod::FinSet) = 
  FinFunction(FinSet(Set(collect(keys(f)))), cod, FinFunctionDict(f))

FinDomFunction(f::AbstractDict, cod::FinSet) = FinDomFunction(FinFunction(f, cod))

FinDomFunction(f::AbstractDict, cod::SetOb) = 
  FinDomFunction(FinSet(Set(collect(keys(f)))), cod, FinFunctionDict(f))



# VarFunction
#############

@struct_hash_equal struct AttrVal{T}
  val::T 
end

function getvalue(a::AttrVal{T})::T where T 
  a.val
end

"""
A VarFunction is a FinFunction with a codomain of "+ T" for some type T.
"""
@struct_hash_equal struct VarFunction{T} <: AbsFun
  impl::FinDomFunction
  function VarFunction{T}(f::FinDomFunction) where T 
    codom(f).impl isa EitherSet || error("VarFunctions have EitherSets as codom")
    rgt = codom(f).impl.right.impl
    rgt == TypeSet{AttrVal{T}}() || error("VarFunction{T} codom is Either(-, T): $rgt")
    new{T}(f)
  end
end

VarFunction{T}(args...) where T = VarFunction{T}(FinDomFunction(args...))

dom(f::VarFunction)::FinSet = f.impl.dom
codom(f::VarFunction)::SetOb = f.impl.codom.impl.left

(f::VarFunction)(i) = f.impl(i) # regular function on non-AttrVals
(f::VarFunction{T})(v::AttrVal{T}) where T = v # no-op on AttrVals

@struct_hash_equal struct AttrC{T} <: Model{Tuple{FinSet,VarFunction{T}}} end 

@instance ThCategory{FinSet,VarFunction{T}} [model::AttrC{T}] where T begin
  id(s::FinSet)::VarFunction{T} = 
    VarFunction{T}(s, SetOb(EitherSet(SetOb(s), SetOb(AttrVal{T}))), IdentityFunction())
  function compose(f::VarFunction{T}, g::VarFunction{T})::VarFunction{T} 
    VarFunction{T}(FinDomFunction(dom(f), g.impl.codom, postcompose(f.impl.impl, g)))
  end
end

postcompose(::IdentityFunction, g::VarFunction{T}) where T = g.impl.impl


end # module 

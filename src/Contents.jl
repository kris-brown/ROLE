module Contents 

export Content, contents, getcontent, ¬, →, ∨, ∧, ⪯, ⊩, ⊮

using StructEquality

using ..Impls, ..ImplSets, ..ImpFrames, ..Roles
using ..Roles: prem_role, conc_role
import ..Roles: ⊔
import ..Impls: prem, conc

# Conceptual contents 
#####################


@struct_hash_equal struct Content{F}
  prem::Role{F}
  conc::Role{F}
end

"""Accessor function"""
function prem(c::Content{F})::Role{F} where F 
  c.prem 
end

"""Accessor function"""
function conc(c::Content{F})::Role{F} where F 
  c.conc
end

getcontent(i::ImpFrame, a::Int) = Content(prem_role(i, a), conc_role(i, a))

contents(i::ImpFrame{N}) where N = [getcontent(i, a) for a in 1:N]

Base.iterate(c::Content, i...) = iterate((prem(c), conc(c)), i...)

¬(c::Content{F}) where F = Content{F}(conc(c), prem(c))

function →(a::Content{F}, b::Content{F}) where F  
  ((a⁺, a⁻), (b⁺, b⁻)) = (a, b)
  Content{F}(a⁻ ⊓ b⁺ ⊓ (a⁻ ⊔ b⁺) , a⁺ ⊔ b⁻) 
end

function ∧(a::Content{F}, b::Content{F}) where F  
  ((a⁺, a⁻), (b⁺, b⁻)) = (a, b)
  Content{F}(a⁺ ⊔ b⁺,  a⁻ ⊓ b⁻ ⊓ (a⁻ ⊔ b⁻)) 
end

function ∨(a::Content{F}, b::Content{F}) where F  
  ((a⁺, a⁻), (b⁺, b⁻)) = (a, b)
  Content{F}(a⁺ ⊓ b⁺ ⊓ (a⁺ ⊔ b⁺), a⁻ ⊔ b⁻) 
end

# "Adjunction" of contents (pointwise)
⊔(r1::Content{F}, r2::Content{F}) where F = 
  Content{F}(prem(r1) ⊔ prem(r2), conc(r1) ⊔ conc(r2))


"""
Content entailment for lists of conceptual contents Γ and Δ

⟦Γ⟧ ⊩ ⟦Δ⟧ := ⟦Γ⟧⁺ ⊔ ⟦Δ⟧⁻ ⊆ 𝕀
"""
function ⊩(x::AbstractVector{Content{F}}, y::AbstractVector{Content{F}}) where {F}
  f = get_frame(F)
  v = ⊔(Role{F}[prem.(x)..., conc.(y)...])
  rsr(f,ImplSet(v)) ⊆ getvalue(f) # 𝕀
end

⊩(x::Content{F}, y::Content{F}) where F = [x] ⊩ [y]
⊩(x::Content{F}, y::AbstractVector{Content{F}}) where F = [x] ⊩ y
⊩(x::AbstractVector{Content{F}}, y::Content{F}) where F = x ⊩ [y]

⊮(x, y) = !(x ⊩ y)

end # module

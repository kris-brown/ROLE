using ROLE, Test
using ROLE.RRels: containment, all_implications, RRelRSR, add
using ROLE.RMaps: naturality_failures, ideal

using GATlab 

using .ThCategory

# Implications
##############
i = Implication([2,4],[1])
@test string(i) == "2,4 ⊢ 1"

@test i + i == i

# Reason relations
##################
rrel = RRel(2, [Int[]=>[1], [1,2]=>Int[], [1]=>[2]]);

@test length(collect(all_implications(3))) == 2^3 * 2^3
@test length(collect(containment(2, false))) == 7
@test length(collect(containment(2, true))) == (2^2 * 2^2) - 7

empty_rrel = RRel(3)
rand_rrel = RRel(3; random=true)

# Reason relations with cached RSRS
###################################
rsrs = RRelRSR(rrel)
RSRa⁺, RSRa⁻ = rsrs[[1],[]], rsrs[[],[1]]
@test RSRa⁺ ∈ rsrs.prem[1]
@test RSRa⁺ ∉ rsrs.conc[1]
RSRb⁺, RSRb⁻ = rsrs[[2],[]], rsrs[[],[2]]
@test RSRb⁺ ∈ rsrs.RSR[RSRa⁺]
@test RSRa⁺ ∈ rsrs.RSR[RSRb⁺]

one′ = rsrs[[],[1]]
@test one′ ∉ rsrs.RSR[RSRb⁺]
@test one′ ∈ rsrs.RSR[one′]

idx₁₂ = rsrs[[1,2],[]]
@test add(rsrs, RSRa⁺, RSRb⁺) == idx₁₂
@test add(rsrs, RSRa⁺, one′) == 0 # these implications intersect

# Computing with RSRs
#####################

@test RSRb⁺ ∈ RSR(rsrs, RSRa⁺)
@test RSRb⁻ ∈ RSR(rsrs, RSRa⁺)
@test RSRa⁺ ∉ RSR(rsrs, RSRa⁺)

@test RSRa⁺ ∉ RSR(rsrs, RSRb⁺)


a⁺,a⁻,b⁺,b⁻  = Role.([[RSRa⁺],[RSRa⁻],[RSRb⁺],[RSRb⁻]])

RSRab⁺ = rsrs[[1,2],[]]
ab⁺ = Role([RSRab⁺])
ab⁻ = Role([rsrs[[],[1,2]]])

a_b⁺ = Role([RSRa⁺, RSRb⁺])
a_b⁻ = Role([RSRa⁻, RSRb⁻])

@test ⊔(rsrs, a_b⁺, a_b⁺) == Role([RSRa⁺, RSRb⁺, RSRab⁺])
@test ⊔(rsrs, a⁺, b⁺) == ab⁺
@test ⊓(b⁺, a_b⁺) == a_b⁺

# RRel morphisms
###############

(m,) = homomorphisms(rsrs, rsrs)
@withmodel RRelC() (id, (⋅)) begin
  @test m == id(rrel)
  @test m == m ⋅ m
end

# Interpretation functions
##########################
# [a, b, ¬a, ¬b, a∧b, a∨b]
elab = RRel(6, [Int[]=>[1], [1,2]=>Int[], [1]=>[2], ]); # TODO

a_b_ab = ⊓(a⁺, b⁺, ⊔(rsrs, a⁻,b⁻))

# elab → rrel
interp = Interp([a⁺,b⁺,a⁻,b⁻,ab⁺, a_b_ab],
                [a⁻,b⁻,a⁺,b⁺, a_b_ab, ab⁺]) 

ideal(interp, rrel)


#               ×        ×          ✓         ✓        ×        ✓
# a- has RSR {∅ ⊢ ∅ || 1 ⊢ ∅ || 1,2 ⊢ ∅ || ∅ ⊢ 1 || 2 ⊢ 1 || 1 ⊢ 2}
a = ideal(Interp([a⁺], [a⁻]), rsrs )

⊤ = Role(1:9)
               # ✓         ×         ×
⊔(rsrs, ⊤, a⁻) # ⊢ 1 ||  2 ⊢ 1  ||  ⊢ 1,2
"""
Γ BitSet([]), Δ BitSet([1])
    p(Γ) BitSet[]
    c(Δ) BitSet[BitSet([5])]
    role(⊔...)) BitSet([5])
    COMPUTING RSR w/ is=BitSet([5])
        intersect BitSet([1, 2, 4, 5, 8])
    RES BitSet([1, 2, 4, 5, 8]) 
"""

neg_a = ideal(Interp([a⁺,b⁺,a⁻], 
                     [a⁻,b⁻,a⁺]), rsrs )


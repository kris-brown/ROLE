using ROLE, Test
using ROLE.RRels: containment, all_implications, RRelRSR
using ROLE.RMaps: naturality_failures

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
idx₁ = rsrs[[1],[]]
@test idx₁ ∈ rsrs.prem[1]
@test idx₁ ∉ rsrs.conc[1]
idx₂ = rsrs[[2],[]]
@test idx₂ ∈ rsrs.RSR[idx₁]
@test idx₁ ∈ rsrs.RSR[idx₂]

one′ = rsrs[[],[1]]
@test one′ ∉ rsrs.RSR[idx₂]
@test one′ ∈ rsrs.RSR[one′]

# RSR morphisms
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

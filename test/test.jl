using ROLE, Test
using ROLE.RRels: containment, all_implications, RRelRSR
using ROLE.RMaps: naturality_failures

i = Implication([2,4],[1])
@test string(i) == "2,4 ⊢ 1"

@test i + i == i

rrel = RRel(2, [Int[]=>[1], [1,2]=>Int[], [1]=>[2]]);

@test length(collect(all_implications(3))) == 2^3 * 2^3
@test length(collect(containment(2, false))) == 7
@test length(collect(containment(2, true))) == (2^2 * 2^2) - 7

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

hs = homomorphisms(rsrs, rsrs)
@test all(is_natural.(hs, Ref(rrel), Ref(rrel)))

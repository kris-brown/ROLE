module TestImpFrames
using ROLE, Test
using Combinatorics: powerset

# Implications
##############
i = Impl([2,4],[1]) # assumes 4 is max bearer
@test string(i) == "2,4 ⊢ 1"
j = Impl([],[2], 4) # explicit: four bearers
union!(i, j) # mutates i
@test string(i) == "2,4 ⊢ 1,2"


@test i ∪ i == i

# Implication sets
##################
X = ImplSet([Impl([2],[1]), Impl([1],[],2)])
Y = ImplSet([Impl([1],[2]), Impl([],[],2)])
Z = ImplSet([Impl([],[2])])

@test ⊗(X, Y, Z) == ImplSet([Impl([1,2],[1,2]), Impl([1],[2]), Impl([2],[1,2])])

@test ⊗(X, Y, ImplSet{2}()) == ImplSet{2}()
@test ⊗(ImplSet{2}[]) == ImplSet([Impl{2}()])

# Reason relations
##################

rrel = ImpFrame([[]=>[1], [1,2]=>[], [1]=>[2]], 2; names=[:a,:b]);
@test string(rrel) |> strip ==  """
|     |   | a | b | a,b |
|-----|---|---|---|-----|
|     | ✓ | ✓ | × |   × |
|   a | × | × | ✓ |   × |
|   b | × | × | × |   × |
| a,b | ✓ | × | × |   × |
""" |> strip

empty_rrel = ImpFrame(3)
@test length(empty_rrel) == 1
@test !isempty(empty_rrel)
rand_rrel = ImpFrame(3; random=true)
@test !isempty(rand_rrel) # most likely true

@test string(rsr(rrel, Impl([], [1], rrel))) == "{( ⊢ ),( ⊢ 1)}"

# Role lattices
###############

rlattice = RoleLattice(rrel);
# In general, it's not feasible to enumerate all possible sets of implications
# In the case of 2 bearers, this is 2^(2^(2+2))=65536
all_imps = BitSet.(powerset(1:2^(2+2)))|> collect

for i in all_imps
  iset = rsr(rrel, ImplSet{2}(i))
  r = rlattice(iset; check=true)
end # check that all possible RSRs can be expressed

# x ⊗ y = z ⟹ rsr(x) ⊔ rsr(y) = rsr(z)
for _ in 1:10
  is1, is2 = is = ImplSet{2}.(rand(all_imps[1:20], 2))
  r1, r2 = rlattice.(rsr.(Ref(rrel), is))
  r1r2 = rlattice(rsr(rrel, is1 ⊗ is2))
  @test r1r2 == r1 ⊔ r2

  c1, c2 = Content(r1, r2), Content(r2,r2)
  @test (c1 → c2) == (¬c1 ∨ c2) # check logical tautology
end

for i in 1:10
  rlattice = RoleLattice(ImpFrame(4; random=false))
end # no errors when processing larger ones


# Blog example
##############

"""
q = 'Zazzles the cat has four legs', 
r = 'Zazzles the cat lost a leg'
"""
C = ImpFrame([[]=>[:q], []=>[:q,:r], [:q,:r]=>[]], [:q,:r]; containment=true)

"""
x = 'It started in state 𝓈', 
y = 'It is presently in state 𝓈', 
z = 'There has been a net change in state'
"""
S = ImpFrame([[:x]=>[:y], [:x]=>[:y,:z], [:x,:y,:z]=>[]], [:x,:y,:z]; containment=true)
x,y,z = contents(S)
f_and = Interp([x ∧ y, x ∧ z])
sound_dom(f_and)
f_imp = Interp([x → y, x → z])
sound_dom(f_imp) # this is close to C except for q,r ⊬ 

# Empty role
rₑ = Role{hash(S)}(BitSet(1))
empt = Interp(fill(Content(rₑ, rₑ), 2))
@test length(getvalue(sound_dom(empt))) == 16 # 𝕀 = 𝒫(ℒ+ℒ)




# Sending q ↦ 𝐱 ∧ 𝐲 and r ↦ 𝐱 ∧ 𝐳
#--------------------------------
D = ImpFrame([[]=>[1], []=>[2], []=>[1,2], []=>[1,3],
              []=>[2,3],[]=>[1,2,3],[1,2,3]=>[]], 3; 
              containment=true, names=[:x,:y,:z])
𝐱, 𝐲, 𝐳 = contents(D) 
∅ = typeof(𝐱)[]
@test ∅ ⊩ [𝐱 ∧ 𝐲]
@test !(∅ ⊩ [𝐱 ∧ 𝐳])
@test !(∅ ⊩ [𝐱 ∧ 𝐲 ∧ 𝐳])

@test sound_dom(Interp([𝐱 ∧ 𝐲, 𝐱 ∧ 𝐳])) == C


# Sending q ↦ 𝐱 → 𝐲 and r ↦ 𝐱 → 𝐳
#--------------------------------
D = ImpFrame([[]=>[1], [1]=>[2], [1]=>[2,3], [2]=>[1],
              [3]=>[1],[2,3]=>[],[2,3]=>[1]], 3; 
              containment=true, names=[:x,:y,:z])
𝐱, 𝐲, 𝐳 = contents(D) 
∅ = typeof(𝐱)[]
@test !(∅ ⊩ [𝐱 ∧ 𝐲])
@test ∅ ⊩ [𝐱 → 𝐲]
@test !(∅ ⊩ [𝐱 → 𝐳])

@test sound_dom(Interp([𝐱 → 𝐲, 𝐱 → 𝐳])) == C


end # module

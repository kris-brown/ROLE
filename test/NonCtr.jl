module TestNCImpFrames
using ROLE, Test, Revise
using Combinatorics: powerset

b1 = BearerMultiset([0,1])
@test string(b1) == "b"
b2 = BearerMultiset([2,2])
@test string(b2) == "a,a,b,b"

i1 = NCImpl(b1,b2)
@test string(i1) == "b ⊢ a,a,b,b"
i2 = NCImpl([0,1],[2,2])
@test string(i2) == "b ⊢ a,a,b,b"

i3 = i1 ∪ i2
@test string(i3) == "b,b ⊢ a,a,a,a,b,b,b,b"


end # module
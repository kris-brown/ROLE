module TestRMaps
using ROLE, Test
using GATlab

using .ThCategory

X = ImpFrame([[]=>[1], [1,2]=>[], [1]=>[2]], 2, [:a,:b]);
Y = ImpFrame([[]=>[1], [1]=>[1],[2]=>[2], [1,2]=>[1], [1,2]=>[2]], 2, [:a,:b]);
Z = ImpFrame([[]=>[1], [1]=>[2]], 2, [:a,:b]);

f = FMap([1,2])

@test length(naturality_failures(ContC, f, X, Y))==4

@test is_natural(ContC, f, X, Z)

idz, = homomorphisms(ContC, Z, Z)

compose[ContC](f, idz)

@test terminal(ContC) == ImpFrame(Pair[], 1)

@test length(terminal(OpenC)) == 4

coproduct(OpenC, X,Y)

coproduct(ContC, X,Y)

@test coproduct(ContC) == initial(ContC)




end # module

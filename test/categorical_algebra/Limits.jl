module TestLimits 

using Test, ROLE, GATlab
using .ThCategory

# Test initial/terminal objects
expected = Colimit(Diagram(FinC()), Multicospan(FinSet(0), FinFunction[]))
@test expected == initial(FinC())
@test apex(initial(FinC())) == FinSet()

@test create(FinSet(4), FinC()) == FinFunction(Int[], FinSet(4))

expected = Limit(Diagram(FinC()), Multispan(FinSet(1), FinFunction[]))
@test expected == terminal(FinC())
@test apex(terminal(FinC())) == FinSet(1)

@test delete(FinSet(2), FinC()) == FinFunction([1,1], 1)


# Test product
#-------------

xdiag = DiscreteDiagram{FinSet,FinFunction}(FinSet.([2,2]))
expected = Limit(Diagram(xdiag, FinC()), Multispan(FinSet(4), 
                 [FinFunction(v, 2) for v in [[1,2,1,2],[1,1,2,2]]]))
@test expected == product(FinSet.([2,2]), FinC())

sp = Span(FinFunction.([[1,2,2],[1,2,1]], 2)...)
@test universal(expected, sp).impl.val == [1,4,2]

# Test coproduct
#---------------
expected = Colimit(Diagram(xdiag, FinC()), Multicospan(FinSet(4), 
                 [FinFunction(v, 4) for v in [[1,2],[3,4]]]))
@test expected == coproduct(FinSet.([2,2]), FinC())

sp = Cospan(FinFunction.([[2,3],[1,4]], 4)...)
@test universal(expected, sp).impl.val == [2,3,1,4]


# Equalizers 
############

f, g = FinFunction([1,2,4,3], 4), FinFunction([3,2,4,1], 4)
eq = equalizer([f,g], FinC())
@test incl(eq) == FinFunction([2,3], 4)
@test factorize(eq, FinFunction([2,3,2], 3)) == FinFunction([1,2,1], 2)

# Equalizer of identical functions.
f = FinFunction([4,2,3,1], 5)
eq = equalizer([f,f], FinC())
@test incl(eq) == force(id[FinC()](FinSet(4)))
@test factorize(eq, FinFunction([2,1,3,3], 3)) == FinFunction([2,1,3,3], 4)

# Equalizer matching nothing.
f, g = id[FinC()](FinSet(5)), FinFunction([2,3,4,5,1], 5)
eq = equalizer([f,g],FinC())
@test incl(eq) == FinFunction(Int[], 5)
@test factorize(eq, FinFunction(Int[], 0)) == FinFunction(Int[], 0)


# Coequalizers
#-------------

f, g = FinFunction([1], 3), FinFunction([3], 3)
coeq = coequalizer([f,g], FinC())
@test proj(coeq) == FinFunction([1,2,1], 2)
@test factorize(coeq, FinFunction([4,1,4], 4)) == FinFunction([4,1], 4)
@test_throws ErrorException factorize(coeq, FinFunction([3,1,4], 4))

# Coequalizer in case of identical functions.
f = FinFunction([4,2,3,1], 5)
coeq = coequalizer([f,f], FinC())
@test proj(coeq) == force(id[FinC()](FinSet(5)))
@test factorize(coeq, FinFunction([2,1,3,3,4],4)) == FinFunction([2,1,3,3,4],4)

# Coequalizer identifying everything.
f, g = id[FinC()](FinSet(5)), FinFunction([2,3,4,5,1], 5)
coeq = coequalizer([f,g], FinC())
@test proj(coeq) == FinFunction(fill(1,5), 1)
@test factorize(coeq, FinFunction(fill(3,5), 5)) == FinFunction([3], 5)

end # module

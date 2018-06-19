from pysmt.shortcuts import Symbol, And, Or, BOOL, Solver, BVType, EqualsOrIff, TRUE, simplify


a = Symbol("a", BOOL)
b = Symbol("b", BOOL)
c = Symbol("c", BOOL)

bv1 = Symbol("bv1", BVType(4))
bv2 = Symbol("bv2", BVType(4))


f = EqualsOrIff(Or(And(a,b), TRUE()), EqualsOrIff(bv1, bv2))

print("f=", f, "f'=", simplify(f))

solver = Solver(name="msat")
solver.add_assertion(f)
print(solver.solve(), solver.get_model())
print([(v, v.symbol_type())for v in f.get_free_variables()])


print(f.args(), f.is_and())

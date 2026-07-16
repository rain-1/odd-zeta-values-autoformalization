from ore_algebra import OreAlgebra
import ore_algebra
# search for a creative telescoping / summation entry point
print("module funcs:", [x for x in dir(ore_algebra) if not x.startswith('_')])
# Try the DifferentialOperators / guess-based. Also check ideal / MonomialIdeal CT.
# Known: ore_algebra.ideal has creative_telescoping? 
try:
    from ore_algebra.ideal import OreIdeal
    print("OreIdeal methods:", [x for x in dir(OreIdeal) if 'tele' in x.lower() or x=='ct'])
except Exception as e: print("no OreIdeal:",str(e)[:60])
# try multivariate over fraction field to dodge Singular
for maker in [lambda: OreAlgebra(PolynomialRing(QQ,'n,k'),'Sn','Sk'),
              lambda: OreAlgebra(FractionField(PolynomialRing(ZZ,'n,k')),'Sn','Sk')]:
    try:
        A=maker(); print("WORKS:",A); 
        Sn,Sk=A.gens(); n,k=A.base_ring().gens() if hasattr(A.base_ring(),'gens') else (None,None)
        print("  op has .ct:", hasattr(Sn,'ct'), " .creative_telescoping:", hasattr(Sn,'creative_telescoping'))
        break
    except Exception as e: print("no:",str(e)[:70])

from ore_algebra import OreAlgebra, guess
import sys
# read q_n values from file (one per line)
vals=[Integer(l.split('=')[1].split('[')[0].strip()) if '=' in l else Integer(l.strip())
      for l in open(sys.argv[1]) if l.strip() and ('=' in l or l.strip().isdigit())]
print("num terms:",len(vals))
R.<n>=QQ['n']; A.<Sn>=OreAlgebra(R)
rec=None
for od in [2,3,4,5,6]:
    try:
        rec=guess(vals,A,order=od); print("FOUND order",rec.order(),"deg",rec.degree()); break
    except Exception as e: print("order",od,"->",str(e)[:40])
if rec is None:
    try: rec=guess(vals,A); print("FOUND (auto) order",rec.order(),"deg",rec.degree())
    except Exception as e: print("auto ->",str(e)[:60]); sys.exit()
print("RECURRENCE:"); print(rec)
# verify it annihilates the sequence
co=rec.coefficients(sparse=False); r=rec.order()
def check(seq):
    ok=True
    for m in range(len(seq)-r):
        s=sum(co[k].subs(n=m)*seq[m+k] for k in range(r+1))
        if s!=0: ok=False; break
    return ok
print("annihilates q_n:",check(vals))
# characteristic polynomial (leading coefficients) -> asymptotic rates
lam=polygen(QQ,'lam')
lead=[c.leading_coefficient() for c in co]
charpoly=sum(lead[k]*lam^k for k in range(r+1))
print("char poly:",charpoly.factor() if charpoly!=0 else 0)
print("roots (asymptotic rate candidates):",[CC(z) for z in charpoly.roots(CC,multiplicities=False)])
# THE PRIZE TEST: does the SAME recurrence propagate P_n from P_0,P_1,P_2 ?
# P_n known: P_0=0, P_1=220, P_2=6021219/32 ; if recurrence order r lets us get P_3
Pknown={0:QQ(0),1:QQ(220),2:QQ(6021219)/32}
# trailing coeff co[0]; if co[0].subs(n=m0)!=0 we solve for P_{m0+r} etc.
# Try to propagate: need r consecutive known values. We have P_0,P_1,P_2 (3).
print("--- P_n propagation test (order",r,") ---")
if r<=2:
    print("order<=2: 3 values suffice to propagate P_3+.")
elif r==3:
    # recurrence at n=0: co[3](0)P_3 + co[2](0)P_2+co[1](0)P_1+co[0](0)P_0 = 0
    a3=co[3].subs(n=0);
    if a3!=0:
        P3=-(co[2].subs(n=0)*Pknown[2]+co[1].subs(n=0)*Pknown[1]+co[0].subs(n=0)*Pknown[0])/a3
        print("order-3 => P_3 =",P3, " den factored:",factor(P3.denominator()))
    else: print("leading coeff vanishes at n=0; shift needed")
elif r==4:
    # need P_{-1}. If co[0](n)=0 at n=... the recurrence at n=-1 relates P_3..P_{-1}.
    # Common Apery structure: trailing poly vanishes so P_{-1} decouples. Test at n such that co[0] vanishes.
    # recurrence at n=m uses P_{m},...,P_{m+4}. To get P_3 from P_0,P_1,P_2 we need m=-1: P_{-1..3}, with co[0](-1) P_{-1} term.
    m=-1
    if co[0].subs(n=m)==0:
        # then P_3 determined by P_0,P_1,P_2 (P_{-1} coeff vanishes)
        a4=co[4].subs(n=m)
        P3=-(co[3].subs(n=m)*Pknown[2]+co[2].subs(n=m)*Pknown[1]+co[1].subs(n=m)*Pknown[0])/a4
        print("order-4, trailing vanishes at n=-1 => P_3 =",P3," den:",factor(P3.denominator()))
    else:
        print("order-4, trailing co[0](-1)=",co[0].subs(n=m),"!=0 : P_3 needs P_{-1} (blocked unless known)")
else:
    print("order",r,": need",r,"consecutive P values; have 3. Report q_3+char poly only.")

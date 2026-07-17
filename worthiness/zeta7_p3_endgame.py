#!/usr/bin/env python3
# ZETA7 endgame: from the certified q_n recurrence -> char poly/roots (asymptotic rates)
# and the P3/s3/Phat3 determination via the trailing-coefficient (n<0) propagation trick,
# self-checked against the KNOWN q_3 = 94357501.
import json, os
from fractions import Fraction as Fr
from math import gcd

HERE=os.path.dirname(os.path.abspath(__file__))
R=json.load(open(os.path.join(HERE,'recurrence.json')))
order=R['order']; deg=R['deg']; Cpoly=R['Cpoly']  # Cpoly[k] = [a0..a_deg], c_k(n)=sum a_j n^j
print(f"recurrence: order {order}, degree {deg}, certified={R['certified']} on {R['ntested']} terms")

def cval(k, n):  # exact c_k(n) as Fraction
    s=Fr(0); nn=Fr(1)
    for j in range(len(Cpoly[k])):
        s+=Cpoly[k][j]*nn; nn*=n
    return s

# ---- characteristic polynomial + roots ----
lead=R['char_lead']
import numpy as np
roots=sorted(np.roots(lead[::-1]), key=lambda z:-abs(z))
print("char poly coeffs (lambda^0..order):", lead)
print("char roots (|.| desc):")
for z in roots:
    print(f"   {z.real:+.6e} {z.imag:+.3e}i   |.|={abs(z):.6e}  log|.|={np.log(abs(z)):.4f}")
lam_max=abs(roots[0]); lam_small=abs(roots[-1])
print(f"lambda_max={lam_max:.6e} (log {np.log(lam_max):.4f}); lambda_small={lam_small:.6e}")

# ---- known ladder values ----
q={0:Fr(1),1:Fr(61),2:Fr(52921)}
s={0:Fr(0),1:Fr(300),2:Fr(261153)}
P={0:Fr(0),1:Fr(220),2:Fr(6021219,32)}
Ph={0:Fr(0),1:Fr(152),2:Fr(535857,4)}
Q3_KNOWN=Fr(94357501)

# ---- trailing-coefficient propagation: recurrence at n=m=3-order isolates X_3 from X_0,X_1,X_2
m=3-order
print(f"\n--- propagation shift n=m={m} (isolates index 3) ---")
# indices used: m..m+order = m..3. Negative indices: m..-1 -> need their coeffs to vanish.
neg_ks=[k for k in range(order+1) if m+k<0]
print("negative-index terms k with c_k(m):", [(k, m+k, str(cval(k,m))) for k in neg_ks])
vanish=all(cval(k,m)==0 for k in neg_ks)
print("all negative-index coefficients vanish:", vanish)

def propagate3(X):
    # solve c_order(m) X_3 + sum_{k: 0<=m+k<=2} c_k(m) X_{m+k} = 0  (neg-index terms vanish)
    lead_c=cval(order,m)   # coeff of X_{m+order}=X_3
    rhs=Fr(0)
    for k in range(order+1):
        idx=m+k
        if idx==3: continue
        if idx<0: continue   # vanishes
        rhs+=cval(k,m)*X[idx]
    return -rhs/lead_c

if vanish and (3-order)>=-order:
    # SELF-CHECK on q_3
    q3p=propagate3(q)
    print(f"\nSELF-CHECK: propagated q_3 = {q3p}")
    print(f"            known    q_3 = {Q3_KNOWN}")
    ok = (q3p==Q3_KNOWN)
    print("            MATCH:", ok)
    if ok:
        s3=propagate3(s); P3=propagate3(P); Ph3=propagate3(Ph)
        print(f"\n=== PROPAGATED n=3 VALUES ===")
        print(f" s_3   = {s3}")
        print(f" P_3   = {P3}")
        print(f" Phat_3= {Ph3}")
        # denominators + per-prime ledger vs d_3^7 (d_3=lcm(1,2,3)=6)
        d3=6
        def ledger(name,val,power):
            den=val.denominator
            print(f"\n den({name}_3) = {den} = ", end="")
            f=den; fac={}
            d=2
            while d*d<=f:
                while f%d==0: fac[d]=fac.get(d,0)+1; f//=d
                d+=1
            if f>1: fac[f]=fac.get(f,0)+1
            print(" * ".join(f"{p}^{e}" for p,e in sorted(fac.items())) or "1")
            # excess over d_3^power = 6^power
            print(f"   vs d_3^{power} = 6^{power}: per-prime excess (v_p(den) - v_p(6^{power})):")
            for p in sorted(set(list(fac)+[2,3])):
                vden=fac.get(p,0)
                v6 = power*(1 if p in (2,3) else 0)
                print(f"     p={p}: v_p(den)={vden}, v_p(6^{power})={v6}, excess={vden-v6}")
        ledger("P",P3,7)
        ledger("Phat",Ph3,7)
        ledger("s",s3,5)
        # ---- forward-propagation validation: propagate P_n, s_n via L; check I'_n, I''_n decay ~ lambda_small^n
        print("\n--- forward-propagation validation (I'_n, I''_n should decay ~ lambda_small^n) ---")
        try:
            import mpmath as mp
            mp.mp.dps=80
            z3=mp.zeta(3); z5=mp.zeta(5); z7=mp.zeta(7)
            # exact q_n for as many n as available
            qex={}
            import re as _re
            for l in open(os.path.join(HERE,'..','zeta7_lc_terms.txt')):
                mm=_re.match(r'q_(\d+)\s*=\s*(\d+)',l.strip())
                if mm: qex[int(mm.group(1))]=int(mm.group(2))
            Nq=max(qex)
            def fwd(X):  # X dict with 0..order-1 (and order) known; propagate forward
                X=dict(X); X[3]=propagate3(X) if 3 not in X else X[3]
                for nn in range(0, Nq-order+1):
                    lead_c=cval(order,nn)
                    if lead_c==0:
                        X[nn+order]=None; continue
                    rhs=sum(cval(k,nn)*X[nn+k] for k in range(order))
                    X[nn+order]=-rhs/lead_c
                return X
            Pf=fwd(P); sf=fwd(s)
            bad=0
            for nn in [3,5,8,12,16,20,25,30]:
                if nn>Nq or Pf.get(nn) is None or sf.get(nn) is None: continue
                q_=qex[nn]
                Ip=mp.mpf(75)/4*q_*z7 - 3*mp.mpf(sf[nn].numerator)/sf[nn].denominator*z5 - mp.mpf(Pf[nn].numerator)/Pf[nn].denominator
                print(f"  n={nn}: I'_n = {mp.nstr(Ip,6)}   (lambda_small^n = {mp.nstr(mp.mpf(lam_small)**nn,3)})")
            # verify propagated P_n stays rational with den | d_n^7-ish (sanity)
        except Exception as e:
            print("forward validation skipped:", str(e)[:80])
        # numeric smallness check of I'_3, I''_3
        try:
            import mpmath as mp
            mp.mp.dps=60
            z3=mp.zeta(3); z5=mp.zeta(5); z7=mp.zeta(7)
            Ip3=mp.mpf(75)/4*int(Q3_KNOWN)*z7 - 3*mp.mpf(s3.numerator)/s3.denominator*z5 - mp.mpf(P3.numerator)/P3.denominator
            Ipp3=-9*int(Q3_KNOWN)*z5 + 2*mp.mpf(s3.numerator)/s3.denominator*z3 - mp.mpf(Ph3.numerator)/Ph3.denominator
            print(f"\n numeric smallness check (should be ~lambda_small^3 = {lam_small**3:.3e}):")
            print(f"   I'_3  = {mp.nstr(Ip3,8)}")
            print(f"   I''_3 = {mp.nstr(Ipp3,8)}")
        except Exception as e:
            print("mpmath smallness check skipped:", str(e)[:60])
    else:
        print("SELF-CHECK FAILED: the recurrence does not reproduce q_3 via the n<0 trick.")
        print(" => q_n and P_n/s_n do NOT share this propagation; use smallness route.")
else:
    print("\nTrailing coefficients do NOT vanish (or order<=3 path).")
    if order<=3:
        # order<=3: recurrence at n=0 gives X_3 from X_0,X_1,X_2 directly (needs c_0(0) etc.)
        m0=0
        def prop0(X):
            lead_c=cval(order,m0); rhs=Fr(0)
            for k in range(order):
                rhs+=cval(k,m0)*X[m0+k]
            return -rhs/lead_c
        q3p=prop0(q); print("SELF-CHECK q_3 (n=0 propagation):",q3p,"==",Q3_KNOWN,":",q3p==Q3_KNOWN)
        if q3p==Q3_KNOWN:
            print("P_3 =",prop0(P),"  s_3 =",prop0(s),"  Phat_3 =",prop0(Ph))
    else:
        print(" => order>=4 without trailing vanish: direct 3-value propagation blocked.")
        print("    Smallness route: I'_3 ~ I''_3 ~ lambda_small^3 =",lam_small**3)
        print("    Two equations (I'_3=eps1, I''_3=eps2 tiny) in (s_3,P_3,Phat_3), plus rationality/denominator bounds.")

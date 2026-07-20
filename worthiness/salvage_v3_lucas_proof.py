"""V3 proof reconstruction: the Lucas-Frobenius congruence Q_{ap+r} ≡ Q_a Q_r (mod p)
for the Brown-Zudilin double sum, as a VERIFIED certificate.

Q_N = Σ_{k,l=0}^N T(k,l;N),   T = C(N+k,N)C(N,k)² C(N+l,N)C(N,l)² C(N+k+l,N).

Split each index in base p: k=bp+s, l=cp+t (0≤s,t<p).  The proof has two claims,
both checked here exactly mod p over a wide (p,a,r) grid:

 (CARRY-KILL) T(k,l) ≡ 0 (mod p) unless ALL of:
      b≤a, c≤a, s≤r, t≤r, r+s<p, r+t<p, r+s+t<p
   (any base-p carry, in C(N,k), C(N,l), C(N+k,N), C(N+l,N) or C(N+k+l,N),
    forces a lower digit below the corresponding digit of N, killing a factor).

 (FACTOR) on the surviving box {0≤b,c≤a}×{0≤s,t≤r, r+s+t<p},
      T(bp+s, cp+t) ≡ T_hi(b,c;a) · T_lo(s,t;r)  (mod p),
   T_hi(b,c;a)=C(a+b,a)C(a,b)²C(a+c,a)C(a,c)²C(a+b+c,a) = (b,c)-summand of Q_a,
   T_lo(s,t;r)=C(r+s,r)C(r,s)²C(r+t,r)C(r,t)²C(r+s+t,r) = (s,t)-summand of Q_r.

Summation over the box then gives  Q_N ≡ (Σ_{b,c} T_hi)(Σ_{s,t} T_lo) = Q_a·Q_r,
because for a<p the surviving high box is exactly {0≤b,c≤a} with a+b,a+c,a+b+c<... .
The r+s+t<p constraint on the low box is automatically the full support of Q_r's
summand mod p (larger s,t give carries, killed).

Usage: python3 salvage_v3_lucas_proof.py
"""

from math import comb


def T_summand(N, k, l, p):
    return (comb(N + k, N) % p) * (comb(N, k) ** 2 % p) % p \
        * (comb(N + l, N) % p) % p * (comb(N, l) ** 2 % p) % p \
        * (comb(N + k + l, N) % p) % p


def T_hi(b, c, a):
    return comb(a + b, a) * comb(a, b) ** 2 * comb(a + c, a) * comb(a, c) ** 2 \
        * comb(a + b + c, a)


def T_lo(s, t, r):
    return comb(r + s, r) * comb(r, s) ** 2 * comb(r + t, r) * comb(r, t) ** 2 \
        * comb(r + s + t, r)


def survives(a, r, b, c, s, t, p):
    return (b <= a and c <= a and s <= r and t <= r
            and r + s < p and r + t < p and r + s + t < p)


def verify(primes=(5, 7, 11, 13, 17), amax=8):
    print("=== V3 Lucas proof: CARRY-KILL + FACTOR certificate (mod p) ===")
    ck_fail = fac_fail = box_fail = 0
    total_summ = 0
    congr_checks = congr_fail = 0
    for p in primes:
        for a in range(0, amax + 1):
            for r in range(0, p):
                N = a * p + r
                # (1) exact congruence Q_N ≡ Q_a Q_r  via direct mod-p sums
                QN = sum(T_summand(N, k, l, p) for k in range(N + 1)
                         for l in range(N + 1)) % p
                Qa = sum(T_hi(b, c, a) % p for b in range(a + 1)
                         for c in range(a + 1)) % p
                Qr = sum(T_lo(s, t, r) % p for s in range(r + 1)
                         for t in range(r + 1)) % p
                congr_checks += 1
                if QN != Qa * Qr % p:
                    congr_fail += 1
                # (2) per-summand carry-kill + factorization
                box_sum = 0
                for k in range(N + 1):
                    b, s = divmod(k, p)
                    for l in range(N + 1):
                        c, t = divmod(l, p)
                        T = T_summand(N, k, l, p)
                        total_summ += 1
                        surv = survives(a, r, b, c, s, t, p)
                        if not surv:
                            if T % p != 0:
                                ck_fail += 1          # a carry summand didn't die
                        else:
                            prod = (T_hi(b, c, a) % p) * (T_lo(s, t, r) % p) % p
                            if T % p != prod:
                                fac_fail += 1
                            box_sum = (box_sum + prod) % p
                if box_sum != Qa * Qr % p:
                    box_fail += 1
    print(f"  congruence Q_{{ap+r}} ≡ Q_a Q_r: {congr_checks} checks, "
          f"{congr_fail} fail")
    print(f"  CARRY-KILL (non-surviving summand ⇒ ≡0 mod p): {total_summ} summands, "
          f"{ck_fail} fail")
    print(f"  FACTOR (surviving summand = T_hi·T_lo mod p): {fac_fail} fail")
    print(f"  BOX (Σ over surviving box = Q_a Q_r mod p): {box_fail} fail")
    ok = (congr_fail == fac_fail == ck_fail == box_fail == 0)
    print(f"  -> certificate {'COMPLETE & VERIFIED' if ok else 'HAS GAPS'} "
          f"on grid p∈{primes}, a≤{amax}, all r<p")
    return ok


if __name__ == "__main__":
    verify((5, 7, 11, 13, 17), 8)

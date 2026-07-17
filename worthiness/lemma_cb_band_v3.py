"""V3 -- Identify the universal constants rho_p (ord -5) and sig_p (ord -3).

Extract the p-adically UNIVERSAL leading digits of rho_p, sig_p (the digits that
agree across all band n, from V2), then compare digit-by-digit against a menu of
standard p-adic constants:
  * Fermat quotients q_p(2)=(2^{p-1}-1)/p, q_p(3) mod p
  * Bernoulli B_{p-3}, B_{p-5} mod p  (the classic basis for such constants)
  * Wolstenholme quotients W_p^{(i)} := H_{p-1}^{(i)}/p^{e_i} mod p
       (e_1=2, e_2=1, e_3=2, e_4=1, e_5=2; standard leading orders)
  * small fixed rationals a/b mod p (factorial / zeta-value candidates:
       1/5!, 1/4!, 1/2, -1/3, 2/15, ... -- a p-adic zeta-value avatar would be a
       FIXED rational times such a block)

A match to >=2 digits across >=2 primes is a finding; near-misses reported too.
Universal digits are read as the base-p expansion of p^{|ord|}*const, mod p^D
where D = #agreeing digits measured in V2 (>=2 for clean primes).
"""
import sys
from fractions import Fraction
from itertools import combinations
sys.path.insert(0, '.')
from lemma_cb_explore import all_data, primes_in, ord_p_fraction

try:
    from sympy import bernoulli
    HAVE_SYMPY = True
except Exception:
    HAVE_SYMPY = False


def band_primes_for(p, nmax=45):
    lo = -(-3 * p // 2)
    hi = min(2 * p - 1, nmax)
    return list(range(lo, hi + 1))


def rho_sig(n):
    d = all_data(n)
    u, ut, w, wt, v, vt = d["u"], d["ut"], d["w"], d["wt"], d["v"], d["vt"]
    q = u * wt - ut * w
    p_n = wt * v - w * vt
    ptil = u * vt - ut * v
    return (p_n / q if q else None), (ptil / q if q else None)


def universal_digits(vals, p):
    """Given list of Fractions (same nominal ord), return (ord, D, residue mod p^D)
    where D = number of leading digits shared by ALL of them, residue is the shared
    p^{|ord|}*value mod p^D as an integer. 'disagree at digit D'."""
    ords = [ord_p_fraction(x, p) for x in vals]
    o = min(ords)
    scaled = [x * Fraction(p) ** (-o) for x in vals]  # now p-adic integers (units)
    # find max D such that all scaled agree mod p^D
    D = 0
    while D < 12:
        mods = set(int((s.numerator % p ** (D + 1)) * pow(s.denominator, -1, p ** (D + 1)) % p ** (D + 1))
                   for s in scaled)
        if len(mods) != 1:
            break
        D += 1
    if D == 0:
        return o, 0, None
    m = p ** D
    res = int((scaled[0].numerator % m) * pow(scaled[0].denominator, -1, m) % m)
    return o, D, res


def digits_of(res, p, D):
    ds = []
    x = res
    for _ in range(D):
        ds.append(x % p)
        x //= p
    return ds  # least-significant (leading p-adic) first


def candidates_modp(p):
    c = {}
    c["q_p(2)"] = ((pow(2, p - 1, p * p) - 1) // p) % p
    c["q_p(3)"] = ((pow(3, p - 1, p * p) - 1) // p) % p
    if HAVE_SYMPY:
        for k in (3, 5):
            if p - k >= 2:
                b = bernoulli(p - k)  # Fraction-like (sympy Rational)
                num, den = int(b.p), int(b.q)
                if den % p != 0:
                    c[f"B_{{p-{k}}}"] = (num % p) * pow(den % p, -1, p) % p
    # Wolstenholme block quotients
    def Hpow(i):
        return sum((Fraction(1, k ** i) for k in range(1, p)), Fraction(0))
    for i, e in [(1, 2), (2, 1), (3, 2), (4, 1), (5, 2)]:
        H = Hpow(i)
        val = H * Fraction(p) ** (-e)
        o = ord_p_fraction(val, p)
        if o is not None and o >= 0:
            c[f"H^{i}/p^{e}"] = int((val.numerator % p) * pow(val.denominator % p, -1, p) % p)
        else:
            c[f"H^{i}/p^{e}"] = f"ord={o}"
    return c


def frac_modp(fr, p):
    return (fr.numerator % p) * pow(fr.denominator % p, -1, p) % p


def run(nmax=45, primes=(11, 13, 17, 19, 23)):
    print("V3 -- identification of universal constants (leading digits)\n")
    small_rats = {"1/120": Fraction(1, 120), "1/24": Fraction(1, 24),
                  "1/12": Fraction(1, 12), "1/6": Fraction(1, 6),
                  "1/2": Fraction(1, 2), "-1/3": Fraction(-1, 3),
                  "2/15": Fraction(2, 15), "1/720": Fraction(1, 720),
                  "-1/30": Fraction(-1, 30)}
    lead = {"rho": {}, "sig": {}}
    for p in primes:
        ns = band_primes_for(p, nmax)
        rhos, sigs = [], []
        for n in ns:
            r, s = rho_sig(n)
            if r is not None:
                rhos.append(r)
                sigs.append(s)
        print(f"===== p={p} (band n={ns}) =====")
        for name, vals in [("rho", rhos), ("sig", sigs)]:
            o, D, res = universal_digits(vals, p)
            ds = digits_of(res, p, D) if D else []
            lead[name][p] = (o, D, ds[0] if ds else None)
            print(f"  {name}: ord={o}  #universal_digits={D}  "
                  f"digits(lead..)={ds}  (leading unit d0={ds[0] if ds else None})")
        cand = candidates_modp(p)
        print(f"  candidates mod {p}: " +
              ", ".join(f"{k}={v}" for k, v in cand.items()))
        print(f"  small rationals mod {p}: " +
              ", ".join(f"{k}={frac_modp(v, p)}" for k, v in small_rats.items()))
        # direct comparison of d0(rho) against each candidate
        d0 = lead["rho"][p][2]
        if d0 is not None:
            matches = [k for k, v in cand.items() if v == d0]
            rmatch = [k for k, v in small_rats.items() if frac_modp(v, p) == d0]
            matches += [f"±{k}" for k, v in cand.items() if isinstance(v, int) and (p - v) % p == d0]
            print(f"  >> rho leading digit d0={d0}: candidate matches = {matches or 'NONE'}; "
                  f"rational matches = {rmatch or 'NONE'}")
        print()
    # cross-prime: is d0(rho)/d0(sig) a fixed rational? is d0 a fixed value?
    print("Cross-prime leading digits:")
    for name in ("rho", "sig"):
        print(f"  {name}: " + ", ".join(f"p={p}:d0={lead[name][p][2]}" for p in primes))

    # PRIMARY identification: reconstruct p^{|ord|}*const mod p^2 as a global rational
    print("\nGlobal-rational identification (CRT of p^{|ord|}*const mod p^2, then"
          " rational reconstruction):")
    for name, ordv in (("rho", 5), ("sig", 3)):
        res, mods = [], []
        for p in primes:
            ns = band_primes_for(p, nmax)
            vals = []
            for n in ns:
                r, s = rho_sig(n)
                vals.append(r if name == "rho" else s)
            vals = [x for x in vals if x is not None]
            o, D, _ = universal_digits(vals, p)
            scaled = vals[0] * Fraction(p) ** ordv  # p-adic unit
            m = p ** 2
            res.append(int((scaled.numerator % m) * pow(scaled.denominator % m, -1, m) % m))
            mods.append(m)
        rr = _crt_ratrecon(res, mods)
        print(f"  {name}_p = ({rr}) * p^(-{ordv})  to 2 p-adic digits at all "
              f"primes {list(primes)}")


def _crt_ratrecon(res, mods):
    import math
    # CRT
    M = 1
    for m in mods:
        M *= m
    x = 0
    for r, m in zip(res, mods):
        Mi = M // m
        x = (x + r * Mi * pow(Mi, -1, m)) % M
    # Wang rational reconstruction
    if x == 0:
        return Fraction(0)
    r0, r1, s0, s1 = M, x, 0, 1
    bound = int(math.isqrt(M // 2))
    while r1 > bound:
        q = r0 // r1
        r0, r1 = r1, r0 - q * r1
        s0, s1 = s1, s0 - q * s1
    if s1 == 0 or abs(s1) > bound:
        return f"NO LOW-HEIGHT RATIONAL (x={x} mod {M})"
    return Fraction(r1, s1)


if __name__ == "__main__":
    nmax = int(sys.argv[1]) if len(sys.argv) > 1 else 45
    run(nmax=nmax)

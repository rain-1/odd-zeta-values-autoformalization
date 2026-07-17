"""V2 -- Solve the 2x2 system for the putative universal constants (rho_p, sigma_p).

Per band n solve, EXACTLY (Fraction), the system
    [ u_n  w_n ] [rho]   [ v_n ]
    [ ut_n wt_n] [sig] = [ vt_n ]
whose determinant is det = u_n wt_n - ut_n w_n = q_n, with ord_p(q_n) = kappa = 1
in the band (NEAR-SINGULAR). Cramer:
    rho_n = (v_n wt_n - w_n vt_n)/q_n = p_n/q_n
    sig_n = (u_n vt_n - ut_n v_n)/q_n = ptil_n/q_n   (third minor / q_n)
where ptil_n := u_n vt_n - ut_n v_n (the (u,v)-minor).

The 2x2 system determines rho_n, sig_n EXACTLY as rationals (no numerical loss --
we invert over Q). The blueprint's "precision loss" is the UNIVERSALITY question:
rho_p, sig_p are claimed n-INDEPENDENT, but each rho_n differs from the next.
We quantify, exactly:
  * ord_p(rho_n), ord_p(sig_n)              (depth of the constant)
  * v_p(rho_n - rho_m) for all band pairs   -> #agreeing p-adic digits
  * distinguish "disagrees at digit d" (genuine n-dependence, difference has ord d)
    from "not determined" (never applies here: exact inversion pins every digit).
Third-minor consistency: sig_n = ptil_n/q_n tests the (u,v)-minor with the same
q_n family (blueprint V2 last clause).

#universal digits of rho = v_p(rho_n - rho_m) - ord_p(rho_n).
Band needs theta=-1 i.e. >=1 digit (blueprint).
"""
import sys
from itertools import combinations
from fractions import Fraction
sys.path.insert(0, '.')
from lemma_cb_explore import all_data, primes_in, ord_p_fraction


def band_primes(n):
    return [p for p in primes_in(n // 2 + 1, (2 * n) // 3) if p >= 5]


def constants(n):
    d = all_data(n)
    u, ut, w, wt = d["u"], d["ut"], d["w"], d["wt"]
    v, vt = d["v"], d["vt"]
    q = u * wt - ut * w                 # = q_n
    p_n = wt * v - w * vt               # (w,v)-minor  = det[[v,w],[vt,wt]]
    ptil = u * vt - ut * v              # (u,v)-minor
    rho = p_n / q if q else None        # Cramer x1
    sig = ptil / q if q else None       # Cramer x2
    return dict(q=q, p_n=p_n, ptil=ptil, rho=rho, sig=sig,
                u=u, ut=ut, w=w, wt=wt, v=v, vt=vt)


def run(pmin=5, pmax=29, nmax=45):
    # group band pairs by prime
    byp = {}
    for n in range(4, nmax + 1):
        for p in band_primes(n):
            if p < pmin or p > pmax:
                continue
            byp.setdefault(p, []).append(n)
    for p in sorted(byp):
        ns = byp[p]
        print(f"\n===== p = {p}  (band n = {ns}) =====")
        data = {}
        for n in ns:
            c = constants(n)
            data[n] = c
            orho = ord_p_fraction(c["rho"], p) if c["rho"] else None
            osig = ord_p_fraction(c["sig"], p) if c["sig"] else None
            oq = ord_p_fraction(c["q"], p)
            opn = ord_p_fraction(c["p_n"], p)
            opt = ord_p_fraction(c["ptil"], p)
            print(f"  n={n:3d}: ord q={oq}  ord p_n={opn}  ord ptil={opt} | "
                  f"ord rho={orho}  ord sig={osig}")
        # cross-n universality of rho and sig
        for name in ("rho", "sig"):
            vals = {n: data[n][name] for n in ns if data[n][name] is not None}
            if len(vals) < 2:
                continue
            base_ord = min(ord_p_fraction(v, p) for v in vals.values())
            print(f"  -- universality of {name} (ord ~ {base_ord}): "
                  f"v_p(diff) and #agreeing digits = v_p(diff)-ord")
            worst = None
            for a, b in combinations(sorted(vals), 2):
                diff = vals[a] - vals[b]
                if diff == 0:
                    vp = 'inf'
                    dig = 'inf'
                else:
                    vp = ord_p_fraction(diff, p)
                    dig = vp - base_ord
                    worst = dig if worst is None else min(worst, dig)
                print(f"       v_p({name}_{a} - {name}_{b}) = {vp:>4}   "
                      f"#digits agree = {dig}")
            if worst is not None:
                print(f"     => MIN #agreeing digits across all pairs = {worst} "
                      f"(band needs >=1)")


if __name__ == "__main__":
    pmax = int(sys.argv[1]) if len(sys.argv) > 1 else 29
    nmax = int(sys.argv[2]) if len(sys.argv) > 2 else 45
    run(pmax=pmax, nmax=nmax)

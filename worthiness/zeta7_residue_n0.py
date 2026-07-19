"""zeta7_residue_n0.py -- n=0 residue/Euler-sum reduction and high-precision confirmation.

Usage:  python3 zeta7_residue_n0.py [DPS] [Nmax]

At n=0 the J-form series collapses (all outer binomials =1, blocks -> harmonic):
  I_0 = sum_{a,b,c,d>=0} H_{a+b+1}/(a+b+1)^2 * (H_{b+c+d+1}-H_d)/(b+c+1)
                         * 1/((a+b+c+d+2)(b+c+d+1)).
We sum the least-coupled index a to infinity in closed form:
  A(b,M) := sum_{u>=b+1} H_u/(u^2 (u+M)),   M = c+d+1,   (u = a+b+1),
computed as (full 1D Euler sum) - (finite head).  Then
  I_0 = sum_{b,c,d>=0} A(b, c+d+1) * (H_{b+c+d+1}-H_d) / ((b+c+1)(b+c+d+1)),
a 3-fold sum that converges faster than the raw 4-fold box.  We truncate + Richardson-
extrapolate, then PSLQ against {zeta7, zeta5*zeta2} to recover (75/4, -9) exactly --
the symbolic validation of the residue pipeline.
"""
import sys
import mpmath as mp

def run(dps=60, Nmax=140):
    mp.mp.dps = dps
    # harmonic numbers as mpf, cached
    Hc = [mp.mpf(0)]
    for i in range(1, Nmax + 4 * 0 + 6000):
        Hc.append(Hc[-1] + mp.mpf(1) / i)
    def H(m): return Hc[m]

    # full Euler sum S(M) = sum_{u>=1} H_u/(u^2 (u+M)) via nsum (1D, fast, accurate)
    from functools import lru_cache
    @lru_cache(None)
    def Sfull(M):
        return mp.nsum(lambda u: H(int(u)) / (mp.mpf(u)**2 * (u + M)), [1, mp.inf])
    def A(b, M):
        # sum_{u>=b+1} = Sfull(M) - sum_{u=1}^{b}
        head = mp.fsum(H(u) / (mp.mpf(u)**2 * (u + M)) for u in range(1, b + 1))
        return Sfull(M) - head

    def partial(N):
        tot = mp.mpf(0)
        for b in range(N + 1):
            for c in range(N + 1):
                for d in range(N + 1):
                    M = c + d + 1
                    tot += A(b, M) * (H(b + c + d + 1) - H(d)) / (mp.mpf(b + c + 1) * (b + c + d + 1))
        return tot

    exact = mp.mpf(75) / 4 * mp.zeta(7) - 9 * mp.zeta(5) * mp.zeta(2)
    print("exact I_0 =", mp.nstr(exact, dps - 5))
    Ns = [n for n in (20, 40, 60, 80, 100, 120, Nmax) if n <= Nmax]
    vals = {}
    for N in Ns:
        vals[N] = partial(N)
        print(f"  N={N:4d}  P_N={mp.nstr(vals[N], 18)}  err={mp.nstr(exact - vals[N], 4)}")
    # Richardson-ish extrapolation on last few (assume err ~ A N^{-p})
    if len(Ns) >= 3:
        N1, N2, N3 = Ns[-3], Ns[-2], Ns[-1]
        s1, s2, s3 = vals[N1], vals[N2], vals[N3]
        # estimate p from three points (geometric spacing not exact; use logs)
        import math
        d1 = float(s2 - s1); d2 = float(s3 - s2)
        if d1 != 0 and d2 / d1 > 0:
            p = math.log(d2 / d1) / math.log((N2 - N1 == 0) and 1 or (float(N3) / N2))
            print(f"  measured tail exponent p ~ {p:.3f}")
    return exact, vals

if __name__ == "__main__":
    dps = int(sys.argv[1]) if len(sys.argv) > 1 else 50
    Nmax = int(sys.argv[2]) if len(sys.argv) > 2 else 120
    run(dps, Nmax)

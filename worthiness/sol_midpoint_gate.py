"""Exact checker for Sol session 3: the a=1 midpoint gate only.

For a generic odd prime p put r=(p-5)//2 and N=p+r, so 2*N+5=3*p.
The target is the saturated witness

    Z_p = p**(-e-1) * (11907*P_N - 334374*P_{N+1} - 19292*P_{N+2}),
    e = min_s v_p(P_{N+s}).

Two modes are deliberately separated.

``cache`` loads the committed n<=360 recurrence ladder (it never regenerates
it) and checks the target at every generic midpoint available in that cache.

``assembly`` performs the slower exact Phi/Bell/partial-fraction check for a
short prime list.  At each of N,N+1,N+2 it keeps the untilded and tilded regular
residuals in the three j-chambers

    head=[0,r_s], middle=[r_s+1,p-1], tail=[p,p+r_s]

until forming wt*R-w*Rt.  It verifies, exactly,

    p^5*p_m-rho*q_m = wt*E-w*Et + p^5*(wt*R-w*Rt),

where E=p^5*Sing-rho*u-sigma*p^2*w and Et is its companion.

All reported grid results are finite exact evidence, never a proof.
"""

from fractions import Fraction
from math import comb
import argparse
import hashlib

import sympy as sp

from dwork_assembly import a_layers_from_bell
from falsify_data import get_ladders
from lemma_cb_explore import (
    all_data,
    base_coefficients,
    companion_coefficients,
    harmonic,
    ord_p_fraction as vp,
)
from sol_hw_allr import error as scalar_head_error
from sol_local_regular import MID_ROW


RHO = Fraction(29, 28)
SIG = Fraction(101, 84)
EXCEPTIONAL = {7, 29, 43, 107, 557, 673, 701}


def midpoint_level(p):
    assert p % 2 == 1
    r = (p - 5) // 2
    N = p + r
    assert 2 * N + 5 == 3 * p
    return r, N


def valuation(x, p):
    return 10**9 if x == 0 else vp(x, p)


def fraction_fingerprint(x):
    raw = f"{x.numerator}/{x.denominator}".encode()
    return hashlib.sha256(raw).hexdigest()[:16]


def mod_p_integral(x, p):
    assert x.denominator % p != 0
    return (x.numerator % p) * pow(x.denominator % p, -1, p) % p


def assembled_base(n):
    """All a[i,j], using Bell away from the central-zero branch.

    At n even, j=n/2 makes the displayed logarithmic D_t singular although
    B_j(y) itself is regular.  We use the direct Taylor coefficient at that
    single point and check every other entry against the direct oracle.
    """
    direct = base_coefficients(n)
    out = {}
    central = Fraction(n, 2)
    for j in range(n + 1):
        if Fraction(j) == central:
            for i in range(1, 7):
                out[i, j] = direct[i, j]
            continue
        row = a_layers_from_bell(n, j)
        for i in range(1, 7):
            out[i, j] = row[i]
            assert row[i] == direct[i, j], (n, j, i)
    return out, direct


def chamber_ranges(p, rs):
    assert 0 <= rs < p
    return {
        "head": range(0, rs + 1),
        "middle": range(rs + 1, p),
        "tail": range(p, p + rs + 1),
    }


def level_assembly(p, m):
    rs = m - p
    assert 0 <= rs < p
    a, direct = assembled_base(m)
    at = companion_coefficients(m, a)
    direct_at = companion_coefficients(m, direct)
    assert at == direct_at

    d = all_data(m)
    assert a == d["a"] and at == d["at"]
    for i in range(1, 7):
        for j in range(m + 1):
            sign_ref = (-1) ** (i + 1)
            assert a[i, m - j] == sign_ref * a[i, j]
            assert at[i, m - j] == sign_ref * at[i, j]
    u = sum((a[5, j] for j in range(m + 1)), Fraction(0))
    w = sum((a[3, j] for j in range(m + 1)), Fraction(0))
    ut = sum((at[5, j] for j in range(m + 1)), Fraction(0))
    wt = sum((at[3, j] for j in range(m + 1)), Fraction(0))
    assert (u, w, ut, wt) == (d["u"], d["w"], d["ut"], d["wt"])

    def head_sing(arr):
        return sum(
            (Fraction((-1) ** (i + 1), p**i)
             * sum((arr[i, j] for j in range(rs + 1)), Fraction(0))
             for i in range(1, 7)),
            Fraction(0),
        )

    sing, singt = head_sing(a), head_sing(at)

    def hhat(j, i):
        return harmonic(j, i) - (Fraction(1, p**i) if j >= p else 0)

    R = {}
    Rt = {}
    for name, js in chamber_ranges(p, rs).items():
        js = tuple(js)
        R[name] = sum(
            (a[i, j] * hhat(j, i) for i in range(1, 7) for j in js),
            Fraction(0),
        )
        Rt[name] = sum(
            (at[i, j] * hhat(j, i) for i in range(1, 7) for j in js),
            Fraction(0),
        )
    rsum = sum(R.values(), Fraction(0))
    rtsum = sum(Rt.values(), Fraction(0))
    # Explicit head<->tail chamber reduction, with b -> rs-b after reflection.
    pair_R = sum(
        (a[i, b] * (harmonic(b, i)
                    + Fraction((-1) ** (i + 1))
                    * (harmonic(m - b, i) - Fraction(1, p**i)))
         for i in range(1, 7) for b in range(rs + 1)),
        Fraction(0),
    )
    pair_Rt = sum(
        (at[i, b] * (harmonic(b, i)
                     + Fraction((-1) ** (i + 1))
                     * (harmonic(m - b, i) - Fraction(1, p**i)))
         for i in range(1, 7) for b in range(rs + 1)),
        Fraction(0),
    )
    assert pair_R == R["head"] + R["tail"]
    assert pair_Rt == Rt["head"] + Rt["tail"]
    assert d["v"] == sing + rsum
    assert d["vt"] == singt + rtsum

    E = Fraction(p**5) * sing - RHO * u - SIG * Fraction(p**2) * w
    Et = Fraction(p**5) * singt - RHO * ut - SIG * Fraction(p**2) * wt
    assert E == scalar_head_error(p, rs, False)
    assert Et == scalar_head_error(p, rs, True)

    q = u * wt - ut * w
    praw = wt * d["v"] - w * d["vt"]
    head_det = wt * E - w * Et
    regular = {name: Fraction(p**5) * (wt * R[name] - w * Rt[name])
               for name in R}
    rhs = RHO * q + head_det + sum(regular.values(), Fraction(0))
    assert Fraction(p**5) * praw == rhs
    assert praw == d["p_n"] and q == d["q_n"]

    C = comb(2 * m, m)
    sign = (-1) ** (m + 1)
    P = Fraction(sign) * praw / C
    Q = Fraction(sign) * q / C
    return {
        "P": P, "Q": Q, "q": q, "praw": praw, "alpha_unit": Fraction(sign, C),
        "E": E, "Et": Et, "head_det": head_det, "regular": regular,
        "R": R, "Rt": Rt,
        "pair_R": pair_R, "pair_Rt": pair_Rt,
    }


def cache_check():
    ladders = get_ladders()  # committed cache only: never call build/extend
    P = ladders["P"]
    hi = max(P)
    rows = []
    for p in list(sp.primerange(11, 2 * hi + 1)):
        if p in EXCEPTIONAL:
            continue
        _, N = midpoint_level(p)
        if N + 2 > hi:
            continue
        ys = [P[N + s] for s in range(3)]
        e = min(vp(y, p) for y in ys)
        M = sum((Fraction(MID_ROW[s]) * ys[s] for s in range(3)), Fraction(0))
        z = M / Fraction(p ** (e + 1)) if e + 1 >= 0 else M * p ** (-e - 1)
        integral = z.denominator % p != 0
        rows.append((p, N, e, valuation(M, p), integral,
                     mod_p_integral(z, p) if integral else None,
                     fraction_fingerprint(z)))
    bad = [row for row in rows if not row[4]]
    tight = sum(row[3] == row[2] + 1 for row in rows)
    print("CACHE midpoint witnesses [FINITE EXACT EVIDENCE]")
    print(f"  loaded ladder n=0..{hi}; generic rows={len(rows)}; violations={len(bad)}; tight={tight}")
    for row in rows:
        p, N, e, got, integral, z0, fp = row
        print(f"  p={p:3d} N={N:3d} e={e:3d} v(M)={got:3d} "
              f"Z_p integral={integral} Z_p(mod p)={z0} sha256[:16]={fp}")
    assert not bad
    return rows


def assembly_check(primes):
    ladders = get_ladders()
    print("ASSEMBLY midpoint witnesses [FINITE EXACT EVIDENCE]")
    for p in primes:
        assert sp.isprime(p) and p >= 11 and p not in EXCEPTIONAL
        _, N = midpoint_level(p)
        assert N + 2 <= max(ladders["P"])
        lev = [level_assembly(p, N + s) for s in range(3)]
        coeff = [Fraction(x) for x in MID_ROW]
        alpha = [coeff[s] * lev[s]["alpha_unit"] for s in range(3)]

        M_direct = sum((coeff[s] * lev[s]["P"] for s in range(3)), Fraction(0))
        M_cache = sum((coeff[s] * ladders["P"][N + s] for s in range(3)), Fraction(0))
        assert M_direct == M_cache

        pieces = {
            "q": sum((alpha[s] * RHO * lev[s]["q"] for s in range(3)), Fraction(0)),
            "head_det": sum((alpha[s] * lev[s]["head_det"] for s in range(3)), Fraction(0)),
        }
        for chamber in ("head", "middle", "tail"):
            pieces[f"regular_{chamber}"] = sum(
                (alpha[s] * lev[s]["regular"][chamber] for s in range(3)),
                Fraction(0),
            )
        assembled = sum(pieces.values(), Fraction(0))
        assert assembled == Fraction(p**5) * M_direct

        e = min(vp(lev[s]["P"], p) for s in range(3))
        z = M_direct / Fraction(p ** (e + 1)) if e + 1 >= 0 else M_direct * p ** (-e - 1)
        assert z.denominator % p != 0
        offsets = {name: valuation(value, p) - (e + 6) for name, value in pieces.items()}
        grouped = {
            "regular_head+tail": pieces["regular_head"] + pieces["regular_tail"],
            "regular_all": (pieces["regular_head"] + pieces["regular_middle"]
                            + pieces["regular_tail"]),
            "q+head_det": pieces["q"] + pieces["head_det"],
        }
        group_offsets = {name: valuation(value, p) - (e + 6)
                         for name, value in grouped.items()}
        print(f"  p={p:3d} N={N:3d}: e={e}, v(M)={valuation(M_direct,p)}, "
              f"v(Z_p)={valuation(z,p)}, Z_p(mod p)={mod_p_integral(z,p)}, "
              f"sha256[:16]={fraction_fingerprint(z)}")
        print("    v(piece)-[e+6] in p^5*M: "
              + ", ".join(f"{name}={offsets[name]}" for name in pieces))
        print("    after chamber/determinant pairing: "
              + ", ".join(f"{name}={group_offsets[name]}" for name in grouped))
        print("    exact gates: Bell=direct; residual chambers sum; E/E~=sol_hw_allr; "
              "determinant; normalized P=cache: PASS")


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("mode", choices=("cache", "assembly", "all"), nargs="?", default="all")
    parser.add_argument("--primes", default="11,13,17,19,23")
    args = parser.parse_args()
    if args.mode in ("cache", "all"):
        cache_check()
    if args.mode in ("assembly", "all"):
        assembly_check([int(x) for x in args.primes.split(",") if x])


if __name__ == "__main__":
    main()

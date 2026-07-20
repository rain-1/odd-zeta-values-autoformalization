"""T1 (PHASE2_FALSIFY): EXTEND the exact (Q_n, P_n, P̂_n) ladders far beyond the
direct all_data range, by forward-recursing the exact normalized order-3
recurrence (V6b, cross-checked vs Zudilin math/0206178) in Q with Fraction
arithmetic, and CROSS-CHECK the propagation against direct salvage_data.triple.

Recurrence (relating Y_n, Y_{n+1}, Y_{n+2}, Y_{n+3} for every Y in {Q,P,P̂}):

  c0(n) Y_n + c1(n) Y_{n+1} + c2(n) Y_{n+2} + c3(n) Y_{n+3} = 0,

  c0(n) = (n+1)^5 (n+2) a0(n+1)
  c1(n) = -2 (n+2) B8(n)          B8 = deg-8 poly below
  c2(n) = -2 B9(n)                B9 = deg-9 poly below
  c3(n) = 2 (n+3)^5 (2n+5) a0(n)        <- LEADING coefficient
  a0(n) = 41218 n^3 + 198849 n^2 + 320790 n + 173057   (irreducible cubic)

Forward step:  Y_{n+3} = -(c0 Y_n + c1 Y_{n+1} + c2 Y_{n+2}) / c3(n).
c3(n) = 2 (n+3)^5 (2n+5) a0(n) > 0 for all n>=0 (a0 has irrational roots, all
positive-n values > 0), so NO division-by-zero ever occurs.

Usage:
  python3 falsify_data.py build 150     # extend + validate, write falsify_data/
  from falsify_data import get_ladders   # -> dict key-> {n: Fraction}
"""

from fractions import Fraction
from math import comb
import json
import os
import sys

_DIR = os.path.join(os.path.dirname(os.path.abspath(__file__)), "falsify_data")
os.makedirs(_DIR, exist_ok=True)

# --- exact recurrence coefficients, evaluated as integers ---------------------

def a0(n):
    return 41218 * n**3 + 198849 * n**2 + 320790 * n + 173057

def B8(n):
    return (3874492 * n**8 + 59373972 * n**7 + 394148190 * n**6
            + 1481084196 * n**5 + 3447878810 * n**4 + 5095855458 * n**3
            + 4673546679 * n**2 + 2433871008 * n + 551502039)

def B9(n):
    return (48802112 * n**9 + 967468896 * n**8 + 8488000862 * n**7
            + 43246197636 * n**6 + 140983768422 * n**5 + 304912330849 * n**4
            + 437406946975 * n**3 + 401272692378 * n**2 + 213593890911 * n
            + 50257929339)

def c0(n):
    return (n + 1)**5 * (n + 2) * a0(n + 1)

def c1(n):
    return -2 * (n + 2) * B8(n)

def c2(n):
    return -2 * B9(n)

def c3(n):
    return 2 * (n + 3)**5 * (2 * n + 5) * a0(n)


def extend(init, hi):
    """init: {0:Y0, 1:Y1, 2:Y2} of Fractions. Return {n: Fraction} up to hi."""
    Y = {k: Fraction(v) for k, v in init.items()}
    for n in range(0, hi - 2):
        cc3 = c3(n)
        assert cc3 != 0, f"division by zero at n={n}"
        Y[n + 3] = -(c0(n) * Y[n] + c1(n) * Y[n + 1] + c2(n) * Y[n + 2]) / cc3
    return Y


# --- build + cross-validate ---------------------------------------------------

def build(hi=150, verbose=True):
    from salvage_data import triple
    inits = {
        "Q": {0: triple(0)["Q"], 1: triple(1)["Q"], 2: triple(2)["Q"]},
        "P": {0: triple(0)["P"], 1: triple(1)["P"], 2: triple(2)["P"]},
        "Ph": {0: triple(0)["Ph"], 1: triple(1)["Ph"], 2: triple(2)["Ph"]},
    }
    ladders = {k: extend(inits[k], hi) for k in inits}
    return ladders


def crossvalidate(ladders, check_ns, verbose=True):
    """Compare recurrence propagation vs DIRECT salvage_data.triple at check_ns."""
    from salvage_data import triple
    fails = []
    checked = []
    for n in check_ns:
        d = triple(n)
        for key in ("Q", "P", "Ph"):
            rec = ladders[key][n]
            dirv = Fraction(d[key])
            if rec != dirv:
                fails.append((n, key, rec, dirv))
        checked.append(n)
    if verbose:
        print(f"cross-validation (recurrence vs direct) at n={checked}: "
              f"{len(fails)} mismatches -> "
              f"{'ALL MATCH' if not fails else 'MISMATCH!'}")
        for f in fails:
            print("   MISMATCH", f)
    return not fails


def save(ladders, hi):
    """Write per-n JSON (num/den strings) + a manifest."""
    for key in ("Q", "P", "Ph"):
        obj = {str(n): [str(v.numerator), str(v.denominator)]
               for n, v in ladders[key].items()}
        with open(os.path.join(_DIR, f"ladder_{key}.json"), "w") as f:
            json.dump(obj, f)
    with open(os.path.join(_DIR, "manifest.json"), "w") as f:
        json.dump({"hi": hi, "keys": ["Q", "P", "Ph"],
                   "recurrence": "normalized order-3 (V6b)"}, f, indent=2)
    print(f"saved ladders Q,P,P̂ for n=0..{hi} to {_DIR}/")


_LOADED = None

def get_ladders():
    global _LOADED
    if _LOADED is None:
        _LOADED = {}
        for key in ("Q", "P", "Ph"):
            with open(os.path.join(_DIR, f"ladder_{key}.json")) as f:
                obj = json.load(f)
            _LOADED[key] = {int(n): Fraction(int(a), int(b))
                            for n, (a, b) in obj.items()}
    return _LOADED


if __name__ == "__main__":
    cmd = sys.argv[1] if len(sys.argv) > 1 else "build"
    hi = int(sys.argv[2]) if len(sys.argv) > 2 else 150
    if cmd == "build":
        print(f"extending ladders to n={hi} via exact recurrence ...")
        ladders = build(hi)
        # validate against ALL cached direct values we can afford
        from salvage_data import _load_disk
        disk = _load_disk()
        avail = sorted(k for k in disk if 3 <= k <= hi)
        # dense low + sparse high among available direct computations
        check = [n for n in avail if n <= 30] + [n for n in avail if n > 30]
        ok = crossvalidate(ladders, check)
        save(ladders, hi)
        print("VALIDATION:", "PASS" if ok else "FAIL")

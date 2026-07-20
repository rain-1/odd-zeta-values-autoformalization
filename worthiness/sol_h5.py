"""Five-digit head-window normal-form ledger for the midpoint levels.

The pairwise p^4 floor is a symbolic target; the final C4 sum printed here is
finite exact evidence until a prime-independent finite-field summation
certificate is supplied.
"""

from fractions import Fraction

from sol_midpoint_gate import (RHO, SIG, level_assembly, midpoint_level,
                               mod_p_integral, valuation)


def local_head_term(p, arr, b):
    return (sum((Fraction((-1)**(i+1))*Fraction(p)**(5-i)*arr[i, b]
                 for i in range(1, 7)), Fraction(0))
            - 2*RHO*arr[5, b] - 2*SIG*p**2*arr[3, b])


def ledger(primes=(11, 13, 17)):
    print("H five-digit reflected head-window normal form [EXACT LEDGER]")
    for p in primes:
        _, N = midpoint_level(p)
        for s in range(3):
            lev = level_assembly(p, N+s)
            r = lev["rs"]
            for label, arr, error in (
                ("base", lev["a"], lev["E"]),
                ("companion", lev["at"], lev["Et"]),
            ):
                pairs = []
                for b in range(r//2+1):
                    c = r-b
                    bs = (b,) if b == c else (b, c)
                    pairs.append(sum((local_head_term(p, arr, bb) for bb in bs), Fraction(0)))
                middle = (-RHO*sum((arr[5, j] for j in range(r+1, p)), Fraction(0))
                          -SIG*p**2*sum((arr[3, j] for j in range(r+1, p)), Fraction(0)))
                # Reflection of odd layers gives the factor 2 on the head;
                # the remaining full sums are precisely the middle correction.
                assert error == sum(pairs, Fraction(0))+middle
                assert valuation(middle, p) >= 5
                floor = min(valuation(x, p) for x in pairs)
                assert floor >= 4
                digits = [mod_p_integral(x/Fraction(p**4), p) for x in pairs]
                assert sum(digits) % p == 0
                assert valuation(error, p) >= 5
                print(f"  p={p} s={s} r={r} {label}: pair floor={floor}; "
                      f"C4={digits}; sum(C4)={sum(digits)%p}; "
                      f"middle v={valuation(middle,p)}; E v={valuation(error,p)}")


if __name__ == "__main__":
    ledger()

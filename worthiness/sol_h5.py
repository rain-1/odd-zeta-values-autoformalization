"""Five-digit head-window certificate ledger for the midpoint levels.

The uniform proof is recorded in PHASE2_H5_CERTIFICATE.md.  This checker is
its exact oracle/transcription gate at the required primes.
"""

from fractions import Fraction

from sol_midpoint_gate import (RHO, SIG, level_assembly, midpoint_level,
                               mod_p_integral, valuation)
from lemma_cb_explore import all_data
from sol_j12 import exact_arrays


# With A_i=p^(6-i)a_i, p*T is this fixed Bell functional.  Keeping the
# coefficients named here prevents the symbolic certificate and exact oracle
# from silently drifting apart.
H5_BELL_ROW = {
    1: Fraction(1),
    2: Fraction(-1),
    3: Fraction(1)-2*SIG,
    4: Fraction(-1),
    5: Fraction(1)-2*RHO,
    6: Fraction(-1),
}

# Surviving jet.  The prime-independent Phi/Bell collection identifies the
# fourth local digit with the simple-pole coefficient at the small index r.
H5_C4_FACTOR = Fraction(-1, 84)


def local_head_term(p, arr, b):
    direct = (sum((Fraction((-1)**(i+1))*Fraction(p)**(5-i)*arr[i, b]
                   for i in range(1, 7)), Fraction(0))
              - 2*RHO*arr[5, b] - 2*SIG*p**2*arr[3, b])
    normalized = sum(
        (H5_BELL_ROW[i]*Fraction(p)**(6-i)*arr[i, b]
         for i in range(1, 7)), Fraction(0)
    ) / p
    assert direct == normalized
    return direct


def ledger(primes=(11, 13, 17)):
    print("H five-digit reflected head-window normal form [EXACT LEDGER]")
    for p in primes:
        _, N = midpoint_level(p)
        for s in range(3):
            lev = level_assembly(p, N+s)
            r = lev["rs"]
            m_j12, a_j12, at_j12 = exact_arrays(p, s)
            assert m_j12 == N+s
            assert lev["a"] == a_j12 and lev["at"] == at_j12
            small = all_data(r)
            for label, arr, error in (
                ("base", lev["a"], lev["E"]),
                ("companion", lev["at"], lev["Et"]),
            ):
                small_arr = small["a" if label == "base" else "at"]
                pairs = []
                predicted = []
                for b in range(r//2+1):
                    c = r-b
                    bs = (b,) if b == c else (b, c)
                    pair = sum((local_head_term(p, arr, bb) for bb in bs), Fraction(0))
                    rhs = H5_C4_FACTOR*p**4*sum(
                        (small_arr[1, bb] for bb in bs), Fraction(0)
                    )
                    # This exact p-adic congruence simultaneously gates all
                    # five coefficients: four zeros and the claimed C4.
                    assert valuation(pair-rhs, p) >= 5
                    pairs.append(pair)
                    predicted.append(rhs)
                middle = (-RHO*sum((arr[5, j] for j in range(r+1, p)), Fraction(0))
                          -SIG*p**2*sum((arr[3, j] for j in range(r+1, p)), Fraction(0)))
                # Reflection of odd layers gives the factor 2 on the head;
                # the remaining full sums are precisely the middle correction.
                assert error == sum(pairs, Fraction(0))+middle
                assert valuation(middle, p) >= 5
                floor = min(valuation(x, p) for x in pairs)
                assert floor >= 4
                digits = [mod_p_integral(x/Fraction(p**4), p) for x in pairs]
                predicted_digits = [mod_p_integral(x/Fraction(p**4), p)
                                    for x in predicted]
                assert digits == predicted_digits
                assert sum(digits) % p == 0
                # E_1 at infinity, retained here as an exact-Q soundness gate.
                assert sum((small_arr[1, b] for b in range(r+1)), Fraction(0)) == 0
                assert valuation(error, p) >= 5
                endpoint = digits[0]
                centre = digits[-1] if r % 2 == 0 else None
                print(f"  p={p} s={s} r={r} {label}: pair floor={floor}; "
                      f"coefficients=(0,0,0,0,C4); C4={digits}; "
                      f"sum(C4)={sum(digits)%p}; endpoint={endpoint}; "
                      f"central={centre if centre is not None else 'n/a'}; "
                      f"middle v={valuation(middle,p)}; E v={valuation(error,p)}")


if __name__ == "__main__":
    ledger()

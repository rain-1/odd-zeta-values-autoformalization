"""Exact checker for Sol session 7: the primitive midpoint Q-triple.

This is a certificate checker, not the proof by itself.  It checks the fixed
integer algebra used by ``PHASE2_Q3_CERTIFICATE.md`` and evaluates the only two
exceptional primes from the manifest Brown--Zudilin double-binomial formula.

No floating point arithmetic and no cached ladder values are used.
"""

from fractions import Fraction
from math import comb


def a0(n):
    return 41218 * n**3 + 198849 * n**2 + 320790 * n + 173057


def closed_casoratian(n):
    return (Fraction((-1) ** (n - 1) * a0(n),
                     16 * (n + 1)**4 * (n + 2)**5
                     * (2*n + 1) * (2*n + 3) * comb(2*n, n)))


def c0(n):
    return (n + 1)**5 * (n + 2) * a0(n + 1)


def c3(n):
    return 2 * (n + 3)**5 * (2*n + 5) * a0(n)


def det3(matrix):
    a, b, c = matrix
    return (a[0] * (b[1]*c[2] - b[2]*c[1])
            - a[1] * (b[0]*c[2] - b[2]*c[0])
            + a[2] * (b[0]*c[1] - b[1]*c[0]))


def choose_mod_small(a, b, p, fac, ifac):
    """C(a,b) mod p for the certificate range 0 <= a < 2p, 0 <= b < p."""
    if b < 0 or b > a:
        return 0
    if a < p:
        return fac[a] * ifac[b] % p * ifac[a-b] % p
    # One-digit Lucas.  Since b < p, the high lower digit is zero.
    low = a - p
    return 0 if b > low else fac[low] * ifac[b] % p * ifac[low-b] % p


def q_double_mod(n, p):
    """The manifest double-binomial Q_n, reduced modulo p."""
    fac = [1] * p
    for j in range(1, p):
        fac[j] = fac[j-1] * j % p
    ifac = [1] * p
    ifac[p-1] = pow(fac[p-1], p-2, p)
    for j in range(p-1, 0, -1):
        ifac[j-1] = ifac[j] * j % p

    def C(a, b):
        return choose_mod_small(a, b, p, fac, ifac)

    atom = [C(n+k, n) * C(n, k)**2 % p for k in range(n+1)]
    return sum(atom[k] * atom[l] * C(n+k+l, n)
               for k in range(n+1) for l in range(n+1)) % p


def main():
    # Initial Casoratian, using the exact n=1,2,3 values of (Q,P,Phat).
    initial = [
        [Fraction(21), Fraction(87, 4), Fraction(101, 4)],
        [Fraction(2989), Fraction(1190161, 384), Fraction(344923, 96)],
        [Fraction(714549), Fraction(7682021239, 10368),
         Fraction(3710571371, 4320)],
    ]
    assert det3(initial) == Fraction(13591, 34560) == closed_casoratian(1)

    # Exact telescoping gate.  A generous range catches transcription errors;
    # the proof is the displayed rational cancellation in the certificate.
    for n in range(1, 1000):
        assert closed_casoratian(n+1) / closed_casoratian(n) == -Fraction(c0(n), c3(n))

    # 8*a0((p-5)/2) = p*(41218*p^2-220572*p+397530)-241144.
    # The only prime divisors >= 11 of 241144 are 43 and 701.
    assert 241144 == 8 * 43 * 701
    for p in (11, 13, 17, 19, 23, 43, 701):
        r = (p - 5) // 2
        assert 8*a0(r) == 41218*p**3 - 220572*p**2 + 397530*p - 241144

    expected = {
        11: [0, 5, 1],
        13: [8, 5, 11],
        17: [14, 10, 16],
        19: [15, 2, 0],
        23: [6, 22, 13],
        43: [33, 0, 26],
        701: [472, 350, 182],
    }
    for p, want in expected.items():
        r = (p - 5) // 2
        got = [q_double_mod(r+s, p) for s in range(3)]
        assert got == want
        assert any(got)
        print(f"p={p:>3}, r={r:>3}: Q triple = {got}  PASS")

    print("Casoratian base/telescope: PASS")
    print("midpoint cubic exceptional set {43,701}: PASS")
    print("(Q3): PASS for every prime p >= 11")


if __name__ == "__main__":
    main()

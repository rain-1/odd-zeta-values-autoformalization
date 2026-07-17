# Verify: phi = (k^p - k)^2 gives the certificate c_M = [k^{M-1}]phi, i.e.
# c_3=1, c_{p+2}=-2, c_{2p+1}=1, and F_i(j) = [i==3] mod p for all i=1..6, j=0..n,
# for every n and prime n<p<=2n (p>=5).  Also the wtilde version with h(k)=-k(k+n).
from sympy import primerange

def Cneg(i, r):  # C(-i, r), integer
    v = 1
    num = 1
    from math import comb
    return ((-1)**r) * comb(i + r - 1, r)

def F_i_via_phi_coeffs(i, j, cM, p):
    # F_i(j) = sum_M c_M * C(-i, M-i) * j^{M-i}, r=M-i>=0
    s = 0
    for M, c in cM.items():
        r = M - i
        if r < 0: continue
        s = (s + c * Cneg(i, r) * pow(j, r, p)) % p
    return s % p

def phi_coeffs_w(p):
    # (k^p - k)^2 = k^{2p} - 2 k^{p+1} + k^2 ; c_M = [k^{M-1}]phi
    return {3: 1, p+2: -2, 2*p+1: 1}

def phi_coeffs_wt(n, p):
    # psi = -k(k+n)(k^p-k)^2 = -(k^2+n k)(k^{2p}-2k^{p+1}+k^2)
    # = -(k^{2p+2} + n k^{2p+1} - 2 k^{p+3} - 2n k^{p+2} + k^4 + n k^3)
    # c_M = [k^{M-1}] psi
    from collections import defaultdict
    c = defaultdict(int)
    base = {2*p:1, p+1:-2, 2:1}  # (k^p-k)^2 coeffs by power of k
    for pw, co in base.items():
        c[(pw+2)+1] += -co        # * -k^2 -> power pw+2, then c_M index = power+1
        c[(pw+1)+1] += -n*co      # * -n k  -> power pw+1
    return dict(c)

def wt_target(i, j, n):
    # want F_i(j) = j(n-j)[i=3] + (2j-n)[i=4] + (-1)[i=5]
    if i==3: return (j*(n-j))
    if i==4: return (2*j-n)
    if i==5: return -1
    return 0

fail_w = fail_wt = 0; checked=0
for n in range(2, 61):
    for p in primerange(n+1, 2*n+1):   # n < p <= 2n
        if p < 5: continue
        checked += 1
        cM = phi_coeffs_w(p)
        for i in range(1,7):
            for j in range(0,n+1):
                got = F_i_via_phi_coeffs(i,j,cM,p)
                want = 1 % p if i==3 else 0
                if got != want:
                    fail_w += 1
        cMt = phi_coeffs_wt(n,p)
        for i in range(1,7):
            for j in range(0,n+1):
                got = F_i_via_phi_coeffs(i,j,cMt,p)
                want = wt_target(i,j,n) % p
                if got != want:
                    fail_wt += 1
print(f"checked {checked} pairs (n in [2,60], n<p<=2n, p>=5)")
print(f"  w  = sum a_3j : closed-form phi=(k^p-k)^2      -> {'ALL PASS' if fail_w==0 else str(fail_w)+' FAIL'}")
print(f"  wt (a~_3 fn)  : closed-form psi=-k(k+n)(k^p-k)^2 -> {'ALL PASS' if fail_wt==0 else str(fail_wt)+' FAIL'}")

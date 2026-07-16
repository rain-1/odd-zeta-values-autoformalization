from ore_algebra import OreAlgebra, guess
# Apery zeta(3) numbers a_n = sum_k C(n,k)^2 C(n+k,k)^2
def apery(n): return sum(binomial(n,k)^2*binomial(n+k,k)^2 for k in range(n+1))
data=[apery(n) for n in range(30)]
print("apery:",data[:6])
R.<n> = QQ['n']; A.<Sn> = OreAlgebra(R)
rec = guess(data, A)
print("guessed recurrence order",rec.order(),"deg",rec.degree())
print(rec)
# characteristic-ish: leading/trailing
print("OK guess works")

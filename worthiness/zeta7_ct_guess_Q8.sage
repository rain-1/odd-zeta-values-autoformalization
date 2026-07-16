from ore_algebra import OreAlgebra, guess
# BZ M_{0,8} leading coefficient Q_n (eq Q_n): computable double sum -> 1,21,2989,...
def Q8(n):
    return sum( binomial(n+k1,n)*binomial(n,k1)^2 *
               sum( binomial(n+k2,n)*binomial(n,k2)^2*binomial(n+k1+k2,n) for k2 in range(n+1))
               for k1 in range(n+1))
vals=[Q8(n) for n in range(70)]
print("Q8:",vals[:6])
R.<n> = QQ['n']; A.<Sn> = OreAlgebra(R)
rec=guess(vals,A)
print("Q8 recurrence order",rec.order(),"deg",rec.degree())
print(rec)
# characteristic polynomial (leading-coeff ratios at n->oo): use the recurrence's
# indicial/char poly = coefficients' leading terms
cs=rec.coefficients(); ld=[c.leading_coefficient() if c!=0 else 0 for c in rec.coefficients(sparse=False)]
lam=polygen(QQ,'lam')
charpoly=sum(ld[i]*lam^i for i in range(len(ld)))
print("char poly (leading):",charpoly)
print("roots:",charpoly.roots(CC,multiplicities=False))

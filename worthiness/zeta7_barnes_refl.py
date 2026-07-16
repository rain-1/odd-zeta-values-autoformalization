import sympy as sp
x=sp.symbols('x1:8',positive=True)
t=[sp.prod(x[j] for j in range(i,7)) for i in range(7)]  # t_i=prod_{j>=i}x_j
# reflected simplex coords s_i = 1 - t_{8-i}; original D in t, expressed then mapped.
# Directly: reflected integral has simplex denominator (in s) = same functional D
# but with t_k -> 1 - s_{8-k}. Equivalent to mapping cubical x to the *reflected*
# staircase. We recompute the 6 "1-product" denom factors for the reflected orientation.
s=[sp.symbols(f's{i}') for i in range(1,8)]
subs={s[i-1]:sp.prod(x[j] for j in range(i-1,7)) for i in range(1,8)}  # s_i=prod_{j>=i}x_j
Dfac=[s[6]-s[4],1-s[4],1-s[2],s[5]-s[2],s[5]-s[0],s[3]-s[0],s[3],s[1]]
for f in Dfac:
    ff=sp.factor(f.subs(subs))
    print(sp.simplify(ff))

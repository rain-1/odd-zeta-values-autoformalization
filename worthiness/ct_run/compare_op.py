#!/usr/bin/env python3
# Compare the Barnes period-level telescoper (from barnes_ct.log COEF lines)
# with the known q_n operator (zeta7_q_recurrence.json).
# Reports: order/degree; whether the two operators are equal (up to content),
# or whether the q_n operator RIGHT-DIVIDES the Barnes telescoper (left-multiple).
import re, os, json, sys
import sympy as sp
HERE=os.path.dirname(os.path.abspath(__file__))
n=sp.symbols('n'); Sn=sp.symbols('Sn')  # Sn = shift, noncommutative handled manually

def parse_log(path):
    coefs={}
    for line in open(path):
        m=re.match(r'COEF c_(\d+)\(n\) = (.+)', line.strip())
        if m:
            k=int(m.group(1)); e=m.group(2).replace('nn','n').replace('^','**')
            coefs[k]=sp.expand(sp.sympify(e))
    if not coefs: return None
    order=max(coefs)
    return [sp.Poly(coefs.get(k,sp.Integer(0)),n) for k in range(order+1)]

def load_json_op(path):
    d=json.load(open(path))
    ops=[]
    for cl in d['Cpoly']:
        ops.append(sp.Poly(sum(sp.Integer(cl[j])*n**j for j in range(len(cl))),n))
    return ops, d

def content_free(polys):
    # divide operator (list of Poly in n) by the gcd of all integer coeffs
    allc=[]
    for p in polys: allc+=[int(c) for c in p.all_coeffs()]
    g=0
    for c in allc: g=sp.gcd(g,c)
    g=int(g) if g else 1
    return [sp.Poly(p.as_expr()/g,n) for p in polys], g

barnes=parse_log(os.path.join(HERE,'barnes_ct.log'))
qops,qd=load_json_op(os.path.join(HERE,'..','zeta7_q_recurrence.json'))
print("q_n operator: order",len(qops)-1,"degree",max(p.degree() for p in qops))
if barnes is None:
    print("No COEF lines in barnes_ct.log yet."); sys.exit(0)
print("Barnes telescoper: order",len(barnes)-1,"degree",max(p.degree() for p in barnes))
bcf,bg=content_free(barnes); qcf,qg=content_free(qops)
if len(bcf)==len(qcf):
    same=all((bcf[i].as_expr()-qcf[i].as_expr()).equals(0) or
             (bcf[i].as_expr()+qcf[i].as_expr()).equals(0) for i in range(len(bcf)))
    # allow global sign
    diff=[sp.simplify(bcf[i].as_expr()-qcf[i].as_expr()) for i in range(len(bcf))]
    diffneg=[sp.simplify(bcf[i].as_expr()+qcf[i].as_expr()) for i in range(len(bcf))]
    if all(d==0 for d in diff) or all(d==0 for d in diffneg):
        print("RESULT: Barnes telescoper == q_n operator (equal up to content/sign). PROVEN.")
    else:
        print("Same order but coefficients differ (up to content). Checking proportionality by ratio...")
        ratios=[sp.simplify(bcf[i].as_expr()/qcf[i].as_expr()) for i in range(len(bcf)) if qcf[i].as_expr()!=0]
        print("  coefficient ratios:",ratios)
else:
    print("Different orders: Barnes order",len(bcf)-1,"vs q_n order",len(qcf)-1)
    print("  -> expect Barnes = A . (q_n operator); need Ore right-division to confirm (run in Mathematica).")
# print leading (characteristic) coeffs for eyeball
D=max(p.degree() for p in barnes)
print("Barnes char (leading deg",D,") coeffs:", [int(p.nth(D)) for p in barnes])
print("q_n char coeffs:", qd['char_lead'])

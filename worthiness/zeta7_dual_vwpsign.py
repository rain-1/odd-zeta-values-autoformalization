#!/usr/bin/env python3
"""Systematic confirmation: across genuinely-VWP single-sum spreads giving clean
{z5,z7} (even zetas killed), is r5=z5/z7 EVER negative? (BZ I'_n needs r5=-48/61<0.)
Symmetric pole windows (contiguous + gapped) about center c, mult m, C in {0,2},
symmetric numerator zero-pairs. Records: #VWP-clean configs, #with r5<0."""
from fractions import Fraction as F
import sys
sys.path.insert(0,'/home/ubuntu/fable-episode-2/zeta-math/worthiness')
from zn_check import linear_form_coeffs

def decomp(denbases, numbases, center, C):
    As,c=linear_form_coeffs(F(1), F(center,2), [F(b) for b in numbases], denbases, C)
    d={s:As.get(s,F(0)) for s in range(1,12)}
    return d,c

def mirror(x, c2):   # reflection about -c2/2 (center given as c2 = 2*center)
    return -c2 - x

vwp_clean=0; negative=0; examples_pos=[]; neg_examples=[]
# contiguous windows {0..-(W-1)} (center (W-1)/2), mult m; num: symmetric zero pairs
for W in range(2,7):
  c2=W-1                      # 2*center; center=(W-1)/2, half-shift (W-1)/2
  den_window=list(range(0,W))
  # candidate symmetric numerator zero-pairs {a, mirror(a)} for a outside window
  cand_a=[a for a in range(W, W+8)]
  for m in range(2,7):
    denbases=den_window*m
    # try numerators = union of t symmetric pairs, t=0..3
    import itertools
    for t in range(0,4):
      for combo in itertools.combinations(cand_a, t):
        numbases=[]
        for a in combo:
            numbases += [-a, -mirror(a,c2)]   # zeros at k=a and k=mirror(a); bases -a and -mirror
        # note: (k - a) has base -a ; (k - mirror) base -mirror
        for C in (0,2):
          try:
            d,c=decomp(denbases, numbases, c2, C)
          except Exception: continue
          if any(d.get(s,F(0))!=0 for s in (2,4,6,8,10)): continue   # must be VWP-clean
          z5,z7=d.get(5,F(0)),d.get(7,F(0))
          if z5==0 or z7==0: continue
          # ensure content is subset {3,5,7} with 5,7 present
          if any(d.get(s,F(0))!=0 for s in (9,11)): continue
          vwp_clean+=1
          r5=z5/z7
          if r5<0:
            negative+=1
            if len(neg_examples)<10: neg_examples.append((W,m,combo,C,r5))
          elif len(examples_pos)<5:
            examples_pos.append((W,m,combo,C,r5))

# gapped windows: {0..a-1} U {b..b+a-1}, symmetric about center
for a in range(1,4):
  for gap in range(1,4):
    left=list(range(0,a)); right=[a+gap+i for i in range(a)]
    window=left+right
    c2=max(window)          # symmetric about -(max)/2? check
    # center so that window symmetric: mirror of 0 is -max, in window? need max in window
    for m in range(3,7):
      denbases=window*m
      cand_a=[x for x in range(max(window)+1, max(window)+8)]
      import itertools
      for t in range(1,3):
        for combo in itertools.combinations(cand_a,t):
          numbases=[]
          for x in combo: numbases+=[-x,-mirror(x,c2)]
          for C in (2,):
            try: d,c=decomp(denbases,numbases,c2,C)
            except Exception: continue
            if any(d.get(s,F(0))!=0 for s in (2,4,6,8,10)): continue
            z5,z7=d.get(5,F(0)),d.get(7,F(0))
            if z5==0 or z7==0 or any(d.get(s,F(0))!=0 for s in (9,11)): continue
            vwp_clean+=1
            r5=z5/z7
            if r5<0:
                negative+=1
                if len(neg_examples)<10: neg_examples.append(('gap',a,gap,m,combo,r5))

print(f"VWP-clean single-sum configs giving {{z5,z7}} (subset {{3,5,7}}): {vwp_clean}")
print(f"  ...with r5=z5/z7 < 0 (the BZ sign): {negative}")
print(f"  sample POSITIVE r5: {[str(e[-1]) for e in examples_pos]}")
print(f"  NEGATIVE examples: {neg_examples}")
print(f"BZ requires r5 = -48/61 = {float(F(-48,61)):.4f} (NEGATIVE).")

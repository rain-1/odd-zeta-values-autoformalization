#!/usr/bin/env python3
"""Scan k=9 VWP tilde F_9 at n=1 for the symmetric c-pattern matching I'_1.
Filter: z3==0, r5=z5/z7==-48/61, rc=const/z7==-176/915."""
from fractions import Fraction as F
from itertools import combinations_with_replacement
import sys
sys.path.insert(0, '/home/ubuntu/fable-episode-2/zeta-math/worthiness')
from zeta7_dual_vwp import tildeF

TGT_R5 = F(-48, 61)
TGT_RC = F(-176, 915)

def eval_ratios(b0, bs):
    As, const = tildeF(b0, bs)
    z3 = As.get(3, F(0)); z5 = As.get(5, F(0)); z7 = As.get(7, F(0))
    z9 = As.get(9, F(0))
    return const, z3, z5, z7, z9

hits = []
CMAX = 5
for c0 in range(1, 13):
    for bs in combinations_with_replacement(range(0, c0//2 + 1), 9):
        if max(bs) == 0:
            continue
        if any(c > CMAX for c in bs):
            continue
        try:
            const, z3, z5, z7, z9 = eval_ratios(c0, list(bs))
        except Exception:
            continue
        if z7 == 0 or z3 != 0 or z9 != 0:
            continue
        r5 = z5 / z7
        rc = const / z7
        if r5 == TGT_R5 and rc == TGT_RC:
            hits.append((c0, bs, const, z3, z5, z7))
            print("MATCH n=1:", c0, bs, "const", const, "z5", z5, "z7", z7)

print(f"\ntotal n=1 hits: {len(hits)}")
# also record near-misses where only z3==0 and r5 matches (rc free)
if not hits:
    print("no exact hits; listing z3==0 & r5 matches:")
    for c0 in range(1, 13):
        for bs in combinations_with_replacement(range(0, c0//2 + 1), 9):
            if max(bs) == 0 or any(c > CMAX for c in bs):
                continue
            try:
                const, z3, z5, z7, z9 = eval_ratios(c0, list(bs))
            except Exception:
                continue
            if z7 == 0 or z3 != 0 or z9 != 0:
                continue
            if z5 / z7 == TGT_R5:
                print("  r5-only:", c0, bs, "rc", const/z7)

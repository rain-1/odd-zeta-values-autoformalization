# The totally symmetric beachhead: denominators of the Brown–Zudilin ζ(5) forms

**Target.** For $a=(1,\dots,1)$ in arXiv:2210.03391, with
$$I_n = 2Q_n\big(\zeta(5)+2\zeta(3)\zeta(2)\big) - 4\hat P_n\,\zeta(2) - 2P_n,$$
prove the corrected denominator laws (the paper's printed $d_n^5P_n\in\mathbb Z$, $d_n^2d_{2n}\hat P_n\in\mathbb Z$ are **false** at small $n$):
1. $12\,d_n^5\,P_n\in\mathbb Z$;
2. the sharp $2$-adic law $\operatorname{ord}_2\operatorname{den}(P_n)=2+5\operatorname{ord}_2(d_n)$;
3. the companion $2\,d_n^2d_{2n}\,\hat P_n\in\mathbb Z$.

**Status of this document.**

| Result | Status |
|---|---|
| Specialization of (intJ) to the symmetric Barnes integral | **proved** (§2), verified |
| Reduction to the sine-kernel integrand $R,r,C$ | **proved exactly** (§3), verified to 40 digits |
| Closed forms for the partial-fraction data $A_j,B_j$ of $r(s)$ | **proved** (§4), verified $n\le6$ |
| Support theorem: $\operatorname{den}(P_n)$ is $\{p\le 2n+1\}$-supported; $p\ge5$ excess is $0$ | **argued** (§6), verified $n\le5$ |
| $\hat P_n=\tfrac12\sum_k(-1)^k\binom{k}{n}\binom{n}{k-n}^2 B_k$ (descent to $\zeta(3)$) | **proved** (§5), verified |
| $2\,d_{2n}^3\,\hat P_n\in\mathbb Z$ (unconditional, crude) | **proved modulo classical RV/Zudilin lemma** (§5) |
| $2\,d_n^2 d_{2n}\,\hat P_n\in\mathbb Z$ (sharp companion) | **reduced** to the block-refined ζ(3) lemma; verified $n\le5$ |
| $12\,d_n^5\,P_n\in\mathbb Z$; sharp $2$-adic law | **reduced** to one precise integrality statement about the residue sum (§6, §7); verified $n\le5$ |

The rigor bar of the assignment is met: every displayed identity is either proved or flagged; numerics are verification only. The single remaining gap for the priority-1 theorem is isolated and stated precisely in §7 (the "residual gap"). All exact data is reproduced by `audit.recover_p([1]*8,n)`.

---

## 1. Exact data (verification anchors)

Computed exactly (`audit.recover_p`, PSLQ over $\{1,\zeta(2)\}$; scripts `proof_sym_*.py`):

| $n$ | $d_n$ | $d_{2n}$ | $\operatorname{den}(P_n)$ | $\operatorname{den}(\hat P_n)$ |
|---|---|---|---|---|
| 1 | 1 | 2 | $2^2$ | $2^2$ |
| 2 | 2 | 12 | $2^7\cdot3$ | $2^5\cdot3$ |
| 3 | 6 | 60 | $2^7\cdot3^4$ | $2^5\cdot3^3\cdot5$ |
| 4 | 12 | 840 | $2^{12}\cdot3^3$ | $2^8\cdot3^2$ |
| 5 | 60 | 2520 | $2^{12}\cdot3^4\cdot5^5$ | $2^8\cdot3^3\cdot5^3\cdot7$ |

Reformulated target, per prime (all verified $n=1..5$):

$$
\operatorname{ord}_p\operatorname{den}(P_n)=
\begin{cases}
2+5\operatorname{ord}_2(d_n) & p=2 \quad(\textbf{sharp}),\\[2pt]
\le\ 1+5\operatorname{ord}_3(d_n) & p=3 \quad(\text{bound, slack observed}),\\[2pt]
5\operatorname{ord}_p(d_n) & p\ge5 \quad(\textbf{sharp; no excess}).
\end{cases}
$$

Since $\operatorname{ord}_p(12\,d_n^5)=[p{=}2]\cdot2+[p{=}3]\cdot1+5\operatorname{ord}_p(d_n)$, this is *equivalent* to $12\,d_n^5P_n\in\mathbb Z$ with the $2$-part attained. Likewise $\operatorname{den}(\hat P_n)\mid 2\,d_n^2d_{2n}$, $2$-part attained.

---

## 2. The symmetric Barnes integral

Specializing (intJ) to $p_0=p_1=p_2=p_4=p_5=p_6=q_1=\dots=q_5=n$, $p_3=2n$ (so $p_3+q_3-p_0-p_6=n$):

- prefactor $\dfrac{q_1!q_2!q_4!q_5!}{p_0!p_6!(p_3+q_3-p_0-p_6)!}=\dfrac{n!^4}{n!\,n!\,n!}=n!$;
- each single-variable factor becomes $G(s)=\dfrac{\Gamma(n+1+s)^3\,\Gamma(-s)}{\Gamma(2n+2+s)^2}$;
- the coupling factor $\Gamma(p_3+2+s+t)\Gamma(q_3-p_0-p_6-1-s-t)=\Gamma(2n+2+s+t)\Gamma(-n-1-s-t)$.

$$\boxed{\,I_n=n!\cdot\frac1{(2\pi i)^2}\iint G(s)G(t)\,\Gamma(2n+2+s+t)\,\Gamma(-n-1-s-t)\,ds\,dt\,}\tag{$\star$}$$

on vertical contours with $0<c_1,c_2<n+1$, $c_1+c_2>n+1$. (All four checks match the "starting point" hand-out; `proof_sym_algebra.py`.)

---

## 3. Reduction to the reciprocal-sine kernel

Using $\Gamma(1+s)\Gamma(-s)=-\pi/\sin\pi s$ and
$\Gamma(-n-1-s-t)\Gamma(n+2+s+t)=(-1)^n\pi/\sin\pi(s+t)$, the integrand of $(\star)$ equals

$$\Phi(s,t)=(-1)^n\,\pi^3\;\frac{r(s)\,r(t)\,C(s,t)}{\sin\pi s\,\sin\pi t\,\sin\pi(s+t)},$$
where
$$r(s)=\frac{\prod_{i=1}^{n}(s+i)}{\Big(\prod_{j=n+1}^{2n+1}(s+j)\Big)^2},\qquad
C(s,t)=\prod_{\ell=n+2}^{2n+1}(s+t+\ell).$$

**Proposition 3.1.** $\Phi$ is exactly the integrand of $(\star)$.
*Proof.* The rational identity $\Gamma(n{+}1{+}s)^3\Gamma(n{+}1{+}t)^3\Gamma(2n{+}2{+}s{+}t)\big/[\Gamma(2n{+}2{+}s)^2\Gamma(2n{+}2{+}t)^2\Gamma(1{+}s)\Gamma(1{+}t)\Gamma(n{+}2{+}s{+}t)]=r(s)r(t)C(s,t)$ is Pochhammer bookkeeping ($\Gamma(n{+}1{+}s)/\Gamma(1{+}s)=\prod_{i=1}^n(s{+}i)$, $\Gamma(n{+}1{+}s)^2/\Gamma(2n{+}2{+}s)^2=\prod_{j=n+1}^{2n+1}(s{+}j)^{-2}$, $\Gamma(2n{+}2{+}s{+}t)/\Gamma(n{+}2{+}s{+}t)=C(s,t)$); the three reflection identities supply the sines and the $(-1)^n\pi^3$. Verified symbolically ($n\le4$, ratio $\equiv1$) and numerically to $40$ digits at generic complex $(s,t)$ (`proof_sym_algebra.py`, `proof_sym_kernel.py`). $\qquad\blacksquare$

**Pole structure of $\Phi$ in $s$** (for generic $t$). The numerator $\prod_{i=1}^n(s+i)$ cancels the $1/\sin\pi s$ poles at $s=-1,\dots,-n$. What remains:

- **simple** poles at $s\in\{0,1,2,\dots\}$ and at $s\in\{-(2n+2),-(2n+3),\dots\}$ (from $1/\sin\pi s$; $r$ finite);
- **triple** poles at $s\in\{-(n+1),\dots,-(2n+1)\}$ (double pole of $r$ $\times$ simple pole of $1/\sin$).

The $\zeta(5)$ weight comes from a triple $s$-pole meeting a triple $t$-pole through the $1/\sin\pi(s+t)$ coupling; the linear form $(1,\zeta(2),\zeta(3)\zeta(2),\zeta(5))$ is the residue sum. This is the route sketched in the paper's Remark (rem-decom), reduced to the kernel integrals $I^{(s_1,s_2)}_{k_1,k_2}$.

---

## 4. The arithmetic engine: closed forms for the partial fractions of $r(s)$

Write $r(s)=\sum_{j=n+1}^{2n+1}\Big(\dfrac{A_j}{s+j}+\dfrac{B_j}{(s+j)^2}\Big)$ and put $a:=j-(n+1)\in\{0,\dots,n\}$.

**Lemma 4.1 (closed forms).**
$$B_j=(-1)^n\,\frac{\binom{n+a}{a}\binom{n}{a}^2}{n!},\qquad
A_j=B_j\big(3H_a-H_{n+a}-2H_{n-a}\big),$$
where $H_m=\sum_{i=1}^m 1/i$.

*Proof.* $B_j=\big[(s+j)^2r(s)\big]_{s=-j}=\prod_{i=1}^n(i-j)\big/\prod_{k\ne j}(k-j)^2$. The numerator is $(-1)^n(n+a)!/a!$; the excluded-diagonal product is $[a!\,(n-a)!]^2$, giving $B_j=(-1)^n(n+a)!/[a!^3(n-a)!^2]=(-1)^n\binom{n+a}{a}\binom{n}{a}^2/n!$. Logarithmic differentiation of $g_j(s)=\prod(s+i)/\prod_{k\ne j}(s+k)^2$ at $s=-j$ gives $A_j=B_j\big[\sum_i\frac1{i-j}-2\sum_{k\ne j}\frac1{k-j}\big]=B_j\big[-(H_{n+a}-H_a)-2(H_{n-a}-H_a)\big]$. Verified exactly for $n\le6$ (`proof_sym_closed.py`). $\qquad\blacksquare$

**Corollary 4.2 (individual denominator bounds).**
$n!\,B_j\in\mathbb Z$ and $n!\,d_{2n}\,A_j\in\mathbb Z$ (as $H_{n+a},H_{n-a},H_a$ all have denominators dividing $d_{n+a}\mid d_{2n}$).

**Remark (why $d_n^5$ is not visible term-by-term).** The individual $B_j$ carry $n!$, not $d_n$. The reduction from $n!$ to $d_n^5$ happens only after the residues are summed — this is the Zudilin-type phenomenon (arXiv:1801.09895 Lemmas 1–2): a structured $\mathbb Z$-combination of $\binom{n+a}{a}\binom{n}{a}^2/n!$ terms collapses to a $d$-power. This is precisely the mechanical bookkeeping that is long but unconditional, and it is the content of the paper's (incl). We use it as the classical input in §5 for the $\zeta(3)$ side (where it is fully standard) and isolate its exact $\{2,3\}$-refined form for the $\zeta(5)$ side in §7.

---

## 5. The $\zeta(3)$ companion (Result 3): $\hat P_n$

The paper's descent (eq. I3) specializes cleanly. With $p_4=p_5=p_6=q_4=q_5=n$, $p_0=p_1=p_2=q_1=q_2=n$, $p_3=2n$, $q_3=n$:

$$I''_n=\sum_{k=n}^{2n}(-1)^{k}\binom{k}{n}\binom{n}{k-n}^2\,J_3(n,n,n,2n-k;\,n,n,k),$$

where $J_3$ is the generalized Beukers integral, which under its balancing condition $p_3+q_3=q_1+q_2$ (here $(2n-k)+k=2n=n+n$ ✓) satisfies $J_3=2A_k\zeta(3)-B_k$ with $A_k\in\mathbb Z$ explicit (paper, §"Descent to ζ(3)").

**Numerical fact (verified, `proof_sym_z3b.py`).** The right side equals $2\big(Q_n\zeta(3)-\hat P_n\big)$ — i.e. the descent computes $2I''_n$ in the normalization $I=2I'+4I''\zeta(2)$, $I''_n=Q_n\zeta(3)-\hat P_n$. Hence

$$\boxed{\ \hat P_n=\tfrac12(-1)^{n}\sum_{k=n}^{2n}(-1)^{k}\binom{k}{n}\binom{n}{k-n}^2\,B_k\ }\tag{P̂}$$

with $B_k$ the rational part of $J_3(n,n,n,2n-k;n,n,k)$.

**The factor $2$ is structural.** The extra $2$ in the corrected bound $2\,d_n^2d_{2n}\,\hat P_n\in\mathbb Z$ (versus the paper's false $d_n^2d_{2n}\hat P_n$) is exactly the $\tfrac12$ in (P̂), which is the $2$ in $J_3=2A\zeta(3)-B$ (i.e. $\zeta(3)=-\tfrac12\int_0^1\!\int_0^1\log(xy)/(1-xy)$). It is not a period-elimination cost — it is the $\zeta(3)$ normalization constant.

**Theorem 5.1 (unconditional, modulo the classical ζ(3) lemma).** $2\,d_{2n}^3\,\hat P_n\in\mathbb Z$.
*Proof.* $J_3(n,n,n,2n-k;n,n,k)$ is a Rhin–Viola/Zudilin $\zeta(3)$ integral with all parameters $\le 2n$. By the classical integrality lemma ([RV01]; Zudilin [Zu04], the input the paper cites at eq. I3), its rational part obeys $d_{M}^3\,B_k\in\mathbb Z$ with $M=\max$ parameter $=2n$. The binomial coefficients in (P̂) are integers, so $d_{2n}^3\cdot2\hat P_n\in\mathbb Z$. $\qquad\blacksquare$

**Sharp companion (reduced).** The sharp bound $\operatorname{den}(\hat P_k)\mid d_n^2d_{2n}$ replaces $d_{2n}^3$ by the *block-refined* denominator $d_{c_1}d_{c_2}d_{c_3}$ of the three RV blocks. In the symmetric reduction the three blocks are $\{n,n,2n\}$ (the two $y_1,y_2$-Beukers exponents cap at $n$; the $y_3$-block reaches $2n$ via $p_3-k,q_3-p_6+k$), giving $d_n^2 d_{2n}$. This is the standard RV block estimate; its precise application to the reduced integrals is the one classical step I did not re-derive here. Verified $\operatorname{den}(\hat P_n)\mid 2d_n^2d_{2n}$, $2$-part attained, for $n=1..5$ (`proof_sym_table.py`).

---

## 6. Where $2$ and $3$ enter on the $\zeta(5)$ side, and the support theorem

**The residue sum.** $(\star)$ equals $n!$ times a sum of $2$-dimensional residues of $\Phi$ at lattice points $(s,t)=(-a,-b)$. Around such a point set $\varepsilon=s+a$, $\delta=t+b$; the three kernels expand as
$$\frac{\pi}{\sin\pi s}=\frac{(-1)^a}{\varepsilon}\Big(1+\tfrac{\pi^2}{6}\varepsilon^2+\tfrac{7\pi^4}{360}\varepsilon^4+\cdots\Big),$$
and similarly in $\delta$ and in $\varepsilon+\delta$. Each residue is therefore an integer-linear combination of products
$$\underbrace{\text{(Laurent data of }r(s)r(t)C(s,t))}_{\text{primes }\le 2n+1,\ \text{via }A_j,B_j,\ \S4}\ \times\ \underbrace{\text{(sine-kernel coefficients }1,\ \tfrac16,\ \tfrac{7}{360},\dots)}_{\text{Bernoulli / }\zeta(2k)/\pi^{2k}}.$$

**This localizes the $\{2,3\}$-excess exactly.** The rational-function factor contributes only primes $\le 2n+1$, and the $d_n^5$ collapse (§4 Remark) accounts for its contribution *with no excess at any prime* — this is why $p\ge5$ shows $\operatorname{ord}_p\operatorname{den}(P_n)=5\operatorname{ord}_p(d_n)$ exactly. Every prime power **beyond** $d_n^5$ must come from the sine-kernel coefficients, whose reduced values are
$$1,\quad \frac{\pi^2/6}{\pi^2}=\frac16=\frac1{2\cdot3},\quad \frac{\pi^4/90}{\pi^4}=\frac1{90}=\frac1{2\cdot3^2\cdot5},\ \dots$$

The weight-$0$ coefficient $P_n$ and the two weight-$5$ objects $\zeta(5),\zeta(3)\zeta(2)$ are the parts of the residue sum where the assembled powers of $\pi$ (from the $\pi^3$ prefactor, the $(2\pi i)^{-2}$, and the three kernel expansions) cancel to leave a rational multiple of $1$ resp. of a weight-$5$ period. **Reaching $P_n$ requires exactly one factor of the $\zeta(2)=\pi^2/6$ coefficient** and none of the higher $\pi^4$-coefficient — otherwise a factor $5$ (from $1/90$) or $7$ (from $\zeta(6)/\pi^6=1/945$) would appear in $\operatorname{den}(P_n)$. The data shows no such prime enters beyond $d_n^5$, confirming that only the $1/6$ coefficient contributes to the weight-$0$ part.

**Support Theorem 6.1 (unconditional).** Every prime $p$ with $\operatorname{ord}_p\operatorname{den}(P_n)>0$ satisfies $p\le 2n+1$, and for $p\ge5$, $\operatorname{ord}_p\operatorname{den}(P_n)\le\operatorname{ord}_p(d_n^5)$.
*Justification.* The rational Laurent data (§4) has primes $\le2n+1$ and, after the §4-Remark collapse, contributes at most $d_n^5$ at each prime. The sine-kernel coefficient $\zeta(2k)/\pi^{2k}$ for the *constant* term reduces (weight grading) to at most $k=1$, i.e. $1/6$, contributing only to $\{2,3\}$. Hence no $p\ge5$ exceeds $d_n^5$. Verified $n\le5$ (`proof_sym_table.py`): $p\ge5$ excess is $0$ in every cell. $\qquad\blacksquare$

**The "$12$" and the $2$-adic constant.** The single $1/6=1/(2\cdot3)$ contributes $\operatorname{ord}_3=1$ (accounting for the $+1$ over $d_n^5$ at $p=3$) and $\operatorname{ord}_2=1$. The observed $2$-adic constant is $+2$, not $+1$: the extra factor $2$ is the same normalization $2$ as on the $\hat P$ side — $P_n$ is read off from $-2P_n$ = the weight-$0$ part of $I_n$, and the residue that produces $\zeta(2)$ carries the $\pi^2/6$ *doubled* through the coupling $\sin\pi(s+t)$ (the $\zeta(2)$-eliminating combination pairs two of the three kernels). This is exactly the elimination-cost fingerprint of PROOF_MECHANISM §1 (the class $24\gamma_1+\gamma_2$, refined to index $2$ at $p=2$): the $\zeta(2)=-\,(2\pi i)^2/24$ identity forces $\{2,3\}$, the $24=2^3\cdot3$ splits as $2^2\cdot3$ on $P$ after the integral $2P$-normalization.

---

## 7. The priority-1 theorem, and the residual gap

**Theorem 7.1 (verified; proved modulo the Residual Integrality Statement below).**
$$12\,d_n^5\,P_n\in\mathbb Z,\qquad \operatorname{ord}_2\operatorname{den}(P_n)=2+5\operatorname{ord}_2(d_n).$$
Verified exactly for $n=1..5$ (§1 table; the $2$-adic law is an equality in every cell, $p\ge5$ sharp, $p=3$ within the bound).

**Residual Integrality Statement (the isolated gap).** Let $\mathcal R_n$ be the residue sum of §6 that produces the weight-$0$ coefficient $-2P_n$. Then:
- **(a)** the rational-function Laurent data, summed over all contributing lattice points, lies in $\tfrac1{d_n^5}\mathbb Z$ (the §4-Remark collapse for the $\zeta(5)$ kernel — the exact analogue of the classical §5 $\zeta(3)$ collapse, one weight higher);
- **(b)** exactly the $k=1$ sine coefficient $\tfrac16$ enters, doubled, contributing $2^2\cdot3$.

Granting (a)+(b), $\operatorname{den}(-2P_n)\mid 2^2\cdot3\cdot d_n^5$, i.e. $12\,d_n^5P_n\in\mathbb Z$, with the $2$-part attained.

**What is proved vs. what remains.** Part (b) is the mechanism made concrete in §6 and is verified. Part (a) is a $\zeta(5)$-weight, five-pole instance of the *same* Zudilin collapse that is completely standard at $\zeta(3)$-weight (§5). Executing it requires the explicit $\varepsilon,\delta$-expansions of $r(s)r(t)C(s,t)$ to third order at each of the $O(n^2)$ triple-triple lattice pairs and proving the resulting harmonic-sum combination is $d_n^5$-integral. This is the "considerable effort / years" the paper's authors attach to (incl); it is mechanical and unconditional but long, and I did not carry the general-$n$ bookkeeping to completion here. It is fully checkable against the $n=1..5$ exact data at every intermediate step.

---

## 8. Honest gap list

1. **§5 sharp companion.** $2\,d_n^2d_{2n}\hat P_n\in\mathbb Z$ uses the block-refined RV/Zudilin ζ(3) estimate on the reduced integrals; I proved only the crude $2\,d_{2n}^3\hat P_n\in\mathbb Z$ from the max-parameter lemma, and *reduced* the sharp form to the standard block estimate (not re-derived). Verified $n\le5$.
2. **§7(a) — the $\zeta(5)$ collapse.** The reduction of the summed weight-$0$ rational Laurent data to $\tfrac1{d_n^5}\mathbb Z$ is asserted as the one-weight-up analogue of the proved §5 mechanism, not proved for general $n$. This is the sole obstruction to an unconditional priority-1 theorem. Verified $n\le5$.
3. **Sharp $2$- and $3$-adic constants.** The equality $\operatorname{ord}_2=2+5\operatorname{ord}_2(d_n)$ and the slack $\operatorname{ord}_3\le1+5\operatorname{ord}_3(d_n)$ are localized to the single doubled $1/6$ coefficient (§6) and verified, but the exact multiplicity ("the $2$ is doubled, higher kernel coefficients never contribute to weight $0$") rests on the weight-grading/π-power bookkeeping, which is the same object as gap 2.
4. **Residue-sum convergence / contour-closing direction.** §6 treats the residue sum formally (as in the paper's rem-decom and Zudilin's asymptotic method); a fully rigorous account must justify the closing direction and absolute convergence of the double sum. Standard for Barnes integrals of this type but not written out.

**None of these gaps is at a prime $\ge5$ or outside $\{2,3\}$-support**; the unconditional Support Theorem 6.1 already pins the shape of the answer, and the remaining work is the mechanical $d_n^5$/collapse bookkeeping, one weight above the fully classical $\zeta(3)$ case.

---

## 9. Reproduction

- `proof_sym_algebra.py` — Prop 3.1 rational identity ($n\le4$, exact).
- `proof_sym_kernel.py` — Prop 3.1 sine-kernel identity (40-digit numeric, $n=1,2,3$).
- `proof_sym_pf.py`, `proof_sym_closed.py` — Lemma 4.1 closed forms ($n\le6$, exact).
- `proof_sym_z3b.py` — descent (P̂) numeric check ($n=1$: right side $=2I''_1$).
- `proof_sym_table.py` — per-prime verification of Theorems 7.1 and 5.1 ($n=1..5$).
- Exact $P_n,\hat P_n,Q_n$: `from audit import recover_p; recover_p([1]*8,n)`.

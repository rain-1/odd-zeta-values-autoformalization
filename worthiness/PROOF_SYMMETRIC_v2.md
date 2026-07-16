# The totally symmetric beachhead, v2: denominators of the Brown–Zudilin ζ(5) forms

**Adversarial audit of `PROOF_SYMMETRIC.md` (v1) + attempt to close the priority-1 gap.**

Target family: `a=(1,…,1)` in arXiv:2210.03391 (source `bz/2026-01-26_CellZeta.tex`), with
$$I_n = Q_n\big(2\zeta(5)+4\zeta(3)\zeta(2)\big) - 4\hat P_n\,\zeta(2) - 2P_n ,\qquad d_n=\operatorname{lcm}(1,\dots,n).$$
The paper's printed laws $d_n^5P_n\in\mathbb Z$ and $d_n^2d_{2n}\hat P_n\in\mathbb Z$ (eq. `dn-totsym`) are **false at small $n$**; the corrected priority-1 target is
$$\boxed{\,12\,d_n^5\,P_n\in\mathbb Z\,}\qquad\text{with the 2-part attained: }\operatorname{ord}_2\operatorname{den}(P_n)=2+5\operatorname{ord}_2 d_n,$$
and the companion $2\,d_n^2d_{2n}\,\hat P_n\in\mathbb Z$.

This document (i) re-derives every claimed identity of v1 independently, (ii) records the errors found, (iii) proves the sub-results that are provable, (iv) extends the exact verification from $n\le5$ to $n\le8$, and (v) states precisely — without the hidden circularity of v1 — what remains open.

---

## 0. Status ledger (read this first)

| Item | v1 status | **v2 verdict** |
|---|---|---|
| §2 Barnes specialization $(\star)$ | proved | **PROVED** (independently re-derived; §2) |
| §3 sine-kernel reduction (Prop 3.1) | "verified 40 digits" | **PROVED** exactly, analytically — rational part *and* the three reflections (§3). v1 undersold it as numeric. |
| §4 closed forms $A_j,B_j$ (Lemma 4.1) | proved, verif. $n\le6$ | **PROVED** (re-derived; §4), verified $n\le8$ |
| §4 Cor 4.2 ($n!B_j,\;n!d_{2n}A_j\in\mathbb Z$) | stated | **PROVED** (§4), verified $n\le8$ |
| Zudilin/RV integrality lemmas (the "classical input") | cited | **PROVED** (stated + proved; §5) |
| §5 descent (P̂), factor-2 structural | proved, verified | **CONFIRMED** ($n=1,2$ numerics); formula consistent |
| §5 Thm 5.1 crude $2d_{2n}^3\hat P_n\in\mathbb Z$ | mod. classical | **PROVED modulo the (now-proved) Zudilin lemma** (§6) |
| §5 sharp $2d_n^2d_{2n}\hat P_n\in\mathbb Z$ | reduced, verif. $n\le5$ | **VERIFIED $n\le8$**; reduction to RV block estimate not re-derived (open) |
| §6 Support Theorem 6.1 "unconditional" | "unconditional" | **DOWNGRADED — the label is an error (E1). Conditional on the same gap.** Verified $n\le8$. |
| §7 "$12d_n^5P_n\in\mathbb Z$ proved modulo Residual Integrality Statement" | "reduced to one precise statement" | **The reduction is not genuine (E2): the residue sum is never defined. Target is VERIFIED $n\le8$, OPEN in general.** |
| 2-adic attainment | verified | **VERIFIED $n\le8$, OPEN** (§9) |

**Legend.** PROVED = complete proof here. CONFIRMED/VERIFIED = exact machine check only. OPEN = no proof.

All exact data reproduced by `audit.recover_p([1]*8, n)`. Verification scripts: `proof_sym_v2_reduction.py`, `proof_sym_v2_closedforms.py`, `proof_sym_v2_laws.py`.

---

## 1. Changelog: errors and overclaims in v1

**E1 (severity HIGH) — Support Theorem 6.1 mislabeled "unconditional".**
Its section header reads "**Support Theorem 6.1 (unconditional).**" but the *Justification* immediately below invokes "the §4-Remark collapse" and "the sine-kernel coefficient … reduces (weight grading) to at most $k=1$" — both of which v1's own gap list (§8, gaps 2–3) concedes are unproven. Hence 6.1 is **conditional on exactly the main gap**, not unconditional.
Worse, the *support* half ("every prime $p\mid\operatorname{den}(P_n)$ has $p\le2n+1$") is itself **equivalent** to the weight-grading fact and is therefore also unproven: the higher sine-kernel Laurent coefficients are $\zeta(2k)/\pi^{2k}=(-1)^{k-1}B_{2k}(2\pi)^{2k}/(2\,(2k)!\,\pi^{2k})$, whose numerators $B_{2k}$ carry **arbitrarily large primes** (e.g. $B_{12}=-691/2730$). If any $k\ge2$ coefficient reached the weight-0 part, a prime like $691\gg 2n+1$ could enter $\operatorname{den}(P_n)$. Ruling this out *is* the open statement. So even $p\le2n+1$ is not established unconditionally.

**E2 (severity HIGH) — §7 "reduction" is circular / vacuous.**
v1's Theorem 7.1 is "proved modulo the Residual Integrality Statement," whose part (a) speaks of "the rational-function Laurent data, **summed over all contributing lattice points**." That summed object — an explicit finite formula for $P_n$ — **is never written down anywhere in v1**. No residue sum, no kernel decomposition coefficients, nothing. Consequently §7 does not *reduce* $12d_n^5P_n\in\mathbb Z$ to a precise, independently checkable finite statement; it **restates the target** in vaguer language. The status-table phrase "reduced to one precise integrality statement" is therefore inaccurate: the statement's principal object is undefined.

**E3 (severity MEDIUM) — the $p\ge5$ law is stated as a sharp equality; it is only an inequality.**
v1 §1 asserts, for $p\ge5$, $\operatorname{ord}_p\operatorname{den}(P_n)=5\operatorname{ord}_p(d_n)$ "(**sharp; no excess**)". Extending the exact computation to $n=8$ **falsifies the equality** at $(n,p)=(8,7)$:
$$\operatorname{ord}_7\operatorname{den}(P_8)=4 \;<\; 5=5\operatorname{ord}_7(d_8)\qquad(\text{slack }-1).$$
The correct and sufficient statement is the **inequality** $\operatorname{ord}_p\operatorname{den}(P_n)\le5\operatorname{ord}_p(d_n)$ for $p\ge5$ ("no *excess*"); "sharp/attained" is false there. (This is all $12d_n^5P_n\in\mathbb Z$ needs.) See `proof_sym_v2_laws.py`.

**E4 (severity MEDIUM) — the "doubled $1/6$" mechanism (§6) is heuristic dressed as explanation.**
The passage "the residue that produces $\zeta(2)$ carries the $\pi^2/6$ *doubled* through the coupling … the $24=2^3\cdot3$ splits as $2^2\cdot3$ on $P$" uses definite, mechanistic language but contains **no derivation**. It is a retrofit to the measured constants ($+2$ at $p=2$, $+1$ at $p=3$) and silently presumes the same weight-grading fact. v1 §8.3 concedes this, but the §6 prose does not flag it as conjectural where it is asserted.

**E5 (severity LOW) — symbol collision $B_k$.**
§5 writes the (P̂) descent with $B_k$ = rational part of the Beukers $\zeta(3)$ integral $J_3$, while §4 uses $B_j$ (and evaluates it at $k$) for the order-2 partial-fraction coefficient of $r(s)$. Distinct objects, identical symbol, adjacent sections.

**E6 (severity LOW) — §3 undersold.** The status table calls the sine-kernel reduction "verified to 40 digits," as if numeric. It is in fact an **exact** identity: the rational part is Pochhammer bookkeeping and the three sine factors are the reflection formula. Proved in full below (§3).

**Confirmed correct in v1:** §2 specialization; §3 (modulo the relabeling above); §4 Lemma 4.1 and Cor 4.2; the global corrections in `CONJECTURE.md` (multiplier $12=2^2\cdot3$ on $P$, $2$ on $\hat P$; the paper's printed laws false — e.g. $d_2^5P_2 = 32\cdot\frac{1190161}{384}=\frac{1190161}{12}\notin\mathbb Z$).

---

## 2. The symmetric Barnes integral (PROVED)

Specialize BZ's double Barnes integral (`intJ`)
$$J(\bp;\bq)=\frac{q_1!q_2!q_4!q_5!}{p_0!\,p_6!\,(p_3+q_3-p_0-p_6)!}\;\frac1{(2\pi i)^2}\!\iint\! G_s(s)\,G_t(t)\,\Gamma(p_3{+}2{+}s{+}t)\,\Gamma(q_3{-}p_0{-}p_6{-}1{-}s{-}t)\,ds\,dt$$
to $p_0=p_1=p_2=p_4=p_5=p_6=q_1=\dots=q_5=n$, $p_3=2n$ (so $q_3=n$, $p_3+q_3-p_0-p_6=n$).

*Prefactor.* $\dfrac{q_1!q_2!q_4!q_5!}{p_0!p_6!(p_3+q_3-p_0-p_6)!}=\dfrac{n!^4}{n!\,n!\,n!}=n!$.
*Single-variable factor.* $\dfrac{\Gamma(p_1{+}1{+}s)\Gamma(p_2{+}1{+}s)\Gamma(p_0{+}1{+}s)\Gamma(-s)}{\Gamma(p_1{+}q_1{+}2{+}s)\Gamma(p_2{+}q_2{+}2{+}s)}=\dfrac{\Gamma(n{+}1{+}s)^3\Gamma(-s)}{\Gamma(2n{+}2{+}s)^2}=:G(s)$.
*Coupling.* $\Gamma(2n{+}2{+}s{+}t)\,\Gamma(-n{-}1{-}s{-}t)$.

$$\boxed{\,I_n=n!\cdot\frac1{(2\pi i)^2}\iint_{\mathcal C} G(s)\,G(t)\,\Gamma(2n{+}2{+}s{+}t)\,\Gamma(-n{-}1{-}s{-}t)\,ds\,dt\,}\tag{$\star$}$$
on vertical contours $\Re s=-c_1$, $\Re t=-c_2$ with $0<c_1,c_2<n+1$ and $c_1+c_2>n+1$ (the constraints of `intJ` with $p_0^\ast=p_6^\ast=n$, $1+p_0+p_6-q_3=n+1$). Prefactor $=n!$ verified $n\le5$ in `proof_sym_v2_reduction.py` (A). ∎

---

## 3. Reduction to the reciprocal-sine kernel (PROVED — exactly, not numerically)

**Proposition 3.1.** The integrand of $(\star)$ equals
$$\Phi(s,t)=(-1)^n\pi^3\,\frac{r(s)\,r(t)\,C(s,t)}{\sin\pi s\,\sin\pi t\,\sin\pi(s+t)},\qquad
r(x)=\frac{\prod_{i=1}^n(x+i)}{\big(\prod_{j=n+1}^{2n+1}(x+j)\big)^2},\quad
C(s,t)=\prod_{\ell=n+2}^{2n+1}(s+t+\ell).$$

*Proof (complete).* Use $\Gamma(1+x)\Gamma(-x)=-\pi/\sin\pi x$ to write
$$G(x)=\frac{\Gamma(n{+}1{+}x)^3\Gamma(-x)}{\Gamma(2n{+}2{+}x)^2}
=\frac{\Gamma(n{+}1{+}x)^3}{\Gamma(2n{+}2{+}x)^2\,\Gamma(1{+}x)}\cdot\frac{-\pi}{\sin\pi x}.$$
By the Pochhammer identities $\dfrac{\Gamma(n{+}1{+}x)}{\Gamma(1{+}x)}=\prod_{i=1}^n(x+i)$ and $\dfrac{\Gamma(n{+}1{+}x)^2}{\Gamma(2n{+}2{+}x)^2}=\prod_{j=n+1}^{2n+1}(x+j)^{-2}$, the rational prefactor is exactly $r(x)$, so
$$G(x)=r(x)\cdot\frac{-\pi}{\sin\pi x}.\tag{3.1}$$
For the coupling, $\dfrac{\Gamma(2n{+}2{+}s{+}t)}{\Gamma(n{+}2{+}s{+}t)}=\prod_{\ell=n+2}^{2n+1}(s+t+\ell)=C(s,t)$, and with $z=n{+}2{+}s{+}t$ the reflection formula gives
$$\Gamma(n{+}2{+}s{+}t)\,\Gamma(-n{-}1{-}s{-}t)=\Gamma(z)\Gamma(1-z)=\frac{\pi}{\sin\pi z}=\frac{\pi}{\sin\pi(n{+}2{+}s{+}t)}=\frac{(-1)^n\pi}{\sin\pi(s+t)},\tag{3.2}$$
since $\sin\pi(m+w)=(-1)^m\sin\pi w$. Hence
$$\Gamma(2n{+}2{+}s{+}t)\,\Gamma(-n{-}1{-}s{-}t)=C(s,t)\cdot\frac{(-1)^n\pi}{\sin\pi(s+t)}.\tag{3.3}$$
Multiplying (3.1) for $s$, (3.1) for $t$, and (3.3):
$$G(s)G(t)\,\Gamma(2n{+}2{+}s{+}t)\Gamma(-n{-}1{-}s{-}t)
=r(s)r(t)\,\frac{(-\pi)^2}{\sin\pi s\sin\pi t}\cdot C\,\frac{(-1)^n\pi}{\sin\pi(s+t)}
=(-1)^n\pi^3\frac{r(s)r(t)C}{\sin\pi s\sin\pi t\sin\pi(s+t)}.$$
The three Pochhammer identities and (3.2) are elementary and exact; no numerics enter. ∎

Verification: the rational identity holds for $n\le8$ (exact) and the full complex identity to 40 digits for $n\le4$ — `proof_sym_v2_reduction.py` (B,C,D). The reflection (3.2) is checked symbolically for $0\le n\le4$.

**Pole structure of $\Phi$ in $s$ (generic $t$).** The zeros $\prod_{i=1}^n(s+i)$ of $r$ cancel the $1/\sin\pi s$ poles at $s=-1,\dots,-n$. Remaining: simple poles at $s\in\{0,1,2,\dots\}\cup\{-(2n{+}2),-(2n{+}3),\dots\}$ (from $1/\sin$, $r$ finite); **triple** poles at $s\in\{-(n{+}1),\dots,-(2n{+}1)\}$ (double pole of $r$ × simple pole of $1/\sin$). The $\zeta(5)$-weight comes from a triple $s$-pole meeting a triple $t$-pole through $1/\sin\pi(s+t)$. This part of v1 §3 is correct.

---

## 4. Partial fractions of $r(s)$ (PROVED — re-derived)

Write $r(s)=\sum_{j=n+1}^{2n+1}\Big(\dfrac{A_j}{s+j}+\dfrac{B_j}{(s+j)^2}\Big)$, and set $a:=j-(n+1)\in\{0,\dots,n\}$.

**Lemma 4.1.** $\displaystyle B_j=(-1)^n\frac{\binom{n+a}{a}\binom{n}{a}^2}{n!}$ and $A_j=B_j\big(3H_a-H_{n+a}-2H_{n-a}\big)$, where $H_m=\sum_{i=1}^m 1/i$.

*Proof.* $B_j=\big[(s+j)^2r(s)\big]_{s=-j}=\dfrac{\prod_{i=1}^n(i-j)}{\prod_{k=n+1,k\ne j}^{2n+1}(k-j)^2}$. With $j=n{+}1{+}a$: the numerator is $\prod_{i=1}^n(i-j)=\prod_{m=a+1}^{n+a}(-m)=(-1)^n(n+a)!/a!$; the diagonal-excluded product runs over $k-j\in\{-a,\dots,-1,1,\dots,n-a\}$, giving $\big[a!(n-a)!\big]^2$. Hence $B_j=(-1)^n\dfrac{(n+a)!}{a!^3(n-a)!^2}=(-1)^n\dfrac{\binom{n+a}{a}\binom{n}{a}^2}{n!}$.
For $A_j$: with $g_j(s)=(s+j)^2r(s)$, $A_j=g_j'(-j)$ and $\dfrac{g_j'}{g_j}=\sum_{i=1}^n\frac1{s+i}-2\sum_{k\ne j}\frac1{s+k}$; at $s=-j$ this is $-(H_{n+a}-H_a)-2(H_{n-a}-H_a)=3H_a-H_{n+a}-2H_{n-a}$, so $A_j=B_j(3H_a-H_{n+a}-2H_{n-a})$. ∎ (Verified $n\le8$.)

**Corollary 4.2.** $n!\,B_j\in\mathbb Z$ and $n!\,d_{2n}\,A_j\in\mathbb Z$.
*Proof.* $n!B_j=\pm\binom{n+a}{a}\binom{n}{a}^2\in\mathbb Z$. Each of $H_a,H_{n+a},H_{n-a}$ has denominator dividing $d_{2n}$ (indices $\le2n$), so $d_{2n}(3H_a-H_{n+a}-2H_{n-a})\in\mathbb Z$; multiply by $n!B_j$. ∎ (Verified $n\le8$.)

**Remark (the crux, stated honestly).** Cor 4.2 carries a *factorial* $n!$, not $d_n$. The passage from $n!$ to $d_n^5$ is **not** visible term-by-term (e.g. $\operatorname{lcm}_j\operatorname{den}(A_j)$ already contains $5^2$ at $n=5$ while $d_5=60$ has only $5^1$). It can only arise after the residues are summed, from *harmonic-sum cancellation*. This is the "collapse" (§7–8); it is genuinely open here.

---

## 5. The classical integrality lemmas (PROVED)

These are the tools the whole program cites as "classical" (BZ's `incl`; Zudilin arXiv:1801.09895 Lemmas 1–3; Rhin–Viola). We state and prove the two we use.

**Lemma 5.1 (Zudilin, partial-fraction integrality).** Let $k_1,\dots,k_q$ be distinct integers in $\{0,1,\dots,N\}$ and $s_1,\dots,s_q\ge1$, $s=\sum s_j$. Write $\dfrac1{\prod_{j}(t+k_j)^{s_j}}=\sum_{j}\sum_{i=1}^{s_j}\dfrac{b_{i,j}}{(t+k_j)^i}$. Then $d_N^{\,s-i}\,b_{i,j}\in\mathbb Z$ for all $i,j$.

*Proof.* By symmetry take $j=1$. For $m\ge0$,
$$\frac1{m!}\Big(\prod_{j\ge2}(t+k_j)^{-s_j}\Big)^{(m)}
=\!\!\sum_{\substack{\ell_2,\dots,\ell_q\ge0\\ \sum\ell_j=m}}\prod_{j\ge2}(-1)^{\ell_j}\binom{s_j+\ell_j-1}{\ell_j}(t+k_j)^{-(s_j+\ell_j)},$$
so $b_{i,1}=\big[\tfrac1{(s_1-i)!}\big(\tfrac{S(t)(t+k_1)^{s_1}}{}\big)^{(s_1-i)}\big]_{t=-k_1}=\sum_{\sum\ell_j=s_1-i}\prod_{j\ge2}(-1)^{\ell_j}\binom{s_j+\ell_j-1}{\ell_j}(k_j-k_1)^{-(s_j+\ell_j)}$. Each summand has $\sum_{j\ge2}(s_j+\ell_j)=s-i$ factors $(k_j-k_1)^{-1}$ with $|k_j-k_1|\le N$; since $d_N/(k_j-k_1)\in\mathbb Z$, multiplying by $d_N^{s-i}$ clears all denominators. ∎ (Sample checks: `proof_sym_v2_closedforms.py` (C).)

**Lemma 5.2 (harmonic clearing).** $d_n^{\,i}\sum_{\ell=1}^k\ell^{-i}\in\mathbb Z$ for $i\ge1$ and $0\le k\le n$. Likewise $d_n^{\,i}\sum_{\ell=0}^{k}(\ell+\tfrac12)^{-i}$ and $d_{n-1}^{\,i}\sum_{\ell=1}^{k}(\ell-\tfrac12)^{-i}$ are integral in the ranges of Zudilin Lemma 3.
*Proof.* $\ell\le n\Rightarrow \ell^i\mid d_n^i$; sum. The half-integer versions are Zudilin's (via $2\ell\pm1\le 2n$). ∎ (Verified $n\le8$, `proof_sym_v2_closedforms.py` (D).)

Lemma 5.1 is exactly what yields BZ's `incl`-type bounds for the coefficients $a_{i,k}$ of a well-poised $R(t)$, and Lemma 5.2 converts the finite-tail corrections into $\mathbb Z$; combined (Zudilin Lemma 3) they give $d_N^{\,s-i}a_i\in\mathbb Z$, $d_N^{\,s}a_0\in\mathbb Z$ for a **single-variable** weight-$s$ form. The BZ ζ(5) side is a **two-variable** analogue; see §7.

---

## 6. The ζ(3) companion $\hat P_n$ (PROVED modulo the now-proved Lemma 5.1)

BZ's descent (`I3`) specializes to
$$\hat P_n=\tfrac12(-1)^n\sum_{k=n}^{2n}(-1)^k\binom{k}{n}\binom{n}{k-n}^2\,B^{(3)}_k,\tag{P̂}$$
where $B^{(3)}_k$ is the **rational part of the Beukers-type $\zeta(3)$ integral** $J_3(n,n,n,2n{-}k;\,n,n,k)$ (note: $B^{(3)}_k\ne B_k$ of §4 — see E5), which under its balancing condition $(2n{-}k)+k=2n=n+n$ satisfies $J_3=2A^{(3)}_k\zeta(3)-B^{(3)}_k$ with $A^{(3)}_k\in\mathbb Z$.

*Numerical confirmation.* The descent sum $\sum_k(-1)^{3n}(-1)^k\binom{k}{n}\binom{n}{k-n}^2 J_3=2I_n''=2(Q_n\zeta(3)-\hat P_n)$. At $n=1$: sum $=-0.013610\ldots=2(21\zeta(3)-\tfrac{101}4)$ to $16$ digits (`proof_sym_v2_descent.py`). The **factor $\tfrac12$** in (P̂) is the $2$ in $J_3=2A^{(3)}\zeta(3)-B^{(3)}$; it is the source of the corrected multiplier $2$ in $2d_n^2d_{2n}\hat P_n\in\mathbb Z$ (versus the paper's false $d_n^2d_{2n}\hat P_n$), not a period-elimination cost. This matches the data at every $n\le8$.

**Theorem 6.1 (crude, unconditional given Lemma 5.1).** $2\,d_{2n}^3\,\hat P_n\in\mathbb Z$.
*Proof.* $J_3(n,n,n,2n{-}k;n,n,k)$ is a Rhin–Viola/Beukers $\zeta(3)$ integral with all parameters $\le2n$; by Lemma 5.1 (weight $3$, max index $2n$) its rational part satisfies $d_{2n}^3B^{(3)}_k\in\mathbb Z$. The binomials in (P̂) are integral, so $2d_{2n}^3\hat P_n\in\mathbb Z$. ∎

The **sharp** companion $2d_n^2d_{2n}\hat P_n\in\mathbb Z$ replaces $d_{2n}^3$ by the block-refined denominator $d_{n}d_{n}d_{2n}$ of the three RV blocks $\{n,n,2n\}$. That block estimate is standard but is **not re-derived here** (open, as in v1). **Verified $n\le8$**, 2-part attained (`proof_sym_v2_laws.py`, C1).

---

## 7. The priority-1 target: what is genuinely proved, and the real gap

### 7.1 The kernel integrals (BZ's building blocks)

Per BZ Remark `rem-decom`, decomposing the rational part of $\Phi$ and shifting contours casts $I_n$ as a $\mathbb Q$-linear combination of
$$I^{(s_1,s_2)}_{k_1,k_2}=\frac1{(2\pi i)^2}\!\iint_{\frac13\pm i\infty}\frac{1}{(t_1{+}k_1)^{s_1}(t_2{+}k_2)^{s_2}}\,\frac{\pi}{\sin\pi t_1}\frac{\pi}{\sin\pi t_2}\frac{\pi}{\sin\pi(t_1{+}t_2)}\,dt_1dt_2,\quad k_i\ge0,\ s_i\in\{1,2\},$$
and BZ give these **explicitly** as $I^{(s_1,s_2)}_{k_1,k_2}=\frac1{\Gamma(s_1)\Gamma(s_2)}\iint_{[0,1]^2}u^{k_1}v^{k_2}f(u,v)(\log u)^{s_1-1}(\log v)^{s_2-1}\frac{du}{u}\frac{dv}{v}$ with
$$f(u,v)=\begin{cases}\dfrac{uv\log u}{(1-u)(1-v)}-\dfrac{u\log(u/v)}{(1-u/v)(1-v)}&0<u<v<1,\\[4pt]\dfrac{uv\log v}{(1-u)(1-v)}-\dfrac{v\log(v/u)}{(1-u)(1-v/u)}&0<v<u<1.\end{cases}$$
So each $I^{(s_1,s_2)}_{k_1,k_2}$ is an **explicit** $\mathbb Q$-combination of weight-$\le5$ multiple zeta values; its **weight-0 (rational) part** is a computable rational number. The weight-0 part of $I_n$ is $-2P_n$.

### 7.2 What this gives, precisely

For each fixed $n$, $P_n$ is a **finite** $\mathbb Q$-linear combination
$$-2P_n=\text{weight-0 part of }\Big(n!\sum_{\text{lattice pairs}} c^{(s_1,s_2)}_{k_1,k_2}\,I^{(s_1,s_2)}_{k_1,k_2}\Big),\tag{7.1}$$
where the coefficients $c^{(s_1,s_2)}_{k_1,k_2}$ are $\mathbb Z$-combinations of the Laurent data of $r(s)r(t)C(s,t)$ (i.e. of $A_j,B_j$ and the Taylor coefficients of $C$) produced by the partial-fraction/contour-shift step. **This is a precise, per-$n$ checkable object** — and computing it and factoring $\operatorname{den}(P_n)$ is exactly what `audit.recover_p` does, giving the verified table of §8.

**The honest status of (7.1): the reduction *coefficients* $c^{(s_1,s_2)}_{k_1,k_2}$ are not available in closed form for general $n$.** The obstruction is the coupling factor $C(s,t)/\sin\pi(s+t)$: $C$ is a degree-$n$ polynomial in $s+t$, so reducing it to the kernel shape (which has *no* polynomial in the coupling) requires the family of contour shifts BZ describe but "skip the details" of. Without those coefficients in closed form, one cannot exhibit the general-$n$ residue sum — which is precisely why v1's §7 "Residual Integrality Statement (a)" was undefined (E2).

### 7.3 Why $d_n^5$ is the expected constant (heuristic, not a proof)

The mechanism the task points to (Rhin–Viola/Zudilin derivative counting) predicts $d_n^5$ as follows. The weight-0 part comes from the triple-$s$/triple-$t$ lattice pairs where the local pole order totals $5$ (order $2$ in $\varepsilon=s+a$, order $2$ in $\delta=t+b$, order $1$ in $\varepsilon+\delta$). Extracting the constant term requires Laurent coefficients of $r(s)r(t)C(s,t)$ up to total order $4$ in $(\varepsilon,\delta)$, i.e. up to $4$ "derivative" operations, plus the leading residue — and by the Rhin–Viola fact "$d_n^{\,m}\times(m\text{-th derivative of a product of linear factors with integer roots, evaluated at an integer})\in\mathbb Z$" together with Lemma 5.2, each derivative order contributes one factor of $d_n$, summing to $d_n^5$ across the weight-5 structure. This is the two-variable analogue of Zudilin Lemma 3 ($d_N^s a_0\in\mathbb Z$ at weight $s$).

**Why this is not yet a proof.** Zudilin Lemma 3 is genuinely single-variable (one $R(t)$, one contour, Lemma 5.1 applies directly). Here the derivative data is coupled through $C(s,t)$ and the shared kernel $1/\sin\pi(s+t)$; the cancellations that collapse $n!\cdot(\text{harmonic data})$ to $d_n^5$ mix the $s$- and $t$-expansions, and no term-by-term application of Lemma 5.1 delivers it (indeed term-by-term the data carries $n!$ and stray prime squares, §4 Remark). Establishing the collapse needs the reduction coefficients of §7.2, which are open.

### 7.4 Statement of the target

**Target 7.1 (VERIFIED $n\le8$; OPEN in general).** $12\,d_n^5P_n\in\mathbb Z$, and $\operatorname{ord}_2\operatorname{den}(P_n)=2+5\operatorname{ord}_2 d_n$.
The **Support Theorem** (v1 6.1) — $\operatorname{den}(P_n)$ supported on $\{p\le2n+1\}$, with $\operatorname{ord}_p\le5\operatorname{ord}_p d_n$ for $p\ge5$ — is **conditional on the same collapse** (E1), not unconditional. All verified for $n=1,\dots,8$ in §8.

---

## 8. Exact data (verification anchors, extended to $n\le8$)

Computed by `audit.recover_p([1]*8,n)` (PSLQ over $\{1,\zeta(2)\}$; anchors reproduce the paper's $P_1=\tfrac{87}4,P_2=\tfrac{1190161}{384},\hat P_1=\tfrac{101}4,\hat P_2=\tfrac{344923}{96}$). New rows $n=6,7,8$ are this document's contribution.

| $n$ | $d_n$ | $d_{2n}$ | $\operatorname{den}(P_n)$ | $\operatorname{den}(\hat P_n)$ |
|---|---|---|---|---|
| 1 | 1 | 2 | $2^2$ | $2^2$ |
| 2 | 2 | 12 | $2^7\!\cdot3$ | $2^5\!\cdot3$ |
| 3 | 6 | 60 | $2^7\!\cdot3^4$ | $2^5\!\cdot3^3\!\cdot5$ |
| 4 | 12 | 840 | $2^{12}\!\cdot3^3$ | $2^8\!\cdot3^2$ |
| 5 | 60 | 2520 | $2^{12}\!\cdot3^4\!\cdot5^5$ | $2^8\!\cdot3^3\!\cdot5^3\!\cdot7$ |
| 6 | 60 | 27720 | $2^{12}\!\cdot3^6\!\cdot5^5$ | $2^8\!\cdot3^4\!\cdot5^3\!\cdot11$ |
| 7 | 420 | 360360 | $2^{12}\!\cdot3^4\!\cdot5^5\!\cdot7^5$ | $2^8\!\cdot3^2\!\cdot5^3\!\cdot7^3\!\cdot11\!\cdot13$ |
| 8 | 840 | 720720 | $2^{17}\!\cdot3^6\!\cdot5^5\!\cdot7^4$ | $2^{11}\!\cdot3^4\!\cdot5^3\!\cdot7^2\!\cdot11\!\cdot13$ |

`proof_sym_v2_laws.py` checks, for all $n\le8$ (**all PASS**):
- **(L1)** $\operatorname{ord}_2\operatorname{den}(P_n)=2+5\operatorname{ord}_2 d_n$ — equality (2-adic law), including the new $n=8$ cell $\operatorname{ord}_2=17=2+5\cdot3$;
- **(L2)** $12d_n^5P_n\in\mathbb Z$ (per-prime $\operatorname{ord}_p\le5\operatorname{ord}_pd_n+[p{=}2]2+[p{=}3]1$);
- **(L3)** $p\ge5$: $\operatorname{ord}_p\le5\operatorname{ord}_pd_n$ — **inequality** (E3: equality fails at $(8,7)$, $7^4$ vs $7^5$);
- **(L4)** support $\subseteq\{p\le2n+1\}$;
- **(C1)** $2d_n^2d_{2n}\hat P_n\in\mathbb Z$, 2-part attained.

Notable new evidence: at $n=7$, $\operatorname{ord}_7\operatorname{den}(P_7)=5=5\operatorname{ord}_7 d_7$ (a $p\ge5$ prime hitting the $d_n^5$ ceiling with **no excess**, i.e. the "no $p\ge5$ excess" claim survives a genuine test at $p=7$); at $n=8$, the same prime slacks to $7^4$ (E3).

---

## 9. The 2-adic attainment question (OPEN)

**Question (from the task).** Is $\operatorname{ord}_2\operatorname{den}(P_n)=2+5\operatorname{ord}_2 d_n$ (equivalently the 2-part $=4\cdot2^{\operatorname{ord}_2 d_n^5}$) provable by exhibiting a non-vanishing 2-adic term?

**Answer: OPEN.** Attainment is a *lower* bound on the denominator; it requires exhibiting a specific term of the residue sum (7.1) with $\operatorname{ord}_2=-(2+5\operatorname{ord}_2 d_n)$ that is not cancelled. That needs the explicit reduction coefficients of §7.2, which are unavailable in general. What *can* be said: (i) the equality holds for all $n\le8$; (ii) the upper bound $\operatorname{ord}_2\le2+5\operatorname{ord}_2 d_n$ is the $p=2$ instance of Target 7.1 (same collapse); (iii) the heuristic of E4 — a single $\zeta(2)=\pi^2/6$ coefficient entering "doubled," contributing $2^2$ after the $-2P_n$ normalization on top of $d_n^5$ — *predicts* the constant $+2$, but is not derived. No non-vanishing argument is available here.

---

## 10. Proven / verified-only / open

**Proven (complete, here):** $(\star)$ specialization (§2); Prop 3.1 sine-kernel reduction incl. all reflections (§3); Lemma 4.1 and Cor 4.2 (§4); Zudilin Lemma 5.1 and harmonic-clearing Lemma 5.2 (§5); Theorem 6.1 crude $2d_{2n}^3\hat P_n\in\mathbb Z$ (§6, using the now-proved 5.1); the identification of the reduction *framework* and kernel integrals (§7.1).

**Verified-only (exact machine check, no general proof):** $12d_n^5P_n\in\mathbb Z$ for $n\le8$; the 2-adic equality $\operatorname{ord}_2=2+5\operatorname{ord}_2 d_n$ for $n\le8$; $p\ge5$ no-excess for $n\le8$; support $\le2n+1$ for $n\le8$; $2d_n^2d_{2n}\hat P_n\in\mathbb Z$ (sharp companion) for $n\le8$; the descent (P̂) and its factor $\tfrac12$ for $n\le2$.

**Open:** the $d_n^5$-collapse (7.2/7.3) — general-$n$ reduction coefficients $c^{(s_1,s_2)}_{k_1,k_2}$ and the two-variable harmonic-sum cancellation — hence Target 7.1 and the Support Theorem in general; the 2-adic attainment (§9); the block-refined RV estimate for the sharp $\hat P$ companion (§6); a rigorous account of contour-closing/absolute convergence of the double residue sum.

**Net change from v1.** Two overclaims corrected to their true (conditional/inequality) status (E1, E3); one non-reduction exposed (E2); one heuristic re-flagged (E4). Reduction §2–§3 upgraded from "numeric" to fully proved. Classical inputs (Lemma 5.1, 5.2) supplied with proofs. Verification extended $n\le5\to n\le8$, adding the first $p\ge5$ ceiling test ($p=7$, $n=7$) and the first slack at a $p\ge5$ prime ($n=8$). The priority-1 theorem's true status — **verified, not proved; the collapse is the sole obstruction and its general-$n$ residue sum is genuinely undefined without BZ's skipped contour-shift bookkeeping** — is now stated without circularity.

---

## 11. Reproduction

- `proof_sym_v2_reduction.py` — §2 prefactor; §3 reflection identity (symbolic); Prop 3.1 rational identity (exact, $n\le8$) and full integrand (40 digits, $n\le4$).
- `proof_sym_v2_closedforms.py` — Lemma 4.1 + Cor 4.2 (exact, $n\le8$); Zudilin Lemma 5.1 (samples); harmonic clearing 5.2 ($n\le8$).
- `proof_sym_v2_descent.py` — (P̂) descent numeric check ($n=1$: sum $=2I''_1$).
- `proof_sym_v2_laws.py` — laws (L1)–(L4),(C1) for $n\le8$ from the exact denominator table.
- Exact $P_n,\hat P_n,Q_n$: `from audit import recover_p; recover_p([1]*8,n)` (`n` up to $\sim8$).

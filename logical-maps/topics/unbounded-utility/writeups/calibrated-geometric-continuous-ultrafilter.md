# Clipped expectation: continuous ultrafilter dominance [−7·4ⁿ/4, 2·4ⁿ]

**Source:** AI-generated results communicated by **Branden Fitelson**,
*Unbounded Utility: Five Top-Ranked Open Conjectures Resolved*, 30 September
2026, §§1 and 4(b). The report names Claude agents but gives no model version.
The specialization and shuffle-copula argument are attributed to those agents;
the underlying continuous clipping method is Goodsell's. GPT-6 (Codex)
expanded and informally checked the proofs on 2 October 2026. No independent
human check or Lean verification is claimed.

## Construction and positive properties

Use all real-valued gambles with identity utility, a free ultrafilter
$\mathcal U$ on the positive integers, and

$$a_n=\tfrac74\,4^n,\quad b_n=2\cdot4^n,\quad
v_X(n)=E[\max(-a_n,\min(X,b_n))].$$

Put $X\succeq Y$ iff for every $\epsilon>0$ the set
$\{n:v_X(n)-v_Y(n)\ge-\epsilon\}$ belongs to $\mathcal U$.
The [common clipping proof](calibrated-geometric-continuous-ultrafilter.html#shared-clipping-and-shuffle-copula-proof) establishes
DTU, CDF-Area Extension, Relative Expectation, Expected Utility, L¹ Continuity,
Shift Invariance, and the fixed-copula invariance $\operatorname{SC}(C_\sigma)$
for the quarter-shuffle copula below, with the copula chosen once rather than
per triple. Uninteractive Sum Invariance follows from Relative Expectation by
the recorded result `relative-independence-equivalence-imply-uninteractive-sum`.

## Exact alternating-game evaluation

Let $\Pr(A=(-2)^j)=2^{-j}$ for $j\ge1$. For each $n\ge1$, the first $2n$
atoms contribute $-n+n=0$. The remaining negative and positive probabilities
are respectively $(2/3)4^{-n}$ and $(1/3)4^{-n}$. They lie beyond the two
cutoffs. Therefore

$$v_A(n)=-\tfrac74\,4^n\tfrac23\,4^{-n}
             +2\cdot4^n\tfrac13\,4^{-n}=-\tfrac12.$$

The same first $2n$ atoms of $2A$ contribute zero, now with the largest
positive atom at $b_n$. The remaining atoms are beyond the cutoffs, with
the same probabilities. Thus $v_{2A}(n)=-1/2$ too. Constants eventually
escape clipping, so

$$A\sim-\tfrac12,\qquad 2A\sim-\tfrac12\succ-1.$$

The first equality verifies the alternating-game principle for every gamble
of that law. Integer Affine Preservation fails: the true comparison
$-1/2\succeq A$ would require $-1\succeq2A$ after doubling. Consequently
this model need not have positive affine or scale invariance.

## Failure of folded expectation and reflection

For a standard symmetric Cauchy variable $C$, put

$$m(r)=E[\min(C_+,r)]
=\frac{r\arctan(1/r)+\tfrac12\log(1+r^2)}{\pi}.$$

Then $v_C(n)=m(b_n)-m(a_n)$ and
$m(r)=(\log r+1)/\pi+o(1)$. Hence

$$v_C(n)\longrightarrow \kappa=\frac{\log(8/7)}{\pi}>0.$$

Thus $C\sim\kappa\succ0$. Its symmetric folded-tail function is zero, so
Folded Expectation and Symmetric Neutrality would instead require $C\sim0$.
Also $-C$ has the same law as $C$, so Reflection Anti-Invariance would turn
$C\succeq0$ into $0\succeq-C$, which is false. Negative Affine Anti-Invariance
fails at its reflection instance as well.

This single model proves both the report's first non-implication and the
fourth consistency claim, including Totality. Its latter proof uses the
shuffle copula, not the separate steered-conclosure proposal in §4(a).

`checks/fitelson_report.py` checks the exact atom sums and the Cauchy limit.
Those diagnostics do not replace the quantified arguments or the ultrafilter
existence assumption.


<a id="shared-clipping-and-shuffle-copula-proof"></a>

## Shared clipping and shuffle-copula proof

The shuffle-copula argument is from *Unbounded Utility: Five Top-Ranked Open
Conjectures Resolved*, 30 September 2026, §4(b), communicated by **Branden
Fitelson**. The report attributes its results to Claude agents without specifying
their model versions. Fitelson is credited as communicator, not as the producer
of the AI proofs. GPT-6 (Codex) expanded and informally checked the proof below
on 2 October 2026. The report's separate referee files were not supplied; their
reported verdicts are not treated as independently inspected certificates.

The underlying clipped-expectation construction is Goodsell's; see *Decision
theory unbound*, Appendix B, Definition 3, Lemma 6 and Remark 3. The shuffle
copula is an additional property, separately attributed to the communicated
report. No Lean verification is claimed.

### Clipped comparison rules

Use all real-valued gambles, real outcomes and identity utility. Let

$$q_i(x)=\max(-a_i,\min(x,b_i)),\qquad v_X(i)=E[q_i(X)],$$

where both positive cutoffs tend to infinity. Each $v_X(i)$ is a finite real
number even when $X$ has no expectation. We use either of these rules:

1. For a free ultrafilter on integer indices, or an ultrafilter on positive
   real indices containing every tail,
   $$X\succeq Y\iff\forall\epsilon>0\quad
     \{i:v_X(i)-v_Y(i)\ge-\epsilon\}\in\mathcal U.$$
2. For real $t\to\infty$,
   $$X\succeq Y\iff\liminf_{t\to\infty}(v_X(t)-v_Y(t))\ge0.$$
   Equivalently, each positive tolerance is respected on some entire tail.

Both rules ignore an error tending to zero. A comparison difference with a
finite limit is ordered by that limit, with indifference at zero. Limits
$+\infty$ and $-\infty$ give the corresponding strict preference.

The positive comparisons are closed under addition and positive scaling:
use tolerance $\epsilon/2$ in two summands and intersect the relevant sets or
tails. This proves reflexivity and transitivity. Equal laws give identical
comparison functions. Randomized mixtures satisfy

$$v_{M_p(X,Z)}-v_{M_p(Y,Z)}=p(v_X-v_Y),$$

so both directions of Mixture Independence hold. Simple gambles eventually
escape clipping, and their comparisons are their ordinary expectations.
Thus the normalized chart is the identity, Rich Outcomes and Archimedean
Outcomes hold, and Simple Expected Utility holds.

The identity

$$v_X(i)-v_Y(i)=\int_{-a_i}^{b_i}(S_X-S_Y)(s)\,ds \tag{1}$$

shows weak Stochastic Dominance. Strict dominance at a threshold persists
over an interval by right continuity, giving a fixed positive lower bound
on every sufficiently late clipped difference. This proves strict dominance
as well. Hence both rules satisfy DU. The ultrafilter rule is also total:
failure of $X\succeq Y$ supplies a positive $\epsilon$ and an ultrafilter-large
set where $v_Y-v_X>\epsilon$, proving $Y\succ X$.

### Area, relative expectation, continuity and shifts

If at least one of $\int(S_X-S_Y)_+$ and $\int(S_X-S_Y)_-$ is finite,
(1) converges to their well-defined extended difference. This follows from
dominated convergence for a finite part and Fatou's lemma for an infinite
part; nested windows also permit monotone convergence. The sign criterion
proves CDF-Area Extension. No difference of two infinite integrals is used.

If $E|X-Y|<\infty$, then

$$q_i(X)-q_i(Y)\longrightarrow X-Y,\qquad
 |q_i(X)-q_i(Y)|\le |X-Y|.$$

Dominated convergence proves Relative Expectation and, in particular,
Expected Utility on integrable gambles. The uniform bound

$$|v_{X_n}(i)-v_X(i)|\le E|X_n-X|$$

proves L¹ Continuity: for a specified tolerance choose one sufficiently
close $X_n$, then use its comparison with $Y$ at half that tolerance.

For a fixed real $b$, the difference $q_i(X+b)-q_i(X)$ tends pointwise to
$b$ and is bounded by $|b|$. Consequently
$v_{X+b}-v_X\to b$. Applying this to each of two compared gambles proves
Shift Invariance. These statements hold without integrability of the
individual gambles.

### A single copula that works for all marginals

Let $\sigma$ exchange adjacent quarters of the unit interval:

$$\sigma(u)=
\begin{cases}
u+1/4,&0\le u<1/4,\\
u-1/4,&1/4\le u<1/2,\\
u+1/4,&1/2\le u<3/4,\\
u-1/4,&3/4\le u<1.
\end{cases}$$

The distribution $C_\sigma$ of $(U,\sigma(U))$ is a copula, since $\sigma$
preserves Lebesgue measure. It is fixed independently of all gamble laws.
It is nonindependent: $H_{C_\sigma}(1/4,1/4)=0$, whereas the product
copula gives $1/16$. The map recorded the conclusion of this section as
Existential Copula Sum Invariance and, from 3 October 2026, also as
Existential Nonindependent Copula Sum Invariance. Both principles were
removed on 11 October 2026 and replaced by Uninteractive Sum Invariance,
which follows from Relative Expectation
(`relative-independence-equivalence-imply-uninteractive-sum`) and implies
$\operatorname{SC}(C)$ for every corner-avoiding copula, $C_\sigma$ included.
This section is retained as the original direct verification, with its
attribution.
For any two real probability laws take

$$A=Q_A(U),\qquad B=Q_B(\sigma(U)).$$

On the first and last quarters, $Q_B(\sigma(U))$ ranges over an interior
quarter and is bounded. On the middle two quarters, $Q_A(U)$ is bounded.
Interior quantiles of any real probability law are finite. Thus on each
quarter at least one summand has a fixed finite absolute bound.

Clipping is 1-Lipschitz and fixes zero, so for all real $x,z$,

$$|q_i(x+z)-q_i(x)-q_i(z)|\le2\min(|x|,|z|).$$

The left side tends pointwise to zero. The bounded-summand observation gives
an integrable constant bound on each of the four pieces. Dominated convergence
therefore proves

$$v_{A+B}(i)-v_A(i)-v_B(i)\longrightarrow0. \tag{2}$$

This is valid even for asymmetric windows and nonintegrable marginals.
If a pair admits $C_\sigma$ in the graph's compatibility definition, its
joint CDF equals that of the displayed quantile pair. It has the same joint
law, hence the same sum law. This observation also covers atomic marginals
and does not presume a uniquely assigned copula.

For every eligible triple $(X,Y,Z)$ whose two pairs admit this fixed copula,
apply (2) to the two pairs separately and subtract:

$$v_{X+Z}-v_{Y+Z}=v_X-v_Y+o(1).$$

Both comparison rules ignore that error, in both directions. Thus
$\operatorname{SC}(C_\sigma)$ holds. There is no additional requirement on
the triple's joint law.
Strict comparisons are preserved because the equivalence holds in both
ordered directions.

This proof also adds the copula property to the map's existing continuous
ultrafilter models with windows $[-t,t]$, $[-t,2t]$, $[-4^n,4^n]$, and
$[-4^n,4^{2n}]$. It makes no assertion about the exact, zero-tolerance
ultrafilter or eventual-comparison rules.

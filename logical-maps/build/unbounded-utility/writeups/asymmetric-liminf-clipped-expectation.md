# Clipped expectation: liminf dominance [−t, 2t]

**Source:** AI-generated results communicated by **Branden Fitelson**,
*Unbounded Utility: Five Top-Ranked Open Conjectures Resolved*, 30 September
2026, §§3 and 4(b). The report identifies Claude agents, with model versions
unspecified. The clipping method is Goodsell's; the liminf specialization
and its witnesses are attributed to the report. GPT-6 (Codex) expanded and
informally checked the proofs on 2 October 2026. No Lean verification is claimed.

## Construction and affine invariance

On all real-valued gambles with identity utility define

$$v_X(t)=E[\max(-t,\min(X,2t))],\qquad
X\succeq Y\iff\liminf_{t\to\infty}(v_X(t)-v_Y(t))\ge0.$$

The parameter ranges over **all positive real numbers**. The
[common proof](calibrated-geometric-continuous-ultrafilter.html#shared-clipping-and-shuffle-copula-proof) establishes DU,
CDF-Area Extension, Relative Expectation, Expected Utility, L¹ Continuity,
Shift Invariance, and the fixed shuffle-copula invariance; Uninteractive Sum
Invariance follows from Relative Expectation
(`relative-independence-equivalence-imply-uninteractive-sum`).

For $a>0$, clipping gives the exact identity

$$v_{aX}(t)-v_{aY}(t)=a\bigl(v_X(t/a)-v_Y(t/a)\bigr).$$

Reparametrizing all real $t$ preserves the liminf sign in both directions.
Together with Shift Invariance this proves full Positive Affine Invariance,
including preservation of strict order, and hence Integer Affine Preservation.
This reparametrization argument is not an assertion that an arbitrary
ultrafilter is invariant under dilation.

## Symmetric St Petersburg has value 1/2

Let $\Pr(S=2^j)=\Pr(S=-2^j)=2^{-j-1}$, $j\ge1$, and put
$m(r)=E[\min(S_+,r)]$. Symmetry gives $v_S(t)=m(2t)-m(t)$.
If $2^k\le t\le2^{k+1}$, $k\ge0$, then

$$m(2t)-m(t)
=(2^{k+1}-t)2^{-k-1}+(2t-2^{k+1})2^{-k-2}=\tfrac12.$$

Thus $S\sim1/2\sim-S$, whereas $-S\succ-1/2$. Reflecting the true comparison
$S\succeq1/2$ would require $-1/2\succeq-S$, which fails. This refutes
Reflection and Negative Affine Anti-Invariance despite full Positive Affine
Invariance. Since $S$ is symmetric, it also refutes Symmetric Neutrality and
Folded Expectation.

## Incompleteness and the alternating game

For incompleteness let $\Pr(R=4^j)=\Pr(R=-4^j)=\tfrac32\,4^{-j}$, $j\ge1$.
These probabilities sum to one. The positive tail is $\tfrac12\,4^{-k}$
on $[4^k,4^{k+1})$. Therefore

$$v_R(4^k)=\tfrac12,\qquad v_R(2\cdot4^k)=1\quad(k\ge1).$$

Against the constant $3/4$ these two unbounded sequences give gaps of
$-1/4$ and $1/4$. Neither ordered comparison holds, proving failure of Totality.

For alternating St Petersburg $A$, pair each negative atom $-2\cdot4^j$
with the positive atom $4\cdot4^j$, for $j\ge0$. The latter has half the
probability, and its positive clipped value is twice the absolute negative
clipped value. Every pair cancels. Boundedness of clipping licenses this
grouping, so $v_A(t)=0$ for every $t>0$. Hence $A\sim0\succ-1/2$, refuting
the alternating evaluation principle in this particular model.

The incompleteness witness and exact atom identities are checked in
`checks/fitelson_report.py`. The model establishes the report's third
non-implication without claiming its Totality strengthening.

## Paper references

- **Origin: Unbounded Utility: Five Top-Ranked Open Conjectures Resolved.** AI-generated report, 30 September 2026, 4 pages; communicated by Branden Fitelson. The report attributes production to Claude agents without specifying model versions. Fitelson is the communicator, not the credited producer of the proofs. — §§3 and 4(b), pp. 2–3
- **Background: [Decision theory unbound](https://doi.org/10.1111/nous.12473).** ([PDF](../sources/Nous%20-%202023%20-%20Goodsell%20-%20Decision%20theory%20unbound%20%281%29.pdf)) Zachary Goodsell (2024). Decision theory unbound. Noûs, 58, 669–695. First published online in 2023. — Appendix B, Definition 3, Lemma 6 and Remark 3

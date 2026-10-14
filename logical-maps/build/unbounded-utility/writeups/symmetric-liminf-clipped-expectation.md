# Clipped expectation: liminf dominance [−t, t]

**Source:** AI-generated results communicated by **Branden Fitelson**,
*Unbounded Utility: Five Top-Ranked Open Conjectures Resolved*, 30 September
2026, §§4(b) and 5(b). The report names Claude agents but gives no model version.
The clipping construction is Goodsell's. The Lévy obstruction was already
recorded in the map from Goodsell's proposal and GPT-6's proof completion;
the report supplies its quantitative realization in this liminf model.
GPT-6 (Codex) expanded and informally checked the present proofs on
2 October 2026. No Lean verification is claimed.

## Construction and positive properties

For all real-valued gambles with identity utility put

$$v_X(t)=E[\max(-t,\min(X,t))],\qquad
X\succeq Y\iff\liminf_{t\to\infty}(v_X(t)-v_Y(t))\ge0.$$

The [common clipping proof](calibrated-geometric-continuous-ultrafilter.html#shared-clipping-and-shuffle-copula-proof) gives DU,
CDF-Area Extension, Relative Expectation, Expected Utility, L¹ Continuity,
Shift Invariance and the fixed shuffle-copula invariance; Uninteractive Sum
Invariance follows from Relative Expectation
(`relative-independence-equivalence-imply-uninteractive-sum`). Scaling reparametrizes
all positive real cutoffs by $t\mapsto t/a$, with a positive multiplier $a$,
so Positive Affine Invariance holds. Oddness of symmetric clipping gives
$v_{-Y}-v_{-X}=v_X-v_Y$, proving Reflection Anti-Invariance.

For the folded-tail function $h_X$, $v_X(t)=\int_0^t h_X(s)\,ds$.
If $h_X,h_Y$ are absolutely integrable, the clipped comparison tends to
$F(X)-F(Y)$, proving Folded Expectation. In particular all symmetric laws
are indifferent to zero in this model.

## Independent Sum Preservation fails

Let $L_1,L_2$ be independent positive Lévy variables with density

$$f(x)=\frac{e^{-1/(4x)}}{2\sqrt\pi\,x^{3/2}},\qquad x>0,$$

and let $\epsilon$ be an independent fair sign. Write $W=\epsilon L_1$ and
$D=L_2-L_1$. Both $W$ and $D$ are symmetric, so all their symmetric clipped
expectations vanish. The Laplace transform $e^{-\sqrt s}$ implies
$L_1+L_2\overset d=4L$. Hence $W+L_2$ is the equal mixture of $4L$ and $D$.
These are the same law identities used in the
[existing Lévy obstruction](levy-refutes-neutral-independent-preservation.html).

The positive Lévy survival is $\operatorname{erf}(1/(2\sqrt x))$. Let

$$G(T)=E[\min(L,T)]
=T\operatorname{erf}\!\left(\frac1{2\sqrt T}\right)
 +\sqrt{\frac T\pi}e^{-1/(4T)}
 -\frac12\operatorname{erfc}\!\left(\frac1{2\sqrt T}\right).$$

Integration of the survival function, or differentiation and the limit at
zero, verifies this formula. Taylor expansion at $1/\sqrt T=0$ gives

$$G(T)=2\sqrt{T/\pi}-\tfrac12+O(T^{-1/2}).$$

Consequently

$$v_{W+L_2}(T)-v_{L_2}(T)=2G(T/4)-G(T)\longrightarrow-\tfrac12.$$

Thus $W\sim0$ but $L_2\succ W+L_2$, although $L_2$ is independent of the
pair $(W,0)$. Even weak Independent Sum Preservation fails, and therefore
so does Independent Sum Invariance. This is a second model for the report's
fifth non-implication, complementing the CDF-area cancellation failure.

## Comonotonic sums and Totality also fail

Take a standard Cauchy $C=Q_C(U)$ and $Z=C_+$. Both $(C,Z)$ and $(0,Z)$
are comonotonic. We have $C\sim0$. If $m(r)=E[\min(C_+,r)]$, then

$$v_Z(t)-v_{C+Z}(t)=2m(t)-2m(t/2)\longrightarrow\frac{2\log2}{\pi}>0.$$

Thus $Z\succ C+Z$, refuting Comonotonic Sum Invariance. This is the same
Cauchy witness already used for the map's continuous ultrafilter models;
the limiting gap verifies it for the liminf rule too.

For alternating St Petersburg $A$, finite-prefix summation and its geometric
tails give

$$v_A(4^n)=-\tfrac13,\qquad
  v_A(2\cdot4^n)=-\tfrac23\quad(n\ge1).$$

The comparison with $-1/2$ has gaps $1/6$ and $-1/6$ along these two
unbounded sequences. The pair is incomparable. This proves failure of
Totality and of the alternating evaluation principle. It does not conflict
with the totality-dependent symmetry evaluation theorems.

`checks/fitelson_report.py` verifies the exact alternating sums, the Lévy
closed-form asymptotic gap and the Cauchy gap. The analytic arguments above
establish the infinite-law claims.

## Paper references

- **Origin: Unbounded Utility: Five Top-Ranked Open Conjectures Resolved.** AI-generated report, 30 September 2026, 4 pages; communicated by Branden Fitelson. The report attributes production to Claude agents without specifying model versions. Fitelson is the communicator, not the credited producer of the proofs. — §§4(b) and 5(b), pp. 3–4
- **Background: [Decision theory unbound](https://doi.org/10.1111/nous.12473).** ([PDF](../sources/Nous%20-%202023%20-%20Goodsell%20-%20Decision%20theory%20unbound%20%281%29.pdf)) Zachary Goodsell (2024). Decision theory unbound. Noûs, 58, 669–695. First published online in 2023. — Appendix B, Definition 3, Lemma 6 and Remark 3

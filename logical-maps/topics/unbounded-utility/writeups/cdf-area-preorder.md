# CDF-area dominance

This is a model of **DU**, but not **DTU**, because Totality fails.

**Update, 2 October 2026:** Independent Sum Cancellation is now refuted for
this exact model by the [block-smoothing counterexample](#cancellation-counterexample)
from the AI-generated report communicated by Branden Fitelson. The earlier
discussion below explains why the manuscript's proof did not settle it;
the new result supplies an actual counterexample, not an inference from that gap.

It is also the **least DU preorder with L¹ Continuity**, equivalently with
Continuity under Vanishing Shifts. The continuity verification below and
the new [DU continuity theorem](du-vanishing-shifts-imply-relative.html)
establish this: every such ordering preserves all of this model's weak
and strict comparisons. Extensions can add comparisons for pairs with
both signed areas infinite.

**Source:** Zachary Goodsell, *Unbounded Utility and Background Risk*, 5 June
2026, §3 (pp. 7–8) and Theorem 7 (pp. 19–20). The supplied manuscript is
**unpublished, marked “do not cite”, and erroneous**. This local provenance
record does not endorse its withdrawn consistency theorem. The construction
is Goodsell’s; the explicit area, Tonelli, and counterexample details below
were recorded by GPT-6 (Codex), 9 September 2026. No separate checker or Lean
verification is claimed.

## Construction

Take all real-valued random variables, with real outcomes and identity utility.
Let $S_X(t)=\Pr(X>t)$ and put

$$d=S_X-S_Y,\qquad A_+=\int_{\mathbb R}d_+(t)\,dt,
\qquad A_-=\int_{\mathbb R}d_-(t)\,dt.$$

Define

$$X\succeq_R Y\quad\Longleftrightarrow\quad
A_-<\infty\ \text{and}\ A_+\ge A_-.$$

Thus both finite equal areas give indifference; one infinite area gives a
strict comparison in the appropriate direction; two infinite areas give
incomparability. Never evaluate $\infty-\infty$. The draft uses survival CDFs
with a different endpoint convention, which has no effect on the integrals.

## Preorder, expectation, and symmetry

Reflexivity is immediate. For transitivity write
$d_{XZ}=d_{XY}+d_{YZ}$. If the two component comparisons hold, their negative
parts are integrable. So is the negative part of their sum, since
$(a+b)_-\le a_-+b_-$. Signed integration is additive when negative parts are
integrable, including a possible positive infinity. Both component integrals
are nonnegative, so the sum comparison holds.

The relation depends only on laws. For integrable $X,Y$, both areas are finite
and $A_+-A_-=E[X]-E[Y]$. This verifies Expected Utility, hence the identity
chart, Simple EU, and Archimedean Outcomes; Rich Outcomes is explicit in the
model. More generally, if $E|X-Y|<\infty$ in the actual coupling, then

$$\int|S_X-S_Y|\le E|X-Y|,\qquad
\int(S_X-S_Y)=E[X-Y],$$

by the indicator formula and Fubini. This verifies Relative Expectation even
when the individual expectations are undefined.

Stochastic dominance gives $d\ge0$. Strict dominance gives a positive area:
strict inequality at a threshold persists on an interval by one-sided
continuity. Hence the relation preserves both weak and strict dominance.

Mixing both gambles with a common third law multiplies $d$ by the positive
mixture weight. It multiplies both areas by that weight, proving the full
Mixture Independence biconditional, including cases with infinite areas.

For $a>0$, replacing $X,Y$ by $aX+b,aY+b$ multiplies both areas by $a$.
Thus Positive Affine Invariance holds. Reflection and reversal give
$d_{-Y,-X}(t)=d_{X,Y}(-t)$ almost everywhere, leaving each area unchanged.
Thus Reflection Anti-Invariance holds as well. The minus sign in the draft’s
equation (16) is a substitution error; Lebesgue integration under $t\mapsto-t$
does not negate the integral.

## Comonotonic Sum Invariance

Let $Q_X,Q_Y$ be increasing quantiles. Tonelli applied to the regions between
the two graphs gives the *separate*, nonnegative area identities

$$A_+=\int_0^1(Q_X(u)-Q_Y(u))_+\,du,\qquad
A_-=\int_0^1(Q_Y(u)-Q_X(u))_+\,du.$$

These identities include infinite areas. For example, the first counts the
region where $Q_Y(u)\le t<Q_X(u)$, either by horizontal or vertical sections.
Monotonicity makes the length of its section at $t$ equal to
$(S_X(t)-S_Y(t))_+$, up to irrelevant endpoint conventions.

A comonotonic sum has quantile $Q_X+Q_Z$ almost everywhere. Adding $Q_Z$ to
both quantiles leaves their difference, and therefore **both** areas,
unchanged. This proves the biconditional on the entire domain. It supplies
the missing infinite-area justification in the manuscript’s informal
“rotate the CDF” argument in Theorem 7.

## Independent sums: the forward result

For an independent common summand with law $\xi$, the new survival difference
is $h=d*\xi$. Suppose $X\succeq_R Y$, so $g=d_-$ is integrable. Set $f=d_+$.
Then $h=f*\xi-g*\xi$ and

$$h_-\le g*\xi,\qquad \int(g*\xi)=\int g<\infty.$$

Tonelli gives $\int(f*\xi)=\int f$, possibly infinite. Since the negative
term is integrable, the signed integral of $h$ equals the original signed
integral of $d$, with the same finite or positive-infinite value. Therefore
weak **and strict** comparisons are preserved.

This does **not** establish the reverse implication. The printed proof
identifies $f*\xi,g*\xi$ with $h_+,h_-$, which is unjustified: the two
convolutions can overlap and cancel. For a simple example, let $X$ be equally
likely $-1$ or $1$, let $Y=0$, and let $\xi$ be equally likely $0$ or $1$.
Originally both areas are $1/2$; after convolution both are $1/4$. Tonelli
still preserves the integrals of the separately convolved $f$ and $g$.
This demonstrates the false identification; it is **not** a counterexample
to convolution invariance itself. Independent Sum Cancellation, and hence
full Independent Sum Invariance, were left unasserted in the original record;
the separately attributed 2 October counterexample below now refutes both.
A [total extension satisfying Independent Sum Invariance](conjectured-total-independent-sum-extension.html)
is now proved separately: saturating the area cone first supplies
cancellation while preserving its strict comparisons, after which an
invariant maximal-cone argument supplies totality.

## L¹ Continuity

**Additional proof: GPT-6 (Codex), 9 September 2026.** The exact area preorder
satisfies the recorded upper-section $L^{1}$ Continuity axiom. This is an elementary
closure argument for Goodsell's construction, not a claim that the manuscript
states or proves this additional property.

Suppose $X_n\succeq_R Y$ for every $n$ and
$\delta_n=E|X_n-X|\to0$. Write

$$d=S_X-S_Y,\qquad d_n=S_{X_n}-S_Y=d+e_n,
\qquad e_n=S_{X_n}-S_X.$$

For all sufficiently large $n$, $\delta_n$ is finite. The pointwise indicator
identity and Tonelli give

$$\int_{\mathbb R}|e_n(t)|\,dt
\le E\int_{\mathbb R}
 |\mathbf1_{\{X_n>t\}}-\mathbf1_{\{X>t\}}|\,dt
=E|X_n-X|=\delta_n. \tag{1}$$

The assumed comparison gives $\int(d_n)_-<\infty$ and a nonnegative
signed integral of $d_n$. Choose one sufficiently large index. Since

$$d_-\le(d_n)_-+|e_n|,$$

we obtain $\int d_-<\infty$. If $\int d_+=\infty$, the area rule already
gives $X\succeq_RY$. Otherwise $d$ is integrable. Equation (1) then makes
every sufficiently late $d_n$ integrable too, and

$$\int d=\int d_n-\int e_n\ge-\|e_n\|_1\ge-\delta_n.$$

Taking $n\to\infty$ gives $\int d\ge0$, again proving $X\succeq_RY$.
No subtraction of infinite areas occurs: the case of infinite positive area
was settled separately after negative-area integrability was established.

The same argument applies when $Y_n\to Y$ in $L^{1}$ with $X$ fixed, and even
when both arguments converge in $L^{1}$, since the change in survival difference
has $L^{1}$ norm at most $E|X_n-X|+E|Y_n-Y|$. Only the upper-section property is
recorded as a principle in this model. No Totality or symmetry assumption is
used in this closure proof. Original work consists of this short verification;
the CDF-area construction remains attributed to Goodsell.

## Verified failures

For a standard symmetric Cauchy variable $C$, comparison with zero has two
infinite areas: on each side the absolute area is the corresponding infinite
first tail moment. Thus $C$ and $0$ are incomparable. This witnesses failure
of Totality and Symmetric Neutrality (the draft’s “Reflection Symmetry”).
Folded Expectation also fails: the symmetric tail difference is identically
zero, so that principle would demand $C\sim0$.

Full and Antitonic Sum Invariance fail by the recorded St Petersburg
arguments, which require only Rich Outcomes and Stochastic Dominance.
See [the full-sum witness](dominance-refutes-full-sum.html) and
[the antitonic witness](dominance-refutes-antitonic-sum.html).

The executable check `checks/background_risk.py` tests finite-law area and
quantile identities, mixture behavior, the convolution-overlap example, and
exact St Petersburg tail identities. It is a sanity check, not a numerical
proof about all distributions or any transfinite extension.

See also the [source inventory and failed-claim audit](symmetric-dtu-refutes-independent-sum-candidate.html).

## Further failures found by the theorem trawl

**Added 25 September 2026.** DeepSeek (`deepseek-flash`) proposed the five
failures below. GPT-6 (Codex) independently checked the arguments, corrected
the shifted-moment calculations for Pasadena and Arroyo, and recorded the
claims as properties of this model. The construction remains Goodsell's.
This addition has informal model review, not Lean verification; the earlier
verification statements describe the original record.
The earlier model statement was marked `stated`, not `verified`. Its expanded
statement now includes the integer-ratio principle without a Lean definition,
so the amended record is marked `lean: none`.

For any real-valued $V$ and sure constant $c$, Tonelli's tail identities give

$$\int(S_V-S_c)_+=E[(V-c)^+],\qquad
  \int(S_V-S_c)_-=E[(c-V)^+].\tag{2}$$

If both quantities are infinite, this exact preorder leaves $V$ and $c$
incomparable. The following calculations use the individual nonnegative
moments, never their undefined difference.

### Alternating St Petersburg and negative self-similarity

Let $\Pr(A=(-2)^n)=2^{-n}$ for $n\ge1$, and let $c=-1/2$. Then

$$E[(A+\tfrac12)^+]
  =\sum_{k\ge1}\left(1+2^{-(2k+1)}\right)=\infty,$$

$$E[(-\tfrac12-A)^+]
  =\sum_{k\ge0}\left(1-2^{-(2k+2)}\right)=\infty.$$

Consequently $A$ and $c$ are incomparable, so the model fails
Alternating St Petersburg $=-1/2$.

They are also two fixed points in value of the same map
$F(V)=M_{1/2}(-2V,-2)$. For $A$, the mixture puts probability $1/2$ on
$-2$ and probability $2^{-m}$ on $(-2)^m$ for every $m\ge2$. This is
exactly the law of $A$, so Stochastic Equivalence gives $A\sim F(A)$.
For $c$, the simple mixture $F(c)=M_{1/2}(1,-2)$ has expectation $-1/2$,
so Expected Utility gives $c\sim F(c)$. Nevertheless $A\not\sim c$.
Thus the instance $p=1/2$, $a=2$, $b=0$, $Z=-2$ refutes both the
integer-ratio and real-ratio Uniqueness of Negative Self-Similarity axioms
**in this model**.

### Pasadena and Arroyo

Put $c=\ln2\in(0,1)$. For Pasadena, with
$\Pr(P=-(-2)^n/n)=2^{-n}$, the positive atoms have odd indices and
the negative atoms have even indices. Equation (2) becomes

$$E[(P-c)^+]=\sum_{k\ge1}
  \left(\frac{1}{2k-1}-c\,2^{-(2k-1)}\right)=\infty,$$

$$E[(c-P)^+]=\sum_{k\ge1}
  \left(\frac{1}{2k}+c\,2^{-2k}\right)=\infty.$$

The odd and even harmonic subseries diverge; the terms involving $c$ have
finite sums. This also corrects the missing denominator $2k-1$ in the
trawl's displayed positive-area calculation.

For Arroyo, with $\Pr(R=(-1)^{n+1}(n+1))=1/(n(n+1))$, the corresponding
expressions are

$$E[(R-c)^+]=\sum_{\substack{n\ge1\\ n\text{ odd}}}
  \left(\frac1n-\frac{c}{n(n+1)}\right)=\infty,$$

$$E[(c-R)^+]=\sum_{\substack{n\ge1\\ n\text{ even}}}
  \left(\frac1n+\frac{c}{n(n+1)}\right)=\infty.$$

Here the corrections are summable because
$\sum_{n\ge1}1/(n(n+1))=1$. They were omitted from the trawl's equalities;
retaining them leaves the divergence conclusion intact. Both gambles are
incomparable with $\ln2$ in this preorder, establishing failure of the
Pasadena and Arroyo evaluation principles.

These are counterexamples to implications, not universal incompatibilities
between the model's positive properties and the failed axioms. In particular,
CDF-Area Extension leaves both-infinite pairs unconstrained; extensions of
this exact preorder can add comparisons. The four proposed contradiction
records were therefore not imported. No conclusion about conclosure or
Independent Sum Cancellation follows from these calculations.

The added cases in `checks/background_risk.py` check the law recursion and
exact finite-prefix area identities, including the shifted harmonic terms.
They are arithmetic diagnostics; the divergent-series arguments above
establish the infinite-law failures.

The original quarantine evidence is
`checkpoint-4efdb29afea94da583b8df9975e053e4`, discovered on source revision
`3d673577f8d071e7230a61ce36d028d4d5a14c38`. The runner identifies the actual
discoverer as `deepseek-flash`, correcting the draft's Claude attribution.
The model's `certificate.trawl` records the corrected checkpoint, scoped
review, admission time, original response identity and evidence references.


<a id="cancellation-counterexample"></a>

## Independent Sum Cancellation refuted

**Source:** AI-generated results communicated by **Branden Fitelson**,
*Unbounded Utility: Five Top-Ranked Open Conjectures Resolved*, 30 September
2026, §§2 and 5(a). The report identifies Claude agents, without model versions.
The CDF-area model is Goodsell's; the cancellation counterexample is credited
to the report's AI producers. GPT-6 (Codex) expanded and informally checked
the proof on 2 October 2026. No human check or Lean verification is asserted.

### The ordering and the plan

For $v=S_X-S_Y$ the [CDF-area ordering](cdf-area-preorder.html) declares
$X\succeq_RY$ iff $\int v_-<\infty$ and $\int v_+\ge\int v_-$.
We construct probability laws whose two signed areas are infinite, but
whose survival difference becomes nonnegative after convolution with one
independent noise law. The smoothed positive area is infinite. Thus
$X+Z\succ_RY+Z$ while $X,Y$ are incomparable.

### A block smoothing lemma

Let $\mu$ have a symmetric density nonincreasing on $[0,\infty)$, and let
$T(r)=\mu(|Z|>r)$. Suppose $L\ge2w>0$,
$\Delta=T(w)-T(L)>0$ and $H\Delta\ge h>0$. Define

$$b=H\mathbf1_{[-L,0)}-h\mathbf1_{[0,w)}
       +H\mathbf1_{[w,w+L)}.$$

We prove $b*\mu\ge0$ everywhere. At location $x$, write

$$N=\mu([x-w,x]),\qquad
P=\mu([x,x+L])+\mu([x-w-L,x-w]).$$

Endpoints have measure zero. The convolution equals $HP-hN$.
For $0\le x\le w$, the two wing intervals contain $[w,L]$ and $[-L,-w]$,
so $P\ge\Delta\ge\Delta N$. For $x\ge2w$, the left wing contains
$[x-2w,x-w]$, whose density integral is at least that on $[x-w,x]$ by
monotonicity on the positive half-line. For $w\le x\le2w$, the left wing
contains $[-w,0]$ because $L\ge2w$; symmetry and monotonicity again make
its integral at least $N$. Thus outside the middle interval on the right
$P\ge N\ge\Delta N$. Reflection about $w/2$ gives the same conclusion
for $x\le0$. In every case $HP-hN\ge(H\Delta-h)N\ge0$.

### Infinite blocks and actual probability laws

Take $Z=\epsilon(U^{-2}-1)$ with $U$ uniform on $(0,1)$ and $\epsilon$ an
independent fair sign. Its density is
$f(z)=\tfrac14(1+|z|)^{-3/2}$, and
$T(r)=(1+r)^{-1/2}$, so $E|Z|=\infty$.
For $k\ge1$ put

$$c=\tfrac3{13},\quad w_k=4^k-1,\quad L_k=16^k-1,
\quad h_k=c4^{-k},\quad H_k=2c2^{-k}.$$

Then $L_k\ge2w_k$ and

$$\Delta_k=2^{-k}-4^{-k},\qquad
\frac{H_k\Delta_k}{h_k}=2(1-2^{-k})\ge1.$$

Place these blocks consecutively. More precisely, set $r_1=0$ and
$r_{k+1}=r_k+2L_k+w_k$, and define $v$ to be $H_k$ on
$[r_k,r_k+L_k)$, $-h_k$ on $[r_k+L_k,r_k+L_k+w_k)$, and $H_k$ on
$[r_k+L_k+w_k,r_{k+1})$. Let $v=0$ on the negative half-line. It is
right-continuous and tends to zero at both infinities.

Its total variation is

$$\operatorname{TV}(v)
=2H_1+2\sum_{k\ge1}(H_k+h_k)
=2c+4c+\tfrac{2c}{3}=\tfrac{20}{13}.$$

Here the initial jump and the downward jumps between consecutive positive
plateaus together contribute $2H_1$. It would be incorrect to count a
return to zero at every adjoining block boundary.

The finite signed atomic measure $\nu=-dv$ has mass zero and Jordan parts
of mass $10/13$ each. Define probability laws

$$\mathcal L(X)=\nu^++\tfrac3{13}\delta_0,\qquad
  \mathcal L(Y)=\nu^-+\tfrac3{13}\delta_0.$$

Then $S_X-S_Y=\nu((t,\infty))=v(t)$, so these are genuine gamble laws,
not merely formal survival differences. They can be realized on the standing
atomless space together with a $Z$ independent of the pair $(X,Y)$.

The negative area is

$$\sum_{k\ge1}h_kw_k=c\sum_{k\ge1}(1-4^{-k})=\infty,$$

and the positive area $\sum 2H_kL_k$ is also infinite. Thus neither
comparison holds before adding the noise.

### Convolution gives strict dominance

Write $v$ as the sum of its translated blocks $b_k$. Their supports are
disjoint, and every finite partial sum is bounded in absolute value by one
fixed constant. Dominated convergence with respect to the probability
measure $\mu$ therefore gives

$$v*\mu=\sum_{k\ge1}b_k*\mu.$$

Every summand is nonnegative by the lemma. Each individual block is integrable,
so Fubini gives

$$\int(b_k*\mu)=\int b_k=2H_kL_k-h_kw_k.$$

These positive quantities have divergent sum. Tonelli, now applied to
nonnegative convolved blocks, yields $\int v*\mu=+\infty$. In particular
$v*\mu$ is not identically zero. Independent convolution gives
$S_{X+Z}-S_{Y+Z}=v*\mu\ge0$. Thus $X+Z$ strictly stochastically dominates
$Y+Z$ and is strictly preferred by the area rule. This refutes Independent
Sum Cancellation and therefore Independent Sum Invariance.

The original model still satisfies Independent Sum Preservation, Positive
Affine Invariance and Comonotonic Sum Invariance. Its comonotonic copula
established the since-retired Existential Copula Sum Invariance (removed
11 October 2026); its Relative Expectation now gives Uninteractive Sum
Invariance by `relative-independence-equivalence-imply-uninteractive-sum`.
Consequently this one model supplies the report's second and fifth
non-implications, in the report's own terms, and also separates Independent
Sum Preservation from Cancellation over DU.

`checks/fitelson_report.py` checks the exact block inequalities, finite-prefix
variation and areas, and samples the closed-form convolution. Those numerical
samples do not substitute for the global smoothing lemma or the divergent
series proof.

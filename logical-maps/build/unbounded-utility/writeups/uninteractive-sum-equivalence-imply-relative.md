# Uninteractive Sum Invariance and Stochastic Equivalence imply Relative Expectation

**Proved implication:** Rich Outcomes + Stochastic Equivalence + Uninteractive
Sum Invariance imply Relative Expectation. Mixture Independence and
Stochastic Dominance are not used. With
[`relative-independence-equivalence-imply-uninteractive-sum`](relative-independence-equivalence-imply-uninteractive-sum.html),
Uninteractive Sum Invariance and Relative Expectation are equivalent under
Mixture Independence, Stochastic Equivalence and Rich Outcomes, in particular
under DU.

Proof: Claude (Fable 5.1), 10–11 October 2026, in response to Zachary
Goodsell's question whether the two principles coincide under DU. No
independent check or Lean verification is claimed.

## Stationary realization of a mean-zero law

**Lemma.** For every law $\mu$ on $\mathbb R$ with $\int|x|\,d\mu<\infty$ and
$\int x\,d\mu=0$ there are real random variables $D\sim\mu$ and $Z$ with
$Z+D\overset{d}{=}Z$.

*Two-point case.* Let $\rho$ put mass $q$ on $x>0$ and $1-q$ on $y<0$ with
mean zero, so $q=|y|/(x+|y|)$. Let $Z$ be uniform on $[-|y|,x)$ and

$$T(z)=\begin{cases}z+x,&z\in[-|y|,0),\\ z-|y|,&z\in[0,x).\end{cases}$$

$T$ translates $[-|y|,0)$ onto $[x-|y|,x)$ and $[0,x)$ onto $[-|y|,x-|y|)$, so
it is a measure-preserving bijection of $[-|y|,x)$ and $T(Z)\overset{d}{=}Z$.
Put $D=T(Z)-Z$. Then $D=x$ exactly on $[-|y|,0)$, an event of probability
$|y|/(x+|y|)=q$, and $D=y$ otherwise. So $D\sim\rho$ and
$Z+D=T(Z)\overset{d}{=}Z$.

*General case.* Let $\mu^+,\mu^-$ be the restrictions of $\mu$ to $(0,\infty)$
and $(-\infty,0)$ and $m=\int x\,d\mu^+=\int|x|\,d\mu^-$, finite by
integrability and positive unless $\mu=\delta_0$. For $x>0>y$ let $\rho_{x,y}$
be the mean-zero two-point law on $\{x,y\}$ and define

$$\pi(dx,dy)=\frac{x+|y|}{m}\,\mu^+(dx)\,\mu^-(dy).$$

For a Borel set $E\subset(0,\infty)$,

$$\int\rho_{x,y}(E)\,d\pi
=\iint 1_E(x)\,\frac{|y|}{x+|y|}\cdot\frac{x+|y|}{m}\,\mu^+(dx)\mu^-(dy)
=\frac{\mu^+(E)}{m}\int|y|\,d\mu^-=\mu^+(E),$$

and symmetrically for $E\subset(-\infty,0)$ with the weight $x/(x+|y|)$. The
total mass of $\pi$ is $(1/m)(m\,\mu^-(\mathbb R)+m\,\mu^+(\mathbb R))=1-\mu(\{0\})$.
Hence $\mu=\int\rho_{x,y}\,d\pi+\mu(\{0\})\,\delta_0$. Now draw $(x,y)$ from
$\pi$ normalized, with probability $\mu(\{0\})$ instead set $D=Z=0$, and
otherwise take $(D,Z)$ for $\rho_{x,y}$ as above. Conditionally on $(x,y)$,
$Z+D$ has the law of $Z$; integrating over $(x,y)$, $Z+D\overset{d}{=}Z$
unconditionally, while $D\sim\int\rho_{x,y}\,d\pi+\mu(\{0\})\delta_0=\mu$.
$\square$

*Refinement.* The decomposition of $\mu$ into two-point laws is any coupling
of the probability measures $x\,\mu^+(dx)/m$ and $|y|\,\mu^-(dy)/m$. Choosing
a coupling that pairs $x>C$ only with $|y|\le C$ and $|y|>C$ only with $x\le C$,
which is possible for large $C$, and noting that in the two-point
construction $\min(|D|,|Z|)\le\min(x,|y|)$, one gets $\min(|D|,|Z|)\le C$. This
bounded version is not needed below.

## Step 1: integrable mean-zero gambles are indifferent to zero

Let $D$ be integrable with $E D=0$ and law $\mu$. Realize $(D',Z)$ on the
standing space with the joint law of the lemma; all joint laws are available,
and Rich Outcomes places the values in the chart. The compared pair $(D',0)$
and the summand $Z$ are uninteractive: $E\min(|D'|,|Z|)\le E|D'|<\infty$ and
$\min(0,|Z|)=0$. Uninteractive Sum Invariance gives

$$D'\succeq 0\iff D'+Z\succeq Z,\qquad 0\succeq D'\iff Z\succeq D'+Z.$$

Both right-hand sides hold by Stochastic Equivalence, since $D'+Z$ and $Z$
have the same law. So $D'\sim 0$, and $D\sim D'$ by Stochastic Equivalence,
whence $D\sim 0$.

## Step 2: Relative Expectation

Let $E|X-Y|<\infty$, $c=E[X-Y]$ and $D_0=X-Y-c$, so $E D_0=0$ and
$X=Y+c+D_0$. The compared pair $(c+D_0,\,0)$ with the summand $Y$ is
uninteractive, because $E\min(|c+D_0|,|Y|)\le|c|+E|D_0|<\infty$. Hence

$$X\succeq Y\iff c+D_0\succeq 0\iff D_0\succeq -c\iff 0\succeq -c\iff c\ge 0.$$

The second equivalence is the principle with the constant summand $-c$, the
third is Step 1, and the fourth is the ordering of constants by utility.
Symmetrically $Y\succeq X\iff c\le 0$. This is Relative Expectation, including
its strict and indifferent cases. $\square$

## Remarks

- Only instances with an integrable compared pair and an arbitrary common
  summand were used. So, under Stochastic Equivalence and Rich Outcomes, that
  restricted principle, the full principle and Relative Expectation are
  equivalent given the forward result and Mixture Independence.
- The summand $Z$ of Step 1 need not be integrable: its mean is finite only
  when $\mu$ has a finite second moment on each side. Invariance under
  integrable common summands alone would therefore not run this argument.
- With the bounded-overlap variant of the principle, the refinement still
  gives Step 1, hence every integrable gamble indifferent to its mean, Shift
  Invariance, Shift Transfer, and Relative Expectation for bounded
  differences. Step 2 needs the integrable overlap, since $\min(|c+D_0|,|Y|)$
  is unbounded when $D_0$ is. Whether the bounded variant implies Relative
  Expectation under DU is open; it reduces to $Y+R\sim Y+E[R]$ for integrable
  $R\ge0$ and arbitrary $Y$.

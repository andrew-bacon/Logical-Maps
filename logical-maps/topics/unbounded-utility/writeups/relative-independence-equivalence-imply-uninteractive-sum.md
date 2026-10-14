# Relative Expectation, Mixture Independence and Stochastic Equivalence imply Uninteractive Sum Invariance

**Proved implication:** Rich Outcomes + Stochastic Equivalence + Mixture
Independence + Relative Expectation imply Uninteractive Sum Invariance.
Stochastic Dominance, Totality, Shift Invariance and every continuity
principle are left out. Together with the converse
[`uninteractive-sum-equivalence-imply-relative`](uninteractive-sum-equivalence-imply-relative.html),
Uninteractive Sum Invariance is equivalent to Relative Expectation under DU.

Proof: Claude (Fable 5.1), 10–11 October 2026, in response to Zachary
Goodsell's request for a minimal set of principles entailing the principle
he proposed on 6 October 2026. No independent check or Lean verification is
claimed.

## Setting

Gambles are real-valued random variables on the standing atomless space, with
identity utility; all joint laws are available. Write $M(X,W)$ for the fair
mixture $M_{1/2}(X,W)$, realized as $X$ on $\{B=0\}$ and $W$ on $\{B=1\}$ for a
fair coin $B$ independent of the gambles mixed; the two mixtures compared in
one application of Mixture Independence use the same coin. This is how the
randomized-selection construction is used throughout the map.

Two variables $X,Z$ are **uninteractive** when $E\min(|X|,|Z|)<\infty$. The
principle to prove: if $(X,Z)$ and $(Y,Z)$ are uninteractive then
$X\succeq Y\iff X+Z\succeq Y+Z$.

## Step 1: integrable common summands cancel

**Lemma 1 (Relative Expectation + Mixture Independence).** If $E|Z|<\infty$
then, for every coupling of $Z$ with $(X,Y)$, $X\succeq Y\iff X+Z\succeq Y+Z$.

*Proof.* By Mixture Independence with the common component $Y+Z$,

$$X\succeq Y\iff M(X,\,Y+Z)\succeq M(Y,\,Y+Z).$$

On the same coin,

$$M(X,Y+Z)-M(X+Z,Y)=(1-B)(X-X-Z)+B(Y+Z-Y)=Z(2B-1),$$

which is integrable with $E[Z(2B-1)]=E[Z]\,E[2B-1]=0$ because $B$ is
independent of $Z$. Relative Expectation therefore gives
$M(X,Y+Z)\sim M(X+Z,Y)$. The same computation gives
$M(Y,Y+Z)\sim M(Y+Z,Y)$. Finally, Mixture Independence with the common
component $Y$ gives $M(X+Z,Y)\succeq M(Y+Z,Y)\iff X+Z\succeq Y+Z$. Chain the
four statements by transitivity. $\square$

With $Z$ constant this is Shift Invariance. Nothing about laws was used.

## Step 2: separability over an event

**Lemma 2 (Mixture Independence + Stochastic Equivalence).** Let $A$ be an
event with $0<P(A)<1$. If $X^\circ,Y^\circ$ vanish on $A$ and $Z$ vanishes off
$A$, then $X^\circ\succeq Y^\circ\iff X^\circ+Z\succeq Y^\circ+Z$.

*Proof.* The recorded result
[`independence-to-sure-thing`](independence-to-sure-thing.html) gives
Sure-Thing. The gambles $X^\circ+Z$ and $Y^\circ+Z$ both equal $Z$ on $A$, so
their restrictions to $A$ are identical, hence indifferent. Sure-Thing with
the event $A$ says $X^\circ+Z\succeq Y^\circ+Z$ iff the restrictions to $A^c$
compare the same way, and those restrictions are $X^\circ$ and $Y^\circ$.
$\square$

This is the only place where Stochastic Equivalence is used.

## Step 3: the reduction

Let $(X,Z)$ and $(Y,Z)$ be uninteractive, so
$m_X=\min(|X|,|Z|)$ and $m_Y=\min(|Y|,|Z|)$ are integrable. Put

$$A=\{|Z|>|X|\}\cap\{|Z|>|Y|\}.$$

On $A$, $|X|=m_X$ and $|Y|=m_Y$, so $X1_A$ and $Y1_A$ are integrable. On
$A^c$, $|Z|\le|X|$ or $|Z|\le|Y|$, so $|Z|1_{A^c}\le m_X+m_Y$ and
$Z_s=Z1_{A^c}$ is integrable. Write $Z_b=Z1_A$.

*If $P(A)=1$*, $X$ and $Y$ are integrable, so $X-Y$ and $(X+Z)-(Y+Z)=X-Y$
are integrable and Relative Expectation decides both comparisons by the sign
of $E[X-Y]$, with indifference at zero. *If $P(A)=0$*, $Z=Z_s$ is integrable
and Lemma 1 finishes. Otherwise let $p=P(A)\in(0,1)$ and

$$a=E[X1_A],\qquad b=E[Y1_A],\qquad \gamma=\frac{b-a}{1-p},\qquad
X^\circ=X1_{A^c},\qquad Y^\circ=(Y+\gamma)1_{A^c}.$$

All these gambles exist in the real chart by Rich Outcomes.

*Left side.* $X-(X^\circ+a)=X1_A-a$ is integrable with mean zero, so
$X\sim X^\circ+a$ by Relative Expectation. Likewise
$Y-(Y^\circ+a)=Y1_A-\gamma1_{A^c}-a$ has mean $b-\gamma(1-p)-a=0$, so
$Y\sim Y^\circ+a$. Hence $X\succeq Y\iff X^\circ+a\succeq Y^\circ+a\iff
X^\circ\succeq Y^\circ$, the last step by Lemma 1 with the constant $-a$.

*Right side.* Lemma 1 removes the integrable $Z_s$:
$X+Z\succeq Y+Z\iff X+Z_b\succeq Y+Z_b$. The same two replacements apply,
since $(X+Z_b)-(X^\circ+Z_b+a)=X1_A-a$ and
$(Y+Z_b)-(Y^\circ+Z_b+a)=Y1_A-\gamma1_{A^c}-a$, so
$X+Z\succeq Y+Z\iff X^\circ+Z_b\succeq Y^\circ+Z_b$.

*Closing.* $X^\circ,Y^\circ$ vanish on $A$ and $Z_b$ vanishes off $A$, so
Lemma 2 gives $X^\circ\succeq Y^\circ\iff X^\circ+Z_b\succeq Y^\circ+Z_b$.
Combining the three displays, $X\succeq Y\iff X+Z\succeq Y+Z$. $\square$

## Which premises are needed

- **Mixture Independence.** Extend the base area preorder
  [`cdf-area-preorder`](cdf-area-preorder.html) by declaring $W\succeq V$
  whenever $W\mathrel{R}C$ and $0\mathrel{R}V$ for a standard Cauchy $C$,
  where $R$ is the area comparison. This is a preorder satisfying CDF-Area
  Extension (every new pair has infinite positive area, so no finite-area
  comparison is added), hence Relative Expectation and Stochastic
  Equivalence, but $C\succeq 0$ while $C+1\not\succeq 1$, so Shift Invariance
  fails and so does the conclusion. Mixture Independence fails there.
- **Some continuity.** [`total-exact-ultrafilter`](total-exact-ultrafilter.html)
  satisfies DTU and fails Shift Invariance, so Mixture Independence and
  Stochastic Equivalence alone do not suffice.
- **Shift Invariance with Sure-Thing is not enough.**
  [`finite-shift-total-extension`](finite-shift-total-extension.html)
  satisfies DTU and Shift Invariance but fails Shift Transfer. Uninteractive
  Sum Invariance implies Relative Expectation (the converse result), which
  gives Shift Transfer at once: $M_p(X+b/p,Y)$ and $M_p(X,Y+b/(1-p))$ differ by
  a bounded mean-zero variable. So that model fails the conclusion.
- **L¹ Continuity is not needed.**
  [`lexicographic-folded-extension`](lexicographic-folded-extension.html)
  satisfies DTU and Relative Expectation but fails L¹ Continuity; the
  conclusion holds there by this result.

## Consequence for fixed copulas

Call a copula corner-avoiding when it gives zero mass to
$([0,\delta)\cup(1-\delta,1])^2$ for some $\delta>0$. If a pair $(X,Z)$ admits
such a copula, it has the joint law of $(Q_X(U),Q_Z(W))$ with $(U,W)$
distributed as the copula, and on each of the two regions one quantile is
evaluated inside $[\delta,1-\delta]$, where it is bounded. So the pair is
uninteractive, and Uninteractive Sum Invariance gives $\operatorname{SC}(C)$
for every corner-avoiding $C$. The adjacent-quarter shuffle copula used in the
clipped-expectation write-ups is corner-avoiding with $\delta=1/4$; its direct
verification there is now a special case of this result together with those
models' Relative Expectation.

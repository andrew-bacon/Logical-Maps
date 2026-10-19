# BF, Weak Rigid Comprehension, Atomicity and Relational Choice imply Intensional Choice

The construction is Cian Dorr's, proposed on 3 October 2026 with Rigid Comprehension. The
restriction to atoms, the uniqueness argument and the weakening to Weak Rigid Comprehension are by
Claude Opus 5.5 (Anthropic), 3 October 2026. Informal proof, not Lean-verified.

Fix $\sigma$ and let $F^{\sigma t}$ be necessarily instantiated. Atomicity is used at type $t$, BF at
types $t$ and $\sigma$, Relational Choice at types $t,\sigma$, and Weak Rigid Comprehension at type
$t\sigma t$. In this write-up an *atom* is an atom of type $t$.

## Two facts about atoms

1. *An atom decides every proposition.* If $w$ is an atom and $\Diamond(w\land p)$, then $w\le p$.
   With BF this extends to quantified propositions. If $w\le\exists x\, .\,\phi$, then
   $\Diamond\exists x\, .\,(w\land\phi)$, so BF gives an $x$ with $\Diamond(w\land\phi)$, and hence
   $w\le\phi$.
2. *Distinct atoms are incompatible.* If atoms $w_1,w_2$ satisfy $\Diamond(w_1\land w_2)$, then
   $w_1\le w_2$ and $w_2\le w_1$, so $w_1=w_2$.

## The construction

Put $U:=\lambda wx\, .\,\operatorname{Atom}(w)\to w\le Fx$. It is serial. A non-atom is related to
everything. An atom $w$ entails $\exists x\, .\,Fx$ by the necessity of that proposition, so by fact 1
$w\le Fx$ for some $x$. Relational Choice gives a functional $V$ with $Vwx\to Uwx$. Restrict it to atoms,
$V':=\lambda wx\, .\,\operatorname{Atom}(w)\land Vwx$. Weak Rigid Comprehension gives a weakly rigid $R$
coextensive with $V'$. So the instances of $R$ are exactly the pairs $(w,x_w)$, where $w$ is an atom and
$x_w$ is its chosen value, and $w\le Fx_w$ in each case. Put
$$G:=\lambda x\, .\,\exists w\, .\,w\land Rwx .$$

**$G\le F$.** Let $X:=\lambda wx\, .\,w\to Fx$. Every instance $(w,x_w)$ of $R$ satisfies $\Box Xwx_w$,
because $w\le Fx_w$. So weak inextensibility gives $R\le X$, that is,
$\Box\forall wx\, .\,Rwx\to(w\to Fx)$. Hence $\Box\forall x\, .\,Gx\to Fx$.

**$\Box\exists x\, .\,Gx$.** Suppose otherwise. Atomicity gives an atom $w_0$ with
$w_0\le\neg\exists x\, .\,Gx$. But $Rw_0x_{w_0}$, so persistence gives $\Box Rw_0x_{w_0}$, and then
$w_0\le\exists x\, .\,Gx$. This contradicts $\Diamond w_0$.

**Lemma (no new instances below an atom).** If $w^*$ is an atom and $w^*\le Rwx$, then some actual
instance $(w_1,x_1)$ of $R$ satisfies $w^*\le(w=w_1\land x=x_1)$.

*Proof.* Suppose not. Let $X:=\lambda ab\, .\,\neg(w^*\land a=w\land b=x)$. For each actual instance
$(w_1,x_1)$, the proposition $w^*\land w_1=w\land x_1=x$ is impossible: otherwise fact 1 would give
$w^*\le(w_1=w\land x_1=x)$. So $\Box Xw_1x_1$. Weak inextensibility gives $R\le X$, hence
$\Box(Rwx\to\neg w^*)$. With $w^*\le Rwx$, that gives $\Box\neg w^*$, which is impossible. ∎

**Uniqueness.** Suppose $\Box\exists!x\, .\,Gx$ fails. Atomicity gives an atom $w^*$ entailing that $G$
does not have exactly one instance. Since $\Box\exists x\, .\,Gx$, that atom entails
$\exists xy\, .\,Gx\land Gy\land x\ne y$. By fact 1, applied three times, there are $x,y,w,w'$ such that
$$w^*\le w\land Rwx,\qquad w^*\le w'\land Rw'y,\qquad w^*\le x\ne y .$$
The lemma gives actual instances $(w_1,x_1)$ and $(w_2,x_2)$ with $w^*\le(w=w_1\land x=x_1)$ and
$w^*\le(w'=w_2\land y=x_2)$.
- Since $w^*\le w$, we get $w^*\le w_1$, and likewise $w^*\le w_2$.
- So $\Diamond(w_1\land w_2)$. Both are actual atoms, since every instance of $R$ has an atom as its
  first term, so $w_1=w_2$ by fact 2.
- $V$ is functional, so $x_1=x_2$, and therefore $w^*\le x=y$.

This contradicts $w^*\le x\ne y$ and $\Diamond w^*$.

So $G\le F$ and $G$ is necessarily uniquely instantiated.

## Remarks

Restricting to atoms is essential. Without ND, a weakly rigid (indeed rigid) relation that is functional
need not be necessarily functional. If distinct arguments $a\ne b$ with distinct values are identified at
some world, the relation gives the merged argument two values there. If $V$ were used unrestricted, a
non-atom related to some value could be identified, at a world, with the true atom and give $G$ a second
instance. Distinct actual atoms can also be identified, but only at worlds where both are false, by
fact 2, and $G$ looks only at true first terms.

Fact 1 is BF in disguise. Atomicity and BF are used only at the evaluation point. Rigidity enters only
through persistence and unboxed weak inextensibility.

## Paper references

- **Background: [Could the truths of mathematics have been different?](https://andrew-bacon.github.io/papers/Could%20mathematics%20have%20been%20different.pdf).** Bacon, Andrew (2025). Could the truths of mathematics have been different? Draft dated 9 October 2025, with online appendix; published in Philosophical Review 135(3), 2026, pp. 221–285, as cited by Barton and Goodsell. Locators refer to the draft. The full Boolean-valued construction is in appendix §B.2, pp. 7–9 of the separately paginated appendix (PDF pp. 41–43); Theorem 4.4 and its proof (Appendix C.1) and Lemma C.6 (Appendix C.2) were read directly on 19 October 2026. — §6, p. 27. Formulation of Intensional Choice.

# Totality ∧ Comonotonic Sum Preservation ⇒ Comonotonic Sum Cancellation

<p class='cert'>Result — Source: Misc.; produced by GPT-6 (Codex), prompted by Zachary Goodsell; recorded by GPT-6 (Codex), prompted by Zachary Goodsell.</p>

## Premises

- **Totality.** For all gambles X,Y, either $X \succeq Y$ or $Y \succeq X$.
- **Comonotonic Sum Preservation.** If X and Z are comonotonic, and Y and Z are comonotonic, then $X\succeq Y$ implies $X+Z\succeq Y+Z$, and $X\succ Y$ implies $X+Z\succ Y+Z$. A pair is comonotonic when its members admit nondecreasing representations in one common uniform random variable.

## Conclusion

- **Comonotonic Sum Cancellation.** If X and Z are comonotonic, and Y and Z are comonotonic, then $X+Z\succeq Y+Z$ implies $X\succeq Y$. A pair is comonotonic when its members admit nondecreasing representations in one common uniform random variable.

## Proof

Suppose X+Z>=Y+Z, with Z comonotonic with both compared gambles. If X were not weakly preferred to Y, Totality would imply Y>X. Strict preservation would then give Y+Z>X+Z, contradicting the premise. Therefore X>=Y. Weak preservation alone would not justify this argument.

## Sources

- **GPT-6 connecting proof 3 Oct** — GPT-6 (Codex), 3 October 2026: elementary connecting proof recording Zachary Goodsell’s requested preservation/cancellation split and nonindependent copula principle.

<p class='cert'>Record: <code>topics/unbounded-utility/results/total-preservation-implies-comonotonic-cancellation.yaml</code></p>

# Comonotonic Sum Invariance ⇒ Comonotonic Sum Preservation

<p class='cert'>Result — Source: Misc.; produced by GPT-6 (Codex), prompted by Zachary Goodsell; recorded by GPT-6 (Codex), prompted by Zachary Goodsell.</p>

## Premises

- **Comonotonic Sum Invariance.** If X and Z are comonotonic, and Y and Z are comonotonic, then $X \succeq Y$ iff $X+Z \succeq Y+Z$. A pair is comonotonic when its members admit nondecreasing representations in one common uniform random variable.

## Conclusion

- **Comonotonic Sum Preservation.** If X and Z are comonotonic, and Y and Z are comonotonic, then $X\succeq Y$ implies $X+Z\succeq Y+Z$, and $X\succ Y$ implies $X+Z\succ Y+Z$. A pair is comonotonic when its members admit nondecreasing representations in one common uniform random variable.

## Proof

The forward implication preserves weak comparisons. If X>Y but Y+Z>=X+Z, cancellation with the compared pair reversed would give Y>=X. Thus the biconditional also preserves strict comparisons.

## Sources

- **GPT-6 connecting proof 3 Oct** — GPT-6 (Codex), 3 October 2026: elementary connecting proof recording Zachary Goodsell’s requested preservation/cancellation split and nonindependent copula principle.

<p class='cert'>Record: <code>topics/unbounded-utility/results/comonotonic-sum-implies-preservation.yaml</code></p>

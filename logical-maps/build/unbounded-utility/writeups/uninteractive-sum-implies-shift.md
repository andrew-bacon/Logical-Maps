# Uninteractive Sum Invariance ⇒ Shift Invariance

<p class='cert'>Result — Source: Misc.; produced by Claude (Opus 5.5), prompted by Zachary Goodsell; recorded by Claude (Fable 5.1), prompted by Zachary Goodsell, 2026-10-11.</p>

## Premises

- **Uninteractive Sum Invariance.** Call real-utility variables X and Z uninteractive when $E[\min(|X|,|Z|)]<\infty$: their tails are jointly rare. Whenever (X,Z) and (Y,Z) are uninteractive, $X \succeq Y$ iff $X+Z \succeq Y+Z$. The condition applies to each pair separately; nothing is assumed about the joint law of (X,Y,Z), and no law invariance is built in.

## Conclusion

- **Shift Invariance.** For every real $b, X \succeq Y$ iff $X+b \succeq Y+b$.

## Proof

Take the common summand Z = b constant. Then $E\min(|X|,|b|)\le |b|<\infty$ and likewise for Y, so the pairs are uninteractive and the principle gives $X\succeq Y$ iff $X+b\succeq Y+b$, which is Shift Invariance. In particular the exact ultrafilter and eventual clipped-expectation models, which fail Shift Invariance, fail Uninteractive Sum Invariance.

## Notes

Immediate instance. Not Lean-checked.

## Sources

- **Claude constant-summand observation 6 Oct** — Claude (Opus 5.5), Logical Maps session, 6 October 2026, while formulating the principle at Zachary Goodsell's request; recorded by Claude (Fable 5.1), 11 October 2026.

<p class='cert'>Record: <code>topics/unbounded-utility/results/uninteractive-sum-implies-shift.yaml</code></p>

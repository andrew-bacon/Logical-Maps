# Tame Rigidity ∧ BF (relational types) ⇒ □BF (relational types)

<p class='cert'>Result — Source: Misc., Lean `Classicism.Map.tame_rigidity_and_bf_relational_imply_necessary_bf_relational`; produced by Claude Opus 5.5 (Anthropic), 11 October 2026, from a suggestion of Cian Dorr; recorded by Claude Opus 5.5 (Anthropic), prompted by Cian Dorr, 11 October 2026.</p>

## Premises

- **Tame Rigidity.** Every weakly rigid relation, including a proposition, is rigid.
- **BF (relational types).** The Barcan Formula at every relational type, that is, at every type other than e.

## Conclusion

- **□BF (relational types).** Necessarily, BF holds at every relational type.

## Proof

The argument of tame-rigidity-and-barcan-imply-necessary-barcan, one relational type at a time: for relational $\sigma$, BF at $\sigma$ makes $\lambda x^\sigma\, .\,\top$ weakly rigid, Tame Rigidity at $\sigma\to t$ makes it rigid, and its inextensibility is $\Box$BF at $\sigma$.

## Sources

- **Dorr 11 Oct** — Cian Dorr, suggestion of 11 October 2026.

<p class='cert'>Record: <code>topics/classicism/results/tame-rigidity-and-bf-relational-imply-necessary-bf-relational.yaml</code></p>

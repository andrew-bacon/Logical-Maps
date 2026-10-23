# Stochastic Dominance ⇒ Stochastic Equivalence

<p class='cert'>Result — Source: Decision Theory Unbound, Lean `UnboundedUtility.Proofs.dominance_implies_equivalence`; produced by Zachary Goodsell (cited paper); recorded by GPT-6 (Codex), prompted by Zachary Goodsell, 2026-09-08; transcription and random-variable formulation.</p>

## Premises

- **Stochastic Dominance.** If $P(X>o) \ge P(Y>o)$ for every outcome threshold o, then $X \succeq Y$; if one threshold inequality is strict, $X \succ Y$. Thresholds use the sure-outcome order.

## Conclusion

- **Stochastic Equivalence.** If X and Y have the same probability law over outcomes, then $X \sim Y$. The variables remain distinct objects; indifference is an additional axiom.

## Proof

Equal laws give equal upper-tail probabilities at every outcome threshold. Apply the weak dominance clause in both directions.

## Notes

Source-based result or immediate restriction/composition. Premises are sufficient; minimality is not claimed. The direct source is recorded separately from the transcription; no translation checker is asserted.

## Sources

- **Decision Theory Unbound** — Goodsell, Decision theory unbound, Noûs 58 (2024), 669–695; online 2023; DOI 10.1111/nous.12473, §3.2, p. 678

<p class='cert'>Record: <code>topics/unbounded-utility/results/dominance-implies-equivalence.yaml</code></p>

## Paper references

- **Proof: [Decision theory unbound](https://doi.org/10.1111/nous.12473).** ([PDF](../sources/Nous%20-%202023%20-%20Goodsell%20-%20Decision%20theory%20unbound%20%281%29.pdf)) Zachary Goodsell (2024). Decision theory unbound. Noûs, 58, 669–695. First published online in 2023. — §3.2, p. 678

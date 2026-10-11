# Tame Rigidity ∧ BF ⇒ □BF

<p class='cert'>Result — Source: Misc., Lean `Classicism.Map.tame_rigidity_and_barcan_imply_necessary_barcan`; produced by Claude Fable 5.1 (Anthropic), 3 October 2026; recorded by Claude Opus 5.5 (Anthropic), 3 October 2026.</p>

## Premises

- **Tame Rigidity.** Every weakly rigid relation, including a proposition, is rigid.
- **BF.** The Barcan Formula at every type. The predicate formulation closes the formula schema using lambda abstraction.

## Conclusion

- **□BF.** Necessarily, the Barcan Formula holds at every type. The predicate formulation closes the formula schema using lambda abstraction.

## Proof

Apply Tame Rigidity at the type tuple $\bar\sigma$ to $Y:=\lambda\bar x\, .\,\top$. $\operatorname{Persistent}(Y)$ is $Y\le\lambda\bar x\, .\,\Box\top$, a theorem. Since $Y\le X$ is $\Box\forall\bar x\, .\,X[\bar x]$, $\operatorname{WeaklyInextensible}(Y)$ unfolds to $\forall X\, .\, (\forall\bar x\, .\,\Box X[\bar x])\to\Box\forall\bar x\, .\,X[\bar x]$, which is BF at $\bar\sigma$, and $\operatorname{Inextensible}(Y)$ is its necessitation. So BF makes $Y$ weakly rigid, Tame Rigidity makes it rigid, and its inextensibility is $\Box$BF at $\bar\sigma$. This for every type tuple gives the result.

## Notes

Tame Rigidity applied to the top relation: weak inextensibility of $\top$ is BF and its inextensibility is $\Box$BF. With it the map derives the failure of Tame Rigidity in finite-support-two-object-all-maps, where BF holds and $\Box$BF fails.

## Sources

- **Fable 3 Oct** — Claude Fable 5.1 (Anthropic), Classicism session of 3 October 2026, answering Cian Dorr's question about Tame Rigidity in the coalesced roots.

<p class='cert'>Record: <code>topics/classicism/results/tame-rigidity-and-barcan-imply-necessary-barcan.yaml</code></p>

## Paper references

- **Background: Possible Worlds Without Atomicity.** Sun, Christopher. Possible Worlds Without Atomicity. Unpublished draft, September 2026.. Tame Rigidity.

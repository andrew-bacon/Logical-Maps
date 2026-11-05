# Maximalism (signature Σ) ∧ Strong Possibility (pure) ⇒ ⊥

<p class='cert'>Result — Source: Misc.; produced by Cian Dorr, 20 October 2026, with two amendments by Claude Fable 5.1 (Anthropic), who verified the consistency premise in coalesced-definable-root; recorded by Claude Fable 5.1 (Anthropic), prompted by Cian Dorr, 20 October 2026.</p>

## Premises

- **Maximalism (signature Σ).** The Maximalism schema for the fixed nonlogical signature Σ: every closed identity of its language not provable in C(Σ) is false.
- **Strong Possibility (pure).** Each closed pure sentence consistent with Maximalist Classicism is possible under the distinctness-preserving modality.

## Conclusion

- **⊥.** These premises cannot all hold together.

## Proof

Suppose $\Sigma$ has a constant $c$ of type $t$. Let C5 be $\Box$ND and let $F:=\lambda p\, .\, (\Diamond p\land\Diamond\neg p)\land\mathrm{C5}\land\mathrm{Atomicity}\land\forall x\forall y\, .\, x=y$, a closed pure term of type $tt$: being contingent while $\Box$ND, Atomicity and "there is exactly one individual" hold. Let $\Psi:=\forall p\, .\,\neg\Diamond F(p)$, closed and pure.
(1) $\Psi$ is consistent with Maximalist Classicism (pure): it holds at the evaluation point of coalesced-definable-root, which satisfies Maximalism (pure) (see its write-up). In brief: at that root $\Box$ND fails, so nothing is $F$ there; and at a world where the side conditions of $F$ hold there is necessarily exactly one individual, so the sentence defining a root proposition is there the same proposition as a pure sentence, which is not contingent by $\Box$ND + Atomicity (type $t$) ⇒ No Pure Contingency.
(2) Strong Possibility (pure) therefore gives $\Diamond_{\ne}\Psi$, that is $\forall q\, .\,q\to\Diamond( \Diamond q\land\Psi)$. Suppose $\Diamond F(p_0)$ for some $p_0$. With $q:=\Diamond F(p_0)$ there is a world $w$ at which $\Psi$ and $\Diamond\Diamond F(p_0)$ hold, hence $\Diamond F(p_0)$ by 4; but $\Psi$ at $w$, instantiated at $p_0$, says $\neg\Diamond F(p_0)$. So $\forall p\, .\,\neg\Diamond F(p)$.
(3) $F(c)$ is a closed sentence of $\mathcal L(\Sigma)$ consistent with C($\Sigma$): the full S5 model over the two-element group with one individual, with $c$ true at one world and false at the other, satisfies it. Maximalism for $\Sigma$, in its possibility form, gives $\Diamond F(c)$, contradicting (2) at $p:=c$.
If the constant of $\Sigma$ has a relational type $\bar\sigma t$ instead, replace "contingent" in $F$ by "contingently universal", $(X\ne\top\land\Diamond X=\top)\lor(X=\top\land\Diamond X\ne\top)$: for a closed term $X=\top$ is the closed sentence $\forall\bar x\, .\,X\bar x$, non-contingent by the same route, and $F(c)$ is satisfied by the same two-world model with $c$ universal at one world only.

## Notes

Uses Maximalism for $\Sigma$ at the one sentence $F(c)$, and Strong Possibility (pure) at the one sentence $\Psi$, whose consistency with Maximalist Classicism is witnessed by a model rather than by a principle of the map. The conjunct $\forall x\forall y\, .\,x=y$ in $F$ is an amendment: without it the consistency of $\Psi$ would need every closed sentence with the individual constant of the model's signature, not only the pure ones, to be non-contingent under $\Box$ND + Atomicity. The argument does not reach Strong Possibility for $\Sigma$, whose consistency premise is stronger; whether Maximalism for $\Sigma$ is compatible with it stays open.

A different proof was given later and independently by GPT-6 Astra (OpenAI), prompted by Daniel Kodsi, 22–23 October 2026: Maximalism for $\Sigma$ splits the proposition that there is exactly one individual and the Fregean Axiom holds, refuting its atomhood, whose consistency with Maximalist Classicism (pure) Astra shows with a separate model; Strong Possibility (pure) then makes that atomhood true. With this incompatibility the conjecture that Strong Possibility for $\Sigma$ implies Strong Possibility (pure) became equivalent to the inconsistency of Strong Possibility for $\Sigma$; it was withdrawn on 29 October 2026 (see [[strong-possibility-signature-r]]).

## Revisions

- **2026-10-29** (Claude Opus 5.5 (Anthropic), prompted by Cian Dorr) — (minor) The notes' reference to the conjecture that Strong Possibility (signature Σ) implies Strong Possibility (pure) now says that it was withdrawn.
- **2026-10-24** (Claude Opus 5.5 (Anthropic), prompted by Cian Dorr) — (minor) Noted the later independent proof by GPT-6 Astra (OpenAI), prompted by Daniel Kodsi.

## Sources

- **Dorr 20 Oct** — Cian Dorr, argument of 20 October 2026.
- **Fable 20 Oct** — Claude Fable 5.1 (Anthropic), prompted by Cian Dorr, 20 October 2026, for the amendments and the model witnessing the consistency premise (coalesced-definable-root).

<p class='cert'>Record: <code>topics/classicism/results/maximalism-signature-incompatible-with-strong-possibility-pure.yaml</code></p>

## Paper references

- **Background: Classicism.** Bacon, Andrew, and Cian Dorr (2024). Classicism. In Peter Fritz and Nicholas K. Jones (eds), Higher-Order Metaphysics, Oxford University Press, pp. 109–190. The map was built from the draft dated 16 May 2023, 87 pages, which does not differ materially from the published version; all page, proposition and footnote locators in this map refer to that draft's numbering. — §2.6, pp. 41–42. Maximalist Classicism, its possibility form, and the distinctness-preserving modality.

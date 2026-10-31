# Rigid Comprehension ⇒ Tame Rigidity

<p class='cert'>Result — Source: Possible Worlds Without Atomicity (draft), Lean `Classicism.Map.rigid_comprehension_implies_tame_rigidity`; produced by Christopher Sun; recorded by Claude Opus 5.5 (Anthropic), prompted by Cian Dorr, 2 October 2026.</p>

## Premises

- **Rigid Comprehension.** Every relation, including a proposition, is coextensive with a rigid one.

## Conclusion

- **Tame Rigidity.** Every weakly rigid relation, including a proposition, is rigid.

## Proof

Lemma: coextensive weakly rigid relations are identical. Let $F$ and $G$ be weakly rigid with $F\equiv G$. If $F[\bar x]$ then $G[\bar x]$, and the weak persistence of $G$ gives $\Box G[\bar x]$. So $\forall\bar x\, .\,F[\bar x]\to\Box G[\bar x]$, and the weak inextensibility of $F$, instantiated at $G$, gives $F\le G$. Symmetrically $G\le F$. Together these say $\Box(F\equiv G)$, and necessarily coextensive relations are identical in C (Intensionality), so $F=G$. Now let $F$ be weakly rigid. Rigid Comprehension at the same type supplies a rigid $G$ coextensive with $F$. A rigid relation is weakly rigid, since T strips the leading boxes from both its conjuncts. By the lemma $F=G$, so $F$ is rigid.

## Notes

The lemma uses only the unboxed persistence of $F$ and $G$, so Rigid Comprehension makes every very weakly rigid relation rigid as well. With Rigid Comprehension ⇒ Weak Rigid Comprehension, this gives Sun's equivalence of Rigid Comprehension with Tame Rigidity plus Weak Rigid Comprehension.

## Revisions

- **2026-10-08** (Claude Opus 5.5 (Anthropic), at Cian Dorr's direction) — "Weakly rigid" now means weakly persistent and weakly inextensible (until then, persistent and weakly inextensible; Very Weak Rigid Comprehension retired); the proof's wording is adjusted to match. A weakly rigid relation is still persistent, so the mathematical content is unchanged.

## Sources

- **Possible Worlds Without Atomicity** — Christopher Sun, Possible Worlds Without Atomicity, draft of September 2026.

<p class='cert'>Record: <code>topics/classicism/results/rigid-comprehension-implies-tame-rigidity.yaml</code></p>

## Paper references

- **Origin: Possible Worlds Without Atomicity.** Sun, Christopher. Possible Worlds Without Atomicity. Unpublished draft, September 2026.
- **Background: Classicism.** Bacon, Andrew, and Cian Dorr (2024). Classicism. In Peter Fritz and Nicholas K. Jones (eds), Higher-Order Metaphysics, Oxford University Press, pp. 109–190. The map was built from the draft dated 16 May 2023, 87 pages, which does not differ materially from the published version; all page, proposition and footnote locators in this map refer to that draft's numbering. — §1.5, pp. 16–17. Intensionality and T.

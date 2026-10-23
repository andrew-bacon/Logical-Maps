# Rigid Comprehension ⇒ Weak Rigid Comprehension

<p class='cert'>Result — Source: Misc., Lean `Classicism.Map.rigid_comprehension_r_implies_weak_rigid_comprehension_r`; produced by Claude Opus 5 (Anthropic), prompted by Cian Dorr, 19 September 2026; recorded by Claude Opus 5 (Anthropic), prompted by Cian Dorr, 19 September 2026.</p>

## Premises

- **Rigid Comprehension.** Every relation, including a proposition, is coextensive with a rigid one.

## Conclusion

- **Weak Rigid Comprehension.** Every relation, including a proposition, is coextensive with a weakly rigid one, that is, with one that is weakly persistent and weakly inextensible.

## Proof

A rigid $Y$ is persistent by definition, and so, by T, weakly persistent. Its other conjunct, $\operatorname{Inextensible}(Y)$, is a necessitated conditional, so T strips the leading box and yields $\operatorname{WeaklyInextensible}(Y)$. Hence every rigid relation is weakly rigid, and the rigid coextension supplied by Rigid Comprehension already witnesses Weak Rigid Comprehension at the same type.

## Revisions

- **2026-10-08** (Claude Opus 5.5 (Anthropic), at Cian Dorr's direction) — "Weakly rigid" now means weakly persistent and weakly inextensible (until then, persistent and weakly inextensible; Very Weak Rigid Comprehension retired); the proof's wording is adjusted to match. A weakly rigid relation is still persistent, so the mathematical content is unchanged.

## Sources

- **BC does not imply RC** — Cian Dorr, Boolean Completeness does not imply Rigid Comprehension, draft of 30 July 2026, pp. 2 and 12, for the definitions; connecting argument original to this record.

<p class='cert'>Record: <code>topics/classicism/results/rigid-comprehension-r-implies-weak-rigid-comprehension-r.yaml</code></p>

## Paper references

- **Background: Boolean Completeness does not imply Rigid Comprehension.** Dorr, Cian. Boolean Completeness does not imply Rigid Comprehension. Unpublished draft in progress, 30 July 2026, 27 pages. All page, proposition and lemma locators for this source refer to that draft. Parts of the draft were drafted with AI assistance; its mathematical claims are attributed to the author. — pp. 2 and 12. Supplies the weak rigidity conditions; the draft records the slogan that rigidity is necessary weak rigidity.
- **Background: Classicism.** Bacon, Andrew, and Cian Dorr (2024). Classicism. In Peter Fritz and Nicholas K. Jones (eds), Higher-Order Metaphysics, Oxford University Press, pp. 109–190. The map was built from the draft dated 16 May 2023, 87 pages, which does not differ materially from the published version; all page, proposition and footnote locators in this map refer to that draft's numbering. — §1.5, p. 17. T for the fixed background modality.

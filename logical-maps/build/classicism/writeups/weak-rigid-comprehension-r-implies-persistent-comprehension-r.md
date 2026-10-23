# Weak Rigid Comprehension ⇒ Persistent Comprehension

<p class='cert'>Result — Source: BC does not imply RC (draft), Lean `Classicism.Map.weak_rigid_comprehension_r_implies_persistent_comprehension_r`; produced by Cian Dorr; recorded by Claude Opus 5 (Anthropic), prompted by Cian Dorr, 19 September 2026.</p>

## Premises

- **Weak Rigid Comprehension.** Every relation, including a proposition, is coextensive with a weakly rigid one, that is, with one that is weakly persistent and weakly inextensible.

## Conclusion

- **Persistent Comprehension.** Every relation, including a proposition, is coextensive with a persistent one.

## Proof

A weakly rigid relation $Y$ is persistent: apply its weak inextensibility to $\lambda\bar x\, .\,\Box Y[\bar x]$, whose hypothesis $Y[\bar x]\to\Box\Box Y[\bar x]$ holds by weak persistence and 4; this gives $Y\le\lambda\bar x\, .\,\Box Y[\bar x]$, which is $\operatorname{Persistent}(Y)$. So a weakly rigid coextension is already a persistent coextension.

## Notes

With the recorded implication from Persistent Comprehension to Actuality, this completes the converse of the implication from Boolean Completeness and Actuality, so Weak Rigid Comprehension is equivalent to their conjunction.

## Revisions

- **2026-10-08** (Claude Opus 5.5 (Anthropic), at Cian Dorr's direction) — "Weakly rigid" now means weakly persistent and weakly inextensible (until then, persistent and weakly inextensible; Very Weak Rigid Comprehension retired); the proof's wording is adjusted to match. A weakly rigid relation is still persistent, so the mathematical content is unchanged.

## Sources

- **BC does not imply RC** — Cian Dorr, Boolean Completeness does not imply Rigid Comprehension, draft of 30 July 2026, footnote on p. 12.

<p class='cert'>Record: <code>topics/classicism/results/weak-rigid-comprehension-r-implies-persistent-comprehension-r.yaml</code></p>

## Paper references

- **Proof: Boolean Completeness does not imply Rigid Comprehension.** Dorr, Cian. Boolean Completeness does not imply Rigid Comprehension. Unpublished draft in progress, 30 July 2026, 27 pages. All page, proposition and lemma locators for this source refer to that draft. Parts of the draft were drafted with AI assistance; its mathematical claims are attributed to the author. — footnote on p. 12. The footnote's opening observation, that weakly rigid properties are persistent, from which it obtains Actuality through Persistent Comprehension.

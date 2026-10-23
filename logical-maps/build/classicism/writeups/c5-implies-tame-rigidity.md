# □ND ⇒ Tame Rigidity

<p class='cert'>Result — Source: Possible Worlds Without Atomicity (draft), Lean `Classicism.Map.c5_implies_tame_rigidity`; produced by Christopher Sun; recorded by Claude Opus 5.5 (Anthropic), prompted by Cian Dorr, 2 October 2026.</p>

## Premises

- **□ND.** Necessarily, distinct things of any type are necessarily distinct.

## Conclusion

- **Tame Rigidity.** Every weakly rigid relation, including a proposition, is rigid.

## Proof

C5 gives BF at every type (via □BF and T) and 5; 4 is a theorem of C. Contraposing with $\neg X$ for $X$, weak inextensibility of $F$ is equivalent to $\forall X\, .\,\Diamond\exists\bar x\, .\,(F[\bar x]\land X[\bar x])\to\exists\bar x\, .\,(F[\bar x]\land\Diamond X[\bar x])$, and inextensibility to its necessitation. Suppose for contradiction that $F$ is weakly rigid but not rigid. A weakly rigid relation is persistent (see Weak Rigid Comprehension), so $F$ is not inextensible: $\Diamond\exists X\, .\,\bigl(\Diamond\exists\bar x\, .\,(F[\bar x]\land X[\bar x])\land\neg\exists\bar x\, .\,(F[\bar x]\land\Diamond X[\bar x])\bigr)$. By BF at the type of $X$ there is an $X$ such that $\Diamond\Diamond\exists\bar x\, .\,(F[\bar x]\land X[\bar x])$, hence by 4 $\Diamond\exists\bar x\, .\,(F[\bar x]\land X[\bar x])$, and also $\Diamond\neg\exists\bar x\, .\,(F[\bar x]\land\Diamond X[\bar x])$. Since $F$ is weakly inextensible, the former gives $\exists\bar x\, .\,(F[\bar x]\land\Diamond X[\bar x])$. For such $\bar x$, the persistence of $F$ (with T) gives $\Box F[\bar x]$, and 5 gives $\Box\Diamond X[\bar x]$. So $\Box(F[\bar x]\land\Diamond X[\bar x])$, and by K applied to the necessitated theorem $(F[\bar x]\land\Diamond X[\bar x])\to\exists\bar y\, .\,(F[\bar y]\land\Diamond X[\bar y])$, $\Box\exists\bar y\, .\,(F[\bar y]\land\Diamond X[\bar y])$, contradicting the second conjunct.

## Notes

The argument uses BF and 5 only at the evaluation point, together with T and 4.

## Revisions

- **2026-10-08** (Claude Opus 5.5 (Anthropic), at Cian Dorr's direction) — "Weakly rigid" now means weakly persistent and weakly inextensible (until then, persistent and weakly inextensible; Very Weak Rigid Comprehension retired); the proof's wording is adjusted to match. A weakly rigid relation is still persistent, so the mathematical content is unchanged.

## Sources

- **Possible Worlds Without Atomicity** — Christopher Sun, Possible Worlds Without Atomicity, draft of September 2026.

<p class='cert'>Record: <code>topics/classicism/results/c5-implies-tame-rigidity.yaml</code></p>

## Paper references

- **Origin: Possible Worlds Without Atomicity.** Sun, Christopher. Possible Worlds Without Atomicity. Unpublished draft, September 2026.
- **Background: Classicism.** Bacon, Andrew, and Cian Dorr (2024). Classicism. In Peter Fritz and Nicholas K. Jones (eds), Higher-Order Metaphysics, Oxford University Press, pp. 109–190. The map was built from the draft dated 16 May 2023, 87 pages, which does not differ materially from the published version; all page, proposition and footnote locators in this map refer to that draft's numbering. — §1.5, p. 17; §2.1, pp. 21–23. 4 in C; ND, B, 5 and BF.

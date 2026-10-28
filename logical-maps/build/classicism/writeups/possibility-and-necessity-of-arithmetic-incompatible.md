# Maximalism (pure) ∧ Necessity of Arithmetic ⇒ ⊥

<p class='cert'>Result — Source: Arithmetic is Necessary (2024 draft); produced by Zachary Goodsell; recorded by Claude Fable 5.1 (Anthropic), prompted by Cian Dorr, 20 September 2026.</p>

## Premises

- **Maximalism (pure).** Every closed pure identity not provable in C is false. The non-theorem condition is metalinguistic.
- **Necessity of Arithmetic.** Every arithmetical sentence is either necessarily true or necessarily false, given that possibly zero is not a successor and successor is injective on numbers, where the numbers are the finite cardinalities of properties of a type $\sigma$. One sentence for each type $\sigma$ and each arithmetical sentence at $\sigma$.

## Conclusion

- **⊥.** These premises cannot all hold together.

## Proof

Theorem 11 of the source, applied to C. The theorems of C are recursively enumerable, and C is consistent with $I$, since $I^*$ and hence $I$ hold in the full Henkin model with a countably infinite individual domain. So the arithmetical sentences $A$ with $C\vdash I\to A$ form a consistent, recursively enumerable extension of Peano arithmetic (the source's Lemma 1 supplies the axioms). By Gödel's first incompleteness theorem there is an arithmetical sentence $A$ for which neither $I\to A$ nor $I\to\neg A$ is a theorem of C, so $I\land A$ and $I\land\neg A$ are both consistent with C. Both are closed pure sentences, so Possibility Maximalism (pure) gives $\Diamond(I\land A)$ and $\Diamond(I\land\neg A)$. But the instance of the Necessity of Arithmetic at $A$ says $\Box(I\to A)$ or $\Box(I\to\neg A)$, and by K each disjunct contradicts one of the two possibilities.

## Notes

The source's theorem is general: the maximalization of any recursively enumerable extension of HK consistent with $I$ refutes some instance of the necessity schema. The record uses Possibility Maximalism (pure) directly; the equivalent Distinctness Maximalism form gives the same through the recorded equivalence. The argument is metatheoretic in two places, the recursive enumerability of C and Gödel's theorem, like the consistency side condition of Possibility Maximalism itself.

## Revisions

- **2026-10-16** (Claude Opus 5.5 (Anthropic), at Cian Dorr's direction) — The Necessity of Arithmetic is now a schema in the type $\sigma$ whose finite cardinalities are the numbers. The premise is stronger than before, and the proof goes through at $\sigma=e$ as before, with $I$ read as $I_e$.
- **2026-10-08** (Claude Opus 5.5 (Anthropic), at Cian Dorr's direction) — Distinctness Maximalism and Possibility Maximalism unified as Maximalism, with Distinctness the official form and Possibility a variant form; this record's premise changed from the Possibility principle to Maximalism. The proof is unchanged, the two forms being equivalent in C.

## Sources

- **Arithmetic is Necessary** — Zachary Goodsell, Arithmetic is Necessary, draft of 5 June 2024, §6, Theorem 11 and n. 14, pp. 24–26.
- **Fable 20 Sep** — Claude Fable 5.1 (Anthropic), prompted by Cian Dorr, 20 September 2026, for the consistency of C with $I$ (full-henkin-infinite-base).

<p class='cert'>Record: <code>topics/classicism/results/possibility-and-necessity-of-arithmetic-incompatible.yaml</code></p>

## Paper references

- **Proof: [Arithmetic is Necessary](https://philpapers.org/archive/GOOAIN.pdf).** Goodsell, Zachary William Lee. Arithmetic is Necessary. Draft dated 5 June 2024, 28 pages. Derives the necessity of arithmetic in the logic HKC (H plus K plus Countable Boolean Completeness) and shows that Boolean Completeness is inconsistent with the maximalization of any recursively enumerable extension of HK consistent with I, answering the question of Classicism, §2.6. Locators refer to this draft. — §6, Theorem 11 and n. 14, pp. 24–26

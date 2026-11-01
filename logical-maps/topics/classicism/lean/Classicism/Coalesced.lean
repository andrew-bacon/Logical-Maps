import Classicism.Semantics.IntensionalFacts

/-!
# Coalesced sums

Classicism, Appendix E (Definition E.2, Theorem 3.26), in a generality that covers the
members of the map's group `coalesced-sums`, for intensional action models.

The construction is a **collage**. The data are a family of intensional action models
`A k` on categories `C k`, indexed by a type `ι`; a functor `R : (Σ k, C k) ⥤ Type`, whose
value at an object `V` is the set of arrows from the new root `W₀` to `V`; and a monoid `M`
of arrows from `W₀` to itself, acting on `R` naturally (trivial except in the
substitution variant). The category has objects `Option (Σ k, C k)`, with `none` the root;
`Hom none none = M`, `Hom none (some V) = R.obj V`, `Hom (some V) none = ∅`, and the
component arrows otherwise. Appendix E's distinguished arrows are the representable case,
`R` restricted to component `k` being `Hom (W k) –`; the interpretation-arrow members take
`R V` to be the interpretations of a signature at `V`.

At the root, the individuals are a type `X` with a natural transport `X × R V → V^e`, and the
domain at a relational type is a chosen set of **landing** intensions, those whose transport
along every root arrow lies in the component's domain: all of them (fullest), the finitely
pinned ones, or the closed-term-definable ones. The general theorems:

* **transport**: along a root arrow `r : W₀ → V`, the value of a term is its value in `V`'s
  component, re-based at `V` with the constants transported along `r`;
* **root closure**: the collage is a model iff the chosen root domains are closed under the
  operations of the language at the root;
* as corollaries, Theorem 3.26 (each component is a truncation of the sum) and the
  possibility at the root of every sentence that holds at some component's base.

To be written (workstream W3); this file will import its parts.
-/

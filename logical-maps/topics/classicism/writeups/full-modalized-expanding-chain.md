# Full modalized domains: two-world chain with expanding individuals

Source construction: Andrew Bacon, *The Broadest Necessity* (2018), §7.5,
Definitions 7.12–7.14; draft of 25 July 2017, pp. 41–42. Concrete instance,
admissibility argument, and witnesses by OpenAI Codex, prompted by Andrew
Bacon, 28 October 2026. No Lean verification.

Take W = {w,v}, reflexivity and wRv, designated world w. The outer
individual set is {a,b}. Its identity PER at w is equality on {a}, and at v
is equality on {a,b}. Thus b exists only at v. At t use all of P(W), with
every proposition existing everywhere and equality at u given by agreement
on R(u). Use the full expanding function spaces of Definition 7.14.
Every relational constant of the map's signature denotes top.

An element of a function space is an outer function preserving the PERs
from some world onward. It exists at u when it preserves them from u
onward. Two such functions are identical at u when their values on related
arguments are identical at every world accessible from u. Quantification
at u ranges over the inner domain of entities existing at u.

## Why this instance is a model

The usual logical-relation induction for the lambda calculus applies to
these full function spaces. The propositional domain is total, avoiding
partial propositional domains of the problematic kind discussed at the
end of §7.5. Boolean operations preserve agreement on future cones.
For quantification, if F and G are related at u, then at every z accessible
from u they give the same truth value on every entity existing at z;
therefore their universal generalizations agree at every such z. The
quantifier thus preserves the PER at every world and exists everywhere.

Leibniz equality agrees with the PER on existing entities: preservation
gives one direction, and the property sending x to the set of worlds z
where x is related to a fixed a separates any pair not related at u.
That property preserves the PERs by symmetry, transitivity and persistence.
At t this yields the usual Kripke box.

H is sound at every world under existing assignments. For C's Logical
Equivalence schema, H-equivalent formulas agree at all future worlds under
all existing assignments. Iterating the function-space PER clause gives
equality of their lambda abstractions. Hence the relational reduct is a
model of C. This supplies the check for this instance, without claiming
that every arbitrary choice of partial propositional domains works.

## The failures

Let H:et send a to W and b to the empty proposition. This function exists
at w. The only individual there is a, and H(a) is necessary. At v, b
exists and fails H. Hence

$$\forall x^e\, .\,\Box Hx\quad\text{but}\quad
\neg\Box\forall x^e\, .\,Hx.$$

For Functionality, compare H with the constant-top property T. At w,
H(x) = T(x) for every existing individual x, but H and T differ at v on
b, so they are not identical at w. For Tractarianism use p = top: it
entails H(x) for every existing individual at w, but does not entail the
universal generalization. These are the same obstruction at input type e;
the model record uses BF failure and the existing implication chains to
avoid redundant verdicts.

B also fails: the proposition {w} is true at w and impossible at v.
No BF-at-t failure is claimed for this construction merely because its
individual domains expand.

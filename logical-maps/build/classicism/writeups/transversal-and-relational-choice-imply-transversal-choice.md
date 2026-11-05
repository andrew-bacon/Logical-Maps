# Transversal ∧ Relational Choice ⇒ Transversal Choice

<p class='cert'>Result — Source: Misc., Lean `Classicism.Map.transversal_and_relational_choice_imply_transversal_choice`; produced by Christopher Sun (the claim and the argument), 26 September 2026; recorded by Claude Opus 5.5 (Anthropic), prompted by Cian Dorr, 28 September 2026.</p>

## Premises

- **Transversal.** There is a property of properties that picks out exactly one property from each coextension class, that is, exactly one property coextensive with any given property.
- **Relational Choice.** Every serial binary relation has a functional subrelation.

## Conclusion

- **Transversal Choice.** Every equivalence relation, at any type including e, has a transversal, that is, a property with exactly one instance in each of its cells.

## Proof

Let $R^{\sigma\sigma t}$ be an equivalence relation, and write $[x]$ for its cell $\lambda z\, .\,(Rx)z$. Transversal at $\sigma$ gives $F^{(\sigma t)t}$ such that each property is coextensive with exactly one $F$-property. Relational Choice at types $(\sigma t,\sigma)$, applied to the serial relation $(UC)y:=Cy\lor\neg\exists z\, .\,Cz$, gives a functional $S$ with $(SC)y\to(UC)y$. Put $Gy:=\exists Y\, .\,FY\land(Y\equiv (Ry))\land(SY)y$. Existence: given $x$, let $Y_x$ be the $F$-property coextensive with $[x]$. It has the instance $x$, so the $y$ with $(SY_x)y$ satisfies $Y_xy$, hence $(Rx)y$. Then $[y]$ is coextensive with $[x]$ and so with $Y_x$, and $Gy$ holds through $Y_x$. Uniqueness: suppose $(Rx)y$ and $(Rx)y'$, with $Gy$ through $Y$ and $Gy'$ through $Y'$. Then $Y$ is coextensive with $[y]$, $[y]$ with $[x]$, $[x]$ with $[y']$, and $[y']$ with $Y'$; so $Y$ and $Y'$ are $F$-properties coextensive with $[x]$, and $Y=Y'$ by the uniqueness clause of Transversal. Now $(SY)y$ and $(SY)y'$, so $y=y'$ by functionality of $S$. Thus $G$ is a transversal of $R$.

## Notes

With the converse arrows from Transversal Choice to Transversal and to Relational Choice, Transversal Choice is equivalent to Transversal together with Relational Choice. The argument is the quotient argument of relational-choice-and-extensionality-imply-transversal-choice, with the $F$-representative of each cell in place of the cell itself; this is the step Relational Choice alone does not supply. Consequently Relational Choice implies Transversal Choice if and only if it implies Transversal.

## Sources

- **Sun 26 Sep** — Christopher Sun, 26 September 2026.

<p class='cert'>Record: <code>topics/classicism/results/transversal-and-relational-choice-imply-transversal-choice.yaml</code></p>

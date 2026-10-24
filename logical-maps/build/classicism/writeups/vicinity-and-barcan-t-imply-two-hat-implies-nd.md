# Vicinity ∧ BF (type t) ⇒ Two-hat necessity implies ND-necessity

<p class='cert'>Result — Source: The Bounds of Possibility (2021), Lean `Classicism.Map.vicinity_and_barcan_t_imply_two_hat_implies_nd`; produced by Claude Fable 5.1 (Anthropic), prompted by Cian Dorr, 14 October 2026, from Proposition D18 of The Bounds of Possibility, Appendix D; Vicinity in place of Actuality suggested by Christopher Sun; recorded by Claude Fable 5.1 (Anthropic), prompted by Cian Dorr, 14 October 2026.</p>

## Premises

- **Vicinity.** There is a true proposition that entails the possibility of each true proposition.
- **BF (type t).** If every proposition necessarily has a property, then necessarily every proposition has it.

## Conclusion

- **Two-hat necessity implies ND-necessity.** Whatever is two-hat necessary is ND-necessary: the distinctness-preserving modality agrees with its hat.

## Proof

Let $w$ witness Vicinity: $w$ is true and $\forall t(t\to\Box(w\to\Diamond t))$. First, $\Box_{\ne}p\leftrightarrow\Box(\Diamond w\to p)$ for every $p$: right to left take $q:=w$ in the definition of $\Box_{\ne}$; left to right, if $q$ is true with $\Box(\Diamond q\to p)$, Vicinity gives $\Box(w\to\Diamond q)$, so $\Box(\Diamond w\to\Diamond q)$ by S4 and $\Box(\Diamond w\to p)$. (Equivalently, by the ND-necessity form of Vicinity, $w$ entails every ND-necessary truth, and $\Diamond r$ is ND-necessary for true $r$; this is Proposition D18 of The Bounds of Possibility for $X=\Box$, with the Vicinity witness in place of the atom.) Second, B for $\Box_{\ne}$ at every true $p$: $\hat\Diamond p=\forall r(r\to\Diamond(\Diamond r\wedge p))$, so by the first step it suffices to show $\Box(\Diamond w\to\forall r(r\to\Diamond(\Diamond r\wedge p)))$, and by BF at type $t$ (with CBF) it suffices to show $\Box(\Diamond w\wedge r\to\Diamond(\Diamond r\wedge p))$ for each $r$. If $\Box\neg r$ this is vacuous. Otherwise $\Diamond r\wedge p$ is true, so Vicinity gives $\Box(w\to\Diamond(\Diamond r\wedge p))$, hence $\Box(\Diamond w\to\Diamond(\Diamond r\wedge p))$ by S4. Finally, if $\hat{\hat\Box}p$ with witness $q$, i.e. $q$ true and $\Box(\hat\Diamond q\to p)$, then B at $q$ gives $\Box(\Diamond w\to\hat\Diamond q)$, hence $\Box(\Diamond w\to p)$, i.e. $\Box_{\ne}p$.

## Notes

With Actuality in place of Vicinity the first step is Proposition D18 of The Bounds of Possibility; Christopher Sun suggested that Vicinity suffices wherever Actuality is applied only to ND-necessary truths, and the second step applies Vicinity to the truth $\Diamond r\wedge p$. BF at type $t$ cannot be dropped (the surjective paired-individuals model), nor Vicinity (the two-object retract full model, which has Actuality).

## Sources

- **Bounds of Possibility** — Cian Dorr, John Hawthorne, and Juhani Yli-Vakkuri, The Bounds of Possibility, Appendix D, Proposition D18, p. 408.
- **Dorr–Claude 14 Oct** — Cian Dorr and Claude Fable 5.1 (Anthropic), conversation of 14 October 2026 (transcript in the private notes).

<p class='cert'>Record: <code>topics/classicism/results/vicinity-and-barcan-t-imply-two-hat-implies-nd.yaml</code></p>

## Paper references

- **Proof: The Bounds of Possibility.** Dorr, Cian, John Hawthorne, and Juhani Yli-Vakkuri (2021). The Bounds of Possibility. Oxford University Press. Appendix D, Narrower Modalities in Higher-Order S4, pp. 400–409; locators follow the OUP corrected proof dated 9 May 2024. Its background logic HS4 (a primitive S4 operator over higher-order logic) is read into C by interpreting the primitive box as $\lambda p\, .\,p=\top$, under which every theorem of HS4 is a theorem of C. — Proposition D18. Stated there with Actuality; the Vicinity strengthening was suggested by Christopher Sun.

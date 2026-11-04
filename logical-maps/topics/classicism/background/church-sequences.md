# Church numerals and sequences

The iteration carrier $\alpha$ and recursion output $\tau$ are relational types
($\alpha,\tau\ne e$); sequence entries have any type $\sigma$, including $e$.
Type variables are schematic and remain outside object-language quantifiers and boxes.
Write $R(x,y)$ for $(Rx)y$, and similarly for longer argument lists.

These Church numerals are separate from the Fregean cardinalities on the
Arithmetic page. No equivalence between their Infinity principles is assumed.

## Church numerals

$$
\begin{aligned}
\nu^C_\alpha&:=(\alpha\to\alpha)\to\alpha\to\alpha,\\
0^C_\alpha&:=\lambda h x\, .\,x,\\
s^C_\alpha&:=\lambda n h x\, .\,(nh)(hx),\\
N^C_\alpha&:=\lambda n\, .\,\forall P^{\nu^C_\alpha\to t}\, .\,
 \bigl(P0^C_\alpha\land\forall m\, .\,Pm\to P(s^C_\alpha m)\bigr)\to Pn.
\end{aligned}
$$

The successor orientation agrees with Bacon's 2023 note. Church Numeral Infinity is

$$
\operatorname{ChInf}_\alpha:=
\bigl(\forall n\, .\,N^C_\alpha n\to s^C_\alpha n\ne0^C_\alpha\bigr)
\land\forall mn\, .\,
N^C_\alpha m\land N^C_\alpha n\land s^C_\alpha m=s^C_\alpha n\to m=n.
$$

The principle [[church-numeral-functional-recursion]] says

$$
\forall a^\tau g^{\tau\to\tau}\,\exists f^{\nu^C_\alpha\to\tau}\, .\,
f0^C_\alpha=a\land\forall n\, .\,
N^C_\alpha n\to f(s^C_\alpha n)=g(fn).
$$

It follows from $\Box\operatorname{ChInf}_\alpha$, with no choice assumption;
see [[necessary-church-numeral-infinity-implies-church-numeral-functional-recursion]].
The function is defined on the entire ambient type, but its successor equation
is restricted to $N^C_\alpha$.

## Sequences

Use a property of Church numerals as the accumulator:

$$
\begin{aligned}
B_\alpha&:=\nu^C_\alpha\to t,\\
L_{\alpha,\sigma}&:=(\sigma\to B_\alpha\to B_\alpha)\to B_\alpha\to B_\alpha,\\
\epsilon&:=\lambda Xp\, .\,p,\\
\operatorname{cons}(b,s)&:=\lambda Xp\, .\,(Xb)((sX)p),\\
\operatorname{Seq}_{\alpha,\sigma}(s)&:=
\forall P^{L_{\alpha,\sigma}\to t}\, .\,
\bigl(P\epsilon\land\forall br\, .\,Pr\to P(\operatorname{cons}(b,r))\bigr)\to Ps.
\end{aligned}
$$

This changes the accumulator $t$ used in the 2023 note. The change is
substantive: in a full one-world extensional model with infinitely many
individuals, $\Box\operatorname{ChInf}_{e\to t}$ holds, but cons for the
original $t$-accumulator is not injective on generated sequences. General
functional recursion for that original encoding also fails in this model.
See the sequence recursion write-up below for the counterexample.

This is a counterexample to the implication from Infinity at a fixed
carrier, not from the entire all-carriers Infinity schema: the model fails
$\operatorname{ChInf}_t$. The result proved here uses
$B_\alpha=\nu^C_\alpha\to t$ and requires only
$\Box\operatorname{ChInf}_\alpha$ at the displayed carrier.

The principle [[sequence-functional-recursion]] says

$$
\forall a^\tau g^{\sigma\to\tau\to\tau}\,
\exists f^{L_{\alpha,\sigma}\to\tau}\, .\,
f\epsilon=a\land\forall bs\, .\,
\operatorname{Seq}_{\alpha,\sigma}(s)\to
f(\operatorname{cons}(b,s))=(gb)(fs).
$$

It follows from the same $\Box\operatorname{ChInf}_\alpha$;
see [[necessary-church-numeral-infinity-implies-sequence-functional-recursion]].
No Infinity assumption at the entry type $\sigma$ or output type $\tau$ is needed.

## Positional observations and constructors

Abbreviate $0^C_\alpha,s^C_\alpha,N^C_\alpha$ by $0,s,N$. For $P:\sigma\to t$ put

$$
\begin{aligned}
E&:=\lambda n\, .\,\bot,\\
H_P&:=\lambda b A n\, .\,
 (n=0\land Pb)\lor\exists m\, .\,Nm\land n=sm\land Am,\\
O_P(u)&:=(uH_P)E.
\end{aligned}
$$

Under unboxed $\operatorname{ChInf}_\alpha$:

$$
\begin{aligned}
(O_P(\epsilon))n&\leftrightarrow\bot,\\
(O_P(\operatorname{cons}(b,u)))0&\leftrightarrow Pb,\\
Nn&\to\bigl((O_P(\operatorname{cons}(b,u)))(sn)\leftrightarrow(O_P(u))n\bigr).
\end{aligned}
$$

The nonzero-successor clause gives the second equation; both Infinity clauses
give the third. These are ordinary biconditionals, not inferred identities.
Induction shows that agreement of all property observations at natural positions
implies identity of generated sequences. At position zero use the property
$\lambda x\, .\,b=x$ to recover the head; successor positions recover the tail's
observations. Consequently cons is injective on generated sequences and never
equals $\epsilon$. This uses Church application and induction, not a sequence
recursion theorem. The full induction is in the sequence result's write-up.

## The modal conversion

For either recursion problem let $S$ be the least relation containing its base
pair and closed under its recursion step. Without Infinity, minimality gives
its base and closure laws, and $S(z,u)\to\Box S(z,u)$: the relation
$\lambda zu\, .\,\Box S(z,u)$ is closed by necessitating those logical laws.
Induction gives totality on the generated inputs. Infinity gives functionality;
boxed Infinity gives necessary functionality by necessitating the conditional
theorem, not a proof with an undischarged hypothesis.

For $\tau=\rho_1\to\cdots\to\rho_k\to t$, including $k=0$, define

$$f:=\lambda z\lambda\vec x\, .\,\forall u^\tau\, .\,S(z,u)\to u(\vec x).$$

If $S(z,u)$, persistence and necessary functionality give
$\Box\forall\vec x\, .\,u(\vec x)\leftrightarrow(fz)(\vec x)$.
Intensionality yields $fz=u$, giving both recursion equations.

**Source and verification.** Andrew Bacon, *Notes for Zach* (25 March 2023),
circulated as *Sequences in Classicism*, §§1–3, supplies the background Church
definitions and least-relation construction. The explicit boxed assumptions,
revised accumulator and positional-observation proof were developed in the
2 November 2026 discussion with Codex (OpenAI), prompted by Andrew Bacon.
The Lean definitions are in `Background/ChurchSequences.lean` and
`Principles/Recursion.lean`; `Certified/ChurchSequences.lean` checks the
constructor proof. Complete functional-recursion derivations are now available
in the modules described below.

**Lean derivation update, 4 November 2026.** Codex (OpenAI), prompted by Andrew
Bacon, formalized both functional-recursion implications in
`Background/ChurchRecursion.lean`, certified in `Certified/ChurchRecursion.lean`
and lifted to all relational output types in `Results/ChurchRecursion.lean`.
All 22 new lemmas pass the Equivalence and relational type audits. The full
Classicism build and certificate audit also passed and marked both implications
`lean: verified`.

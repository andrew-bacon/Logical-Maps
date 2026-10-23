# Lottery algebra: isolated actual point

**Construction:** Andrew Bacon, *Arbitrarily Large Models of Classicism with □Rigid Comprehension, Intensional Choice and Mathematical Possibilism*, handout supplied 19 October 2026. **Transcription and supplementary deductions:** OpenAI Codex, 19 October 2026. No independent checker or Lean verification is claimed.

## Construction and evaluation

Work in ZFC. Choose a strong limit cardinal μ > ω with cf(μ) = ω. For example μ = beth_ω works. Choose one representative B_i of every isomorphism class of nontrivial complete Boolean algebras of size less than μ. Let B = ∏_i B_i and A = 2 × B. Equivalently, A is the algebra of regular open downsets of the disjoint union of an isolated point ∗ and the nonzero parts of the B_i, ordered by Boolean refinement within each component. The cloud W_c is the union of those components. Accessibility sends ∗ to all points and a cloud point to its refinements.

For a proposition a, write π(a) for its cloud part. Necessity satisfies

$$\pi(\Box a)=\pi(a),\qquad *\in\Box a\ \Longleftrightarrow\ a=W.$$

In product coordinates, $\Box(\epsilon,b)=(\epsilon\wedge[b=1],b)$. This operator preserves arbitrary meets and is S4.

The individual domain is ω. The proposition domain is A. Identity at e is literal equality; at t, a ~_v b means agreement at every R-successor of v. Recursively set

$$f\sim_v g\ \Longleftrightarrow\ \forall u\,(Rvu\Rightarrow\forall x,y\,(x\sim_u y\Rightarrow fx\sim_u gy)).$$

The function domain contains precisely the functions self-related everywhere. Retain only types allowed by the map (e, t, and function types ending in t). Application and abstraction have their usual interpretations; Boolean connectives act in A; universal and existential quantifiers are meets and joins over the type domains; identity denotes the set of points where the corresponding relation holds. The evaluation point is ∗. If a signature expansion is required, interpret every relational constant as top; no signature properties are inferred from that choice in this record.

The handout's §4 proves that identity values are regular open, logical constants inhabit the domains, and abstraction preserves the logical relations. It verifies β, η, Leibniz's law, the quantifier rules and Logical Equivalence, hence Classicism. Restricting to admitted relational types leaves the recursive domains at those types unchanged.

## Decoupling

For a tuple x let ε(x,y) be the cloud part of its identity value. A relation F is exactly a pair (S,h), where its actual extension S is an arbitrary subset of the tuple domain and its cloud profile h satisfies

$$\varepsilon(x,y)\wedge h(x)\le h(y).$$

Indeed define $F(x)=h(x)\cup\{*:x\in S\}$. At ∗ identity is literal, so there is no restriction on S; in the cloud the displayed condition is exactly preservation of the logical relation. Consequently actual quantification over relations represents all external relations, and actual cardinal comparisons are genuine external cardinal comparisons. This is the handout's §5.

## Necessary Rigid Comprehension

Given S put $\chi_S(z)=\bigvee_{y\in S}\varepsilon(y,z)$. Transitivity of ε makes this profile extensional. Decoupling supplies $\widehat S=(S,\chi_S)$. For any cloud-extensional h, the inequality χ_S ≤ h is equivalent to h being top on S. This is precisely the equivalence between necessary inclusion of $\widehat S$ in Y and every actual instance of $\widehat S$ necessarily being Y, required by rigidity at ∗. In the cloud necessity is the identity, so every relation is rigid. Thus each relation has a coextensive rigidification at ∗, and can serve as its own rigidification in the cloud. Every RC instance and its box have value top (handout §6).

## Necessary Intensional Choice

For F let $e=\bigvee_x h_F(x)$. Choose a maximal antichain of cloud conditions b_k below values h_F(x_k), with join e, and put

$$g(y)=\bigvee_k(b_k\wedge\varepsilon(x_k,y)).$$

This is cloud-extensional and pointwise below h_F. On b_k, x_k is a G-instance and every G-instance is identical to it. Therefore the cloud value of unique instantiation includes e. At ∗ choose a singleton S contained in the actual extension of F if that extension is nonempty, and otherwise choose the empty set. Decoupling gives G = (S,g), necessarily included in F. If F is necessarily instantiated at ∗, e is the entire cloud and S is a singleton, so G is necessarily uniquely instantiated. In the cloud, the same witness establishes IC on e, the value of its antecedent. Hence IC and □IC have value top (handout §7). The maximal-antichain choice uses ZFC.

## Mathematical Possibilism and size

There are at most μ factors, giving |B| ≤ μ^μ = 2^μ. For an increasing cofinal sequence μ_n < μ, the factors include the pairwise nonisomorphic algebras P(μ_n). Their product has size ∏_n 2^{μ_n} = 2^μ. Thus |A| = 2^μ, and μ^ω = 2^μ.

Pierce's theorem states that every infinite complete Boolean algebra C satisfies |C|^ω = |C| (R. S. Pierce, “A note on complete Boolean algebras”, Proc. Amer. Math. Soc. 9 (1958), 892–896; also Comfort and Hager, Pacific J. Math. 40 (1972), 541–545). Consequently no complete Boolean algebra has size in [μ,2^μ): such a cardinal ν would satisfy ν^ω ≥ μ^ω = 2^μ > ν.

At ∗, decoupling identifies internal completeness with external completeness and internal relation-based injections with external injections. A complete Boolean algebra that is finite or strictly smaller than A therefore has size < μ. A nontrivial one is isomorphic to a factor B_i, realized by the interval below its component proposition W_i. The degenerate algebra is realized below bottom. Each realizing proposition is different from top; the required isomorphism is represented by an actual relation. This proves MP as defined by the accompanying principle entry (handout §8).

**Convention:** “small” means finite or strictly fewer elements than there are propositions. The handout distinguishes this from the non-strict appendix formulation and explains that the latter fails here. MP is an actual truth, not a boxed verdict. Its cloud failure is discussed in the handout, but no new boxed-MP node is introduced by this contribution.

## Supplementary verdicts

**□BF.** For every type and predicate F,

$$\llbracket\forall x\,\Box Fx\rrbracket=\bigwedge_{d\in D^\sigma}\Box(Fd)=\Box\bigwedge_{d\in D^\sigma}Fd=\llbracket\Box\forall x\,Fx\rrbracket.$$

Every closed BF instance has value top, hence so does its box.

**Failure of Atomicity.** The completion of countable Cohen forcing is an atomless complete Boolean algebra of size at most 2^ω < μ. It occurs as a factor. Its component W_i is nonzero but the interval below it is atomless, so there is no propositional atom below W_i at ∗. A single failed type instance refutes the map's schema.

**Actuality.** The proposition {∗} is true and lies below every actually true proposition. It witnesses Actuality. In particular the algebra is not atomless: {∗} itself is an atom. This distinguishes failure of Atomicity from Atomlessness.

## Scope of this contribution

The model record cites the supplied paper proofs and adds the deductions above. The original PDF and TeX are not bundled into the public source tree. The original handout's structural-CH remark relies on a transfer argument not reproduced there; no CH verdict is claimed here. Generated consequences of the recorded verdicts are left to the map's existing implication rules.

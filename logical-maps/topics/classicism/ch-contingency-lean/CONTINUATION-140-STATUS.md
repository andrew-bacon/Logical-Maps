# Checkpoint 140: Hartogs closed-segment bounds discharged

728/743 target certificates pass. The historical pending count falls from 16 to 15.
This batch completes HartogsPairing02 and adds six new certificates across three modules.
Baseline: full checkpoint 138. Next checkpoints: source 141 / full 142.

## Result

Both original closed-segment bounds are proved: every closed initial segment of H(N) embeds into N, and every closed initial segment of H(H(N)) embeds into H(N). NaturalCHClosedSegments is now a theorem from LowerPeano e and the original RC instances for predicates and binary relations on H(N). No rigidity premise is needed for these bounds.

natural_CH_contingency_closedBounds removes NaturalCHClosedSegments from the checkpoint-138 CH theorem. The regular-open completion premise was already discharged in checkpoint 138. Only ONE mathematical deferral remains: Rigid LowerNat. Both the order-type and subset-cardinality formulations of CH contingency retain their checked conclusions. No real-number structure is constructed.

## Proof and non-circularity

1. The existing hartogs_closedSegment_embeds source proof was already available but its certificate was pending. It extends the certified open-segment embedding by one point, using a pairing relation and two distinct base elements. Its statement and source proof are unchanged; its certificate driver now uses the established deep-split translator. The certificate and fresh-import audit pass.
2. closedSegments_of_pairing_and_two eliminates the pairing and two-point witnesses at a generic type before substitutions.
3. hartogs_pairing_and_two derives the first closed bound, invokes the CERTIFIED conditional pairing theorem for H(A), and transports two distinct points along the existing embedding A -> H(A). It does not assume the second closed bound.
4. iterated_hartogs_closedSegments applies the generic one-point extension result again, now to H(A). Thus first bound -> pairing/two points on H(A) -> second bound, without circular dependence on either deferred premise.
5. lowerNat_pairing_and_two supplies LowerPair and zero/successor-of-zero from LowerPeano. natural_hartogs_closedSegments specializes the generic result to the exact two bounds consumed by NaturalCHClosedSegments.
6. natural_CH_contingency_closedBounds supplies those proved bounds to the previous endpoint. The RC instances are extracted from the EXISTING NaturalNegativeRC bundle by box elimination. No extra RC instance or principle is added by this batch.

## Exact final assumptions

The final theorem takes K,L with StronglyInaccessible K L; MPAt at the two explicit regular-open carrier types (predicates on countable-bit and double-Hartogs Cohen conditions); DraftBoxInfinity e; NaturalPositiveRC and NaturalNegativeRC; the boxed predicate-on-Cohen-conditions RC instance already introduced in checkpoint 138; the original unboxed IC instances in NaturalCHChoice; and Rigid LowerNat.

The only remaining mathematical obligation beyond the original principles is that last rigidity premise. There are no regular-open, closed-segment, pairing, surjection, or stable-index witness assumptions in the final theorem. The full RC/IC schemes supply the displayed finite instances. Do not claim an unconditional proof before natural rigidity is discharged.

## Verification

All six new source/gate/type checks, seven certificate checks, axiom audits and fresh imports pass. Exported certificate axioms are exactly propext and Quot.sound. Checked and VerifiedCheckpoint pass with cached dependencies. The same 15 OTHER historical pending records are unchanged; no historical target was silently removed or renamed.

All prior mathematical Lean sources, including HartogsPairing.lean, RegularOpenCH.lean and NaturalOrderTypeCH.lean, are unchanged. The only modified prior Lean files are the three aggregate import files and the HartogsPairing02 certificate driver (monolithic derive replaced by the already-established deep-split derive). Both translators are unchanged. CHECKPOINT-140-AUDIT.json verifies these facts against checkpoint 138 and contains the successful certificate sizes, conversion-lemma counts, times, memory peaks and hashes.

A missing type annotation in the new natural two-point existential was corrected before source acceptance. No new axiom, sorry/admit, checker change, statement weakening or increased budget. Guards remain 7 GiB RSS and 900 seconds. No clean historical rebuild or FullyCertified pass is claimed; 15 historical certificate targets remain separately tracked.

## Next work

Prove rigidity of LowerNat from the original boxed infinity/RC/IC principles actually available, then supply it to natural_CH_contingency_closedBounds. Inspect the definition of LowerNat and the existing modal/number-rigidity lemmas before choosing a proof route. Do not confuse necessary distinctness of natural numbers (already available) with rigidity of the natural-number predicate (still deferred).

Source checkpoint 139 and full checkpoint 140 preserve the batch. The full archive includes compiled proofs, source checks, logs, audits and recovery instructions.

import Proof.SourceAssembly.SourceLoop

/-! # The refill step: `SourceTrace._hrefill` at one loop point, from the prologue clear

**Consumer.** `RCFive.Source.SourceTrace._hrefill` (`closeout-five-checks-20260921/RCFiveSourceTrace.lean:196`):
for every `j` and EVERY family output `Z`,
`Step family (fuel j) (H j) (A j) (outH j) (outA j Z) → MaskFamilyCode.Prepared refillCode (ds (j+1)) refillCost
(outH j) (H (j+1)) (pad reserve ∘ outA j Z) (padded (j+1))`, where
`outA j Z = install app (install enc (install slots (A j) (r_outputT … Z)) E) T`.

**What this module proves.** The refill prologue is `clear ; rest`, with `clear` the H1 clear docked on the clear
set (`SourceClearBound.clear_on_layout`). Its exit does not depend on `Z`: the family writes `Z` only on `slots`,
and `slots` lies inside the clear set, so the clear's exit is
`install clearSlots (pad reserve ∘ base) blank` with the `Z`-free `base = install app (install enc (A j) E) T`
(`absorb`). The clear's premise (every clear-set word and head `≤ Rc`) comes from the family step itself
(`dirty_bound`), given the loop point's dirt bound `|A j x| ≤ Rc`, `H j x + fuel j + 1 ≤ Rc` on the clear set.
`refill_step` then closes `_hrefill`'s conclusion from `SourceLoop.cycle_prepared_all`'s first conjunct
(`∀` prologue runs reaching the prologue exit), one `Z`-free `rest` run, and `prepared_mono` (the
`refillCost` bound).

**Paper.** The refill re-enters ONE fixed machine after an arbitrary callee exit (`paper.tex:4280-4290`); the
clear is paid inside the call (`:721-733`). **Budget**: `4Rc+7` for the clear, TABLE class
(`SourceCleanupClass.perCall_class`); `rest` is charged by its own run.
-/
section
set_option autoImplicit false
set_option maxRecDepth 120000
set_option warningAsError true

open NearCubicWires LocalBitMultitape ExtDecompositionBatch RepairOrdinary RepairRepresentation
open RepairOrdinary.RecoveryRootRound RepairSource.VerifierDecoding SourceInterfaces
open PCJ9eff70d512234a4c_Fixed PCJd4d1d9d7d1fa4313_Production PCJc4297ab269d8423a_Source
namespace NearCubicWires.SourceConstruction.Refill
noncomputable section

/-- An `install`'s value at `x` reads its ambient only at `x`. -/
theorem install_at {t u : Nat} (s : Fin t → Fin u) (W W' : Fin u → List Bool) (R : Fin t → List Bool)
    (x : Fin u) (h : W x = W' x) : install s W R x = install s W' R x := by
  simp only [install]
  cases RecoveryFocus.pick s x <;> simp [h]

/-- Off the family slots, the family's output is the `Z`-free ambient. -/
theorem out_off_slots {t1 t2 t3 u : Nat} (slots : Fin t1 → Fin u) (enc : Fin t2 → Fin u)
    (app : Fin t3 → Fin u) (B : Fin u → List Bool) (Y : Fin t1 → List Bool)
    (E : Fin t2 → List Bool) (T : Fin t3 → List Bool) (x : Fin u) (hs : ∀ i, slots i ≠ x) :
    install app (install enc (install slots B Y) E) T x = install app (install enc B E) T x := by
  apply install_at
  apply install_at
  exact install_other slots B Y x hs

/-- `Prepared` is monotone in its fuel (its last conjunct is a `≤`). -/
theorem prepared_mono {mask : MaskProducer} {selector : CyclicChoice.Laws} {a : DecompositionAlgorithm}
    {printer : WilliamsAlgorithm} {packet : PacketWriter selector a}
    {rows : RowProducer selector a printer} {U : Nat} (p : MaskFamilyCode mask packet rows U)
    (ds : List P1TopDownPaidReusable.Datum) {fuel fuel' : Nat} (hf : fuel ≤ fuel')
    {H H' : Fin U → Nat} {A A' : Fin U → List Bool}
    (h : p.Prepared ds fuel H H' A A') : p.Prepared ds fuel' H H' A A' := by
  obtain ⟨r, layout, facts, caps, good, hds, poolReserve, familyReserve, poolH, poolA,
    ambientH, ambientA, seedFuel, setupLoadFuel, finishFuel, rewindCap, descriptorReserve,
    seed, setup, cap, heads, bank, finish, bound⟩ := h
  exact ⟨r, layout, facts, caps, good, hds, poolReserve, familyReserve, poolH, poolA,
    ambientH, ambientA, seedFuel, setupLoadFuel, finishFuel, rewindCap, descriptorReserve,
    seed, setup, cap, heads, bank, finish, bound.trans hf⟩

/-- The padded length of a word. -/
theorem pad_length_le (c R : Nat) (w : List Bool) (hc : c ≤ R) (hw : w.length ≤ R) :
    (ZeroPadding.pad c w).length ≤ R := by
  simp only [ZeroPadding.pad, List.length_append, List.length_replicate]
  omega

end
end NearCubicWires.SourceConstruction.Refill
end

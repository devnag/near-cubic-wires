import Proof.SourceAssembly.SourceSkelChain

section
set_option autoImplicit false
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unusedVariables false

open NearCubicWires NearCubicWires.ComponentwisePolynomial NearCubicWires.RepairOrdinary.CompetitorRawFieldEmit NearCubicWires.RepairOrdinary.CloseoutRowsOriginalSchedule LocalBitMultitape ExtDecompositionBatch RepairOrdinary RepairRepresentation SourceInterfaces RepairSource RepairSource.CloseoutFinal P1TopDown RepairSource.VerifierDecoding RecoveryRootRound RecoveryExecution CloseoutRowsEstimator CloseoutRowsEstimatorCoefficients CompetitorSelectedCount MatrixScoreBatch CompetitorCountMask SupplierPipeline SupplierEstimator SupplierPrime CanonicalFourfoldRowProgram CloseoutRawRows C10ExternalRowLoop C10ThresholdNaturalRowPrint C10ThresholdParityRow C10ThresholdEstimateRowJoin CloseoutFinalC10RowAnswerWord P1Closure P1TopDownPaidReusable P1TopDownPaidReusableReserves P1TopDownPaidBinaryReserves
open PCJ1fef9807c6954e94_Native
open PCJ9eff70d512234a4c_Fixed PCJd4d1d9d7d1fa4313_Production
open PCJc4297ab269d8423a_Source
namespace NearCubicWires.SourceSkeleton
noncomputable section
attribute [local irreducible] P1TopDownPaidPayload.tapes

section good
variable {mask : MaskProducer} {selector : CyclicChoice.Laws}
  {packets : PCJc4297ab269d8423a_Source.PacketLibrary selector}
  {rows : PCJc4297ab269d8423a_Source.RowLibrary selector}
  {sources : EightSources} {gamma : Real} {p : Parameters sources gamma} {k r scratch : Nat} {ph : Phase}
  (code : RCFive.Source.SourceCode mask selector packets rows sources p k r scratch ph) (b : Nat) {Atom : Type}
  (vd : RCFive.Source.CallValues Atom code.sourceTapes)

/-- `_hrefill`'s `family`: the row family on the slots ; the entry emitter on `enc` ; the append on `app`. -/
abbrev famOf := Composition.machine (RecoveryFocus.machine code.slots (f_machine code.a))
  (Composition.machine (RecoveryFocus.machine code.enc e_machine)
    (RecoveryFocus.machine code.app CloseoutFinalC10SingleAppend.machine))

/-- `_hrefill`'s `fuel j` (the call's family fuel). -/
abbrev fuelOf (j : Nat) : Nat :=
  f_budget code.a (vd.S j) (vd.rowWidth j) b (vd.xs j).length + 1 +
    (2 * vd.D j + 4 + 1 + (2 * e_emitCost b + 2) + 1 +
      CloseoutFinalC10AppendPositioning.budget b (vd.phasePrefix ++ vd.entries.take j).length)

/-- `_hrefill`'s `outH j` at the call's start heads `H`. -/
abbrev outHOf (j : Nat) (H : Fin code.sourceTapes → Nat) : Fin code.sourceTapes → Nat :=
  dockH code.slots H (r_outputH code.a (vd.ds j) (vd.S j) (vd.R j) (vd.B j) (vd.rowWidth j) (vd.xs j))

/-- `_hrefill`'s `outA j Z` at the call's start bank `A`. -/
abbrev outAOf (j : Nat) (A : Fin code.sourceTapes → List Bool) (Z : Fin 10 → List Bool) :
    Fin code.sourceTapes → List Bool :=
  install code.app
    (install code.enc (install code.slots A
      (r_outputT code.a (vd.ds j) (vd.S j) (vd.R j) (vd.B j) (vd.rowWidth j) b (vd.xs j) Z))
     (e_bank b ⟨vd.coefficient j, vd.total j, vd.denominator j⟩ (vd.D j) (vd.cap j)
       (ZeroPadding.pad (vd.D j) (Stream.entryWord b ⟨vd.coefficient j, vd.total j, vd.denominator j⟩))))
    (CloseoutFinalC10AppendPositioning.tapes b (vd.D j) (vd.logSize j) (vd.resetSize j)
      ⟨vd.coefficient j, vd.total j, vd.denominator j⟩
      ((vd.phasePrefix ++ vd.entries.take j) ++ [⟨vd.coefficient j, vd.total j, vd.denominator j⟩]))

/-- `_hrefill`'s `reserve`. -/
abbrev reserveOf : Fin code.sourceTapes → Nat := fun i =>
  if (PCJda54a286946142d3_BranchPhases.offset sources p k r + 1155) ≤ i.val then vd.reserveSize else 0

/-- The family input on the slots at call `j` (`_hA`'s right side). -/
abbrev inTOf (j : Nat) : Fin (r_tapes code.a) → List Bool := fun i =>
  r_inputT code.a (vd.ds j) (vd.S j) (vd.R j) (vd.B j) (vd.rowWidth j) b (vd.xs j).length i

/-- **What `_hrefill` demands between call `j` and call `j+1`** (`A'` is the next call's UNPADDED bank), plus the next
family input heads on the slots (`_hH` at `j+1`). -/
def goodOf (j : Nat) (H : Fin code.sourceTapes → Nat) (A : Fin code.sourceTapes → List Bool)
    (H' : Fin code.sourceTapes → Nat) (A' : Fin code.sourceTapes → List Bool) : Prop :=
  (∀ Z, Step (famOf code) (fuelOf code b vd j) H A (outHOf code vd j H) (outAOf code b vd j A Z) →
    MaskFamilyCode.Prepared code.refillCode (vd.ds (j+1)) vd.refillCost (outHOf code vd j H) H'
      (fun i => ZeroPadding.pad (reserveOf code vd i) (outAOf code b vd j A Z i))
      (fun i => ZeroPadding.pad (reserveOf code vd i) (A' i))) ∧
  (∀ i, H' (code.slots i) = r_inputH code.a (vd.ds (j+1)) (vd.S (j+1)) (vd.R (j+1)) (vd.B (j+1)) (vd.xs (j+1)).length i)

/-- The source code's slots are injective (`_hs`). -/
theorem slots_injective : Function.Injective code.slots := fun i i' h => Fin.ext (by
  have h1 := code._hs i; have h2 := code._hs i'; have h3 := congrArg Fin.val h; omega)

variable {N : Nat} {Inv : Nat → (Fin code.sourceTapes → Nat) → (Fin code.sourceTapes → List Bool) → Prop}

/-- The per-call values with the chain's banks. -/
abbrev chainVals (seam : SeamSpec N (fun _ => 0) code.slots (inTOf code b vd) Inv (goodOf code b vd))
    (H0 : Fin code.sourceTapes → Nat) (A0 : Fin code.sourceTapes → List Bool) :
    RCFive.Source.CallValues Atom code.sourceTapes :=
  { vd with
    H := fun j => (callChain N (fun _ => 0) code.slots (inTOf code b vd) Inv (goodOf code b vd) seam H0 A0 j).1
    A := fun j => (callChain N (fun _ => 0) code.slots (inTOf code b vd) Inv (goodOf code b vd) seam H0 A0 j).2 }

/-- The chain's re-padding at the zero reserve is the identity. -/
theorem pad_zero_fun (A : Fin code.sourceTapes → List Bool) :
    (fun x => ZeroPadding.pad ((fun (_ : Fin code.sourceTapes) => 0) x) (A x)) = A :=
  funext fun x => ZeroPadding.pad_zero (A x)

/-- **`_hrefill` at the chain's banks** (verbatim field text at `values := chainVals …`). -/
theorem hrefill_of_chain (seam : SeamSpec N (fun _ => 0) code.slots (inTOf code b vd) Inv (goodOf code b vd))
    (H0 : Fin code.sourceTapes → Nat) (A0 : Fin code.sourceTapes → List Bool) (h0 : Inv 0 H0 A0)
    (hN : vd.entries.length ≤ N)
    (vv : RCFive.Source.CallValues Atom code.sourceTapes) (hv : vv = chainVals code b vd seam H0 A0) :
    let a := code.a
    let sourceTapes := code.sourceTapes
    let slots := code.slots
    let enc := code.enc
    let app := code.app
    let refillCode := code.refillCode
    let ds := vv.ds
    let xs := vv.xs
    let S := vv.S
    let R := vv.R
    let B := vv.B
    let rowWidth := vv.rowWidth
    let total := vv.total
    let denominator := vv.denominator
    let D := vv.D
    let cap := vv.cap
    let logSize := vv.logSize
    let resetSize := vv.resetSize
    let coefficient := vv.coefficient
    let phasePrefix := vv.phasePrefix
    let entries := vv.entries
    let H := vv.H
    let A := vv.A
    let reserveSize := vv.reserveSize
    let refillCost := vv.refillCost
    let reserve := fun (i : Fin sourceTapes) => if (PCJda54a286946142d3_BranchPhases.offset sources p k r + 1155) ≤ i.val then reserveSize else 0
    let family := Composition.machine (RecoveryFocus.machine slots (f_machine a))
      (Composition.machine (RecoveryFocus.machine enc e_machine)
        (RecoveryFocus.machine app CloseoutFinalC10SingleAppend.machine))
    let fuel := fun j=>f_budget a (S j) (rowWidth j) b (xs j).length+1+
       (2*D j+4+1+(2*e_emitCost b+2)+1+
        CloseoutFinalC10AppendPositioning.budget b (phasePrefix++entries.take j).length)
    let outH := fun j=>dockH slots (H j)
       (r_outputH a (ds j) (S j) (R j) (B j) (rowWidth j) (xs j))
    let outA := fun j Z=>
       let entry : Stream.Entry := ⟨coefficient j,total j,denominator j⟩
       install app
        (install enc (install slots (A j)
          (r_outputT a (ds j) (S j) (R j) (B j) (rowWidth j) b (xs j) Z))
         (e_bank b entry (D j) (cap j) (ZeroPadding.pad (D j) (Stream.entryWord b entry))))
        (CloseoutFinalC10AppendPositioning.tapes b (D j) (logSize j) (resetSize j)
          entry ((phasePrefix++entries.take j)++[entry]))
    let padded := fun j i=>ZeroPadding.pad (reserve i) (A j i)
    (∀ j<entries.length,∀ Z,Step family (fuel j) (H j) (A j) (outH j) (outA j Z)  →
       MaskFamilyCode.Prepared refillCode (ds (j+1)) refillCost
        (outH j) (H (j+1)) (fun i=>ZeroPadding.pad (reserve i) (outA j Z i)) (padded (j+1))) := by
  subst hv
  intro _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ j hj Z hstep
  have hg := callChain_good seam H0 A0 h0 j (Nat.lt_of_lt_of_le hj hN)
  rw [pad_zero_fun code] at hg
  exact hg.1 Z hstep

/-- **`_hH` at the chain's banks**, from the first call's heads (the first prologue). -/
theorem hH_of_chain (seam : SeamSpec N (fun _ => 0) code.slots (inTOf code b vd) Inv (goodOf code b vd))
    (H0 : Fin code.sourceTapes → Nat) (A0 : Fin code.sourceTapes → List Bool) (h0 : Inv 0 H0 A0)
    (hN : vd.entries.length ≤ N)
    (hH0 : ∀ i, H0 (code.slots i) = r_inputH code.a (vd.ds 0) (vd.S 0) (vd.R 0) (vd.B 0) (vd.xs 0).length i)
    (vv : RCFive.Source.CallValues Atom code.sourceTapes) (hv : vv = chainVals code b vd seam H0 A0) :
    let a := code.a
    let slots := code.slots
    let ds := vv.ds
    let xs := vv.xs
    let S := vv.S
    let R := vv.R
    let B := vv.B
    let entries := vv.entries
    let H := vv.H
    ∀ j<entries.length,∀ i,H j (slots i)=r_inputH a (ds j) (S j) (R j) (B j) (xs j).length i := by
  subst hv
  intro _ _ _ _ _ _ _ _ _ j hj i
  cases j with
  | zero => exact hH0 i
  | succ j =>
    have hg := callChain_good seam H0 A0 h0 j (Nat.lt_of_lt_of_le (Nat.lt_of_succ_lt hj) hN)
    exact hg.2 i

/-- **`_hA` at the chain's banks**, from the first call's family input (the first prologue). -/
theorem hA_of_chain (seam : SeamSpec N (fun _ => 0) code.slots (inTOf code b vd) Inv (goodOf code b vd))
    (H0 : Fin code.sourceTapes → Nat) (A0 : Fin code.sourceTapes → List Bool) (h0 : Inv 0 H0 A0)
    (hN : vd.entries.length ≤ N)
    (hA0 : ∀ i, A0 (code.slots i) = r_inputT code.a (vd.ds 0) (vd.S 0) (vd.R 0) (vd.B 0) (vd.rowWidth 0) b
      (vd.xs 0).length i)
    (vv : RCFive.Source.CallValues Atom code.sourceTapes) (hv : vv = chainVals code b vd seam H0 A0) :
    let a := code.a
    let slots := code.slots
    let ds := vv.ds
    let xs := vv.xs
    let S := vv.S
    let R := vv.R
    let B := vv.B
    let rowWidth := vv.rowWidth
    let entries := vv.entries
    let A := vv.A
    ∀ j<entries.length,∀ i,A j (slots i)=r_inputT a (ds j) (S j) (R j) (B j)
       (rowWidth j) b (xs j).length i := by
  subst hv
  intro _ _ _ _ _ _ _ _ _ _ j hj i
  cases j with
  | zero => exact hA0 i
  | succ j =>
    exact callChain_slots seam H0 A0 h0 (slots_injective code) j
      (Nat.lt_of_lt_of_le (Nat.lt_of_succ_lt hj) hN) i

end good

section bridge
open NearCubicWires.SourceParent NearCubicWires.SourcePhase NearCubicWires.SourceConstruction
attribute [local irreducible] WorkspaceSelectedAdmission.originalTapes WorkspaceSelectedEntry.size SelectedRecoveryIntegration.outer

/-- **The chain's values ARE `clauseVals` at the chain's banks** (`rfl`): so `traceOf`'s `hv` holds for `vv := chainVals …`. -/
theorem chainVals_clauseVals (mask : MaskProducer) (selector : CyclicChoice.Laws)
    (packets : PCJc4297ab269d8423a_Source.PacketLibrary selector)
    (rows : PCJc4297ab269d8423a_Source.RowLibrary selector) (compiler : Packets.CompilerLaws)
    (sources : EightSources) {gamma : Real} (p : Parameters sources gamma)
    (den : Nat) (hden : 0 < den) (k r scratch n : Nat) (x : BitInput n) (bits : List Bool)
    (hp : P1Independent.CappedLegalAdmission.passed sources p
      (ControllerCappedSelected.reference den hden k (PolynomialClock.ordinaryClock k))
      (WorkspaceSelectedAdmission.coldCutoff sources) n x bits = true)
    (site : Bool → Phase → Σ states, Machine (ControllerSelectedContinuation.bodyTapes sources p k r scratch) states)
    (code : (ph : Phase) → RCFive.Source.SourceCode mask selector packets rows sources p k r scratch ph) (ph : Phase) (ci : Fin (NC sources k (PolynomialClock.ordinaryClock k) x (C10TotalDecode.oracleOf sources k (PolynomialClock.ordinaryClock k) p.degree n bits))) (L : Nat)
    (lay : TraceData.LayoutFamily (PCJd04de0277f804fcc_.coordinate sources k (PolynomialClock.ordinaryClock k) p den x (C10TotalDecode.oracleOf sources k (PolynomialClock.ordinaryClock k) p.degree n bits) bits) ph ci sources L (C10SupplierAccuracyChain.accuracyTargetAll (constantsOf sources) (CloseoutFinalC10StageFields.stageLimits sources p)) (PCJ374c44bb8b7f47d9_.S.mode sources p den hden k r scratch n x bits hp) selector) (deg : Nat → Nat) (V : Nat)
    (dflt : P1TopDownPaidReusable.Datum) (Dw capw logw resetw : Nat) (old : Nat → List Bool)
    (Hd : Nat → Fin (code ph).sourceTapes → Nat) (Ad : Nat → Fin (code ph).sourceTapes → List Bool)
    (Rc familyCost refillCost firstCost counterReserve : Nat) (b N : Nat)
    (Inv : Nat → (Fin (code ph).sourceTapes → Nat) → (Fin (code ph).sourceTapes → List Bool) → Prop)
    (seam : SeamSpec N (fun _ => 0) (code ph).slots
      (inTOf (code ph) b (clauseVals mask selector packets rows compiler sources p den hden k r scratch n x bits hp site code ph ci L lay deg V dflt Dw capw logw resetw old Hd Ad Rc familyCost refillCost firstCost counterReserve)) Inv
      (goodOf (code ph) b (clauseVals mask selector packets rows compiler sources p den hden k r scratch n x bits hp site code ph ci L lay deg V dflt Dw capw logw resetw old Hd Ad Rc familyCost refillCost firstCost counterReserve)))
    (H0 : Fin (code ph).sourceTapes → Nat) (A0 : Fin (code ph).sourceTapes → List Bool) :
    chainVals (code ph) b (clauseVals mask selector packets rows compiler sources p den hden k r scratch n x bits hp site code ph ci L lay deg V dflt Dw capw logw resetw old Hd Ad Rc familyCost refillCost firstCost counterReserve) seam H0 A0 =
      clauseVals mask selector packets rows compiler sources p den hden k r scratch n x bits hp site code ph ci L lay deg V dflt Dw capw logw resetw old
        (fun j => (callChain N (fun _ => 0) (code ph).slots
          (inTOf (code ph) b (clauseVals mask selector packets rows compiler sources p den hden k r scratch n x bits hp site code ph ci L lay deg V dflt Dw capw logw resetw old Hd Ad Rc familyCost refillCost firstCost counterReserve)) Inv
          (goodOf (code ph) b (clauseVals mask selector packets rows compiler sources p den hden k r scratch n x bits hp site code ph ci L lay deg V dflt Dw capw logw resetw old Hd Ad Rc familyCost refillCost firstCost counterReserve)) seam H0 A0 j).1)
        (fun j => (callChain N (fun _ => 0) (code ph).slots
          (inTOf (code ph) b (clauseVals mask selector packets rows compiler sources p den hden k r scratch n x bits hp site code ph ci L lay deg V dflt Dw capw logw resetw old Hd Ad Rc familyCost refillCost firstCost counterReserve)) Inv
          (goodOf (code ph) b (clauseVals mask selector packets rows compiler sources p den hden k r scratch n x bits hp site code ph ci L lay deg V dflt Dw capw logw resetw old Hd Ad Rc familyCost refillCost firstCost counterReserve)) seam H0 A0 j).2)
        Rc familyCost refillCost firstCost counterReserve := rfl

end bridge

end
end NearCubicWires.SourceSkeleton
end

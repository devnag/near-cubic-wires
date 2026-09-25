import Proof.SourceAssembly.SourceStepsNextHole
import Proof.SourceAssembly.SourceClauseInv

section
set_option autoImplicit false
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unusedVariables false

open NearCubicWires NearCubicWires.ComponentwisePolynomial NearCubicWires.RepairOrdinary.CompetitorRawFieldEmit NearCubicWires.RepairOrdinary.CloseoutRowsOriginalSchedule LocalBitMultitape ExtDecompositionBatch RepairOrdinary RepairRepresentation SourceInterfaces RepairSource RepairSource.CloseoutFinal P1TopDown RepairSource.VerifierDecoding RecoveryRootRound RecoveryExecution CloseoutRowsEstimator CloseoutRowsEstimatorCoefficients CompetitorSelectedCount MatrixScoreBatch CompetitorCountMask SupplierPipeline SupplierEstimator SupplierPrime CanonicalFourfoldRowProgram CloseoutRawRows C10ExternalRowLoop C10ThresholdNaturalRowPrint C10ThresholdParityRow C10ThresholdEstimateRowJoin CloseoutFinalC10RowAnswerWord P1Closure P1TopDownPaidReusable P1TopDownPaidReusableReserves P1TopDownPaidBinaryReserves
open PCJ1fef9807c6954e94_Native
open PCJ9eff70d512234a4c_Fixed PCJd4d1d9d7d1fa4313_Production
open PCJc4297ab269d8423a_Source
namespace NearCubicWires.SourceFactorSel.Next
open NearCubicWires.SourceSkeleton NearCubicWires.SourceParent NearCubicWires.SourcePhase NearCubicWires.SourceConstruction
open NearCubicWires.SourceSteps
noncomputable section
attribute [local irreducible] P1TopDownPaidPayload.tapes WorkspaceSelectedAdmission.originalTapes
  WorkspaceSelectedEntry.size SelectedRecoveryIntegration.outer

theorem addCases_cs {m : Nat} {α : Type} (f : Fin m → α) (g : Fin 1 → α) (z : Fin m) :
    Fin.addCases (motive := fun _ => α) f g z.castSucc = f z :=
  Fin.addCases_left z

theorem addCases_last {m : Nat} {α : Type} (f : Fin m → α) (g : Fin 1 → α) :
    Fin.addCases (motive := fun _ => α) f g (Fin.last m) = g 0 :=
  Fin.addCases_right 0

theorem pad_pad (R : Nat) (w : List Bool) : ZeroPadding.pad R (ZeroPadding.pad R w) = ZeroPadding.pad R w := by
  unfold ZeroPadding.pad
  simp only [List.length_append, List.length_replicate]
  have h : R - (w.length + (R - w.length)) = 0 := by omega
  rw [h, List.replicate_zero, List.append_nil]

theorem pad_len (R : Nat) (w : List Bool) : (ZeroPadding.pad R w).length = max R w.length := by
  unfold ZeroPadding.pad
  simp only [List.length_append, List.length_replicate]
  omega

theorem pad_exact (R : Nat) (w : List Bool) (h : w.length = R) : ZeroPadding.pad R w = w := by
  unfold ZeroPadding.pad
  rw [h, Nat.sub_self, List.replicate_zero, List.append_nil]

section final
variable (mask : MaskProducer) (selector : CyclicChoice.Laws)
    (packets : PCJc4297ab269d8423a_Source.PacketLibrary selector)
    (rows : PCJc4297ab269d8423a_Source.RowLibrary selector) (compiler : Packets.CompilerLaws)
    (sources : EightSources) {gamma : Real} (p : Parameters sources gamma)
    (den : Nat) (hden : 0 < den) (k r scratch n : Nat) (x : BitInput n) (bits : List Bool)
    (hp : P1Independent.CappedLegalAdmission.passed sources p
      (ControllerCappedSelected.reference den hden k (PolynomialClock.ordinaryClock k))
      (WorkspaceSelectedAdmission.coldCutoff sources) n x bits = true)
    (site : Bool → Phase → Σ states, Machine (ControllerSelectedContinuation.bodyTapes sources p k r scratch) states)
    (code : (ph : Phase) → RCFive.Source.SourceCode mask selector packets rows sources p k r scratch ph)
    (ph : Phase) (ci : Fin (NC sources k (PolynomialClock.ordinaryClock k) x (C10TotalDecode.oracleOf sources k (PolynomialClock.ordinaryClock k) p.degree n bits)))
    (H0 : Fin (ControllerSelectedContinuation.bodyTapes sources p k r scratch) → Nat) (A0 : Fin (ControllerSelectedContinuation.bodyTapes sources p k r scratch) → List Bool)
    (values : RCFive.Source.CallValues (C10TotalDecode.Atom (pcppAt sources k (PolynomialClock.ordinaryClock k) x (C10TotalDecode.oracleOf sources k (PolynomialClock.ordinaryClock k) p.degree n bits))) (code ph).sourceTapes)

theorem whole_inj (hw : ∀ y, ((code ph).whole y).val = y.val) : Function.Injective (code ph).whole :=
  fun a b h => Fin.ext (by rw [← hw a, ← hw b, h])

/-- `finalA` on a source tape. -/
theorem finalA_cs (hw : ∀ y, ((code ph).whole y).val = y.val) (z : Fin (code ph).sourceTapes) :
    finalA mask selector packets rows compiler sources p den hden k r scratch n x bits hp site code ph ci A0 values ((code ph).whole z.castSucc) =
      ZeroPadding.pad (if PCJda54a286946142d3_BranchPhases.offset sources p k r + 1155 ≤ z.val then values.reserveSize else 0)
        (values.A values.entries.length z) := by
  show install (code ph).whole _ (fun i => ZeroPadding.pad (if i.val = (code ph).sourceTapes then values.counterReserve else 0)
      (Fin.addCases (motive := fun _ => List Bool)
        (fun j => ZeroPadding.pad (if PCJda54a286946142d3_BranchPhases.offset sources p k r + 1155 ≤ j.val then values.reserveSize else 0)
          (values.A values.entries.length j))
        (fun _ => CompareMachine.word values.entries.length) i)) ((code ph).whole z.castSucc) = _
  rw [install_slot _ (whole_inj mask selector packets rows sources p k r scratch code ph hw), addCases_cs]
  have hne : (Fin.castSucc z).val ≠ (code ph).sourceTapes := by
    rw [Fin.val_castSucc]
    exact Nat.ne_of_lt z.isLt
  rw [if_neg hne, ZeroPadding.pad_zero]

/-- `finalA` on the loop counter. -/
theorem finalA_last (hw : ∀ y, ((code ph).whole y).val = y.val) :
    finalA mask selector packets rows compiler sources p den hden k r scratch n x bits hp site code ph ci A0 values
        ((code ph).whole (Fin.last (code ph).sourceTapes)) =
      ZeroPadding.pad values.counterReserve (CompareMachine.word values.entries.length) := by
  show install (code ph).whole _ (fun i => ZeroPadding.pad (if i.val = (code ph).sourceTapes then values.counterReserve else 0)
      (Fin.addCases (motive := fun _ => List Bool)
        (fun j => ZeroPadding.pad (if PCJda54a286946142d3_BranchPhases.offset sources p k r + 1155 ≤ j.val then values.reserveSize else 0)
          (values.A values.entries.length j))
        (fun _ => CompareMachine.word values.entries.length) i)) ((code ph).whole (Fin.last (code ph).sourceTapes)) = _
  rw [install_slot _ (whole_inj mask selector packets rows sources p k r scratch code ph hw), addCases_last, Fin.val_last, if_pos rfl]

/-- `finalH` on a source tape. -/
theorem finalH_cs (hw : ∀ y, ((code ph).whole y).val = y.val) (z : Fin (code ph).sourceTapes) :
    finalH mask selector packets rows compiler sources p den hden k r scratch n x bits hp site code ph H0 values ((code ph).whole z.castSucc) =
      values.H values.entries.length z := by
  show dockH (code ph).whole H0 (Fin.addCases (motive := fun _ => Nat) (values.H values.entries.length) (fun _ => 1))
    ((code ph).whole z.castSucc) = _
  rw [dockH_slot _ (whole_inj mask selector packets rows sources p k r scratch code ph hw), addCases_cs]

/-- `finalH` on the loop counter. -/
theorem finalH_last (hw : ∀ y, ((code ph).whole y).val = y.val) :
    finalH mask selector packets rows compiler sources p den hden k r scratch n x bits hp site code ph H0 values
      ((code ph).whole (Fin.last (code ph).sourceTapes)) = 1 := by
  show dockH (code ph).whole H0 (Fin.addCases (motive := fun _ => Nat) (values.H values.entries.length) (fun _ => 1))
    ((code ph).whole (Fin.last (code ph).sourceTapes)) = _
  rw [dockH_slot _ (whole_inj mask selector packets rows sources p k r scratch code ph hw), addCases_last]

/-- The next entry's site bank off the cache is `finalA`. -/
theorem site_off (t : Fin (ControllerSelectedContinuation.bodyTapes sources p k r scratch))
    (ht : ∀ j, t ≠ PCJda54a286946142d3_BranchPhases.cache sources p k r scratch (PCJ374c44bb8b7f47d9_.S.mode sources p den hden k r scratch n x bits hp) j) :
    queriedAt sources p den hden k r scratch n x bits hp (ci.val + 1)
        (install (PCJda54a286946142d3_BranchPhases.cache sources p k r scratch (PCJ374c44bb8b7f47d9_.S.mode sources p den hden k r scratch n x bits hp))
          (finalA mask selector packets rows compiler sources p den hden k r scratch n x bits hp site code ph ci A0 values)
          (CD sources k (PolynomialClock.ordinaryClock k) x (C10TotalDecode.oracleOf sources k (PolynomialClock.ordinaryClock k) p.degree n bits) (ci.val + 1))) t =
      finalA mask selector packets rows compiler sources p den hden k r scratch n x bits hp site code ph ci A0 values t := by
  rw [queriedAt_off sources p den hden k r scratch n x bits hp (ci.val + 1) _ t ht,
    install_other _ _ _ _ (fun j hj => ht j hj.symm)]

/-- The next entry's site bank on the cache is `cdAt (ci+1)`. -/
theorem site_cache (t : Fin (ControllerSelectedContinuation.bodyTapes sources p k r scratch)) (j : Fin 19)
    (ht : t = PCJda54a286946142d3_BranchPhases.cache sources p k r scratch (PCJ374c44bb8b7f47d9_.S.mode sources p den hden k r scratch n x bits hp) j) :
    queriedAt sources p den hden k r scratch n x bits hp (ci.val + 1)
        (install (PCJda54a286946142d3_BranchPhases.cache sources p k r scratch (PCJ374c44bb8b7f47d9_.S.mode sources p den hden k r scratch n x bits hp))
          (finalA mask selector packets rows compiler sources p den hden k r scratch n x bits hp site code ph ci A0 values)
          (CD sources k (PolynomialClock.ordinaryClock k) x (C10TotalDecode.oracleOf sources k (PolynomialClock.ordinaryClock k) p.degree n bits) (ci.val + 1))) t =
      cdAt sources p k n x bits (ci.val + 1) j := by
  rw [ht, queriedAt_cache]

end final

end
end NearCubicWires.SourceFactorSel.Next
end


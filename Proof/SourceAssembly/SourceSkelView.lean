import Proof.SourceAssembly.SourceSkelGood

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

section view
variable {mask : MaskProducer} {selector : CyclicChoice.Laws}
  {packets : PCJc4297ab269d8423a_Source.PacketLibrary selector}
  {rows : PCJc4297ab269d8423a_Source.RowLibrary selector}
  {sources : EightSources} {gamma : Real} {p : Parameters sources gamma} {k r scratch : Nat} {ph : Phase}
  (code : RCFive.Source.SourceCode mask selector packets rows sources p k r scratch ph) (b : Nat) {Atom : Type}
  (vd : RCFive.Source.CallValues Atom code.sourceTapes)

/-- `_hfields`' entry-emitter words at call `j` (`old j` is the clause's choice). -/
abbrev encInOf (j : Nat) :=
  e_bank b ⟨vd.coefficient j, vd.total j, vd.denominator j⟩ (vd.D j) (vd.cap j) (vd.old j)

/-- `_hfields`' appender words at call `j`. -/
abbrev appInOf (j : Nat) :=
  CloseoutFinalC10AppendPositioning.tapes b (vd.D j) (vd.logSize j) (vd.resetSize j)
    ⟨vd.coefficient j, vd.total j, vd.denominator j⟩ (vd.phasePrefix ++ vd.entries.take j)

/-- **The chain's call-`j` view of a machine bank `Am`**: exact family input on the slots, exact emitter words on `enc`, exact appender
words on `app`, `Am` elsewhere. -/
def viewOf (j : Nat) (Am : Fin code.sourceTapes → List Bool) : Fin code.sourceTapes → List Bool :=
  install code.slots (install code.enc (install code.app Am (appInOf code b vd j)) (encInOf code b vd j)) (inTOf code b vd j)

theorem viewOf_slot (j : Nat) (Am : Fin code.sourceTapes → List Bool) (i : Fin (r_tapes code.a)) :
    viewOf code b vd j Am (code.slots i) = inTOf code b vd j i :=
  install_slot _ (slots_injective code) _ _ i

theorem viewOf_enc (henc : Function.Injective code.enc) (j : Nat) (Am : Fin code.sourceTapes → List Bool) (i : Fin 11)
    (hs : ∀ i', code.slots i' ≠ code.enc i) :
    viewOf code b vd j Am (code.enc i) = encInOf code b vd j i := by
  unfold viewOf
  rw [install_other _ _ _ _ hs]
  exact install_slot _ henc _ _ i

theorem viewOf_app (happ : Function.Injective code.app) (j : Nat) (Am : Fin code.sourceTapes → List Bool) (i : Fin 6)
    (hs : ∀ i', code.slots i' ≠ code.app i) (he : ∀ i', code.enc i' ≠ code.app i) :
    viewOf code b vd j Am (code.app i) = appInOf code b vd j i := by
  unfold viewOf
  rw [install_other _ _ _ _ hs, install_other _ _ _ _ he]
  exact install_slot _ happ _ _ i

theorem viewOf_other (j : Nat) (Am : Fin code.sourceTapes → List Bool) (x : Fin code.sourceTapes)
    (hs : ∀ i, code.slots i ≠ x) (he : ∀ i, code.enc i ≠ x) (ha : ∀ i, code.app i ≠ x) :
    viewOf code b vd j Am x = Am x := by
  unfold viewOf
  rw [install_other _ _ _ _ hs, install_other _ _ _ _ he, install_other _ _ _ _ ha]

/-- **The view re-pads to the machine bank** (per tape class). -/
theorem pad_viewOf (henc : Function.Injective code.enc) (happ : Function.Injective code.app)
    (reserve : Fin code.sourceTapes → Nat) (j : Nat) (Am : Fin code.sourceTapes → List Bool)
    (hS : ∀ i, ZeroPadding.pad (reserve (code.slots i)) (inTOf code b vd j i) = Am (code.slots i))
    (hE : ∀ i, (∀ i', code.slots i' ≠ code.enc i) →
      ZeroPadding.pad (reserve (code.enc i)) (encInOf code b vd j i) = Am (code.enc i))
    (hA : ∀ i, (∀ i', code.slots i' ≠ code.app i) → (∀ i', code.enc i' ≠ code.app i) →
      ZeroPadding.pad (reserve (code.app i)) (appInOf code b vd j i) = Am (code.app i))
    (hO : ∀ x, (∀ i, code.slots i ≠ x) → (∀ i, code.enc i ≠ x) → (∀ i, code.app i ≠ x) → reserve x ≤ (Am x).length) :
    (fun x => ZeroPadding.pad (reserve x) (viewOf code b vd j Am x)) = Am := by
  funext x
  by_cases hs : ∃ i, code.slots i = x
  · obtain ⟨i, rfl⟩ := hs
    rw [viewOf_slot]
    exact hS i
  · have hs' : ∀ i, code.slots i ≠ x := fun i h => hs ⟨i, h⟩
    by_cases he : ∃ i, code.enc i = x
    · obtain ⟨i, rfl⟩ := he
      rw [viewOf_enc code b vd henc j Am i hs']
      exact hE i hs'
    · have he' : ∀ i, code.enc i ≠ x := fun i h => he ⟨i, h⟩
      by_cases ha : ∃ i, code.app i = x
      · obtain ⟨i, rfl⟩ := ha
        rw [viewOf_app code b vd happ j Am i hs' he']
        exact hA i hs' he'
      · have ha' : ∀ i, code.app i ≠ x := fun i h => ha ⟨i, h⟩
        rw [viewOf_other code b vd j Am x hs' he' ha']
        unfold ZeroPadding.pad
        rw [Nat.sub_eq_zero_of_le (hO x hs' he' ha')]
        simp

/-- **The chain's bank at call `j` for a clause of `M` calls**: the exact view `viewOf` while a call follows (`j < M`); at the loop end
(`M ≤ j`: no `_hfields` there, and the last refill's empty request writes no coefficient words on `enc 0..2`) only the slots are unpadded. -/
def chainView (M j : Nat) (Am : Fin code.sourceTapes → List Bool) : Fin code.sourceTapes → List Bool :=
  if j < M then viewOf code b vd j Am else install code.slots Am (inTOf code b vd j)

theorem chainView_lt (M j : Nat) (hj : j < M) (Am : Fin code.sourceTapes → List Bool) :
    chainView code b vd M j Am = viewOf code b vd j Am := by
  unfold chainView; rw [if_pos hj]

theorem chainView_ge (M j : Nat) (hj : M ≤ j) (Am : Fin code.sourceTapes → List Bool) :
    chainView code b vd M j Am = install code.slots Am (inTOf code b vd j) := by
  unfold chainView; rw [if_neg (by omega)]

/-- The loop-end bank re-pads to the machine bank (slots padded, every other tape at least its reserve long). -/
theorem pad_install_slots (reserve : Fin code.sourceTapes → Nat) (j : Nat) (Am : Fin code.sourceTapes → List Bool)
    (hS : ∀ i, ZeroPadding.pad (reserve (code.slots i)) (inTOf code b vd j i) = Am (code.slots i))
    (hO : ∀ x, (∀ i, code.slots i ≠ x) → reserve x ≤ (Am x).length) :
    (fun x => ZeroPadding.pad (reserve x) (install code.slots Am (inTOf code b vd j) x)) = Am := by
  funext x
  by_cases hs : ∃ i, code.slots i = x
  · obtain ⟨i, rfl⟩ := hs
    rw [install_slot _ (slots_injective code)]
    exact hS i
  · have hs' : ∀ i, code.slots i ≠ x := fun i h => hs ⟨i, h⟩
    rw [install_other _ _ _ _ hs']
    unfold ZeroPadding.pad
    rw [Nat.sub_eq_zero_of_le (hO x hs')]
    simp

end view

end
end NearCubicWires.SourceSkeleton
end

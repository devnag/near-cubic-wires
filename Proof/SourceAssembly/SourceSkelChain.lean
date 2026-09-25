import Proof.SourceAssembly.SourceSkelTrace

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

section chain
variable {U t : Nat} (N : Nat) (reserve : Fin U → Nat) (slots : Fin t → Fin U)
  (inT : Nat → Fin t → List Bool)
  (Inv : Nat → (Fin U → Nat) → (Fin U → List Bool) → Prop)
  (Good : Nat → (Fin U → Nat) → (Fin U → List Bool) → (Fin U → Nat) → (Fin U → List Bool) → Prop)

/-- **S's per-call seam, abstractly** (`Rest.refill_seam` + `view_padded` + `Inv.view`). -/
def SeamSpec : Prop :=
  ∀ j, j < N → ∀ (H : Fin U → Nat) (A : Fin U → List Bool), Inv j H A →
    ∃ (H' : Fin U → Nat) (A' : Fin U → List Bool), Good j H A H' A' ∧
      (fun x => ZeroPadding.pad (reserve x) (install slots A' (inT (j+1)) x)) = A' ∧
      Inv (j+1) H' (install slots A' (inT (j+1)))

open Classical in
/-- The chain of per-call UNPADDED banks from the first call's bank `(H0, A0)`. -/
def callChain (seam : SeamSpec N reserve slots inT Inv Good) (H0 : Fin U → Nat) (A0 : Fin U → List Bool) :
    Nat → (Fin U → Nat) × (Fin U → List Bool)
  | 0 => (H0, A0)
  | j+1 =>
    if h : j < N ∧ Inv j (callChain seam H0 A0 j).1 (callChain seam H0 A0 j).2 then
      (Classical.choose (seam j h.1 _ _ h.2),
        install slots (Classical.choose (Classical.choose_spec (seam j h.1 _ _ h.2))) (inT (j+1)))
    else callChain seam H0 A0 j

variable {N reserve slots inT Inv Good}

/-- One chain step, with its facts, whenever the invariant holds. -/
theorem callChain_succ (seam : SeamSpec N reserve slots inT Inv Good) (H0 : Fin U → Nat) (A0 : Fin U → List Bool)
    (j : Nat) (hj : j < N) (hI : Inv j (callChain N reserve slots inT Inv Good seam H0 A0 j).1
      (callChain N reserve slots inT Inv Good seam H0 A0 j).2) :
    ∃ A' : Fin U → List Bool,
      Good j (callChain N reserve slots inT Inv Good seam H0 A0 j).1 (callChain N reserve slots inT Inv Good seam H0 A0 j).2
        (callChain N reserve slots inT Inv Good seam H0 A0 (j+1)).1 A' ∧
      (fun x => ZeroPadding.pad (reserve x) ((callChain N reserve slots inT Inv Good seam H0 A0 (j+1)).2 x)) = A' ∧
      (callChain N reserve slots inT Inv Good seam H0 A0 (j+1)).2 = install slots A' (inT (j+1)) ∧
      Inv (j+1) (callChain N reserve slots inT Inv Good seam H0 A0 (j+1)).1
        (callChain N reserve slots inT Inv Good seam H0 A0 (j+1)).2 := by
  have hs := Classical.choose_spec (Classical.choose_spec (seam j hj _ _ hI))
  refine ⟨Classical.choose (Classical.choose_spec (seam j hj _ _ hI)), ?_, ?_, ?_, ?_⟩
  · simp only [callChain]
    rw [dif_pos (And.intro hj hI)]
    exact hs.1
  · simp only [callChain]
    rw [dif_pos (And.intro hj hI)]
    exact hs.2.1
  · simp only [callChain]
    rw [dif_pos (And.intro hj hI)]
  · simp only [callChain]
    rw [dif_pos (And.intro hj hI)]
    exact hs.2.2

/-- **The invariant along the chain.** -/
theorem callChain_inv (seam : SeamSpec N reserve slots inT Inv Good) (H0 : Fin U → Nat) (A0 : Fin U → List Bool)
    (h0 : Inv 0 H0 A0) :
    ∀ j, j ≤ N → Inv j (callChain N reserve slots inT Inv Good seam H0 A0 j).1
      (callChain N reserve slots inT Inv Good seam H0 A0 j).2 := by
  intro j
  induction j with
  | zero => intro _; exact h0
  | succ j ih =>
    intro hj
    obtain ⟨_, _, _, _, h4⟩ := callChain_succ seam H0 A0 j (Nat.lt_of_succ_le hj) (ih (Nat.le_of_succ_le hj))
    exact h4

/-- **`Good` between consecutive calls, at the NEXT bank padded** (`_hrefill`'s `padded (j+1)`). -/
theorem callChain_good (seam : SeamSpec N reserve slots inT Inv Good) (H0 : Fin U → Nat) (A0 : Fin U → List Bool)
    (h0 : Inv 0 H0 A0) (j : Nat) (hj : j < N) :
    Good j (callChain N reserve slots inT Inv Good seam H0 A0 j).1 (callChain N reserve slots inT Inv Good seam H0 A0 j).2
      (callChain N reserve slots inT Inv Good seam H0 A0 (j+1)).1
      (fun x => ZeroPadding.pad (reserve x) ((callChain N reserve slots inT Inv Good seam H0 A0 (j+1)).2 x)) := by
  obtain ⟨A', hG, hpad, _, _⟩ := callChain_succ seam H0 A0 j hj
    (callChain_inv seam H0 A0 h0 j (Nat.le_of_lt hj))
  rw [hpad]
  exact hG

/-- **The next call's family slots** (`_hA` at `j+1`, on the unpadded view). -/
theorem callChain_slots (seam : SeamSpec N reserve slots inT Inv Good) (H0 : Fin U → Nat) (A0 : Fin U → List Bool)
    (h0 : Inv 0 H0 A0) (hinj : Function.Injective slots) (j : Nat) (hj : j < N) (i : Fin t) :
    (callChain N reserve slots inT Inv Good seam H0 A0 (j+1)).2 (slots i) = inT (j+1) i := by
  obtain ⟨A', _, _, heq, _⟩ := callChain_succ seam H0 A0 j hj
    (callChain_inv seam H0 A0 h0 j (Nat.le_of_lt hj))
  rw [heq]
  exact install_slot slots hinj A' (inT (j+1)) i

end chain

end
end NearCubicWires.SourceSkeleton
end

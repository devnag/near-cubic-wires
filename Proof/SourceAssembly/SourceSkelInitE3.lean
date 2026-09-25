import Proof.SourceAssembly.SourceSkelInitE2

section
set_option autoImplicit false
set_option maxRecDepth 120000
set_option warningAsError true

open NearCubicWires LocalBitMultitape ExtDecompositionBatch RepairOrdinary
open RepairOrdinary.RecoveryRootRound RepairSource.VerifierDecoding RepairSource.ProjectionNormalization
open NearCubicWires.SupplierEstimator RepairRepresentation
open PCJ1fef9807c6954e94_Native
open NearCubicWires.SourceConstruction NearCubicWires.SourceConstruction.InitRun
namespace NearCubicWires.SourceSkeleton.InitS
noncomputable section

variable {d : Dims} {eX pX gW eR eV X T : Nat} (pl : Place d eX pX gW eR eV X T) {NS : Nat}
  (hh : HeadExt d eX pX gW X NS)

/-- **The encoder/appender banks** (SI's `InitOutM` form), heads `0`. -/
def EncOut (Rc b : Nat) (H : Fin T → ℕ) (A : Fin T → List Bool) : Prop :=
  (∀ (en : CloseoutRowsEstimatorCoefficients.Stream.Entry) (old : List Bool),
    A (Dims.encT (d := d) pl.hT 3) = ZeroPadding.pad Rc (e_bank b en (D0 b) (cap0 b) old 3) ∧ H (Dims.encT (d := d) pl.hT 3) = 0) ∧
  (∀ (en : CloseoutRowsEstimatorCoefficients.Stream.Entry) (old : List Bool),
    A (Dims.encT (d := d) pl.hT 6) = ZeroPadding.pad Rc (e_bank b en (D0 b) (cap0 b) old 7) ∧ H (Dims.encT (d := d) pl.hT 6) = 0) ∧
  (∀ (en : CloseoutRowsEstimatorCoefficients.Stream.Entry) (old : List Bool),
    A (Dims.encT (d := d) pl.hT 7) = ZeroPadding.pad Rc (e_bank b en (D0 b) (cap0 b) old 8) ∧ H (Dims.encT (d := d) pl.hT 7) = 0) ∧
  (∀ (en : CloseoutRowsEstimatorCoefficients.Stream.Entry) (old : List Bool),
    A (Dims.encT (d := d) pl.hT 8) = ZeroPadding.pad Rc (e_bank b en (D0 b) (cap0 b) old 9) ∧ H (Dims.encT (d := d) pl.hT 8) = 0) ∧
  (∀ (en : CloseoutRowsEstimatorCoefficients.Stream.Entry) (old : List Bool),
    A (Dims.encT (d := d) pl.hT 9) = ZeroPadding.pad Rc (e_bank b en (D0 b) (cap0 b) old 10) ∧ H (Dims.encT (d := d) pl.hT 9) = 0) ∧
  (∀ (en : CloseoutRowsEstimatorCoefficients.Stream.Entry) (xs : List CloseoutRowsEstimatorCoefficients.Stream.Entry),
    A (Dims.encT (d := d) pl.hT 10) = ZeroPadding.pad Rc (CloseoutFinalC10AppendPositioning.tapes b (D0 b)
      (CloseoutFinalC10AppendWorkspaceInit.capacity b) (CloseoutFinalC10AppendWorkspaceInit.capacity b) en xs 2) ∧
    H (Dims.encT (d := d) pl.hT 10) = 0) ∧
  (∀ (en : CloseoutRowsEstimatorCoefficients.Stream.Entry) (xs : List CloseoutRowsEstimatorCoefficients.Stream.Entry),
    A (Dims.encT (d := d) pl.hT 11) = ZeroPadding.pad Rc (CloseoutFinalC10AppendPositioning.tapes b (D0 b)
      (CloseoutFinalC10AppendWorkspaceInit.capacity b) (CloseoutFinalC10AppendWorkspaceInit.capacity b) en xs 4) ∧
    H (Dims.encT (d := d) pl.hT 11) = 0) ∧
  (∀ (en : CloseoutRowsEstimatorCoefficients.Stream.Entry) (xs : List CloseoutRowsEstimatorCoefficients.Stream.Entry),
    A (Dims.encT (d := d) pl.hT 12) = ZeroPadding.pad Rc (CloseoutFinalC10AppendPositioning.tapes b (D0 b)
      (CloseoutFinalC10AppendWorkspaceInit.capacity b) (CloseoutFinalC10AppendWorkspaceInit.capacity b) en xs 5) ∧
    H (Dims.encT (d := d) pl.hT 12) = 0) ∧
  (∀ kk : Fin 13, (kk.val = 4 ∨ kk.val = 5) →
    A (Dims.encT (d := d) pl.hT kk) = List.replicate Rc false ∧ H (Dims.encT (d := d) pl.hT kk) = 0)

/-- **Every init state carries the encoder/appender banks** (they lie below the strip, off the extension scratch). -/
theorem encOut_of_inv {NR NE : Nat}
    {L cS cR q b Rc Vv CP CW CL DP DW DL : Nat} {mode : Bool} {tg : Nat} {val : Nat → Option (List Bool)} {u : Nat}
    {H : Fin T → ℕ} {A : Fin T → List Bool} {H' : Fin T → ℕ} {A' : Fin T → List Bool}
    (hi : InitInv pl hh NR NE L cS cR q b Rc Vv CP CW CL DP DW DL mode tg val u H A H' A') :
    EncOut pl Rc b H' A' := by
  obtain ⟨H1, A1, ho, hag⟩ := hi.base
  have hsbB : sb d eX pX gW = d.B + 29 + restPc eX pX gW := rfl
  have hBG : d.B = d.G + d.R1 + 410 + d.w + d.tc := rfl
  have hG : d.G = d.F + d.rt + 13 := rfl
  have hv : ∀ kk : Fin 13, (Dims.encT (d := d) pl.hT kk).val = d.F + d.rt + kk.val := fun _ => rfl
  have ag : ∀ kk : Fin 13, A' (Dims.encT (d := d) pl.hT kk) = A1 (Dims.encT (d := d) pl.hT kk) ∧
      H' (Dims.encT (d := d) pl.hT kk) = H1 (Dims.encT (d := d) pl.hT kk) := fun kk => by
    have hk := kk.isLt
    exact hag _ (by rw [hv]; omega) (by rw [hv]; unfold eb; omega)
  refine ⟨fun en old => ?_, fun en old => ?_, fun en old => ?_, fun en old => ?_, fun en old => ?_,
    fun en xs => ?_, fun en xs => ?_, fun en xs => ?_, fun kk hk => ?_⟩
  · rw [(ag 3).1, (ag 3).2]; exact ho.enc3 en old
  · rw [(ag 6).1, (ag 6).2]; exact ho.enc7 en old
  · rw [(ag 7).1, (ag 7).2]; exact ho.enc8 en old
  · rw [(ag 8).1, (ag 8).2]; exact ho.enc9 en old
  · rw [(ag 9).1, (ag 9).2]; exact ho.enc10 en old
  · rw [(ag 10).1, (ag 10).2]; exact ho.app2 en xs
  · rw [(ag 11).1, (ag 11).2]; exact ho.app4 en xs
  · rw [(ag 12).1, (ag 12).2]; exact ho.app5 en xs
  · rw [(ag kk).1, (ag kk).2]; exact ho.encOld kk hk

end
end NearCubicWires.SourceSkeleton.InitS
end


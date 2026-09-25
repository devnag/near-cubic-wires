import Proof.SourceAssembly.SourceSkelInitC
import Proof.SourceAssembly.SourceSkelInitLong

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

theorem rw1_val : (Dims.rewind2Slots pl.ext.rest.ext pl.hT 1).val = 278 := rfl
theorem rw2_val : (Dims.rewind2Slots pl.ext.rest.ext pl.hT 2).val = 279 := rfl

include pl hh in
/-- **The rewind residents at the init's exit**: `278 = 1^Vv`, `279 = 0^Vv`, heads 0. -/
theorem init_rewinds {NR NE : Nat} (hE : ResExt d eX pX gW X NS NE)
    {L cS cR q b Rc Vv CP CW CL DP DW DL : Nat} {mode : Bool} {tg : Nat} {val : Nat → Option (List Bool)} {u : Nat}
    {H H' : Fin T → ℕ} {A A' : Fin T → List Bool}
    (hi : InitInv pl hh NR NE L cS cR q b Rc Vv CP CW CL DP DW DL mode tg val u H A H' A') :
    (A' (Dims.rewind2Slots pl.ext.rest.ext pl.hT 1) = List.replicate Vv true ∧ H' (Dims.rewind2Slots pl.ext.rest.ext pl.hT 1) = 0) ∧
    (A' (Dims.rewind2Slots pl.ext.rest.ext pl.hT 2) = List.replicate Vv false ∧ H' (Dims.rewind2Slots pl.ext.rest.ext pl.hT 2) = 0) := by
  obtain ⟨hF0, hB0, h11, h12, hU, hJB, hjk, hP⟩ := lay pl.ext
  have hres := hE.hres
  have hG : d.G = d.F + d.rt + 13 := rfl
  have hBG : d.B = d.G + d.R1 + 410 + d.w + d.tc := rfl
  have hsbB : sb d eX pX gW = d.B + 29 + restPc eX pX gW := rfl
  have hsb : sb d eX pX gW + 32 ≤ eb d eX pX gW X NS := by unfold sb eb; omega
  obtain ⟨H1, A1, ho, hag⟩ := hi.base
  have v1 := rw1_val pl
  have v2 := rw2_val pl
  have e1 := hag (Dims.rewind2Slots pl.ext.rest.ext pl.hT 1) (by omega) (by omega)
  have e2 := hag (Dims.rewind2Slots pl.ext.rest.ext pl.hT 2) (by omega) (by omega)
  rw [e1.1, e1.2, e2.1, e2.2]
  exact ⟨ho.rew1, ho.rew2⟩

end
end NearCubicWires.SourceSkeleton.InitS
end

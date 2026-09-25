import Proof.SourceAssembly.SourceRest

section
set_option autoImplicit false
set_option maxRecDepth 120000
set_option warningAsError true

open NearCubicWires LocalBitMultitape ExtDecompositionBatch
open RepairOrdinary RepairOrdinary.RecoveryRootRound
open RepairRepresentation SupplierEstimator SupplierPipeline SourceInterfaces
open RepairSource.VerifierDecoding
open NearCubicWires.P1Closure
open PCJ9eff70d512234a4c_Fixed PCJd4d1d9d7d1fa4313_Production PCJc4297ab269d8423a_Source
open NearCubicWires.RepairSource NearCubicWires.RepairSource.CloseoutFinal
open NearCubicWires.SourceRequest NearCubicWires.SourceRequest.FactorLoop
namespace NearCubicWires.SourceConstruction.Rest
noncomputable section

/-- A tape `Resident` reads, by value: below the family bank's end, in the loader scratch, or `lenTape`. -/
def LowT (d : SourceConstruction.Dims) (v : Nat) : Prop :=
  v < d.F + d.rt ∨ (d.G ≤ v ∧ v < d.G + d.pscr) ∨ v = d.B

section low
variable {d : SourceConstruction.Dims} (e : d.Ext) {V : Nat} (hV : d.U ≤ V)

theorem low_slot (j : Fin 13) : LowT d (d.slot hV j).val := by
  have := j.isLt; unfold LowT; right; left
  simp only [SourceConstruction.Dims.slot, SourceConstruction.Dims.slotV, SourceConstruction.Dims.pscr]; omega
theorem low_mask (i : Fin (5 + d.w)) : LowT d (d.maskSlots hV i).val := by
  have := i.isLt; unfold LowT; right; left
  simp only [SourceConstruction.Dims.maskSlots, SourceConstruction.Dims.maskV, SourceConstruction.Dims.slotV,
    SourceConstruction.Dims.pscr]
  split_ifs <;> omega
theorem low_pslots (j : Fin d.tc) : LowT d (d.pslots hV j).val := by
  have := j.isLt; have := d.hdesc; have := d.hdesc440; unfold LowT; right; left
  simp only [SourceConstruction.Dims.pslots, SourceConstruction.Dims.pV, SourceConstruction.Dims.slotV,
    SourceConstruction.Dims.pscr]
  split_ifs <;> omega
theorem low_pool (i : Fin 373) : LowT d (d.poolSlots hV i).val := by
  have := i.isLt; unfold LowT; right; left
  simp only [SourceConstruction.Dims.poolSlots, SourceConstruction.Dims.poolV, SourceConstruction.Dims.pscr]
  split_ifs <;> omega
theorem low_family (j : Fin d.R1) : LowT d (d.familySlots hV j).val := by
  have := j.isLt; have := d.hsp; unfold LowT
  simp only [SourceConstruction.Dims.familySlots, SourceConstruction.Dims.famV, SourceConstruction.Dims.pscr]
  split_ifs <;> omega
theorem low_rewind (i : Fin 3) : LowT d (Dims.rewind2Slots e hV i).val := by
  have := i.isLt; have := d.hsp; have := e.hF; unfold LowT; left
  simp only [Dims.rewind2Slots, Dims.rw2V]
  split_ifs <;> omega
theorem low_ret (k : Fin 4) : LowT d (d.ret hV k).val := by
  have := k.isLt; unfold LowT; right; left
  simp only [SourceConstruction.Dims.ret, SourceConstruction.Dims.retV, SourceConstruction.Dims.pscr]; omega
theorem low_scr (m : Fin 13) (hm : m.val ≤ 10) : LowT d (d.scr hV m).val := by
  unfold LowT; right; left
  simp only [SourceConstruction.Dims.scr, SourceConstruction.Dims.scrV, SourceConstruction.Dims.pscr]; omega
theorem low_len : LowT d (Dims.lenTape e hV).val := by
  unfold LowT; right; right; rfl

end low

/-- A `LowT` tape is outside the back half's footprint. -/
theorem low_back {d : SourceConstruction.Dims} {v : Nat} (h : LowT d v) (eX pX : Nat) :
    v ≠ d.B + 13 ∧ ¬ (d.B + 19 ≤ v ∧ v < d.B + 19 + 71 + eX + pX) ∧
      ¬ (d.F + d.rt ≤ v ∧ v ≤ d.F + d.rt + 4 ∧ v ≠ d.F + d.rt + 3) ∧
      ¬ (d.B + 19 + 71 ≤ v ∧ v < d.B + 19 + 71 + eX + pX) := by
  have hG : d.G = d.F + d.rt + 13 := rfl
  have hB : d.B = d.G + d.R1 + 410 + d.w + d.tc := rfl
  have hp : d.pscr = d.R1 + 408 + d.w + d.tc := rfl
  unfold LowT at h
  omega

end
end NearCubicWires.SourceConstruction.Rest
end

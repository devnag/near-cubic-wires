import Proof.SourceAssembly.SourceRefillJoin

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
namespace NearCubicWires.SourceConstruction
noncomputable section

namespace Dims
variable (d : Dims)

/-- The rest layout with the twelve high residents of decisions 41 and 47. -/
structure RestExt3 (eX pX gW : Nat) : Prop where
  ext2 : d.RestExt2 eX pX gW
  hres3 : 19 + restPc eX pX gW + 22 ≤ d.res

/-- The lower per-call block: the tapes of the back half (frame input, metadata stages, F6, slope, cursor, `nT`). -/
def InZ (eX pX v : Nat) : Prop := d.B + 19 ≤ v ∧ v < d.B + 19 + 71 + eX + pX

instance (eX pX v : Nat) : Decidable (d.InZ eX pX v) := by unfold InZ; infer_instance

/-- The ten FactorSelection residents `hrT 0..9`. -/
def HiRes (eX pX gW v : Nat) : Prop :=
  d.B + 29 + restPc eX pX gW ≤ v ∧ v < d.B + 29 + restPc eX pX gW + 10

variable {d} {eX pX gW : Nat} (e : d.RestExt3 eX pX gW) {V : Nat} (hV : d.U ≤ V)

/-- A high resident. -/
def hrT (i : Fin 12) : Fin V :=
  ⟨d.B + 29 + restPc eX pX gW + i.val, Nat.lt_of_lt_of_le (by
    have := i.isLt; have := e.hres3; unfold B U G prepT; omega) hV⟩

theorem hrT_val (i : Fin 12) : (hrT e hV i).val = d.B + 29 + restPc eX pX gW + i.val := rfl

/-- The outer clear set `Z`, then the driver `hrT 10`, then the log `hrT 11`, by value. -/
def clrZV (eX pX gW i : Nat) : Nat :=
  if i < 71 + eX + pX then d.B + 19 + i
  else if i = 71 + eX + pX then d.B + 29 + restPc eX pX gW + 10
  else d.B + 29 + restPc eX pX gW + 11

/-- The outer clear's slot map. -/
def clrZ : Fin (71 + eX + pX + 1 + 1) → Fin V := fun i =>
  ⟨d.clrZV eX pX gW i.val, Nat.lt_of_lt_of_le (by
    have := i.isLt; have := e.hres3
    simp only [clrZV, restPc, B, U, G, prepT] at *
    split_ifs <;> omega) hV⟩

theorem clrZ_injective : Function.Injective (clrZ e hV) := by
  intro i j h
  have hv := congrArg Fin.val h
  have hi := i.isLt; have hj := j.isLt
  simp only [clrZ, clrZV, restPc] at hv hi hj
  apply Fin.ext
  split_ifs at hv <;> omega

theorem clrZ_stage (k : Fin (71 + eX + pX)) :
    (clrZ e hV (Fin.castAdd 1 (Fin.castAdd 1 k))).val = d.B + 19 + k.val := by
  have := k.isLt
  simp only [clrZ, clrZV, Fin.val_castAdd]
  rw [if_pos this]

theorem clrZ_in (k : Fin (71 + eX + pX)) : d.InZ eX pX (clrZ e hV (Fin.castAdd 1 (Fin.castAdd 1 k))).val := by
  have := k.isLt
  rw [clrZ_stage]; unfold InZ; omega

theorem clrZ_driver : clrZ e hV (Fin.castAdd 1 ((0 : Fin 1).natAdd (71 + eX + pX))) = hrT e hV 10 := by
  apply Fin.ext
  simp only [clrZ, clrZV, hrT, Fin.val_natAdd, Fin.val_castAdd, Fin.val_zero]
  split_ifs <;> first | rfl | omega

theorem clrZ_log : clrZ e hV ((0 : Fin 1).natAdd (71 + eX + pX + 1)) = hrT e hV 11 := by
  apply Fin.ext
  simp only [clrZ, clrZV, hrT, Fin.val_natAdd, Fin.val_zero]
  split_ifs <;> first | rfl | omega

/-- Every `Z` tape is a stage tape of the outer clear. -/
theorem clrZ_cover (x : Fin V) (hx : d.InZ eX pX x.val) :
    ∃ kk : Fin (71 + eX + pX), clrZ e hV (Fin.castAdd 1 (Fin.castAdd 1 kk)) = x := by
  unfold InZ at hx
  refine ⟨⟨x.val - d.B - 19, by omega⟩, Fin.ext ?_⟩
  rw [clrZ_stage]; simp only; omega

/-- Off `Z` and off the outer driver/log, a tape is not in the outer clear. -/
theorem clrZ_off (x : Fin V) (h1 : ¬ d.InZ eX pX x.val) (h2 : x ≠ hrT e hV 10) (h3 : x ≠ hrT e hV 11) :
    ∀ kk, clrZ e hV kk ≠ x := by
  intro kk hk
  have hkv := kk.isLt
  by_cases hs : kk.val < 71 + eX + pX
  · have e1 : kk = Fin.castAdd 1 (Fin.castAdd 1 ⟨kk.val, hs⟩) := Fin.ext rfl
    rw [e1] at hk
    exact h1 (hk ▸ clrZ_in e hV _)
  by_cases hd : kk.val = 71 + eX + pX
  · have e1 : kk = Fin.castAdd 1 ((0 : Fin 1).natAdd (71 + eX + pX)) := Fin.ext (by simp [hd])
    rw [e1, clrZ_driver] at hk
    exact h2 hk.symm
  · have e1 : kk = (0 : Fin 1).natAdd (71 + eX + pX + 1) := Fin.ext (by simp; omega)
    rw [e1, clrZ_log] at hk
    exact h3 hk.symm

/-! ### value facts -/

theorem InZ_clear {v : Nat} (h : d.InZ eX pX v) : d.InClear eX pX gW v := by
  unfold InZ at h; unfold InClear restPc; omega

theorem hrT_notClear (i : Fin 12) : ¬ d.InClear eX pX gW (hrT e hV i).val := by
  have hB : d.B = d.G + d.R1 + 410 + d.w + d.tc := rfl
  have hG : d.G = d.F + d.rt + 13 := rfl
  have hp : d.pscr = d.R1 + 408 + d.w + d.tc := rfl
  unfold InClear; simp only [hrT_val, restPc]; omega

theorem hrT_notZ (i : Fin 12) : ¬ d.InZ eX pX (hrT e hV i).val := by
  unfold InZ; simp only [hrT_val, restPc]; omega

theorem hrT_notOut (i : Fin 12) : ¬ Rest.OutV d eX pX gW (hrT e hV i).val := by
  have hB : d.B = d.G + d.R1 + 410 + d.w + d.tc := rfl
  have hp : d.pscr = d.R1 + 408 + d.w + d.tc := rfl
  unfold Rest.OutV; simp only [hrT_val, restPc]; omega

theorem hrT_ne_scr (i : Fin 12) (m : Fin 13) : hrT e hV i ≠ d.scr hV m := by
  intro h; have hv := congrArg Fin.val h
  have hB : d.B = d.G + d.R1 + 410 + d.w + d.tc := rfl
  have := m.isLt
  simp only [hrT_val, scr, scrV] at hv; omega

theorem hrT_ne_rsT (i : Fin 12) (m : Fin 5) : hrT e hV i ≠ d.rsT e.ext2.ext1 hV m := by
  intro h; have hv := congrArg Fin.val h
  have := m.isLt
  simp only [hrT_val, rsT] at hv; omega

theorem hrT_ne_mT (i : Fin 12) (m : Fin 5) : hrT e hV i ≠ mT e.ext2 hV m := by
  intro h; have hv := congrArg Fin.val h
  have := m.isLt
  simp only [hrT_val, mT] at hv; omega

theorem hrT_ne_rfT (i : Fin 12) (m : Fin 5) : hrT e hV i ≠ rfT e.ext2 hV m := by
  intro h; have hv := congrArg Fin.val h
  have := m.isLt
  simp only [hrT_val, rfT] at hv; omega

theorem hrT_free (i : Fin 12) :
    Cycle.Free (d.slot hV) (d.maskSlots hV) (d.pslots hV) (d.poolSlots hV) (d.familySlots hV)
      (rewind2Slots e.ext2.ext1.ext hV) (hrT e hV i) :=
  free_res e.ext2.ext1.ext hV _ (by simp only [hrT_val]; omega)

end Dims

namespace Rest

/-- **The refill prologue of the window repair**: the outer clear of `Z` (driver `hrT 10 = 1^Rk`, log
`hrT 11 = 0^(Rk+2)`), then the verified refill prologue `refillPro = clear (clr2) ; rest ; refresh`. ONE fixed machine. -/
def refillPro3 {a : DecompositionAlgorithm} {vE vP : Request → Nat}
    (se : PacketsGlue.RequestMeta.UnaryStage a vE) (sp : PacketsGlue.RequestMeta.UnaryStage a vP)
    {d : SourceConstruction.Dims} {gW : Nat} (e : d.RestExt3 se.extra sp.extra gW) {V : Nat} (hV : d.U ≤ V)
    {s7 : Nat} (g7M : Machine V s7) :=
  Composition.machine
    (RecoveryFocus.machine (Dims.clrZ e hV) (PCJ6e421fabe2aa4155_SourceClear.machine (71 + se.extra + sp.extra)))
    (refillPro se sp e.ext2 hV g7M)

def srcK3 {d : SourceConstruction.Dims} {eX pX gW : Nat} {V : Nat} (cacheT : Fin 19 → Fin V) (x : Fin V) : Prop :=
  x.val = 1 ∨ x.val = 284 ∨ (∃ i, cacheT i = x) ∨ d.HiRes eX pX gW x.val

end Rest
end
end NearCubicWires.SourceConstruction
end

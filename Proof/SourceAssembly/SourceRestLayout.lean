import Proof.SourceAssembly.SourceWiring
import Proof.SourceAssembly.SourceRefillStep

section
set_option autoImplicit false
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unusedVariables false

open NearCubicWires LocalBitMultitape ExtDecompositionBatch RepairOrdinary
namespace NearCubicWires.SourceConstruction
noncomputable section

/-- The size of the per-call block. -/
def restPc (eX pX gW : Nat) : Nat := 71 + eX + pX + gW

namespace Dims
variable (d : Dims)
/-- The enlarged clear set's stage count. -/
def tcl2 (eX pX gW : Nat) : Nat := d.tcl + 14 + restPc eX pX gW

/-- The extra fact this placement needs: the reserved region holds `B .. B+18`, the per-call block and five
residents. -/
structure RestExt (eX pX gW : Nat) : Prop where
  ext : d.Ext
  hres : 19 + restPc eX pX gW + 5 ≤ d.res

/-- The enlarged clear set, by value. -/
def clr2V (eX pX gW i : Nat) : Nat :=
  if i < d.tcl then d.clearV i
  else if i < d.tcl + 14 then d.B + (i - d.tcl)
  else if i < d.tcl2 eX pX gW then d.B + 19 + (i - d.tcl - 14)
  else if i = d.tcl2 eX pX gW then d.scrV 11
  else d.scrV 12

/-- Membership in the enlarged clear set, by value. -/
def InClear (eX pX gW v : Nat) : Prop :=
  (d.F ≤ v ∧ v < d.F + d.rt) ∨ (d.G ≤ v ∧ v < d.G + d.pscr) ∨ (d.B ≤ v ∧ v < d.B + 14) ∨
    (d.B + 19 ≤ v ∧ v < d.B + 19 + restPc eX pX gW)

instance (eX pX gW v : Nat) : Decidable (d.InClear eX pX gW v) := by
  unfold InClear; infer_instance

variable {d} {eX pX gW : Nat} (e : d.RestExt eX pX gW) {V : Nat} (hV : d.U ≤ V)

/-- A per-call block tape. -/
def pcT (i : Fin (restPc eX pX gW)) : Fin V :=
  ⟨d.B + 19 + i.val, Nat.lt_of_lt_of_le (by
    have := i.isLt; have := e.hres; unfold B U G prepT; omega) hV⟩
/-- A prologue resident. -/
def rsT (i : Fin 5) : Fin V :=
  ⟨d.B + 19 + restPc eX pX gW + i.val, Nat.lt_of_lt_of_le (by
    have := i.isLt; have := e.hres; unfold B U G prepT; omega) hV⟩
/-- The thirteen tapes between the family bank and `G` (`enc 0..4`, `enc 6..10`, `app 2, 4, 5`). -/
def encT (k : Fin 13) : Fin V :=
  ⟨d.F + d.rt + k.val, Nat.lt_of_lt_of_le (by have := k.isLt; unfold U G prepT; omega) hV⟩

/-- The enlarged clear set: stage tapes, then the driver `scr 11`, then the log `scr 12`. -/
def clr2 : Fin (d.tcl2 eX pX gW + 1 + 1) → Fin V := fun i =>
  ⟨d.clr2V eX pX gW i.val, Nat.lt_of_lt_of_le (by
    have := i.isLt; have := e.hres
    simp only [clr2V, clearV, scrV, tcl2, tcl, pscr, restPc, B, U, G, prepT] at *
    split_ifs <;> omega) hV⟩

def Rpad (Rc : Nat) : Fin V → Nat := fun x => if d.InClear eX pX gW x.val then Rc else 0

end Dims

/-- Unfold every value of the rest layout and close an interval (in)equality. -/
macro "rgeo" : tactic => `(tactic| (simp only [Dims.pcT, Dims.rsT, Dims.encT, Dims.clr2, Dims.clr2V,
  Dims.clearV, Dims.scrV, Dims.tcl2, Dims.tcl, Dims.pscr, restPc, Dims.B, Dims.G, Dims.slot, Dims.maskSlots,
  Dims.pslots, Dims.poolSlots, Dims.ret, Dims.scr, Dims.familySlots, Dims.rewind2Slots, Dims.csSlots,
  Dims.drvSlots, Dims.natSlots, Dims.lenTape, Dims.slotV, Dims.maskV, Dims.pV, Dims.poolV, Dims.retV,
  Dims.famV, Dims.rw2V, Dims.csV, Dims.drvV, Dims.InClear, Fin.val_mk] at * <;> (try split_ifs at *) <;> omega))

namespace Dims
variable {d : Dims} {eX pX gW : Nat} (e : d.RestExt eX pX gW) {V : Nat} (hV : d.U ≤ V)

theorem rsT_injective : Function.Injective (rsT e hV) := fun a b h => Fin.ext (by
  have hv := congrArg Fin.val h; simp only [rsT] at hv; omega)

theorem clr2_injective : Function.Injective (clr2 e hV) := by
  intro i j h
  have hv := congrArg Fin.val h
  have hi := i.isLt; have hj := j.isLt; have := d.hsp
  simp only [clr2, clr2V, clearV, scrV, tcl2, tcl, pscr, restPc, B, G] at hv hi hj
  apply Fin.ext
  split_ifs at hv <;> omega

/-- The family bank `F + i` is in the enlarged clear set (its first `rt` entries). -/
theorem slots_in_clr2 {U : Nat} (hU : d.U ≤ U) (slots : Fin d.rt → Fin U)
    (hslots : ∀ i, (slots i).val = d.F + i.val) (i : Fin d.rt) :
    ∃ k : Fin (d.tcl2 eX pX gW), clr2 e hU (Fin.castAdd 1 (Fin.castAdd 1 k)) = slots i := by
  have hi := i.isLt
  refine ⟨⟨i.val, by unfold tcl2 tcl; omega⟩, Fin.ext ?_⟩
  rw [hslots i]
  simp only [clr2, clr2V, clearV, Fin.val_castAdd]
  have h1 : i.val < d.tcl := by unfold tcl; omega
  simp [h1, hi]

/-- Every stage tape of the enlarged clear set is in `InClear`, and so padded at `Rc`. -/
theorem clr2_in (k : Fin (d.tcl2 eX pX gW)) :
    d.InClear eX pX gW (clr2 e hV (Fin.castAdd 1 (Fin.castAdd 1 k))).val := by
  have hk := k.isLt; have := d.hsp
  simp only [clr2, clr2V, clearV, Fin.val_castAdd, InClear, tcl2, tcl, pscr, restPc, B, G] at *
  split_ifs <;> omega

theorem clr2_driver : (clr2 e hV (Fin.castAdd 1 ((0 : Fin 1).natAdd (d.tcl2 eX pX gW)))) = d.scr hV 11 := by
  apply Fin.ext
  have h14 : d.tcl + 14 ≤ d.tcl2 eX pX gW := by unfold tcl2; omega
  simp only [clr2, clr2V, scr, Fin.val_natAdd, Fin.val_castAdd, Fin.val_zero]
  split_ifs <;> first | rfl | omega

theorem clr2_log : (clr2 e hV ((0 : Fin 1).natAdd (d.tcl2 eX pX gW + 1))) = d.scr hV 12 := by
  apply Fin.ext
  have h14 : d.tcl + 14 ≤ d.tcl2 eX pX gW := by unfold tcl2; omega
  simp only [clr2, clr2V, scr, Fin.val_natAdd, Fin.val_zero]
  split_ifs <;> first | rfl | omega

end Dims

end
end NearCubicWires.SourceConstruction
end

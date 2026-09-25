import Proof.SourceAssembly.SourceG9

section
set_option autoImplicit false
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unusedVariables false

open NearCubicWires LocalBitMultitape ExtDecompositionBatch RepairOrdinary
open RepairOrdinary.RecoveryRootRound
namespace NearCubicWires.SourceConstruction
noncomputable section

/-! ## 1. The dirty bound from a run's cost alone -/

/-- A run of `n` steps moves no head by more than `n` and grows no tape beyond its head's reach. -/
theorem dirty_bound {t s n : Nat} {p : Machine t s} {H H' : Fin t → Nat} {A A' : Fin t → List Bool}
    (h : Step p n H A H' A') (i : Fin t) :
    (A' i).length ≤ max (A i).length (H i + n + 1) ∧ H' i ≤ H i + n := by
  obtain ⟨r, hr, rh, rt, rs⟩ := h
  have hl := P1Closure.LocalSupport.run_bound p n ⟨p.start, H, A⟩ r hr i
  have hh := SelectiveReset.prefix_head (prefix_of_run p n _ r hr).1 i
  rw [rt] at hl
  rw [rh] at hh
  change (A' i).length ≤ max (A i).length (H i + r.steps + 1) at hl
  change H' i ≤ H i + r.steps at hh
  constructor <;> omega

/-! ## 2. The clear set and the two docking maps -/

namespace Dims
variable (d : Dims)

/-- Size of the private scratch (every loader tape of the cycle). -/
def pscr : Nat := d.R1 + 408 + d.w + d.tc
/-- Size of the clear set: family bank + private scratch. -/
def tcl : Nat := d.rt + d.pscr

/-- The clear set, by value. -/
def clearV (i : Nat) : Nat := if i < d.rt then d.F + i else d.G + (i - d.rt)

end Dims

/-! ## 3. The prologue clear on the layout -/

/-- The clear's log as G9 leaves it: `replicate (R+2) false`; `SourceClear` wants `R+1`, so the
log is padded by `R+2` (`Step.pad`, i.e. `ZeroPadding.run_config`). -/
def logPad (t R : Nat) : Fin (t+1+1) → Nat := PCJ6e421fabe2aa4155_SourceClear.join (fun _ => 0) 0 (R+2)

/-- **H1 at the layout (local form).** Arbitrary dirty words and heads `≤ R` on the clear set,
the G9 driver `replicate R true` and log `replicate (R+2) false`: the clear leaves the clear
set at exactly `replicate R false`, every head `0`, driver and log unchanged, at `4R+7`. -/
theorem clear_local (t R : Nat) (Z : Fin t → List Bool) (HZ : Fin t → Nat)
    (hH : ∀ i, HZ i ≤ R) (hA : ∀ i, (Z i).length ≤ R) :
    Step (PCJ6e421fabe2aa4155_SourceClear.machine t) (4*R+7)
      (PCJ6e421fabe2aa4155_SourceClear.join HZ 0 0)
      (PCJ6e421fabe2aa4155_SourceClear.join Z (List.replicate R true) (List.replicate (R+2) false))
      (fun _ => 0)
      (PCJ6e421fabe2aa4155_SourceClear.join (fun _ => List.replicate R false) (List.replicate R true)
        (List.replicate (R+2) false)) := by
  have h := (PCJ6e421fabe2aa4155_SourceClear.clear_run Z HZ R hH hA).pad (logPad t R)
  have hpad : ZeroPadding.pad (R+2) (List.replicate (R+1) false) = List.replicate (R+2) false := by
    simp only [ZeroPadding.pad, List.length_replicate, List.replicate_append_replicate]
    congr 1
    omega
  refine (h.congr_in rfl ?_).congr rfl ?_
  · funext i
    refine Fin.addCases (fun k => ?_) (fun k => ?_) i
    · refine Fin.addCases (fun k => ?_) (fun k => ?_) k
      · simp [logPad, PCJ6e421fabe2aa4155_SourceClear.join]
      · simp [logPad, PCJ6e421fabe2aa4155_SourceClear.join]
    · simpa [logPad, PCJ6e421fabe2aa4155_SourceClear.join] using hpad
  · funext i
    refine Fin.addCases (fun k => ?_) (fun k => ?_) i
    · refine Fin.addCases (fun k => ?_) (fun k => ?_) k
      · simp [logPad, PCJ6e421fabe2aa4155_SourceClear.join]
      · simp [logPad, PCJ6e421fabe2aa4155_SourceClear.join]
    · simpa [logPad, PCJ6e421fabe2aa4155_SourceClear.join] using hpad

/-! ## 4. What the call cost must pay: the typed bound -/

end
end NearCubicWires.SourceConstruction
end

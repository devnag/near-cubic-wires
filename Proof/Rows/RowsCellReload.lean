import Proof.Rows.VerdictFinish

set_option autoImplicit false
set_option maxRecDepth 120000
set_option warningAsError true

namespace RowsConstruction.CellReload
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.RepairRepresentation NearCubicWires.SupplierPipeline NearCubicWires.SupplierPrime
open NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairOrdinary.RecoveryRootRound
open NearCubicWires.RepairSource.VerifierDecoding
noncomputable section

/-! ## 1. Layout -/

abbrev CT : Nat := 257+254

def cellPort (i : Fin 257) : Fin CT := i.castAdd 254
def masterPort (k : Fin 254) : Fin CT := k.natAdd 257

def layout {α : Type} (X : Fin 257 → α) (Y : Fin 254 → α) : Fin CT → α :=
  Fin.addCases (m:=257) (n:=254) X Y

@[simp] theorem layout_cell {α : Type} (X : Fin 257 → α) (Y : Fin 254 → α) (i : Fin 257) :
    layout X Y (cellPort i) = X i := by
  simp [layout, cellPort]
@[simp] theorem layout_master {α : Type} (X : Fin 257 → α) (Y : Fin 254 → α) (k : Fin 254) :
    layout X Y (masterPort k) = Y k := by
  simp [layout, masterPort]

theorem cover {motive : Fin CT → Prop} (hc : ∀ i, motive (cellPort i))
    (hm : ∀ k, motive (masterPort k)) (x : Fin CT) : motive x :=
  Fin.addCases (m:=257) (n:=254) (fun i => hc i) (fun k => hm k) x

/-! ## 2. The fanout slots: masters, the 254 cell inputs, the clock (254), the log (255) -/

def fanSlots : Fin (254+(254+1)+1) → Fin CT :=
  Fin.addCases (m:=254+(254+1)) (n:=1)
    (Fin.addCases (m:=254) (n:=254+1) masterPort
      (Fin.addCases (m:=254) (n:=1) (fun i => cellPort (i.castAdd 3)) (fun _ => cellPort 254)))
    (fun _ => cellPort 255)

theorem fanSlots_master (k : Fin 254) :
    fanSlots ((k.castAdd (254+1)).castAdd 1) = masterPort k := by
  simp only [fanSlots, Fin.addCases_left]
theorem fanSlots_dest (i : Fin 254) :
    fanSlots (((i.castAdd 1).natAdd 254).castAdd 1) = cellPort (i.castAdd 3) := by
  simp only [fanSlots, Fin.addCases_left, Fin.addCases_right]
theorem fanSlots_clock (j : Fin 1) :
    fanSlots (((j.natAdd 254).natAdd 254).castAdd 1) = cellPort 254 := by
  simp only [fanSlots, Fin.addCases_left, Fin.addCases_right]
theorem fanSlots_log (j : Fin 1) : fanSlots (j.natAdd (254+(254+1))) = cellPort 255 := by
  simp only [fanSlots, Fin.addCases_right]

theorem fanSlots_val (j : Fin (254+(254+1)+1)) :
    (fanSlots j).val = if j.val < 254 then 257+j.val else if j.val < 508 then j.val-254
      else if j.val = 508 then 254 else 255 := by
  refine Fin.addCases (m:=254+(254+1)) (n:=1) (fun a => ?_) (fun a => ?_) j
  · refine Fin.addCases (m:=254) (n:=254+1) (fun b => ?_) (fun b => ?_) a
    · rw [fanSlots_master]
      have hb := b.isLt
      simp only [masterPort, Fin.val_natAdd, Fin.val_castAdd]
      rw [if_pos hb]
    · refine Fin.addCases (m:=254) (n:=1) (fun c => ?_) (fun c => ?_) b
      · rw [fanSlots_dest]
        have hc := c.isLt
        simp only [cellPort, Fin.val_natAdd, Fin.val_castAdd]
        split_ifs <;> omega
      · rw [fanSlots_clock]
        have hc : c.val = 0 := Nat.lt_one_iff.mp c.isLt
        simp only [cellPort, Fin.val_natAdd, Fin.val_castAdd, hc]
        split_ifs <;> first | rfl | omega
  · rw [fanSlots_log]
    have ha : a.val = 0 := Nat.lt_one_iff.mp a.isLt
    simp only [cellPort, Fin.val_natAdd, Fin.val_castAdd, ha]
    split_ifs <;> first | rfl | omega

theorem fanSlots_injective : Function.Injective fanSlots := by
  intro i j h
  have hv := congrArg Fin.val h
  rw [fanSlots_val, fanSlots_val] at hv
  have hi := i.isLt
  have hj := j.isLt
  apply Fin.ext
  split_ifs at hv <;> omega

theorem fanSlots_ne_out (j : Fin (254+(254+1)+1)) : fanSlots j ≠ cellPort 256 := by
  intro h
  have hv := congrArg Fin.val h
  rw [fanSlots_val] at hv
  have hj := j.isLt
  change _ = 256 at hv
  split_ifs at hv <;> omega

/-! ## 3. The three stages -/

def fanStage := RecoveryFocus.machine fanSlots
  (ExtIncidence.NativeFanout.machine (k:=254) (m:=254) some)

/-! ## 4. Stage lemmas -/

theorem fan_step (R : Nat) (out : List Bool) (M : Fin 254 → List Bool)
    (hMl : ∀ i, (M i).length ≤ R) :
    Step fanStage (2*R+4)
      (layout (PCJ45bee56da9f34d5a_VerdictFinish.heads (fun _ => 0) out.length) (fun _ => 0))
      (layout (PCJ45bee56da9f34d5a_VerdictFinish.bank (fun _ => List.replicate R false) R out) M)
      (layout (PCJ45bee56da9f34d5a_VerdictFinish.heads (fun _ => 0) out.length) (fun _ => 0))
      (layout (PCJ45bee56da9f34d5a_VerdictFinish.bank (fun i => ZeroPadding.pad R (M i)) R out) M) := by
  have base := (ExtIncidence.NativeFanout.reusable (k:=254) (m:=254) some M R hMl).focus fanSlots
    fanSlots_injective
    (layout (PCJ45bee56da9f34d5a_VerdictFinish.heads (fun _ => 0) out.length) (fun _ => 0))
    (layout (PCJ45bee56da9f34d5a_VerdictFinish.bank (fun _ => List.replicate R false) R out) M)
  have hH : dockH fanSlots
      (layout (PCJ45bee56da9f34d5a_VerdictFinish.heads (fun _ => 0) out.length) (fun _ => 0))
      (fun _ => 0) =
      layout (PCJ45bee56da9f34d5a_VerdictFinish.heads (fun _ => 0) out.length) (fun _ => 0) := by
    apply dockH_existing
    intro j
    refine Fin.addCases (m:=254+(254+1)) (n:=1) (fun a => ?_) (fun a => ?_) j
    · refine Fin.addCases (m:=254) (n:=254+1) (fun b => ?_) (fun b => ?_) a
      · rw [fanSlots_master, layout_master]
      · refine Fin.addCases (m:=254) (n:=1) (fun c => ?_) (fun c => ?_) b
        · rw [fanSlots_dest, layout_cell]
          simp [PCJ45bee56da9f34d5a_VerdictFinish.heads]
        · rw [fanSlots_clock, layout_cell]
          rfl
    · rw [fanSlots_log, layout_cell]
      rfl
  have hA : install fanSlots
      (layout (PCJ45bee56da9f34d5a_VerdictFinish.bank (fun _ => List.replicate R false) R out) M)
      (ExtIncidence.NativeFanout.reusableInput (m:=254) M R) =
      layout (PCJ45bee56da9f34d5a_VerdictFinish.bank (fun _ => List.replicate R false) R out) M := by
    apply install_existing
    intro j
    refine Fin.addCases (m:=254+(254+1)) (n:=1) (fun a => ?_) (fun a => ?_) j
    · refine Fin.addCases (m:=254) (n:=254+1) (fun b => ?_) (fun b => ?_) a
      · rw [fanSlots_master, layout_master]
        simp only [ExtIncidence.NativeFanout.reusableInput, Fin.addCases_left]
      · refine Fin.addCases (m:=254) (n:=1) (fun c => ?_) (fun c => ?_) b
        · rw [fanSlots_dest, layout_cell]
          simp [PCJ45bee56da9f34d5a_VerdictFinish.bank, ExtIncidence.NativeFanout.reusableInput]
        · rw [fanSlots_clock, layout_cell]
          have hc : c = 0 := Fin.eq_zero c
          subst hc
          simp only [ExtIncidence.NativeFanout.reusableInput, Fin.addCases_left, Fin.addCases_right]
          rfl
    · rw [fanSlots_log, layout_cell]
      have ha : a = 0 := Fin.eq_zero a
      subst ha
      simp only [ExtIncidence.NativeFanout.reusableInput, Fin.addCases_right]
      rfl
  have hO : install fanSlots
      (layout (PCJ45bee56da9f34d5a_VerdictFinish.bank (fun _ => List.replicate R false) R out) M)
      (ExtIncidence.NativeFanout.output (k:=254) (m:=254) some M R) =
      layout (PCJ45bee56da9f34d5a_VerdictFinish.bank (fun i => ZeroPadding.pad R (M i)) R out) M := by
    funext x
    refine cover (motive := fun x => install fanSlots
      (layout (PCJ45bee56da9f34d5a_VerdictFinish.bank (fun _ => List.replicate R false) R out) M)
      (ExtIncidence.NativeFanout.output (k:=254) (m:=254) some M R) x =
      layout (PCJ45bee56da9f34d5a_VerdictFinish.bank (fun i => ZeroPadding.pad R (M i)) R out) M x)
      (fun i => ?_) (fun k => ?_) x
    · rw [layout_cell]
      refine Fin.addCases (m:=254) (n:=3) (motive := fun i => install fanSlots
        (layout (PCJ45bee56da9f34d5a_VerdictFinish.bank (fun _ => List.replicate R false) R out) M)
        (ExtIncidence.NativeFanout.output (k:=254) (m:=254) some M R) (cellPort i) =
        PCJ45bee56da9f34d5a_VerdictFinish.bank (fun i => ZeroPadding.pad R (M i)) R out i)
        (fun c => ?_) (fun c => ?_) i
      · rw [← fanSlots_dest, install_slot _ fanSlots_injective]
        simp [PCJ45bee56da9f34d5a_VerdictFinish.bank, ExtIncidence.NativeFanout.output,
          ExtIncidence.NativeFanout.word]
      · fin_cases c
        · change install fanSlots _ _ (cellPort 254) = _
          rw [← fanSlots_clock 0, install_slot _ fanSlots_injective]
          simp only [ExtIncidence.NativeFanout.output, Fin.addCases_left, Fin.addCases_right]
          rfl
        · change install fanSlots _ _ (cellPort 255) = _
          rw [← fanSlots_log 0, install_slot _ fanSlots_injective]
          simp only [ExtIncidence.NativeFanout.output, Fin.addCases_right]
          rfl
        · change install fanSlots _ _ (cellPort 256) = _
          rw [install_other _ _ _ _ fanSlots_ne_out, layout_cell]
          rfl
    · rw [layout_master, ← fanSlots_master, install_slot _ fanSlots_injective]
      simp only [ExtIncidence.NativeFanout.output, Fin.addCases_left]
  rw [hH, hA, hO] at base
  exact base

end
end RowsConstruction.CellReload

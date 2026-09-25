import Proof.CaseAnalysis.RowsTouchingSupportFold

/-! Reuse the physical support scanner at the actual shifted mask position.
The existing zero-origin fold would require a new resident mask at each shift. -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unusedVariables false

namespace PCJ93d4cfe17dc847a3.Scan
open NearCubicWires LocalBitMultitape RepairOrdinary RecoveryExecution
open NearCubicWires.RepairOrdinary.CloseoutRowsTouching.SupportScan

def cells (mask : Fin 3 → List Bool) : Nat → List Bool → List Cell
  | _, [] => []
  | j, b::bs => (b,readTapeBit (mask 0) j,readTapeBit (mask 1) j,
      readTapeBit (mask 2) j) :: cells mask (j+1) bs

theorem offset_timed (lead pre : List Bool) (bs tail : List Bool)
    (mask : Fin 3 → List Bool) (j n : Nat) (hit cur : Bool) :
    Timed machine (2*bs.length+1)
      (prefixedCfg lead 0 (pre++frame bs++tail) pre.length mask j n hit cur)
      (prefixedCfg lead 2 (pre++frame bs++tail) (pre.length+2*bs.length+1)
        mask (j+bs.length) (n+count (cells mask j bs))
        (hit||(cells mask j bs).any touched) (cur||(cells mask j bs).any current)) := by
  induction bs generalizing pre j n hit cur with
  | nil =>
    simpa [cells,count,frame] using
      Timed.single (by rfl) (prefixed_stop_step lead pre tail mask j n hit cur)
  | cons b bs ih =>
    let cell : Cell := (b,readTapeBit (mask 0) j,readTapeBit (mask 1) j,
      readTapeBit (mask 2) j)
    have first := prefixed_bit_steps lead pre (frame bs++tail) cell mask j n hit cur
      (by rfl) (by rfl) (by rfl)
    have rest := ih (pre++[true,b]) (j+1) (n+(kept cell).toNat)
      (hit||touched cell) (cur||current cell)
    have actual := first.trans (by
      simpa only [cell,List.append_assoc,List.cons_append,List.nil_append,
        List.length_append,List.length_cons,List.length_nil,Nat.add_zero] using rest)
    have ht : 2+(2*bs.length+1) = 2*(b::bs).length+1 := by simp; omega
    rw [ht] at actual
    simpa [cells,cell,count,frame,List.append_assoc,Nat.add_assoc,Nat.add_comm,
      Nat.add_left_comm,Nat.mul_add,Bool.or_assoc] using actual

theorem offset_run (lead pre : List Bool) (bs tail : List Bool)
    (mask : Fin 3 → List Bool) (j n : Nat) (hit cur : Bool) :
    ∃ r, runFrom machine (2*bs.length+1)
      (prefixedCfg lead 0 (pre++frame bs++tail) pre.length mask j n hit cur) = some r ∧
      r.final = prefixedCfg lead 2 (pre++frame bs++tail) (pre.length+2*bs.length+1)
        mask (j+bs.length) (n+count (cells mask j bs))
        (hit||(cells mask j bs).any touched) (cur||(cells mask j bs).any current) ∧
      r.steps = 2*bs.length+1 := by
  exact (offset_timed lead pre bs tail mask j n hit cur).run (by rfl)

end PCJ93d4cfe17dc847a3.Scan

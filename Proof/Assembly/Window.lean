import Proof.Assembly.ResetBank
import Proof.Assembly.Decision

/-! Literal slices of the physically constructed doubled window. These are
proof descriptions of existing cells, not supplied or newly allocated inputs. -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unusedVariables false

namespace PCJ93d4cfe17dc847a3.Window
open NearCubicWires LocalBitMultitape RepairOrdinary RecoveryExecution
open NearCubicWires.RepairSource.VerifierDecoding
open PCJc4297ab269d8423a_Source

def pre (d : MaskData) (i : Nat) := (State.double d).take (d.q-i)
def slice (d : MaskData) (i : Nat) := ((State.double d).drop (d.q-i)).take d.q
def rest (d : MaskData) (i : Nat) := ((State.double d).drop (d.q-i)).drop d.q

@[simp] theorem double_length (d : MaskData) : (State.double d).length = 2*d.q := by
  simp [State.double]; omega
@[simp] theorem pre_length (d : MaskData) (i : Nat) : (pre d i).length = d.q-i := by
  simp only [pre,List.length_take,double_length]
  omega
@[simp] theorem slice_length (d : MaskData) (i : Nat) : (slice d i).length = d.q := by
  simp only [slice,List.length_take,List.length_drop,double_length]
  omega

theorem decomposition (d : MaskData) (i : Nat) :
    pre d i ++ slice d i ++ rest d i = State.double d := by
  simp only [pre,slice,rest,List.append_assoc,List.take_append_drop]

theorem heads_next (d : MaskData) (i : Nat) :
    Decision.shiftHeads (State.heads d i) = State.heads d (i+1) := by
  funext j
  fin_cases j <;> simp [Decision.shiftHeads,State.heads] <;> omega

noncomputable def winner (d : MaskData) (i best : Nat) (old : List Bool) :=
  if best < (State.result d (d.q-i)).1 then slice d i else old

theorem output_bank (d : MaskData) (i best : Nat) (old : List Bool) :
    Decision.output (ResetBank.afterBank d i best old) best (State.result d (d.q-i)).1
      (slice d i) =
    State.bank d (i+1) (max best (State.result d (d.q-i)).1) (winner d i best old) := by
  classical
  by_cases h : best < (State.result d (d.q-i)).1
  · funext j
    fin_cases j <;> simp [Decision.output,Decision.updated,ResetBank.afterBank,
      State.bank,State.logCapacity,winner,h]
  · have he : max best (State.result d (d.q-i)).1 = best := max_eq_left (by omega)
    funext j
    fin_cases j <;> simp [Decision.output,Decision.updated,ResetBank.afterBank,
      State.bank,State.logCapacity,winner,h,he]

end PCJ93d4cfe17dc847a3.Window

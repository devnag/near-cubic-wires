import Proof.Assembly.PlanOrdinaryCyclicMaskProduction
import Proof.Assembly.Program

/-! Exact banks for the concrete program. Candidate storage follows the same
maximum as the winning score; no independently chosen reserve is assumed. -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unusedVariables false

namespace PCJ93d4cfe17dc847a3.State
open NearCubicWires LocalBitMultitape RepairOrdinary RecoveryExecution
open NearCubicWires.RepairSource.VerifierDecoding
open NearCubicWires.RepairOrdinary.CloseoutRowsTouching.SupportScan
open PCJc4297ab269d8423a_Source

noncomputable def rows (d : MaskData) : List (List Bool) :=
  List.ofFn (fun i : Fin d.m => List.ofFn (fun x : Fin d.q => decide (x ∈ d.support i)))

@[simp] theorem rows_length (d : MaskData) : (rows d).length = d.m := by simp [rows]
theorem row_length (d : MaskData) : ∀ bs ∈ rows d, bs.length = d.q := by
  intro bs hb
  simp only [rows,List.mem_ofFn] at hb
  obtain ⟨i,rfl⟩ := hb
  simp
theorem rows_word (d : MaskData) : (rows d).flatMap frame = d.supportWord := by
  simp [rows,MaskData.supportWord,List.flatMap_def,Function.comp_def]

def double (d : MaskData) := Init.bits d.K d.q ++ Init.bits d.K d.q
def masks (d : MaskData) : Fin 3 → List Bool := ![[],[],double d]
noncomputable def result (d : MaskData) (offset : Nat) : Rows.Score :=
  (rows d).foldl (Rows.next (masks d) offset) (0,false,false)

theorem cells_flags (word : List Bool) (offset : Nat) (bs : List Bool) :
    (Scan.cells ![[],[],word] offset bs).any touched = false ∧
    (Scan.cells ![[],[],word] offset bs).any current = false := by
  induction bs generalizing offset with
  | nil => simp [Scan.cells]
  | cons b bs ih =>
    simp [Scan.cells,touched,current,readTapeBit,List.getD,ih (offset+1)]

theorem fold_flags (word : List Bool) (offset : Nat) (rs : List (List Bool)) (n : Nat) :
    (rs.foldl (Rows.next ![[],[],word] offset) (n,false,false)).2 = (false,false) := by
  induction rs generalizing n with
  | nil => rfl
  | cons bs rs ih =>
    simpa only [List.foldl_cons,Rows.next,(cells_flags word offset bs).1,
      (cells_flags word offset bs).2,Bool.false_or] using
      ih (n+count (Scan.cells ![[],[],word] offset bs))

theorem result_flags (d : MaskData) (offset : Nat) : (result d offset).2 = (false,false) :=
  fold_flags (double d) offset (rows d) 0

theorem result_bound (d : MaskData) (offset : Nat) : (result d offset).1 ≤ d.m*d.q := by
  simpa only [result,rows_length,Nat.zero_add] using
    Reset.score_le d.q (masks d) offset (rows d) (0,false,false) (row_length d)

def logCapacity (d : MaskData) (iteration : Nat) : Nat :=
  if iteration = 0 then 0 else Reset.fuel d.q d.m

def heads (d : MaskData) (iteration : Nat) : Fin 13 → Nat :=
  ![0,1,0,1,0,d.q-iteration,d.q-iteration,d.q-iteration,1,0,0,1,0]

noncomputable def bank (d : MaskData) (iteration best : Nat) (winner : List Bool) :
    Fin 13 → List Bool :=
  ![d.supportWord,CompareMachine.word d.q,CompareMachine.word d.K,CompareMachine.word d.m,
    winner,double d,[],[],List.replicate (best+1) false,[false],[false],
    CompareMachine.word best,List.replicate (logCapacity d iteration) false]

theorem candidate_empty (best : Nat) :
    ZeroPadding.pad (best+1) (CompareMachine.word 0) = List.replicate (best+1) false := by
  change ZeroPadding.pad (best+1) (List.replicate 1 false) = _
  rw [Rewind.Workspace.pad_zeros,max_eq_left (by omega)]

theorem candidate_cleared (best score : Nat) :
    ZeroPadding.pad (best+1) (List.replicate (score+1) false) =
      List.replicate (max best score+1) false := by
  rw [Rewind.Workspace.pad_zeros]
  congr 1
  omega

end PCJ93d4cfe17dc847a3.State

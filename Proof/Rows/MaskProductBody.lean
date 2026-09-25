import Proof.Rows.MaskProductInner
import Proof.Rows.MaskProductBack
import Proof.Rows.PhysicalFocusBoundary

/-! One complete outer iteration: emit the right-minor products, restore
its right-bank cursor by counted traversal, then advance the left cursor. -/
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 120000
set_option warningAsError true
namespace PCJ9eff70d512234a4c_Fixed.Materializer.MaskProduct
open NearCubicWires NearCubicWires.LocalBitMultitape
open NearCubicWires.RepairOrdinary NearCubicWires.RepairOrdinary.RecoveryExecution
open NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairSource.VerifierDecoding

noncomputable def backSlots : Fin 4→Fin 6 := ![0,2,3,5]
noncomputable def seekSlots : Fin 3→Fin 6 := ![0,1,3]
noncomputable def body := Composition.machine inner
  (Composition.machine (RecoveryFocus.machine backSlots MaskBack.machine)
    (RecoveryFocus.machine seekSlots MaskSeek.body))

def H (mh pos : Nat) (out count : List Bool) : Fin 6→Nat := ![1,mh,pos,out.length,count.length,1]
def A (B N : Nat) (left right out count : List Bool) : Fin 6→List Bool :=
  ![UnaryTemplate.tape B,left,right,out,count,CompareMachine.word N]
def budget (B N : Nat) := N*(5*B+14)+2*B+10

 theorem flatten_length (B : Nat) (rows : List (List Bool)) (hw : ∀ row∈rows,row.length=B) :
    rows.flatten.length=rows.length*B := by
  induction rows with
  | nil => simp
  | cons row rows ih =>
    have hr:=hw row (by simp)
    have ht:=ih (fun r h=>hw r (by simp [h]))
    simp only [List.flatten_cons,List.length_append,List.length_cons,hr,ht]
    ring

 theorem body_run (B : Nat) (mask : List Bool) (rows : List (List Bool))
    (mpre mtail pre tail out count : List Bool) (hm : mask.length=B)
    (hw : ∀ row∈rows,row.length=B) :
    Step body (budget B rows.length) (H mpre.length pre.length out count)
      (A B rows.length (mpre++mask++mtail) (pre++rows.flatten++tail) out count)
      (H (mpre.length+B) pre.length (out++records mask rows)
        (count++List.replicate rows.length true))
      (A B rows.length (mpre++mask++mtail) (pre++rows.flatten++tail)
        (out++records mask rows) (count++List.replicate rows.length true)) := by
  obtain ⟨r,hr,hf,_⟩:=inner_run B mask rows mpre mtail pre tail out count hm hw
  have first:=Step.of_run hr (congrArg Configuration.heads hf) (congrArg Configuration.tapes hf)
  have fh0 : (innerCfg 0 B mpre.length (mpre++mask++mtail) (pre++rows.flatten++tail)
      pre.length out count rows.length 1).heads=H mpre.length pre.length out count := by
    funext i;fin_cases i <;> rfl
  have fa0 : (innerCfg 0 B mpre.length (mpre++mask++mtail) (pre++rows.flatten++tail)
      pre.length out count rows.length 1).tapes=A B rows.length (mpre++mask++mtail)
        (pre++rows.flatten++tail) out count := by
    funext i;fin_cases i <;> rfl
  have fh1 : (innerCfg 3 B mpre.length (mpre++mask++mtail) (pre++rows.flatten++tail)
      (pre.length+rows.flatten.length) (out++records mask rows)
      (count++List.replicate rows.length true) rows.length 1).heads=
      H mpre.length (pre.length+rows.length*B) (out++records mask rows)
        (count++List.replicate rows.length true) := by
    rw [flatten_length B rows hw]
    funext i;fin_cases i <;> rfl
  have fa1 : (innerCfg 3 B mpre.length (mpre++mask++mtail) (pre++rows.flatten++tail)
      (pre.length+rows.flatten.length) (out++records mask rows)
      (count++List.replicate rows.length true) rows.length 1).tapes=
      A B rows.length (mpre++mask++mtail) (pre++rows.flatten++tail)
        (out++records mask rows) (count++List.replicate rows.length true) := by
    funext i;fin_cases i <;> rfl
  have first:=first.congr fh1 fa1
  have first:=first.congr_in fh0 fa0
  obtain ⟨r,hr,hf,_⟩:=MaskBack.back_run B rows.length pre.length
    (pre++rows.flatten++tail) (out++records mask rows)
  have rb:=Step.of_run hr (congrArg Configuration.heads hf) (congrArg Configuration.tapes hf)
  have second:=PhysicalFocusBoundary.focus rb backSlots (by decide)
    (H mpre.length (pre.length+rows.length*B) (out++records mask rows)
      (count++List.replicate rows.length true))
    (H mpre.length pre.length (out++records mask rows) (count++List.replicate rows.length true))
    (A B rows.length (mpre++mask++mtail) (pre++rows.flatten++tail)
      (out++records mask rows) (count++List.replicate rows.length true))
    (A B rows.length (mpre++mask++mtail) (pre++rows.flatten++tail)
      (out++records mask rows) (count++List.replicate rows.length true))
    (by intro i;fin_cases i <;> rfl) (by intro i;fin_cases i <;> rfl)
    (by intro i;fin_cases i <;> rfl) (by intro i;fin_cases i <;> rfl)
    (by intro i hi;fin_cases i <;> first | exact ⟨rfl,rfl⟩ | exact False.elim (hi 1 rfl))
  obtain ⟨r,hr,hf,_⟩:=MaskSeek.row_run B mpre.length (mpre++mask++mtail) (out++records mask rows)
  have rs:=Step.of_run hr (congrArg Configuration.heads hf) (congrArg Configuration.tapes hf)
  have third:=PhysicalFocusBoundary.focus rs seekSlots (by decide)
    (H mpre.length pre.length (out++records mask rows) (count++List.replicate rows.length true))
    (H (mpre.length+B) pre.length (out++records mask rows) (count++List.replicate rows.length true))
    (A B rows.length (mpre++mask++mtail) (pre++rows.flatten++tail)
      (out++records mask rows) (count++List.replicate rows.length true))
    (A B rows.length (mpre++mask++mtail) (pre++rows.flatten++tail)
      (out++records mask rows) (count++List.replicate rows.length true))
    (by intro i;fin_cases i <;> rfl) (by intro i;fin_cases i <;> rfl)
    (by intro i;fin_cases i <;> rfl) (by intro i;fin_cases i <;> rfl)
    (by intro i hi;fin_cases i <;> first | exact ⟨rfl,rfl⟩ | exact False.elim (hi 1 rfl))
  have h:=first.seq (second.seq third)
  have fuel : (rows.length*(3*B+9)+3)+1+((rows.length*(2*B+5)+3)+1+(2*B+2))=
      budget B rows.length := by unfold budget;ring
  rw [fuel] at h
  exact h

end PCJ9eff70d512234a4c_Fixed.Materializer.MaskProduct

import Proof.Assembly.RowsConstantWords

set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unusedVariables false

namespace PCJ45bee56da9f34d5a_Constants
open NearCubicWires NearCubicWires.LocalBitMultitape
open NearCubicWires.RepairOrdinary RecoveryExecution

def cfg (s : Fin 798) (source : Fin 4 → List Bool) (H : Fin 4 → Nat)
    (out : Fin 11 → List Bool) : Configuration 15 798 :=
  ⟨s,(fun j=>Fin.addCases (m:=4) (n:=11) H (fun i=> (out i).length) j),
    (fun j=>Fin.addCases (m:=4) (n:=11) source out j)⟩
def appended (out : Fin 11 → List Bool) (phase k : Nat) : Fin 11 → List Bool :=
  fun i=>out i++((blocks phase i)[k]?).toList

def moved (H : Fin 4 → Nat) (phase : Nat) (last : Bool) : Fin 4 → Nat :=
  fun i=> if last then HeadMove.apply (sourceMove phase i) (H i) else H i

theorem emit_action (s target : Fin 798) (source : Fin 4 → List Bool)
    (H : Fin 4 → Nat) (out : Fin 11 → List Bool) (phase k : Nat) (last : Bool) :
    applyAction (cfg s source H out) (emit phase k last target)=
      cfg target source (moved H phase last) (appended out phase k) := by
  apply configuration_ext
  · rfl
  · funext i
    refine Fin.addCases (m:=4) (n:=11) (fun j=>?_) (fun j=>?_) i
    · cases last <;> simp [applyAction,cfg,emit,moved,Fin.addCases_left,HeadMove.apply]
    · by_cases hj : k < (blocks phase j).length <;>
        simp [applyAction,cfg,emit,appended,Fin.addCases_right,hj,HeadMove.apply]
  · funext i
    refine Fin.addCases (m:=4) (n:=11) (fun j=>?_) (fun j=>?_) i
    · simp [applyAction,cfg,emit,Fin.addCases_left]
    · by_cases hj : k < (blocks phase j).length <;>
        simp [applyAction,cfg,emit,appended,Fin.addCases_right,hj,Streaming.write_append]

def partialOut (out : Fin 11 → List Bool) (phase k : Nat) : Fin 11 → List Bool :=
  fun i=>out i++(blocks phase i).take k

theorem appended_partial (out : Fin 11 → List Bool) (phase k : Nat) :
    appended (partialOut out phase k) phase k=partialOut out phase (k+1) := by
  funext i
  simp only [appended,partialOut,List.take_add_one,List.append_assoc]

def code (phase : Fin 13) (k : Fin 57) : Fin 798 := ⟨phase.val*57+k.val,by omega⟩
def incCode (phase : Fin 13) (k : Fin 57) : Fin 798 := ⟨phase.val*57+k.val+1,by omega⟩
def Emits (phase : Fin 13) : Prop :=
  phase.val=0 ∨ phase.val=2 ∨ phase.val=4 ∨ phase.val=6 ∨ phase.val=7 ∨
    phase.val=9 ∨ phase.val=11 ∨ phase.val=12

theorem raw_emit_rule (phase : Fin 13) (k : Fin 57) (h : Emits phase)
    (bits : Fin 15 → Bool) :
    raw.rule (code phase k) bits=
      if k.val+1 < width phase.val then some (emit phase.val k.val false (incCode phase k))
      else some (emit phase.val k.val true (after phase.val)) := by
  have hdiv : (phase.val*57+k.val)/57=phase.val := by omega
  have hmod : (phase.val*57+k.val)%57=k.val := by omega
  have h1 : phase.val≠1 := by unfold Emits at h;omega
  have h3 : phase.val≠3 := by unfold Emits at h;omega
  have h5 : phase.val≠5 := by unfold Emits at h;omega
  have h8 : phase.val≠8 := by unfold Emits at h;omega
  have h10 : phase.val≠10 := by unfold Emits at h;omega
  simp only [raw,code,hdiv,hmod,if_neg h1,if_neg h3,if_neg h5,if_neg h8,if_neg h10,
    dif_pos phase.isLt,incCode]

theorem raw_halted (phase : Fin 13) (k : Fin 57) : raw.halted (code phase k)=false := by
  have h : phase.val*57+k.val≠741 := by omega
  simpa only [raw,code,beq_eq_false_iff_ne] using h


end PCJ45bee56da9f34d5a_Constants

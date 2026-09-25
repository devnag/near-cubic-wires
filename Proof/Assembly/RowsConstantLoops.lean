import Proof.Assembly.RowsConstantChunks

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unusedVariables false

namespace PCJ45bee56da9f34d5a_Constants
open NearCubicWires NearCubicWires.LocalBitMultitape
open NearCubicWires.RepairOrdinary RecoveryExecution

/-- These are precisely the p, Q and C passes of the fixed writer. -/
def passPhase : Fin 3 → Fin 13 := ![2,9,11]
def passCheck : Fin 3 → Fin 798 := ![57,456,570]
def passNext : Fin 3 → Fin 798 := ![171,570,684]
def passDriver : Fin 3 → Fin 4 := ![0,2,3]
def shift (H : Fin 4 → Nat) (kind : Fin 3) (k : Nat) :=
  fun i=>H i+if i=passDriver kind then k else 0

def appendedMany (out : Fin 11 → List Bool) (phase n : Nat) :=
  fun i=>out i++repeatWord n (blocks phase i)

theorem pass_check (kind : Fin 3) (source : Fin 4 → List Bool) (H : Fin 4 → Nat)
    (out : Fin 11 → List Bool) (b : Bool)
    (hb : readTapeBit (source (passDriver kind)) (H (passDriver kind))=b) :
    step raw (cfg (passCheck kind) source H out)=
      some (cfg (if b then code (passPhase kind) 0 else passNext kind) source H out) := by
  have key : ∀ bits : Fin 15 → Bool, raw.rule (passCheck kind) bits=
      some (jump (if bits (Fin.castAdd 11 (passDriver kind)) then code (passPhase kind) 0
        else passNext kind)) := by
    intro bits
    fin_cases kind <;> rfl
  have hs : (cfg (passCheck kind) source H out).scanned (Fin.castAdd 11 (passDriver kind))=b := by
    simp only [Configuration.scanned,cfg,Fin.addCases_left]
    exact hb
  change (raw.rule (passCheck kind) _).map _=_
  rw [key,hs,Option.map_some]
  congr 1
  apply configuration_ext
  · rfl
  · funext i
    refine Fin.addCases (m:=4) (n:=11) (fun j=>?_) (fun j=>?_) i <;>
      simp [applyAction,cfg,jump,HeadMove.apply]
  · rfl

theorem pass_chunk (kind : Fin 3) (source : Fin 4 → List Bool) (H : Fin 4 → Nat)
    (out : Fin 11 → List Bool) (k : Nat) :
    Timed raw (width (passPhase kind).val)
      (cfg (code (passPhase kind) 0) source (shift H kind k) out)
      (cfg (passCheck kind) source (shift H kind (k+1))
        (fun i=>out i++blocks (passPhase kind).val i)) := by
  have he : Emits (passPhase kind) := by fin_cases kind <;> simp [Emits,passPhase]
  have path:=chunk (passPhase kind) he source (shift H kind k) out
  have ha : after (passPhase kind).val=passCheck kind := by fin_cases kind <;> rfl
  have hm : moved (shift H kind k) (passPhase kind).val true=shift H kind (k+1) := by
    funext i
    fin_cases kind <;> fin_cases i <;> simp [moved,shift,sourceMove,passPhase,passDriver,HeadMove.apply,Nat.add_assoc]
  rw [ha,hm] at path
  exact path

theorem appendedMany_next (out : Fin 11 → List Bool) (phase k : Nat) :
    (fun i=>appendedMany out phase k i++blocks phase i)=appendedMany out phase (k+1) := by
  funext i
  simp only [appendedMany,repeatWord,List.replicate_succ',List.flatten_append,List.flatten_cons,
    List.flatten_nil,List.append_nil,List.append_assoc]

theorem pass_loop (kind : Fin 3) (source : Fin 4 → List Bool) (H : Fin 4 → Nat)
    (out : Fin 11 → List Bool) (n remaining k : Nat)
    (read : ∀ j≤n, readTapeBit (source (passDriver kind))
      (H (passDriver kind)+j)=decide (j<n)) (hk : k+remaining=n) :
    Timed raw ((width (passPhase kind).val+1)*remaining+1)
      (cfg (passCheck kind) source (shift H kind k) (appendedMany out (passPhase kind).val k))
      (cfg (passNext kind) source (shift H kind n) (appendedMany out (passPhase kind).val n)) := by
  have halt : raw.halted (passCheck kind)=false := by fin_cases kind <;> rfl
  induction remaining generalizing k with
  | zero =>
    have hkn : k=n := by omega
    subst k
    have hr : readTapeBit (source (passDriver kind)) ((shift H kind n) (passDriver kind))=false := by
      simpa only [shift,↓reduceIte,Nat.lt_irrefl,decide_false] using read n (by omega)
    have hs:=pass_check kind source (shift H kind n) (appendedMany out (passPhase kind).val n) false hr
    simpa only [Bool.false_eq_true,↓reduceIte,Nat.mul_zero,Nat.zero_add] using Timed.single halt hs
  | succ remaining ih =>
    have hr : readTapeBit (source (passDriver kind)) ((shift H kind k) (passDriver kind))=true := by
      simpa only [shift,↓reduceIte,show decide (k<n)=true from decide_eq_true (by omega)] using read k (by omega)
    have hs:=pass_check kind source (shift H kind k) (appendedMany out (passPhase kind).val k) true hr
    simp only [↓reduceIte] at hs
    have hc:=pass_chunk kind source H (appendedMany out (passPhase kind).val k) k
    rw [appendedMany_next] at hc
    have path:=((Timed.single halt hs).trans hc).trans (ih (k+1) (by omega))
    have ht : 1+width (passPhase kind).val+((width (passPhase kind).val+1)*remaining+1)=
        (width (passPhase kind).val+1)*(remaining+1)+1 := by
      rw [Nat.mul_add,Nat.mul_one]
      omega
    rw [ht] at path
    exact path

theorem pass_run (kind : Fin 3) (source : Fin 4 → List Bool) (H : Fin 4 → Nat)
    (out : Fin 11 → List Bool) (n : Nat)
    (read : ∀ j≤n, readTapeBit (source (passDriver kind))
      (H (passDriver kind)+j)=decide (j<n)) :
    Timed raw ((width (passPhase kind).val+1)*n+1)
      (cfg (passCheck kind) source H out)
      (cfg (passNext kind) source (shift H kind n) (appendedMany out (passPhase kind).val n)) := by
  have path:=pass_loop kind source H out n n 0 read (by omega)
  have h0 : shift H kind 0=H := by
    funext i
    simp only [shift,ite_self,Nat.add_zero]
  have o0 : appendedMany out (passPhase kind).val 0=out := by
    funext i
    simp only [appendedMany,repeatWord_zero,List.append_nil]
  rw [h0,o0] at path
  exact path


end PCJ45bee56da9f34d5a_Constants

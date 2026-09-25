import Proof.Rows.PhysicalFocusBoundary

/-! Compare two actual unary counters and write their order bit. Paid head
reset restores both counters; equal counters, including zero, are accepted. -/
set_option autoImplicit false
set_option maxHeartbeats 650000
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unusedSimpArgs false
namespace PCJ9eff70d512234a4c_Fixed.Materializer.UnaryCompareFlag
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.RepairOrdinary.RecoveryExecution NearCubicWires.ExtDecompositionBatch
open NearCubicWires.RepairSource.VerifierDecoding

def machine : Machine 3 2 where
  descriptionBits:=0
  start:=0
  halted:=fun q=>q.val==1
  rule:=fun q scan=>if q.val=0 then
    if scan 0 && scan 1 then some ⟨0,fun _=>none,![.right,.right,.stay]⟩
    else some ⟨1,![none,none,some (!scan 0)],fun _=>.stay⟩
    else none

def heads (pos : Nat) : Fin 3→Nat:=![pos+1,pos+1,0]
def data (n m : Nat) (flag : Bool) : Fin 3→List Bool:=![CompareMachine.word n,CompareMachine.word m,[flag]]
def cfg (q : Fin 2) (n m pos : Nat) (flag : Bool) : Configuration 3 2:=⟨q,heads pos,data n m flag⟩

theorem scan_step (n m pos : Nat) (flag : Bool) (hn : pos < n) (hm : pos < m) :
    step machine (cfg 0 n m pos flag)=some (cfg 0 n m (pos+1) flag) := by
  have h0:readTapeBit (CompareMachine.word n) (pos+1)=true:=(CompareMachine.read_mark n pos).trans (decide_eq_true hn)
  have h1:readTapeBit (CompareMachine.word m) (pos+1)=true:=(CompareMachine.read_mark m pos).trans (decide_eq_true hm)
  simp only [step,machine,cfg,Configuration.scanned,data,heads,Matrix.cons_val_zero,
    Matrix.cons_val_one,Matrix.cons_val_two,h0,h1,Bool.true_and,↓reduceIte]
  apply congrArg some
  apply configuration_ext
  · rfl
  · funext i;fin_cases i  <;>simp [applyAction,heads,HeadMove.apply]
  · rfl

theorem scan (n m k pos : Nat) (flag : Bool) (hn : pos+k ≤ n) (hm : pos+k ≤ m) :
    Timed machine k (cfg 0 n m pos flag) (cfg 0 n m (pos+k) flag) := by
  induction k generalizing pos with
  | zero=>simpa only [Nat.add_zero] using Timed.refl machine (cfg 0 n m pos flag)
  | succ k ih=>
    have one:=Timed.single (by rfl) (scan_step n m pos flag (by omega) (by omega))
    have rest:=ih (pos+1) (by omega) (by omega)
    simpa only [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using one.trans rest

theorem stop (n m : Nat) (flag : Bool) :
    step machine (cfg 0 n m (min n m) flag)=some (cfg 1 n m (min n m) (decide (n ≤ m))) := by
  by_cases h:n ≤ m
  · have hn:readTapeBit (CompareMachine.word n) (min n m+1)=false:=by
      rw [Nat.min_eq_left h,CompareMachine.read_mark];simp
    simp [step,machine,cfg,Configuration.scanned,data,heads,hn,h]
    apply configuration_ext
    · rfl
    · funext i;fin_cases i  <;>rfl
    · funext i;fin_cases i  <;>rfl
  · have hn:readTapeBit (CompareMachine.word n) (min n m+1)=true:=by
      rw [Nat.min_eq_right (by omega),CompareMachine.read_mark];simp;omega
    have hm:readTapeBit (CompareMachine.word m) (min n m+1)=false:=by
      rw [Nat.min_eq_right (by omega),CompareMachine.read_mark];simp
    simp [step,machine,cfg,Configuration.scanned,data,heads,hn,hm,h]
    apply configuration_ext
    · rfl
    · funext i;fin_cases i  <;>rfl
    · funext i;fin_cases i  <;>rfl

theorem run (n m : Nat) (flag : Bool) :
    Step machine (min n m+1) (heads 0) (data n m flag)
      (heads (min n m)) (data n m (decide (n ≤ m))) := by
  have a:=scan n m (min n m) 0 flag (by omega) (by omega)
  simp only [Nat.zero_add] at a
  have all:=a.trans (Timed.single (by rfl) (stop n m flag))
  obtain ⟨r,hr,hf,_⟩:=all.run (by rfl)
  exact Step.of_run hr (congrArg Configuration.heads hf) (congrArg Configuration.tapes hf)

def boot : Machine 3 2 where
  descriptionBits:=0
  start:=0
  halted:=fun q=>q.val==1
  rule:=fun q _=>if q.val=0 then some ⟨1,fun _=>none,![.right,.right,.stay]⟩ else none

theorem boot_run (a : Fin 3→List Bool) : Step boot 1 (fun _=>0) a (heads 0) a := by
  have hs : step boot (⟨0,fun _=>0,a⟩ : Configuration 3 2)=some ⟨1,heads 0,a⟩ := by
    simp [step,boot]
    apply configuration_ext
    · rfl
    · funext i;fin_cases i <;>rfl
    · rfl
  obtain ⟨r,hr,hf,_⟩:=(Timed.single (by rfl) hs).run (by rfl)
  exact Step.of_run hr (congrArg Configuration.heads hf) (congrArg Configuration.tapes hf)

def selected (i : Fin 3):Bool:=decide (i.val < 2)
noncomputable def core:=Composition.machine boot machine
noncomputable def ready:=MaskedReset.machine core selected

theorem ready_run (R n m : Nat) (flag : Bool) (hR : min n m+3 ≤ R) :
    Step ready (2*min n m+8) (fun _ : Fin 4=>0)
      ![ZeroPadding.pad R (CompareMachine.word n),ZeroPadding.pad R (CompareMachine.word m),[flag],List.replicate R false]
      (fun _ : Fin 4=>0)
      ![ZeroPadding.pad R (CompareMachine.word n),ZeroPadding.pad R (CompareMachine.word m),[decide (n ≤ m)],List.replicate R false] := by
  have raw:=(boot_run (data n m flag)).seq (run n m flag)
  have h:=(raw.pad (![R,R,0] : Fin 3→Nat)).mask selected (by intros;rfl) (by omega : 1+1+(min n m+1)≤R)
  rw [show 2*(1+1+(min n m+1))+2=2*min n m+8 by omega] at h
  refine (h.congr_in ?_ ?_).congr ?_ ?_
  all_goals funext i;fin_cases i <;>simp [heads,data,selected,Fin.addCases,ZeroPadding.pad_zero]

end PCJ9eff70d512234a4c_Fixed.Materializer.UnaryCompareFlag

import Proof.Assembly.RowsConstantPairs

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unusedVariables false

namespace PCJ45bee56da9f34d5a_Constants
open NearCubicWires NearCubicWires.LocalBitMultitape
open NearCubicWires.RepairOrdinary RecoveryExecution
open NearCubicWires.ExtDecompositionBatch
open NearCubicWires.RepairOrdinary.RecoveryRootRound

def source (p n Q C : Nat) : Fin 4 → List Bool :=
  ![List.replicate p true,UnaryTemplate.tape n,false::List.replicate Q true,List.replicate C true]

def output (p n Q C : Nat) : Fin 16 → List Bool :=
  fun i=>Fin.addCases (m:=15) (n:=1)
    (fun j=>Fin.addCases (m:=4) (n:=11) (source p n Q C) (fields p n Q C) j)
    (fun _=>List.replicate (rawBudget p n Q C) false) i

theorem raw_run (p n Q C : Nat) :
    ∃ H, Timed raw (rawBudget p n Q C)
      (cfg 0 (source p n Q C) (fun _=>0) (fun _=>[]))
      (cfg 741 (source p n Q C) H (fields p n Q C)) := by
  let S:=source p n Q C
  let A : Fin 11 → List Bool := blocks 0
  let B:=appendedMany A 2 p
  let D:=fun i=>appendedMany B 4 ((n+1)/2) i++blocks (if n%2=1 then 7 else 6) i
  let E:=appendedMany D 9 Q
  let F:=appendedMany E 11 C
  have hstart:=chunk (0 : Fin 13) (by simp [Emits]) S (fun _=>0) (fun _=>[])
  have hs : moved (fun _=>0) (0 : Fin 13).val true=(![0,1,0,0] : Fin 4 → Nat) := by
    funext i;fin_cases i <;> rfl
  rw [hs] at hstart
  simp only [List.nil_append] at hstart
  have hp:=pass_run 0 S (![0,1,0,0] : Fin 4 → Nat) A p (by
    intro j hj
    simpa only [passDriver,S,source,Matrix.cons_val_zero,Nat.zero_add] using
      ClockUnaryProduct.read_unary p j)
  have hpHead : shift (![0,1,0,0] : Fin 4 → Nat) 0 p=![p,1,0,0] := by
    funext i;fin_cases i <;> simp [shift,passDriver]
  rw [hpHead] at hp
  have hn:=n_run S (![p,1,0,0] : Fin 4 → Nat) B n (by
    intro j hj
    change readTapeBit (UnaryTemplate.tape n) (1+j)=decide (j<n)
    rw [Nat.add_comm 1]
    by_cases h : j<n
    · rw [UnaryTemplate.tape_mark n j h];simp [h]
    · have he : j=n := by omega
      subst j
      simp)
  have hnHead : shift (nShift (![p,1,0,0] : Fin 4 → Nat) n) 1 1=![p,n+1,1,0] := by
    funext i;fin_cases i <;> simp [shift,nShift,passDriver,Nat.add_comm]
  rw [hnHead] at hn
  have hQ:=pass_run 1 S (![p,n+1,1,0] : Fin 4 → Nat) D Q (by
    intro j hj
    change readTapeBit (false::List.replicate Q true) (1+j)=decide (j<Q)
    rw [Nat.add_comm 1]
    exact ClockUnaryProduct.read_sentinel Q j)
  have hQHead : shift (![p,n+1,1,0] : Fin 4 → Nat) 1 Q=![p,n+1,Q+1,0] := by
    funext i;fin_cases i <;> simp [shift,passDriver,Nat.add_comm]
  rw [hQHead] at hQ
  have hC:=pass_run 2 S (![p,n+1,Q+1,0] : Fin 4 → Nat) E C (by
    intro j hj
    change readTapeBit (List.replicate C true) (0+j)=decide (j<C)
    simpa only [Nat.zero_add] using ClockUnaryProduct.read_unary C j)
  have hCHead : shift (![p,n+1,Q+1,0] : Fin 4 → Nat) 2 C=![p,n+1,Q+1,C] := by
    funext i;fin_cases i <;> simp [shift,passDriver]
  rw [hCHead] at hC
  have hlast:=chunk (12 : Fin 13) (by simp [Emits]) S (![p,n+1,Q+1,C] : Fin 4 → Nat) F
  have lastHead : moved (![p,n+1,Q+1,C] : Fin 4 → Nat) (12 : Fin 13).val true=![p,n+1,Q+1,C] := by
    funext i;fin_cases i <;> rfl
  rw [lastHead] at hlast
  have h12 : ((12 : Fin 13) : Nat)=12 := rfl
  rw [h12] at hlast
  have ho : (fun i=>F i++blocks 12 i)=fields p n Q C := by
    rw [←produced_fields]
    funext i
    simp only [F,E,D,B,A,appendedMany,produced,List.append_assoc]
  rw [ho] at hlast
  have path:=(((((hstart.trans hp).trans hn).trans hQ).trans hC).trans hlast)
  have ht : 56+(17*p+1)+(n+16*((n+1)/2)+4)+(9*Q+1)+(3*C+1)+3=rawBudget p n Q C := by
    unfold rawBudget;omega
  change Timed raw (56+(17*p+1)+(n+16*((n+1)/2)+4)+(9*Q+1)+(3*C+1)+3) _ _ at path
  rw [ht] at path
  exact ⟨_,path⟩

theorem run (p n Q C : Nat) :
    Step machine (2*rawBudget p n Q C+2) (fun _=>0) (input p n Q C)
      (fun _=>0) (output p n Q C) := by
  obtain ⟨H,path⟩:=raw_run p n Q C
  obtain ⟨r,hr,hf,hs⟩:=path.run (by rfl)
  obtain ⟨z,hz,hzf,_,_⟩:=Rewind.recorded_run raw (rawBudget p n Q C)
    (cfg 0 (source p n Q C) (fun _=>0) (fun _=>[])) r hr 0 (by
      intro i
      refine Fin.addCases (m:=4) (n:=11) (fun j=>?_) (fun j=>?_) i <;> simp [cfg])
  rw [hs] at hz hzf
  simp only [Nat.zero_add] at hz hzf
  have hi : Rewind.recording (cfg 0 (source p n Q C) (fun _=>0) (fun _=>[])) 0=
      (⟨machine.start,fun _=>0,input p n Q C⟩ : Configuration 16 800) := by
    apply configuration_ext
    · rfl
    · funext i
      refine Fin.addCases (m:=15) (n:=1) (fun j=>?_) (fun j=>?_) i
      · refine Fin.addCases (m:=4) (n:=11) (fun k=>?_) (fun k=>?_) j <;>
          simp [Rewind.recording,Rewind.config,cfg]
      · simp [Rewind.recording,Rewind.config]
    · rfl
  rw [hi] at hz
  refine Step.of_run hz ?_ ?_
  · rw [hzf]
    funext i
    refine Fin.addCases (m:=15) (n:=1) (fun j=>?_) (fun j=>?_) i <;>
      simp [Rewind.finished,Rewind.config]
  · rw [hzf,hf]
    rfl


end PCJ45bee56da9f34d5a_Constants

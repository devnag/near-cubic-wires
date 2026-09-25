import Proof.Rows.MaskProductBody

/-! Constant polynomial banks are physically generated from the runtime
width template. No all-false mask or result-count word is supplied as input. -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 120000
set_option warningAsError true
namespace PCJ9eff70d512234a4c_Fixed.Materializer.MaskConstant
open NearCubicWires NearCubicWires.LocalBitMultitape
open NearCubicWires.RepairOrdinary NearCubicWires.RepairOrdinary.RecoveryExecution
open NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairSource.VerifierDecoding

def maskMachine : Machine 2 3 where
  descriptionBits := 0
  start := 0
  halted := fun q=>q.val==2
  rule := fun q scan=>if q.val=0 then
    some (if scan 0 then ⟨0,![none,some false],![.right,.right]⟩
      else ⟨1,fun _=>none,![.left,.stay]⟩)
    else if q.val=1 then
      some (if scan 0 then ⟨1,fun _=>none,![.left,.left]⟩
        else ⟨2,fun _=>none,![.right,.stay]⟩)
    else none

def cfg (q : Fin 3) (B dh pos : Nat) (out : List Bool) : Configuration 2 3 :=
  ⟨q,![dh,pos],![UnaryTemplate.tape B,out]⟩

theorem copy_step (B k : Nat) (out : List Bool) (hk : k<B) :
    step maskMachine (cfg 0 B (k+1) out.length out)=
      some (cfg 0 B (k+2) (out++[false]).length (out++[false])) := by
  simp [step,maskMachine,cfg,Configuration.scanned,UnaryTemplate.tape_mark B k hk]
  apply configuration_ext
  · rfl
  · funext i;fin_cases i <;> simp [applyAction,HeadMove.apply]
  · funext i;fin_cases i <;> simp [applyAction,Streaming.write_append]

theorem copy (B n done : Nat) (out : List Bool) (hn : done+n=B) :
    Timed maskMachine n (cfg 0 B (done+1) out.length out)
      (cfg 0 B (B+1) (out++List.replicate n false).length (out++List.replicate n false)) := by
  induction n generalizing done out with
  | zero =>
    have hd : done=B := by omega
    subst done
    simpa using Timed.refl maskMachine (cfg 0 B (B+1) out.length out)
  | succ n ih =>
    have first:=Timed.single (by rfl) (copy_step B done out (by omega))
    have rest:=ih (done+1) (out++[false]) (by omega)
    have h:=first.trans (by simpa only [Nat.add_assoc] using rest)
    simpa [List.append_assoc,List.replicate_succ,Nat.add_comm] using h

theorem turn (B pos : Nat) (out : List Bool) :
    step maskMachine (cfg 0 B (B+1) pos out)=some (cfg 1 B B pos out) := by
  simp [step,maskMachine,cfg,Configuration.scanned]
  apply configuration_ext
  · rfl
  · funext i;fin_cases i <;> simp [applyAction,HeadMove.apply]
  · rfl

theorem back_step (B k base : Nat) (out : List Bool) (hk : k<B) :
    step maskMachine (cfg 1 B (k+1) (base+k+1) out)=
      some (cfg 1 B k (base+k) out) := by
  simp [step,maskMachine,cfg,Configuration.scanned,UnaryTemplate.tape_mark B k hk]
  apply configuration_ext
  · rfl
  · funext i;fin_cases i <;> simp [applyAction,HeadMove.apply]
  · rfl

theorem back_stop (B base : Nat) (out : List Bool) :
    step maskMachine (cfg 1 B 0 base out)=some (cfg 2 B 1 base out) := by
  simp [step,maskMachine,cfg,Configuration.scanned]
  apply configuration_ext
  · rfl
  · funext i;fin_cases i <;> simp [applyAction,HeadMove.apply]
  · rfl

theorem back (B k base : Nat) (out : List Bool) (hk : k≤B) :
    Timed maskMachine (k+1) (cfg 1 B k (base+k) out) (cfg 2 B 1 base out) := by
  induction k with
  | zero => simpa using Timed.single (by rfl) (back_stop B base out)
  | succ k ih =>
    have h:=(Timed.single (by rfl) (back_step B k base out (by omega))).trans (ih (by omega))
    simpa [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using h

theorem mask_run (B : Nat) (out : List Bool) :
    ∃ r,runFrom maskMachine (2*B+2) (cfg 0 B 1 out.length out)=some r ∧
      r.final=cfg 2 B 1 out.length (out++List.replicate B false) ∧ r.steps=2*B+2 := by
  have first:=copy B B 0 out (by omega)
  have second:=Timed.single (by rfl) (turn B (out++List.replicate B false).length
    (out++List.replicate B false))
  have last:=back B B out.length (out++List.replicate B false) le_rfl
  have h:=first.trans (second.trans (by simpa only [List.length_append,List.length_replicate] using last))
  have fuel : B+(1+(B+1))=2*B+2 := by omega
  simpa only [Nat.zero_add,fuel] using h.run (by rfl)

def countMachine (one : Bool) : Machine 1 3 where
  descriptionBits := 0
  start := 0
  halted := fun q=>q.val==2
  rule := fun q _=>if q.val=0 then
    some ⟨if one then 1 else 2,fun _=>some false,fun _=>.right⟩
    else if q.val=1 then some ⟨2,fun _=>some true,fun _=>.stay⟩
    else none

def countCfg (q : Fin 3) (pos : Nat) (out : List Bool) : Configuration 1 3 :=
  ⟨q,fun _=>pos,fun _=>out⟩

theorem seed_step (one : Bool) :
    step (countMachine one) (countCfg 0 0 [])=
      some (countCfg (if one then 1 else 2) 1 [false]) := by
  simp [step,countMachine,countCfg]
  apply configuration_ext
  · rfl
  · funext i;simp [applyAction,HeadMove.apply]
  · funext i;rfl

theorem one_step :
    step (countMachine true) (countCfg 1 1 [false])=some (countCfg 2 1 [false,true]) := by
  simp [step,countMachine,countCfg]
  apply configuration_ext
  · rfl
  · funext i;simp [applyAction,HeadMove.apply]
  · funext i;rfl

theorem count_run (one : Bool) :
    ∃ r,runFrom (countMachine one) (if one then 2 else 1) (countCfg 0 0 [])=some r ∧
      r.final=countCfg 2 1 (CompareMachine.word (if one then 1 else 0)) ∧
      r.steps=(if one then 2 else 1) := by
  cases one with
  | false => exact (Timed.single (by rfl) (seed_step false)).run (by rfl)
  | true => exact ((Timed.single (by rfl) (seed_step true)).trans
      (Timed.single (by rfl) one_step)).run (by rfl)

noncomputable def countSlots : Fin 1→Fin 3 := ![2]
noncomputable def oneMachine := Composition.machine (TapeEmbedding.machine 1 maskMachine)
  (RecoveryFocus.machine countSlots (countMachine true))

end PCJ9eff70d512234a4c_Fixed.Materializer.MaskConstant

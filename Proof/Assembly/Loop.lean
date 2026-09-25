import Proof.Assembly.Window
import Proof.Assembly.Winner

set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

namespace PCJ93d4cfe17dc847a3.Loop
open NearCubicWires LocalBitMultitape RepairOrdinary RecoveryExecution ExtDecompositionBatch
open NearCubicWires.RepairSource.VerifierDecoding
open PCJc4297ab269d8423a_Source

def bodyFuel (d : MaskData) := 2*Reset.fuel d.q d.m+6*(d.m*d.q)+2*d.q+21

theorem position_step (d : MaskData) (j : Nat) (A : Fin 13 → List Bool) :
    Step Program.position 1 (ResetBank.afterHeads d j) A (State.heads d j) A := by
  obtain ⟨r,hr,hf,_⟩ := Program.single_run (t := 13) (fun _ => none)
    (fun i => if i.val=8 then .right else .stay) (ResetBank.afterHeads d j) A
  apply Step.of_run hr
  · rw [hf]
    funext i
    fin_cases i <;> rfl
  · rw [hf]
    rfl

theorem decision_step (d : MaskData) (j best : Nat) (old : List Bool)
    (hlen : old.length = d.q) :
    Step Program.decision (6*(d.m*d.q)+2*d.q+16)
      (State.heads d j) (ResetBank.afterBank d j best old)
      (State.heads d (j+1))
      (State.bank d (j+1) (max best (Winner.score d j)) (Window.winner d j best old)) := by
  obtain ⟨n,hb,ht⟩ := Decision.timed (State.heads d j) (ResetBank.afterBank d j best old)
    (Winner.score d j) best (Window.pre d j) (Window.slice d j) old (Window.rest d j)
    (hlen.trans (Window.slice_length d j).symm) rfl rfl rfl
    (Window.pre_length d j).symm rfl rfl rfl
    (by rw [Window.slice_length]; rfl) (Window.decomposition d j).symm rfl
  obtain ⟨r,hr,hf,_⟩ := ht.run (by simp [Program.decision,RecoveryCalls.machine,RecoveryCalls.stopped])
  have hrun : Step Program.decision n (State.heads d j) (ResetBank.afterBank d j best old)
      (State.heads d (j+1))
      (State.bank d (j+1) (max best (Winner.score d j)) (Window.winner d j best old)) := by
    apply Step.of_run hr
    · rw [hf]
      exact Window.heads_next d j
    · rw [hf]
      exact Window.output_bank d j best old
  apply hrun.enlarge
  rw [Window.slice_length] at hb
  have hs := State.result_bound d (d.q-j)
  change Winner.score d j ≤ d.m*d.q at hs
  omega

theorem body_step (d : MaskData) (j : Nat) (hj : j < d.q) :
    Step Program.body (bodyFuel d)
      (State.heads d j) (State.bank d j (Winner.scan d j).1 (Winner.scan d j).2)
      (State.heads d (j+1)) (State.bank d (j+1) (Winner.scan d (j+1)).1 (Winner.scan d (j+1)).2) := by
  obtain ⟨r,hr,hh,ha,_⟩ := ResetBank.run d j (Winner.scan d j).1 (Winner.scan d j).2
  have reset := Step.of_run hr hh ha
  have pos := position_step d j (ResetBank.afterBank d j (Winner.scan d j).1 (Winner.scan d j).2)
  have dec := decision_step d j (Winner.scan d j).1 (Winner.scan d j).2
    (Winner.length d j (by omega))
  have hword : Window.winner d j (Winner.scan d j).1 (Winner.scan d j).2 =
      (Winner.scan d (j+1)).2 := by
    change (if (Winner.scan d j).1 < Winner.score d j then Window.slice d j else (Winner.scan d j).2) = _
    rw [show Window.slice d j = Winner.word d j from Bridge.slice_eq d j hj]
    rfl
  have joined := reset.seq (pos.seq dec)
  rw [hword] at joined
  convert joined using 1 <;> first | rfl | (simp [bodyFuel,Nat.add_assoc]; omega)

noncomputable def state (d : MaskData) (j : Nat) (_ : List Bool) :=
  (⟨Program.body.start,State.heads d j,
    State.bank d j (Winner.scan d j).1 (Winner.scan d j).2⟩ : Configuration 13 _)

theorem outer_run (d : MaskData) :
    ∃ r, runFrom Program.outer (d.q*(bodyFuel d+3)+3)
      (RepeatMachine.cfg 0 (state d 0 []) d.q 1) = some r ∧
      r.final = RepeatMachine.cfg 3 (state d d.q []) d.q 1 ∧
      r.steps ≤ d.q*(bodyFuel d+3)+3 := by
  simpa [Program.outer,state] using
    CloseoutRowsDegreeLoop.loop_run Program.body (state d) (fun _ => []) (bodyFuel d) d.q
      (by intros; rfl) (by intro j hj out; exact body_step d j hj) []

end PCJ93d4cfe17dc847a3.Loop

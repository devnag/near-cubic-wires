import Proof.Assembly.DecisionOps

/-! The actual finite comparison/update/clear/shift call graph. Both branches
include their return transitions and preserve the literal ambient words. -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unusedVariables false

namespace PCJ93d4cfe17dc847a3.Decision
open NearCubicWires LocalBitMultitape RepairOrdinary RecoveryExecution RecoveryRootRound
open NearCubicWires.RepairSource.VerifierDecoding

noncomputable def entry (j : Fin 5) (H : Fin 13 → Nat) (A : Fin 13 → List Bool) :=
  controlConfig (RecoveryCalls.code Program.sizes j) ⟨(Program.parts j).start,H,A⟩

def shiftHeads (H : Fin 13 → Nat) (i : Fin 13) : Nat :=
  if i.val=5 ∨ i.val=6 ∨ i.val=7 then H i-1 else H i

noncomputable def updated (A : Fin 13 → List Bool) (old n : Nat) (xs : List Bool) :=
  if old < n then Function.update (Function.update A 11 (CompareMachine.word (max old n))) 4 xs
  else A
noncomputable def output (A : Fin 13 → List Bool) (old n : Nat) (xs : List Bool) :=
  Function.update (updated A old n xs) 8 (List.replicate (max old n+1) false)

theorem call (j l : Fin 5) (H : Fin 13 → Nat) (A B : Fin 13 → List Bool)
    (state : Fin (Program.sizes j)) (fuel : Nat) (r : ExecutionReceipt 13 (Program.sizes j))
    (hr : runFrom (Program.parts j) fuel ⟨(Program.parts j).start,H,A⟩ = some r)
    (hf : r.final = ⟨state,H,B⟩)
    (hn : ∀ bits, Program.next j state bits = some l) :
    ∃ n ≤ fuel+1, Timed Program.decision n (entry j H A) (entry l H B) := by
  obtain ⟨n,hb,ht⟩ := call_receipt Program.sizes Program.parts 0 Program.next j l fuel _ r hr
    (by rw [hf]; exact hn _)
  rw [hf] at ht
  exact ⟨n,hb,ht⟩

theorem shift (H : Fin 13 → Nat) (A : Fin 13 → List Bool) :
    ∃ n ≤ 2, Timed Program.decision n (entry 4 H A)
      (RecoveryCalls.stopped Program.sizes (shiftHeads H) A) := by
  obtain ⟨r,hr,hf,ht⟩ := Program.single_run (t := 13) (fun _ => none)
    (fun i => if i.val=5 ∨ i.val=6 ∨ i.val=7 then .left else .stay) H A
  have he : r.final = (⟨1,shiftHeads H,A⟩ : Configuration 13 2) := by
    rw [hf]
    apply configuration_ext
    · rfl
    · funext i; simp [applyAction,shiftHeads,HeadMove.apply]; split_ifs <;> rfl
    · rfl
  obtain ⟨n,hb,hstep⟩ := stop_receipt Program.sizes Program.parts 0 Program.next 4 1 _ r hr
    (by simp [Program.next])
  rw [he] at hstep
  exact ⟨n,hb,hstep⟩

theorem tail (H : Fin 13 → Nat) (A : Fin 13 → List Bool) (n old : Nat)
    (h8 : H 8 = 1) (a8 : A 8 = ZeroPadding.pad (old+1) (CompareMachine.word n)) :
    ∃ steps ≤ 2*n+5, Timed Program.decision steps (entry 3 H A)
      (RecoveryCalls.stopped Program.sizes (shiftHeads H)
        (Function.update A 8 (List.replicate (max old n+1) false))) := by
  obtain ⟨r,hr,hf,_⟩ := DecisionOps.clear H A n old h8 a8
  obtain ⟨n1,h1,t1⟩ := call 3 4 H A _ 2 (2*n+2) r hr hf (by intro bits; rfl)
  obtain ⟨n2,h2,t2⟩ := shift H (Function.update A 8 (List.replicate (max old n+1) false))
  exact ⟨n1+n2,by omega,t1.trans t2⟩

theorem timed (H : Fin 13 → Nat) (A : Fin 13 → List Bool) (n old : Nat)
    (pre xs winner rest : List Bool) (hlen : winner.length = xs.length)
    (h8 : H 8 = 1) (h11 : H 11 = 1)
    (h1 : H 1 = 1) (h5 : H 5 = pre.length) (h4 : H 4 = 0)
    (a8 : A 8 = ZeroPadding.pad (old+1) (CompareMachine.word n))
    (a11 : A 11 = CompareMachine.word old)
    (a1 : A 1 = CompareMachine.word xs.length)
    (a5 : A 5 = pre++xs++rest) (a4 : A 4 = winner) :
    ∃ steps ≤ 6*n+2*xs.length+16, Timed Program.decision steps (entry 0 H A)
      (RecoveryCalls.stopped Program.sizes (shiftHeads H) (output A old n xs)) := by
  classical
  obtain ⟨r,hr,hf,_⟩ := DecisionOps.compare H A n old h8 h11 a8 a11
  have hmin := Nat.min_le_left n old
  by_cases hb : old < n
  · have hn : ¬ n ≤ old := by omega
    rw [if_neg hn] at hf
    obtain ⟨n0,h0,t0⟩ := call 0 1 H A A 6 (2*min n old+3) r hr hf (by intro bits; rfl)
    obtain ⟨r1,hr1,hf1,_⟩ := DecisionOps.best H A n old h8 h11 a8 a11
    let A1 := Function.update A 11 (CompareMachine.word (max old n))
    obtain ⟨n1,hb1,t1⟩ := call 1 2 H A A1 2 (2*n+2) r1 hr1 hf1 (by intro bits; rfl)
    obtain ⟨r2,hr2,hf2,_⟩ := DecisionOps.copy H A1 pre xs winner rest hlen h1 h5 h4
      (by simpa [A1] using a1) (by simpa [A1] using a5) (by simpa [A1] using a4)
    let A2 := Function.update A1 4 xs
    obtain ⟨n2,hb2,t2⟩ := call 2 3 H A1 A2 2 (2*xs.length+2) r2 hr2 hf2
      (by intro bits; rfl)
    obtain ⟨n3,hb3,t3⟩ := tail H A2 n old h8 (by simpa [A2,A1] using a8)
    refine ⟨n0+n1+n2+n3,by omega,?_⟩
    simpa only [output,updated,if_pos hb] using ((t0.trans t1).trans t2).trans t3
  · have hn : n ≤ old := by omega
    rw [if_pos hn] at hf
    obtain ⟨n0,h0,t0⟩ := call 0 3 H A A 5 (2*min n old+3) r hr hf (by intro bits; rfl)
    obtain ⟨n1,hb1,t1⟩ := tail H A n old h8 a8
    refine ⟨n0+n1,by omega,?_⟩
    simpa only [output,updated,if_neg hb] using t0.trans t1

end PCJ93d4cfe17dc847a3.Decision

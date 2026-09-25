import Proof.Assembly.ResetShape
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unusedVariables false

namespace PCJ93d4cfe17dc847a3.ResetBank
open NearCubicWires LocalBitMultitape RepairOrdinary RecoveryExecution
open NearCubicWires.RepairSource.VerifierDecoding
open PCJc4297ab269d8423a_Source

def afterHeads (d : MaskData) (iteration : Nat) : Fin 13 → Nat :=
  ![0,1,0,1,0,d.q-iteration,d.q-iteration,d.q-iteration,0,0,0,1,0]

noncomputable def afterBank (d : MaskData) (iteration best : Nat) (winner : List Bool) :
    Fin 13 → List Bool :=
  ![d.supportWord,CompareMachine.word d.q,CompareMachine.word d.K,CompareMachine.word d.m,
    winner,State.double d,[],[],
    ZeroPadding.pad (best+1) (CompareMachine.word (State.result d (d.q-iteration)).1),
    [false],[false],CompareMachine.word best,List.replicate (Reset.fuel d.q d.m) false]

theorem assemble_heads (d : MaskData) (iteration : Nat) (H : Fin 13 → Nat)
    (hs : ∀ k, H (Program.resetSlots k) =
      (![0,d.q-iteration,d.q-iteration,d.q-iteration,0,0,0,1,1,0] : Fin 10 → Nat) k)
    (h2 : H 2 = 0) (h4 : H 4 = 0) (h11 : H 11 = 1) : H = afterHeads d iteration := by
  funext i
  fin_cases i
  · exact hs 0
  · exact hs 7
  · exact h2
  · exact hs 8
  · exact h4
  · exact hs 3
  · exact hs 1
  · exact hs 2
  · exact hs 4
  · exact hs 5
  · exact hs 6
  · exact h11
  · exact hs 9

theorem assemble_bank (d : MaskData) (iteration best : Nat) (winner : List Bool)
    (A : Fin 13 → List Bool)
    (hs : ∀ k, A (Program.resetSlots k) = ZeroPadding.pad (capacity best k)
      ((Reset.finished d.q (State.logCapacity d iteration) (State.rows d)
          (State.masks d) (d.q-iteration)).tapes k))
    (h2 : A 2 = CompareMachine.word d.K) (h4 : A 4 = winner)
    (h11 : A 11 = CompareMachine.word best) : A = afterBank d iteration best winner := by
  simp only [final_tapes] at hs
  have hc : State.logCapacity d iteration ≤ Reset.fuel d.q d.m := by
    simp only [State.logCapacity]
    split_ifs <;> omega
  funext i
  fin_cases i
  · simpa [capacity,Program.resetSlots,afterBank] using hs 0
  · simpa [capacity,Program.resetSlots,afterBank] using hs 7
  · exact h2
  · simpa [capacity,Program.resetSlots,afterBank] using hs 8
  · exact h4
  · simpa [capacity,Program.resetSlots,afterBank] using hs 3
  · simpa [capacity,Program.resetSlots,afterBank] using hs 1
  · simpa [capacity,Program.resetSlots,afterBank] using hs 2
  · simpa [capacity,Program.resetSlots,afterBank] using hs 4
  · simpa [capacity,Program.resetSlots,afterBank] using hs 5
  · simpa [capacity,Program.resetSlots,afterBank] using hs 6
  · exact h11
  · simpa [capacity,Program.resetSlots,afterBank,max_eq_right hc] using hs 9

theorem run (d : MaskData) (iteration best : Nat) (winner : List Bool) :
    ∃ r, runFrom (RecoveryFocus.machine Program.resetSlots Reset.machine)
      (2*Reset.fuel d.q d.m+2)
      ⟨(RecoveryFocus.machine Program.resetSlots Reset.machine).start,
        State.heads d iteration,State.bank d iteration best winner⟩ = some r ∧
      r.final.heads = afterHeads d iteration ∧
      r.final.tapes = afterBank d iteration best winner ∧ r.steps = 2*Reset.fuel d.q d.m+2 := by
  obtain ⟨s,hs,hf,ht⟩ := Reset.reset_run d.q (State.logCapacity d iteration)
    (State.rows d) (State.masks d) (d.q-iteration) (State.row_length d)
  rw [State.rows_length] at hs ht
  obtain ⟨p,hp,hpf,hpt,_⟩ := ZeroPadding.run_config Reset.machine (capacity best) _ _ s hs
  have hh : ∀ k, (State.heads d iteration) (Program.resetSlots k) =
      (ZeroPadding.config (capacity best)
        (Reset.initial d.q (State.logCapacity d iteration) (State.rows d)
          (State.masks d) (d.q-iteration))).heads k := by
    intro k
    change (State.heads d iteration) (Program.resetSlots k) =
      (Reset.initial d.q (State.logCapacity d iteration) (State.rows d)
        (State.masks d) (d.q-iteration)).heads k
    rw [initial_heads]
    fin_cases k <;> rfl
  have hb : ∀ k, (State.bank d iteration best winner) (Program.resetSlots k) =
      (ZeroPadding.config (capacity best)
        (Reset.initial d.q (State.logCapacity d iteration) (State.rows d)
          (State.masks d) (d.q-iteration))).tapes k := by
    intro k
    simp only [ZeroPadding.config,initial_tapes]
    fin_cases k <;> simp [capacity,State.bank,Program.resetSlots,State.candidate_empty]
  obtain ⟨r,hr,_,hrt,hrh,hrb,hother⟩ := RecoveryFocus.dock Program.resetSlots
    Program.resetSlots_injective Reset.machine _ (State.heads d iteration)
    (State.bank d iteration best winner) _ hh hb p hp
  refine ⟨r,hr,?_,?_,hrt.trans (hpt.trans ht)⟩
  · apply assemble_heads d iteration
    · simpa only [hpf,hf,ZeroPadding.config,final_heads] using hrh
    · exact (hother 2 (by decide)).1
    · exact (hother 4 (by decide)).1
    · exact (hother 11 (by decide)).1
  · apply assemble_bank d iteration best winner
    · simpa only [hpf,hf,ZeroPadding.config] using hrb
    · exact (hother 2 (by decide)).2
    · exact (hother 4 (by decide)).2
    · exact (hother 11 (by decide)).2

end PCJ93d4cfe17dc847a3.ResetBank

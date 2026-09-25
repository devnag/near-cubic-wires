import Proof.Rows.FinalNativeResidueRestore

namespace NearCubicWires.RepairSource.CloseoutFinal.C10NativeResidueReset
open LocalBitMultitape RepairOrdinary RecoveryExecution RecoveryRootRound ExtDecompositionBatch
open RepairRepresentation VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def head (pos len : ℕ) : Fin 27 → ℕ := fun i=>if i=0 then pos else if i=22 then len else 0

/-- Local tape support depends on this tape's own initial head, not on the
retained source cursor or accumulated coefficient-stream length. -/
theorem support_at {t s : ℕ} (p : Machine t s) (i : Fin t) (fuel : ℕ)
    (c : Configuration t s) (r : ExecutionReceipt t s) (hr : runFrom p fuel c=some r)
    (cap pos : ℕ) (hh : c.heads i≤pos) (ht : (c.tapes i).length≤ max cap (pos+1)) :
    (r.final.tapes i).length≤ max cap (pos+r.steps+1) := by
  induction fuel generalizing c r pos with
  | zero =>
    simp only [runFrom] at hr
    split at hr
    · cases hr; simpa using ht
    · contradiction
  | succ fuel ih =>
    simp only [runFrom] at hr
    split at hr
    · cases hr; simpa using ht
    · cases hs : step p c with
      | none => simp [hs] at hr
      | some d =>
        cases htail : runFrom p fuel d with
        | none => simp [hs,htail] at hr
        | some tail =>
          simp only [hs,htail,Option.some.injEq] at hr
          subst r
          have hnext : d.heads i≤pos+1 ∧ (d.tapes i).length≤ max cap (pos+1+1) := by
            unfold step at hs
            obtain ⟨a,_,he⟩ := Option.map_eq_some_iff.mp hs
            subst d
            constructor
            · simp only [applyAction]
              cases a.move i <;> simp only [HeadMove.apply] <;> omega
            · simp only [applyAction]
              cases a.write i
              · dsimp only; omega
              · simp only [RecoveryTapeSupport.write_length]; omega
          have h := ih d tail htail (pos+1) hnext.1 hnext.2
          simpa only [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using h

end NearCubicWires.RepairSource.CloseoutFinal.C10NativeResidueReset

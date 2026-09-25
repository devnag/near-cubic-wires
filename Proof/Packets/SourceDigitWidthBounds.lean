import Proof.Packets.SourceDigitWidth

/-! Polynomial execution and workspace bounds for the actual width producer.
Padding is applied to the already allocated common-reserve bank. -/
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option warningAsError true
set_option linter.unusedSimpArgs false
namespace Completion.SourceDigitWidth
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.ExtDecompositionBatch
open NearCubicWires.RepairOrdinary NearCubicWires.RepairSource.VerifierDecoding

def capacity (M : Nat):=128*(M+1)^2

theorem budget_bound (M : Nat) : budget M+1 ≤ capacity M := by
  have hl:=Nat.log_le_self 2 M
  have hb:(CloseoutRowsCountBinary.bits M).length ≤ M+1:=by
    by_cases hm:M=0
    · subst M;simp [CloseoutRowsCountBinary.bits]
    · simp only [CloseoutRowsCountBinary.bits,if_neg hm,SignedSortKey.binary_length]
      exact Nat.add_le_add_right hl 1
  unfold budget capacity CloseoutRowsCountBinary.budget
  nlinarith

theorem padded_run (M R : Nat) (hr:capacity M ≤ R) : ∃ O,
    Step machine (budget M) (fun _=>0) (fun i=>ZeroPadding.pad R (input M i)) (fun _=>0) O ∧
    O 10=ZeroPadding.pad R (CompareMachine.word (digitWidth M)) ∧
    O 1=ZeroPadding.pad R (List.replicate M true) ∧
    O 3=ZeroPadding.pad R (UnaryTemplate.tape M) ∧
    O 5=ZeroPadding.pad R (frame (CloseoutRowsCountBinary.bits M)) ∧
    ∀i,(O i).length=R := by
  obtain ⟨A,step,h10,h1,h3,h5⟩:=run M
  have bound:∀i,(A i).length ≤ R:=by
    obtain ⟨r,rr,_rh,rt,rs⟩:=step
    intro i
    have hi:(input M i).length ≤ max M (0+1):=by
      simp only [input]
      split_ifs <;>simp
    have hb:=PCPSerializerReuse.tape_support machine (budget M) _ r rr i M 0 (by rfl) hi
    rw [rt] at hb
    have ht:budget M+1 ≤ R:=(budget_bound M).trans hr
    have hm:M ≤ R:=by
      have hm:M ≤ capacity M:=by unfold capacity;nlinarith
      exact hm.trans hr
    exact hb.trans (by simp only [Nat.zero_add];omega)
  refine ⟨fun i=>ZeroPadding.pad R (A i),step.pad (fun _=>R),?_,?_,?_,?_,?_⟩
  · exact congrArg (ZeroPadding.pad R) h10
  · exact congrArg (ZeroPadding.pad R) h1
  · exact congrArg (ZeroPadding.pad R) h3
  · exact congrArg (ZeroPadding.pad R) h5
  · intro i;rw [ZeroPadding.pad_length,Nat.max_eq_left (bound i)]

end Completion.SourceDigitWidth

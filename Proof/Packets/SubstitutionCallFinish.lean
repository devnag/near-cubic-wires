import Proof.Packets.SubstitutionCallHeads
import Proof.Packets.SubstitutionScratchErase

/-! Actual output transfer and scratch erasure restore the reusable boundary. -/
set_option autoImplicit false
set_option maxHeartbeats 350000
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unusedSimpArgs false
namespace PCJ9eff70d512234a4c_Fixed.Materializer.SubstitutionCall
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairSource.VerifierDecoding

def resultCopied (A : Fin 44→List Bool) := Function.update (Function.update A 26 (A 39)) 27 (A 40)
noncomputable def copyResult := PhysicalCopyPair.machine (31 : Fin 44) 39 26 40 27
noncomputable def finish := Composition.machine copyResult
  (Composition.machine (moveDrivers .left) SubstitutionScratch.machine)
def finishBudget (R : Nat) := 6*R+16

theorem copy_result_run (C R M : Nat) (left stored : Packet) (atoms source : List Bool)
    (hC : C+2≤R) (hs : VectorAccumulator.Fits R stored) :
    Step copyResult (4*R+5) (loopHeads 0) (loopTapes C R M left stored atoms source)
      (loopHeads 0) (resultCopied (loopTapes C R M left stored atoms source)) := by
  apply PhysicalCopyPair.run R (31 : Fin 44) 39 26 40 27 (loopHeads 0) _
    (by decide) (by decide) (by decide) (by decide) rfl rfl rfl rfl rfl (by exact (loop_core C R M left stored atoms source 31).trans rfl)
  · change (ZeroPadding.pad 0 (ZeroPadding.pad R stored.flatten)).length=R
    rw [ZeroPadding.pad_zero]
    exact VectorAccumulator.flat_length R stored hs
  · change (loopTapes C R M left stored atoms source ((26 : Fin 34).castAdd 10)).length=R
    rw [loop_core]
    change (ZeroPadding.pad R (SubstitutionOuter.one C).flatten).length=R
    rw [one_flat C R (by omega)];simp
  · change (ZeroPadding.pad 0 (ZeroPadding.pad R (CompareMachine.word stored.length))).length=R
    rw [ZeroPadding.pad_zero]
    exact VectorAccumulator.count_length R stored hs
  · change (loopTapes C R M left stored atoms source ((27 : Fin 34).castAdd 10)).length=R
    rw [loop_core]
    change (ZeroPadding.pad R (CompareMachine.word 1)).length=R
    rw [ZeroPadding.pad_length,Nat.max_eq_left (by simp [CompareMachine.word];omega)]

theorem result_core (C R M : Nat) (left stored : Packet) (atoms source : List Bool) (i : Fin 34) :
    resultCopied (loopTapes C R M left stored atoms source) (i.castAdd 10)=ReusableArithmetic.state C R left stored i := by
  by_cases h26 : i=26
  · subst i
    change ZeroPadding.pad 0 (ZeroPadding.pad R stored.flatten)=ZeroPadding.pad R stored.flatten
    exact ZeroPadding.pad_zero _
  by_cases h27 : i=27
  · subst i
    change ZeroPadding.pad 0 (ZeroPadding.pad R (CompareMachine.word stored.length))=ZeroPadding.pad R (CompareMachine.word stored.length)
    exact ZeroPadding.pad_zero _
  have hi26 : i.castAdd 10≠(26 : Fin 44) := by
    intro he;apply h26;apply Fin.ext;exact congrArg (fun x : Fin 44=>x.val) he
  have hi27 : i.castAdd 10≠(27 : Fin 44) := by
    intro he;apply h27;apply Fin.ext;exact congrArg (fun x : Fin 44=>x.val) he
  simp only [resultCopied,Function.update_of_ne hi26,Function.update_of_ne hi27,loop_core]
  have h:=VectorAccumulator.tapes_right_outside C R left (SubstitutionOuter.one C) stored [] (i.castAdd 2)
    (by intro he;apply h26;apply Fin.ext;exact congrArg (fun x : Fin 36=>x.val) he)
    (by intro he;apply h27;apply Fin.ext;exact congrArg (fun x : Fin 36=>x.val) he)
  simpa only [VectorAccumulator.tapes_engine] using h

theorem result_extra (A : Fin 44→List Bool) (i : Fin 10) :
    resultCopied A (i.natAdd 34)=A (i.natAdd 34) := by
  have hn (n : Fin 44) (h : n.val<34) : i.natAdd 34≠n := by
    intro he;have hv:=congrArg (fun x : Fin 44=>x.val) he
    simp only [Fin.val_natAdd] at hv;omega
  simp only [resultCopied,Function.update_of_ne (hn 26 (by decide)),Function.update_of_ne (hn 27 (by decide))]

theorem cleaned_eq (C R M : Nat) (left stored : Packet) (atoms source : List Bool) (hC : C≤R) :
    SubstitutionScratch.cleared R (resultCopied (loopTapes C R M left stored atoms source))=
      resident C R left stored atoms := by
  funext i
  refine Fin.addCases (m:=34) (n:=10) (fun j=>?_) (fun j=>?_) i
  · have hn : ¬35 ≤ (j.castAdd 10).val := by simp only [Fin.val_castAdd];omega
    rw [SubstitutionScratch.cleared,if_neg hn,result_core C R M left stored atoms source,resident_core]
  · rw [resident_extra]
    by_cases hj : j=0
    · subst j
      change resultCopied (loopTapes C R M left stored atoms source) ((0 : Fin 10).natAdd 34)=atoms
      rw [result_extra,loop_extra C R M left stored atoms source hC];rfl
    · have hn : 35 ≤ (j.natAdd 34).val := by
        have h : j.val≠0 := by intro he;apply hj;exact Fin.ext he
        simp only [Fin.val_natAdd];omega
      simp only [SubstitutionScratch.cleared,if_pos hn,if_neg hj]

theorem scratch_fits (C R M : Nat) (left stored : Packet) (atoms source : List Bool)
    (hC : C+2≤R) (hM : M+1≤R) (hsource : source.length≤R) (hs : VectorAccumulator.Fits R stored) :
    ∀ i : Fin 44,35 ≤ i.val→(resultCopied (loopTapes C R M left stored atoms source) i).length≤R := by
  intro i
  refine Fin.addCases (m:=34) (n:=10) (fun j=>?_) (fun j=>?_) i
  · intro hi;have hj:=j.isLt;simp only [Fin.val_castAdd] at hi;omega
  · intro hi
    rw [result_extra,loop_extra C R M left stored atoms source (by omega)]
    have hj : 1≤j.val := by simp only [Fin.val_natAdd] at hi;omega
    rcases hs with ⟨hs1,hs2⟩
    fin_cases j <;> simp_all [ZeroPadding.pad_length,CompareMachine.word,List.length_replicate] <;>omega

theorem finish_run (C R M : Nat) (left stored : Packet) (atoms source : List Bool)
    (hC : C+2≤R) (hM : M+1≤R) (hsource : source.length≤R) (hs : VectorAccumulator.Fits R stored) :
    Step finish (finishBudget R) (loopHeads 0) (loopTapes C R M left stored atoms source)
      heads (resident C R left stored atoms) := by
  have first:=copy_result_run C R M left stored atoms source hC hs
  have second:=(move_drivers_run .left (loopHeads 0) (resultCopied (loopTapes C R M left stored atoms source))).congr moved_down rfl
  have third:=SubstitutionScratch.run R heads (resultCopied (loopTapes C R M left stored atoms source))
    (by intro j;fin_cases j <;>rfl)
    (by exact (result_core C R M left stored atoms source 32).trans rfl)
    (by exact (result_core C R M left stored atoms source 33).trans rfl) (scratch_fits C R M left stored atoms source hC hM hsource hs)
  rw [cleaned_eq C R M left stored atoms source (by omega)] at third
  have h:=first.seq (second.seq third)
  have hf : (4*R+5)+1+(5+1+(2*R+4))=finishBudget R := by unfold finishBudget;omega
  rw [hf] at h
  exact h

end PCJ9eff70d512234a4c_Fixed.Materializer.SubstitutionCall

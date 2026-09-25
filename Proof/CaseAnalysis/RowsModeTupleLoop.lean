import Proof.CaseAnalysis.RowsDegreeLoop
import Proof.CaseAnalysis.RowsModeTupleDigit

/-! The paid degree driver consumes the actual tuple digits and appends
their raw index blocks in order. The private binary copy is reused. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsModeTupleLoop
open LocalBitMultitape RecoveryExecution ExtDecompositionBatch
open RepairSource.VerifierDecoding
open CloseoutRowsModeTupleDigit
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

noncomputable def machine:=RepeatMachine.machine CloseoutRowsModeTupleDigit.machine (fun _ _=>true)
noncomputable def cfg (phase : Fin 5) (pos driver w k C : Nat) (source copy out : List Bool):=
  RepeatMachine.cfg phase
    (⟨CloseoutRowsModeTupleDigit.machine.start,heads pos out,data w C source copy out false⟩ :
      Configuration 6 _) k driver

theorem remaining (w k C M j : Nat) (ds : List Nat) (pre tail copy out : List Bool)
    (hj : j+ds.length=k) (hc : 2*w+1≤C) (hcopy : copy.length≤w)
    (hd : ∀ d∈ds,d<2^w) (hM : ∀ d∈ds,d≤M) :
    ∃ residue : List Bool,residue.length≤w ∧ ∃ time≤ds.length*(CloseoutRowsModeTupleDigit.budget w M+2)+k+3,
      Timed machine time
        (cfg 0 pre.length (j+1) w k C (pre++RowTupleFilterLoop.word w ds++tail) copy out)
        (cfg 3 (pre.length+(RowTupleFilterLoop.word w ds).length) 1 w k C
          (pre++RowTupleFilterLoop.word w ds++tail) residue (out++ds.flatMap ExtIncidence.block)) := by
  induction ds generalizing j pre copy out with
  | nil =>
      have he:j=k:=by simpa using hj
      subst j
      refine ⟨copy,hcopy,k+3,by simp,?_⟩
      simpa only [RowTupleFilterLoop.word,List.flatMap_nil,List.length_nil,Nat.add_zero,List.append_nil,
        machine,cfg] using RepeatMachine.exhaust CloseoutRowsModeTupleDigit.machine (fun _ _=>true)
          (⟨CloseoutRowsModeTupleDigit.machine.start,heads pre.length out,
            data w C (pre++tail) copy out false⟩) k
  | cons d ds ih =>
      have hdn:=hd d (by simp)
      have hdm:=hM d (by simp)
      obtain ⟨nextCopy,nextLength,raw⟩:=digit_run w d C pre (RowTupleFilterLoop.word w ds++tail)
        copy out false hdn hc hcopy
      obtain ⟨r,hr,rh,rt,rs⟩:=raw
      have iteration:=RepeatMachine.iteration CloseoutRowsModeTupleDigit.machine (fun _ _=>true)
        _ k j r (by rfl) (by simp only [List.length_cons] at hj;omega) hr
      simp only [↓reduceIte] at iteration
      rw [RowOccurrenceLoop.cfg_eq 0 r.final
        (⟨CloseoutRowsModeTupleDigit.machine.start,heads (pre.length+2*w) (out++ExtIncidence.block d),
          data w C (pre++Streaming.marks (SignedSortKey.binary w d)++(RowTupleFilterLoop.word w ds++tail))
            nextCopy (out++ExtIncidence.block d) false⟩) k (j+2) rh rt] at iteration
      obtain ⟨residue,hres,time,ht,rest⟩:=ih (j+1) (pre++Streaming.marks (SignedSortKey.binary w d))
        nextCopy (out++ExtIncidence.block d) (by simp only [List.length_cons] at hj;omega)
        nextLength.le (fun n hn=>hd n (by simp [hn])) (fun n hn=>hM n (by simp [hn]))
      have hdriver:j+1+1=j+2:=by omega
      simp only [List.length_append,Streaming.marks_length,SignedSortKey.binary_length,hdriver,
        List.append_assoc] at rest iteration
      have whole:=iteration.trans rest
      refine ⟨residue,hres,r.steps+2+time,?_,?_⟩
      · have hbudget : CloseoutRowsModeTupleDigit.budget w d≤CloseoutRowsModeTupleDigit.budget w M:=by
          unfold CloseoutRowsModeTupleDigit.budget CloseoutRowsModeIndexBlock.budget
          have hm:=Nat.mul_le_mul_right (4*w+7) hdm
          omega
        simp only [List.length_cons]
        nlinarith
      · simpa only [machine,cfg,RowTupleFilterLoop.word,List.flatMap_cons,List.length_append,
          Streaming.marks_length,SignedSortKey.binary_length,List.append_assoc,Nat.add_assoc] using whole

end NearCubicWires.RepairOrdinary.CloseoutRowsModeTupleLoop

import Proof.CaseAnalysis.RowsModeEnumeratorFields

/-! The concrete cold-field prefix retains the two loop drivers at their
live sentinel positions for the following raw stream writer. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsModeEnumeratorCold
open LocalBitMultitape RecoveryExecution RecoveryRootRound SignedSortKey
open RowTupleEnumeration RowTupleColdEnumeration
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem cold_run (w k M : ℕ) (hM : 0<M) (hMw : M≤2^w) :
    ∃ r,run machine (budget w k) (RowTupleColdFields.input w k M)=some r ∧
      r.final.tapes 0=frame (binary (w*k+1) (2^(w*k))) ∧
      r.final.tapes 17=word w k M ∧ r.final.heads 0=0 ∧
      r.final.heads 17=(word w k M).length ∧
      r.final.tapes 2=RepairSource.VerifierDecoding.CompareMachine.word w ∧
      r.final.tapes 12=RepairSource.VerifierDecoding.CompareMachine.word k ∧
      r.final.heads 2=1 ∧ r.final.heads 12=1 ∧ r.steps≤budget w k := by
  obtain ⟨middle,⟨a,ha,atapes,ah,as⟩,a0,a1,a6,aother⟩ := RowTupleColdFields.prepare_run w k M
  obtain ⟨base,hbase,b0,b17,bh,b2,b12,bs⟩ := CloseoutRowsModeEnumeratorFields.logs_run w k M [] hM hMw
  have hcore := prepare_core w k M middle a0 a1 a6 aother
  obtain ⟨b,hb,bf,bsteps⟩ := RecoveryFocus.run_config slots injective RowTupleColdLogs.machine
    (fun _=>0) middle _ _ base hbase
  have hi : RecoveryFocus.config slots (fun _=>0) middle
      (RowTupleColdLogs.input RowTupleColdLogs.machine.start w k M [])=
      Composition.restart a.final enumeration.start := by
    rw [show Composition.restart a.final enumeration.start=initialConfiguration enumeration middle from by
      apply configuration_ext
      · rfl
      · funext i; exact ah i
      · exact atapes]
    apply WilliamsSourceCrop.focus_same slots (initialConfiguration enumeration middle)
    · intro i; simp [RowTupleColdLogs.input,RowTupleColdLogs.heads,initialConfiguration]
    · exact hcore
  rw [hi] at hb
  have hwhole := Composition.run_join RowTupleColdFields.machine enumeration _ _ _ a b ha hb
  have bfield (i : Fin 18) : b.final.tapes (slots i)=base.final.tapes i := by
    rw [bf]; simp [RecoveryFocus.config,RecoveryFocus.pick_slot slots injective]
  have bhead (i : Fin 18) : b.final.heads (slots i)=base.final.heads i := by
    rw [bf]; simp [RecoveryFocus.config,RecoveryFocus.pick_slot slots injective]
  refine ⟨Composition.joinedReceipt a b,hwhole,(bfield 0).trans b0,?_,?_,?_,(bfield 2).trans b2,(bfield 12).trans b12,?_,?_,?_⟩
  · change b.final.tapes (slots 17)=word w k M
    simpa only [List.nil_append] using (bfield 17).trans b17
  · change b.final.heads 0=0
    rw [show (0 : Fin 29)=slots 0 from rfl,bhead,bh]
    rfl
  · change b.final.heads 17=_
    rw [show (17 : Fin 29)=slots 17 from rfl,bhead,bh]
    rfl
  · change b.final.heads (slots 2)=1
    rw [bhead,bh]
    rfl
  · change b.final.heads (slots 12)=1
    rw [bhead,bh]
    rfl
  · change a.steps+1+b.steps≤budget w k
    unfold budget
    rw [bsteps]
    omega

end NearCubicWires.RepairOrdinary.CloseoutRowsModeEnumeratorCold

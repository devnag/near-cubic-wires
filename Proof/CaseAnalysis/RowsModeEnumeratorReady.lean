import Proof.CaseAnalysis.RowsModeEnumerator

/-! The original complete enumerator supplies both reusable loop drivers and
its paid returned tuple stream to the following concrete raw writer. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsModeEnumeratorReady
open LocalBitMultitape RecoveryExecution RecoveryRootRound SignedSortKey
open RepairSource.VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

section Derived
open RowTupleDerivedEnumeration
theorem derived_run (w k M : ℕ) (hM : 0<M) (hMw : M≤2^w) :
    ∃ r,run machine (budget w k) (input w k M)=some r ∧
      r.final.tapes 17=RowTupleEnumeration.word w k M ∧
      r.final.heads 17=(RowTupleEnumeration.word w k M).length ∧
      r.final.tapes 2=CompareMachine.word w ∧ r.final.tapes 12=CompareMachine.word k ∧
      r.final.heads 2=1 ∧ r.final.heads 12=1 ∧ r.steps≤budget w k := by
  obtain ⟨middle,⟨a,ha,atapes,ah,as⟩,hcore⟩ := metadata_run w k M
  obtain ⟨base,hbase,_,b17,_,bh17,b2,b12,bh2,bh12,_⟩ := CloseoutRowsModeEnumeratorCold.cold_run w k M hM hMw
  obtain ⟨b,hb,bf,_⟩ := RecoveryFocus.run_config rowSlots row_injective RowTupleColdEnumeration.machine
    (fun _=>0) middle _ _ base hbase
  have hi : RecoveryFocus.config rowSlots (fun _=>0) middle
      (initialConfiguration RowTupleColdEnumeration.machine (RowTupleColdFields.input w k M))=
      Composition.restart a.final enumeration.start := by
    rw [show Composition.restart a.final enumeration.start=initialConfiguration enumeration middle from by
      apply configuration_ext
      · rfl
      · funext i; exact ah i
      · exact atapes]
    apply WilliamsSourceCrop.focus_same rowSlots (initialConfiguration enumeration middle)
    · intro i; rfl
    · exact hcore
  rw [hi] at hb
  have hwhole := Composition.run_join metadata enumeration _ _ _ a b ha hb
  refine ⟨Composition.joinedReceipt a b,hwhole,?_,?_,?_,?_,?_,?_,runFrom_steps_le machine _ _ _ hwhole⟩
  · change b.final.tapes (rowSlots 17)=_
    rw [bf]
    simp only [RecoveryFocus.config,RecoveryFocus.pick_slot rowSlots row_injective]
    exact b17
  · change b.final.heads (rowSlots 17)=_
    rw [bf]
    simp only [RecoveryFocus.config,RecoveryFocus.pick_slot rowSlots row_injective]
    exact bh17
  · change b.final.tapes (rowSlots 2)=_
    rw [bf]
    simpa only [RecoveryFocus.config,RecoveryFocus.pick_slot rowSlots row_injective] using b2
  · change b.final.tapes (rowSlots 12)=_
    rw [bf]
    simpa only [RecoveryFocus.config,RecoveryFocus.pick_slot rowSlots row_injective] using b12
  · change b.final.heads (rowSlots 2)=_
    rw [bf]
    simpa only [RecoveryFocus.config,RecoveryFocus.pick_slot rowSlots row_injective] using bh2
  · change b.final.heads (rowSlots 12)=_
    rw [bf]
    simpa only [RecoveryFocus.config,RecoveryFocus.pick_slot rowSlots row_injective] using bh12

end Derived
section Ready
open RowTupleEnumerationReady
theorem ready_run (w k M : ℕ) (hM:0<M) (hMw:M≤2^w) :
    ∃ r,run machine (budget w k) (input w k M)=some r ∧
      r.final.tapes 17=RowTupleEnumeration.word w k M ∧ r.final.heads 17=0 ∧
      r.final.tapes 2=CompareMachine.word w ∧ r.final.tapes 12=CompareMachine.word k ∧
      r.final.heads 2=1 ∧ r.final.heads 12=1 ∧ r.steps≤budget w k := by
  obtain ⟨base,hbase,bt,_,b2,b12,bh2,bh12,bs⟩:=derived_run w k M hM hMw
  obtain ⟨r,hr,rf,rs,_⟩:=MaskedReset.reset_run RowTupleDerivedEnumeration.machine selected _ _ base hbase (by
    intro i hi
    have h:=SelectiveReset.prefix_head (prefix_of_run RowTupleDerivedEnumeration.machine _ _ base hbase).1 i
    simpa only [initialConfiguration,zero_add] using h)
  have hb : 2*base.steps+2≤budget w k := by unfold budget; omega
  have more:=runFrom_moreFuel machine _ (budget w k-(2*base.steps+2)) _ r hr
  rw [Nat.add_sub_of_le hb] at more
  have hi : Rewind.recording (initialConfiguration RowTupleDerivedEnumeration.machine (RowTupleDerivedEnumeration.input w k M)) 0=
      initialConfiguration machine (input w k M) := by
    apply configuration_ext
    · rfl
    · funext i; refine Fin.addCases (m:=40) (n:=1) (fun j=>?_) (fun j=>?_) i
      all_goals simp [Rewind.recording,Rewind.config,initialConfiguration,input,Fin.addCases]
    · funext i; refine Fin.addCases (m:=40) (n:=1) (fun j=>?_) (fun j=>?_) i <;> rfl
  rw [hi] at more
  refine ⟨r,more,?_,?_,?_,?_,?_,?_,rs.le.trans hb⟩
  · rw [rf]
    exact bt
  · rw [rf]
    rfl
  · rw [rf];exact b2
  · rw [rf];exact b12
  · rw [rf];exact bh2
  · rw [rf];exact bh12

end Ready
end NearCubicWires.RepairOrdinary.CloseoutRowsModeEnumeratorReady

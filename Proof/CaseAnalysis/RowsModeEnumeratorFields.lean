import Proof.Supplier.RowTupleEnumerationReady

/-! Retain the already manufactured width and degree tapes of the actual cold
subset enumerator. This strengthens its receipt without changing its program. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsModeEnumeratorFields
open LocalBitMultitape RecoveryExecution RecoveryRootRound SignedSortKey
open RowTupleOutputParts RowTupleEnumeration RowTupleColdLogs
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem logs_run (w k M : ℕ) (out : List Bool) (hM : 0<M) (hMw : M≤2^w) :
    ∃ r,runFrom machine (time w k+2) (input machine.start w k M out)=some r ∧
      r.final.tapes 0=frame (SignedSortKey.binary (w*k+1) (2^(w*k))) ∧
      r.final.tapes 17=out++word w k M ∧
      r.final.heads=(cfg RowTupleOutputLoop.machine.start w k (result w k M) false (out++word w k M)).heads ∧
      r.final.tapes 2=RepairSource.VerifierDecoding.CompareMachine.word w ∧
      r.final.tapes 12=RepairSource.VerifierDecoding.CompareMachine.word k ∧
      r.steps≤time w k+2 := by
  obtain ⟨base,hbase,bh,bt,b0,b17,bs⟩ := RowTupleEnumeration.enumerate_run w k M out hM hMw
  rw [←pad_prepared] at hbase
  obtain ⟨b,hb,bf,bsteps,_⟩ := ZeroPadding.run_unpad RowTupleOutputLoop.machine (capacities w k)
    (time w k) (prepared RowTupleOutputLoop.machine.start w k M out) base hbase
  have b0' := congrArg (fun c=>c.tapes 0) bf
  have b17' := congrArg (fun c=>c.tapes 17) bf
  have bh' := congrArg Configuration.heads bf
  simp only [ZeroPadding.config,capacities,Matrix.cons_val_zero,ZeroPadding.pad_zero] at b0'
  have hout : b.final.tapes 17=out++word w k M := by
    have he : ZeroPadding.pad 0 (b.final.tapes 17)=base.final.tapes 17 := b17'
    simpa only [ZeroPadding.pad_zero] using he.trans b17
  obtain ⟨a,ha,af,as⟩ := flag_run w k M out
  have hi : prepared RowTupleOutputLoop.machine.start w k M out=
      Composition.restart a.final RowTupleOutputLoop.machine.start := by rw [af]; rfl
  rw [hi] at hb
  have h := Composition.run_join flagMachine RowTupleOutputLoop.machine _ _ _ a b ha hb
  have he : 1+1+time w k=time w k+2 := by omega
  rw [he] at h
  have field (i : Fin 18) (hi : capacities w k i=0) :
      b.final.tapes i=(cfg RowTupleOutputLoop.machine.start w k (result w k M) false (out++word w k M)).tapes i := by
    have he:=congrArg (fun c=>c.tapes i) bf
    change ZeroPadding.pad (capacities w k i) (b.final.tapes i)=base.final.tapes i at he
    rw [hi,ZeroPadding.pad_zero] at he
    exact he.trans (congrFun bt i)
  exact ⟨Composition.joinedReceipt a b,h,b0'.trans b0,hout,bh'.trans bh,
    field 2 rfl,field 12 rfl,
    by change a.steps+1+b.steps≤_; rw [as,bsteps]; omega⟩

end NearCubicWires.RepairOrdinary.CloseoutRowsModeEnumeratorFields

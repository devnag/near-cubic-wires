import Proof.Packets.PacketsXVectorWorkerChildNat
import Proof.Packets.PacketsXVectorWorkerState
import Proof.Packets.PacketsXVectorParentPrefix
import Proof.Packets.PhysicalIndexedExists

/-! The actual child loop, with ordered literal-polynomial accumulator and
existential private workspace. Its provider parameter is the concrete delta
machine from VectorBottomUpMachine; the provider run is discharged separately
by the metadata, window emission, and normalization assembly. -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 120000
set_option warningAsError true
namespace PCJ9eff70d512234a4c_Fixed.Materializer.VectorBottomUp
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairSource.VerifierDecoding
open NormalizedFiniteTransport
noncomputable section

def ChildReady (C R pi li : Nat) (ps : List (Ring.Poly Nat)) (d : Nat→Ring.Poly Nat)
    (next : List Bool) (Q : (Fin 222→List Bool)→(Fin 32→List Bool)→Prop)
    (i : Nat) (t : Fin 296→List Bool) : Prop :=
  ∃left right fields extra,VectorAccumulator.Fits R left ∧ VectorAccumulator.Fits R right ∧ Q fields extra ∧
    t=A C R i pi li left right (masks C (VectorParentPrefix.value ps d i)) (vectorBank C R ps) next fields extra

attribute [local irreducible] VectorWorkerArena.reusableMetadata VectorChildTransaction.machine
attribute [local irreducible] delta child children childBody

theorem child_loop_run {s : Nat} (provider : Machine 256 s) (C R pi li D E : Nat)
    (ps : List (Ring.Poly Nat)) (d : Nat→Ring.Poly Nat) (next : List Bool)
    (Q : (Fin 222→List Bool)→(Fin 32→List Bool)→Prop)
    (input : Fin 296→List Bool) (hinput : ChildReady C R pi li ps d next Q 0 input)
    (hps : ∀P∈ps,VectorAccumulator.Fits R (masks C P))
    (hpscode : ∀P∈ps,Fits C P) (hdcode : ∀i,i<ps.length→Fits C (d i))
    (hpref : ∀i,i≤ps.length→VectorAccumulator.Fits R (masks C (VectorParentPrefix.value ps d i)))
    (hterm : ∀i : Fin ps.length,VectorAccumulator.Fits R (masks C (Ring.mul ps[i.val] (d i.val))))
    (hmd : ∀i : Fin ps.length,∀j,(ReusableArithmetic.data C (masks C ps[i.val]) (masks C (d i.val)) j).length≤R)
    (hmc : ∀i : Fin ps.length,NormalizedMultiply.budget C (masks C ps[i.val]) (masks C (d i.val))+3≤R)
    (had : ∀i : Fin ps.length,∀j,(ReusableArithmetic.data C
      (masks C (VectorParentPrefix.value ps d i.val)) (masks C (Ring.mul ps[i.val] (d i.val))) j).length≤R)
    (hac : ∀i : Fin ps.length,NormalizedAddition.budget C
      (masks C (VectorParentPrefix.value ps d i.val)) (masks C (Ring.mul ps[i.val] (d i.val)))+3≤R)
    (hcost : ∀i : Fin ps.length,D+1+VectorChildTransaction.budget C R i.val
      (masks C (d i.val)) (masks C ps[i.val]) (masks C (VectorParentPrefix.value ps d i.val))≤E)
    (provider_run : ∀i : Fin ps.length,∀left right fields extra,
      VectorAccumulator.Fits R left→VectorAccumulator.Fits R right→Q fields extra→
      ∃fields' extra',Step (delta provider) D (H (fun _=>0))
        (A C R i.val pi li left right (masks C (VectorParentPrefix.value ps d i.val))
          (vectorBank C R ps) next fields extra) (H (fun _=>0))
        (A C R i.val pi li left (masks C (d i.val)) (masks C (VectorParentPrefix.value ps d i.val))
          (vectorBank C R ps) next fields' extra') ∧ Q fields' extra') :
    ∃output,Step (children provider) (ps.length*(E+2*ps.length+6)+3)
      (Fin.addCases (H (fun _ : Fin 222=>0)) (fun _ : Fin 1=>1))
      (Fin.addCases input (fun _ : Fin 1=>ZeroPadding.pad R (CompareMachine.word ps.length)))
      (Fin.addCases (H (fun _ : Fin 222=>0)) (fun _ : Fin 1=>1))
      (Fin.addCases output (fun _ : Fin 1=>ZeroPadding.pad R (CompareMachine.word ps.length))) ∧
      ChildReady C R pi li ps d next Q ps.length output := by
  have step (i : Nat) (hi : i<ps.length) (t : Fin 296→List Bool)
      (ht : ChildReady C R pi li ps d next Q i t) :
      ∃b,Step (childBody provider) E (H (fun _=>0)) t (H (fun _=>0)) b ∧
      b 258=ZeroPadding.pad R (CompareMachine.word i) ∧
      ChildReady C R pi li ps d next Q (i+1)
        (Function.update b 258 (ZeroPadding.pad R (CompareMachine.word (i+1)))) := by
    obtain ⟨left,right,fields,extra,hl,hr,hq,rfl⟩:=ht
    let j : Fin ps.length:=⟨i,hi⟩
    obtain ⟨fields',extra',hp,hq'⟩:=provider_run j left right fields extra hl hr hq
    have good:=VectorParentPrefix.good C ps d hpscode hdcode i
    have hc:=child_vector_nat C R pi li ps j (d i) (VectorParentPrefix.value ps d i) left next
      (fun _=>0) fields' extra' hps hl (hdcode i hi) (hpscode _ (List.getElem_mem hi)) good.1 good.2
      (hmd j) (hmc j) (had j) (hac j)
    have succ:=VectorParentPrefix.succ ps d i hi
    rw [←succ] at hc
    let b:=A C R i pi li (masks C (VectorParentPrefix.value ps d (i+1)))
      (masks C (Ring.mul ps[i] (d i))) (masks C (VectorParentPrefix.value ps d (i+1)))
      (vectorBank C R ps) next fields' extra'
    refine ⟨b,?_,child_index _ _ _ _ _ _ _ _ _ _ _ _,?_⟩
    · simpa only [childBody] using (hp.seq hc).enlarge (hcost j)
    · rw [show Function.update b 258 (ZeroPadding.pad R (CompareMachine.word (i+1)))=
          A C R (i+1) pi li (masks C (VectorParentPrefix.value ps d (i+1)))
            (masks C (Ring.mul ps[i] (d i))) (masks C (VectorParentPrefix.value ps d (i+1)))
            (vectorBank C R ps) next fields' extra' from update_child_index _ _ _ _ _ _ _ _ _ _ _ _ _]
      exact ⟨_,_,fields',extra',hpref (i+1) (by omega),hterm j,hq',rfl⟩
  obtain ⟨output,run,ready,_⟩:=PhysicalIndexedExists.run_padded (258 : Fin 296) (childBody provider)
    ps.length E R (H (fun _=>0)) rfl (ChildReady C R pi li ps d next Q) input hinput
    (by intro i _ t ht;obtain ⟨l,r,f,e,_,_,_,rfl⟩:=ht;exact child_index _ _ _ _ _ _ _ _ _ _ _ _) step
  exact ⟨output,by simpa only [children] using run,ready⟩

end
end PCJ9eff70d512234a4c_Fixed.Materializer.VectorBottomUp

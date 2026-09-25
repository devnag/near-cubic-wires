import Proof.Packets.PacketsXVectorCoordinateStore
import Proof.Packets.PacketsXVectorWorkerLookup
import Proof.Packets.PacketsXVectorWorkerState
import Proof.Packets.PhysicalIndexedExists

/-! Enumerate final coordinates, run the whole-coordinate callback, and store
the exact answers in ascending slots. The resulting resident bank can feed
the frozen outer fold in its required order. -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 120000
set_option warningAsError true
namespace PCJ9eff70d512234a4c_Fixed.Materializer.VectorBottomUp
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairSource.VerifierDecoding
noncomputable section

def coordinateTable (N : Nat) (answer : Nat→PacketVector.Packet) (done : Nat) :=
  List.ofFn (fun j : Fin N=>if j.val<done then answer j.val else [])

theorem coordinateTable_length (N : Nat) (answer : Nat→PacketVector.Packet) (done : Nat) :
    (coordinateTable N answer done).length=N:=List.length_ofFn
theorem coordinateTable_zero (N : Nat) (answer : Nat→PacketVector.Packet) :
    coordinateTable N answer 0=List.replicate N []:=by simp [coordinateTable]
theorem coordinateTable_full (N : Nat) (answer : Nat→PacketVector.Packet) :
    coordinateTable N answer N=List.ofFn (fun j : Fin N=>answer j.val):=by simp [coordinateTable]
theorem coordinateTable_set (N : Nat) (answer : Nat→PacketVector.Packet) (i : Fin N) :
    (coordinateTable N answer i.val).set i.val (answer i.val)=coordinateTable N answer (i.val+1):=by
  apply List.ext_getElem
  · simp only [List.length_set,coordinateTable_length]
  · intro j hleft hright
    have hj:j<N:=by simpa only [coordinateTable_length] using hright
    simp only [coordinateTable,List.getElem_set,List.getElem_ofFn]
    by_cases he:j=i.val
    · subst j;simp
    · simp only [Ne.symm he,if_false]
      split_ifs <;>first|rfl|omega

theorem coordinateTable_fits (R N done : Nat) (answer : Nat→PacketVector.Packet) (hR:1≤R)
    (hanswer:∀i,i<N→VectorAccumulator.Fits R (answer i)) :
    ∀P∈coordinateTable N answer done,PacketVector.Fits R P:=by
  intro P hP
  obtain ⟨j,rfl⟩:=List.mem_ofFn.mp hP
  split_ifs
  · exact packet_fits R _ (hanswer j.val j.isLt)
  · exact packet_fits R [] (by constructor; simp; simpa using hR)

attribute [local irreducible] lookupRight coordinateStore
def coordinateBody {s : Nat} (callback : Machine 296 s):=
  Composition.machine lookupRight (Composition.machine callback coordinateStore)
def coordinateCollect {s : Nat} (callback : Machine 296 s):=
  PhysicalIndexedAt.machine (258 : Fin 296) (coordinateBody callback)
def CollectReady (C R pi li : Nat) (ps : List PacketVector.Packet) (answer : Nat→PacketVector.Packet)
    (Q : Nat→PacketVector.Packet→PacketVector.Packet→(Fin 222→List Bool)→(Fin 32→List Bool)→Prop)
    (i : Nat) (t : Fin 296→List Bool) : Prop:=
  ∃left right acc fields extra,VectorAccumulator.Fits R right ∧Q i left acc fields extra ∧
    t=A C R i pi li left right acc (PacketVector.bank R ps)
      (PacketVector.bank R (coordinateTable ps.length answer i)) fields extra

attribute [local irreducible] coordinateBody coordinateCollect

theorem coordinate_collect_run {s : Nat} (callback : Machine 296 s) (C R pi li K E : Nat)
    (ps : List PacketVector.Packet) (answer : Nat→PacketVector.Packet)
    (Q : Nat→PacketVector.Packet→PacketVector.Packet→(Fin 222→List Bool)→(Fin 32→List Bool)→Prop)
    (input : Fin 296→List Bool) (hinput : CollectReady C R pi li ps answer Q 0 input)
    (hR:1≤R) (hps:∀P∈ps,PacketVector.Fits R P)
    (hanswer:∀i,i<ps.length→VectorAccumulator.Fits R (answer i))
    (hcost:∀i,i<ps.length→2*PacketBank.lookupBudget R i+K+10≤E)
    (callback_run:∀i : Fin ps.length,∀left acc fields extra,Q i.val left acc fields extra→
      ∃left' acc' fields' extra',Step callback K (H (fun _=>0))
        (A C R i.val pi li left ps[i.val] acc (PacketVector.bank R ps)
          (PacketVector.bank R (coordinateTable ps.length answer i.val)) fields extra)
        (H (fun _=>0))
        (A C R i.val pi li left' (answer i.val) acc' (PacketVector.bank R ps)
          (PacketVector.bank R (coordinateTable ps.length answer i.val)) fields' extra') ∧
        Q (i.val+1) left' acc' fields' extra') :
    ∃output,Step (coordinateCollect callback) (ps.length*(E+2*ps.length+6)+3)
      (Fin.addCases (H (fun _ : Fin 222=>0)) (fun _ : Fin 1=>1))
      (Fin.addCases input (fun _ : Fin 1=>ZeroPadding.pad R (CompareMachine.word ps.length)))
      (Fin.addCases (H (fun _ : Fin 222=>0)) (fun _ : Fin 1=>1))
      (Fin.addCases output (fun _ : Fin 1=>ZeroPadding.pad R (CompareMachine.word ps.length))) ∧
      CollectReady C R pi li ps answer Q ps.length output:=by
  have step (i : Nat) (hi:i<ps.length) (t : Fin 296→List Bool)
      (ht:CollectReady C R pi li ps answer Q i t) :
      ∃b,Step (coordinateBody callback) E (H (fun _=>0)) t (H (fun _=>0)) b ∧
      b 258=ZeroPadding.pad R (CompareMachine.word i) ∧
      CollectReady C R pi li ps answer Q (i+1)
        (Function.update b 258 (ZeroPadding.pad R (CompareMachine.word (i+1)))):=by
    obtain ⟨left,right,acc,fields,extra,hr,hq,rfl⟩:=ht
    let j : Fin ps.length:=⟨i,hi⟩
    have first:=lookup_vector_run C R pi li ps j left right acc
      (PacketVector.bank R (coordinateTable ps.length answer i)) (fun _=>0) fields extra hps hr
    obtain ⟨left',acc',fields',extra',middle,hq'⟩:=callback_run j left acc fields extra hq
    let k : Fin (coordinateTable ps.length answer i).length:=⟨i,by rw [coordinateTable_length];exact hi⟩
    have last:=coordinate_store_run C R pi li (coordinateTable ps.length answer i) k
      left' (answer i) acc' (PacketVector.bank R ps) fields' extra'
      (coordinateTable_fits R ps.length i answer hR hanswer) (hanswer i hi)
    have table:=(coordinateTable_set ps.length answer j)
    dsimp only [j] at table
    dsimp only [k] at last
    rw [table] at last
    let b:=A C R i pi li left' (answer i) acc' (PacketVector.bank R ps)
      (PacketVector.bank R (coordinateTable ps.length answer (i+1))) fields' extra'
    refine ⟨b,?_,child_index _ _ _ _ _ _ _ _ _ _ _ _,?_⟩
    · simpa only [coordinateBody] using (first.seq (middle.seq last)).enlarge
        (by have cost:=hcost i hi;omega : PacketBank.lookupBudget R i+4+1+(K+1+(PacketBank.lookupBudget R i+4))≤E)
    · rw [show Function.update b 258 (ZeroPadding.pad R (CompareMachine.word (i+1)))=
        A C R (i+1) pi li left' (answer i) acc' (PacketVector.bank R ps)
          (PacketVector.bank R (coordinateTable ps.length answer (i+1))) fields' extra' from
        update_child_index _ _ _ _ _ _ _ _ _ _ _ _ _]
      exact ⟨left',answer i,acc',fields',extra',hanswer i hi,hq',rfl⟩
  obtain ⟨output,run,ready,_⟩:=PhysicalIndexedExists.run_padded (258 : Fin 296) (coordinateBody callback)
    ps.length E R (H (fun _=>0)) rfl (CollectReady C R pi li ps answer Q) input hinput
    (by intro i _ t ht;obtain ⟨l,r,a,f,e,_,_,rfl⟩:=ht;exact child_index _ _ _ _ _ _ _ _ _ _ _ _) step
  exact ⟨output,by simpa only [coordinateCollect] using run,ready⟩

end
end PCJ9eff70d512234a4c_Fixed.Materializer.VectorBottomUp

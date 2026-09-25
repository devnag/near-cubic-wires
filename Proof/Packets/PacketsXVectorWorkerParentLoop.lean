import Proof.Packets.PacketsXVectorWorkerChildLoop
import Proof.Packets.PacketsXVectorWorkerParentBody
import Proof.Packets.PacketsXVectorParentTable
import Proof.Packets.PhysicalAppendUpdate

/-! The actual parent loop fills every next-level vector slot exactly once.
Each body resets the child index, runs its full ordered child fold, stores the
result at the resident parent index, and erases the saved accumulator. -/
set_option autoImplicit false
set_option maxHeartbeats 1300000
set_option maxRecDepth 120000
set_option warningAsError true
namespace PCJ9eff70d512234a4c_Fixed.Materializer.VectorBottomUp
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairSource.VerifierDecoding
noncomputable section

def parentAnswer (ps : List (Ring.Poly Nat)) (d : Nat→Nat→Ring.Poly Nat) (i : Nat) :=
  VectorParentPrefix.value ps (d i) ps.length

def ParentReady (C R li : Nat) (ps : List (Ring.Poly Nat)) (d : Nat→Nat→Ring.Poly Nat)
    (Q : (Fin 222→List Bool)→(Fin 32→List Bool)→Prop) (i : Nat) (t : Fin 297→List Bool) : Prop :=
  ∃ci left right fields extra,ci+1≤R ∧ (i≠0→ci=ps.length) ∧ VectorAccumulator.Fits R left ∧ VectorAccumulator.Fits R right ∧ Q fields extra ∧
    t=parentA C R ps.length ci i li left right [] (vectorBank C R ps)
      (vectorBank C R (parentTable ps.length (parentAnswer ps d) i)) fields extra

attribute [local irreducible] children parentBody parents

theorem parent_loop_run {s : Nat} (provider : Machine 256 s) (C R li childFuel F : Nat)
    (ps : List (Ring.Poly Nat)) (d : Nat→Nat→Ring.Poly Nat)
    (Q : (Fin 222→List Bool)→(Fin 32→List Bool)→Prop)
    (input : Fin 297→List Bool) (hinput : ParentReady C R li ps d Q 0 input)
    (hR : ps.length+1≤R)
    (hanswer : ∀i,i<ps.length→VectorAccumulator.Fits R (masks C (parentAnswer ps d i)))
    (hcost : ∀i,i<ps.length→childFuel+VectorParentCommit.budget R i+2*R+8≤F)
    (child_run : ∀i : Fin ps.length,∀next left right fields extra,
      VectorAccumulator.Fits R left→VectorAccumulator.Fits R right→Q fields extra→
      ∃output,Step (children provider) childFuel
        (parentH (fun _=>0))
        (parentA C R ps.length 0 i.val li left right [] (vectorBank C R ps) next fields extra)
        (parentH (fun _=>0))
        (Fin.addCases output (fun _ : Fin 1=>ZeroPadding.pad R (CompareMachine.word ps.length))) ∧
        ChildReady C R i.val li ps (d i.val) next Q ps.length output) :
    ∃output,Step (parents provider) (ps.length*(F+2*ps.length+6)+3)
      (Fin.addCases (parentH (fun _ : Fin 222=>0)) (fun _ : Fin 1=>1))
      (Fin.addCases input (fun _ : Fin 1=>ZeroPadding.pad R (CompareMachine.word ps.length)))
      (Fin.addCases (parentH (fun _ : Fin 222=>0)) (fun _ : Fin 1=>1))
      (Fin.addCases output (fun _ : Fin 1=>ZeroPadding.pad R (CompareMachine.word ps.length))) ∧
      ParentReady C R li ps d Q ps.length output := by
  have partial_fit (i : Nat) : ∀P∈parentTable ps.length (parentAnswer ps d) i,VectorAccumulator.Fits R (masks C P) := by
    intro P hp
    obtain ⟨j,rfl⟩:=List.mem_ofFn.mp hp
    split
    · exact hanswer j.val j.isLt
    · exact ⟨by simp,by simpa using (show 1≤R by omega)⟩
  have step (i : Nat) (hi : i<ps.length) (t : Fin 297→List Bool)
      (ht : ParentReady C R li ps d Q i t) :
      ∃b,Step (parentBody provider) F (parentH (fun _=>0)) t (parentH (fun _=>0)) b ∧
        b 259=ZeroPadding.pad R (CompareMachine.word i) ∧
        ParentReady C R li ps d Q (i+1)
          (Function.update b 259 (ZeroPadding.pad R (CompareMachine.word (i+1)))) := by
    obtain ⟨ci,left,right,fields,extra,hci,_hciDone,hl,hr,hq,rfl⟩:=ht
    let j : Fin ps.length:=⟨i,hi⟩
    let ns:=parentTable ps.length (parentAnswer ps d) i
    obtain ⟨output,hchildren,ready⟩:=child_run j (vectorBank C R ns) left right fields extra hl hr hq
    obtain ⟨left',right',fields',extra',hl',hr',hq',rfl⟩:=ready
    let k : Fin ns.length:=⟨i,by rw [parentTable_length];exact hi⟩
    have body:=parent_body_run provider C R ps.length ci li childFuel ns k (parentAnswer ps d i)
      left right left' right' (vectorBank C R ps) (fun _=>0) fields fields' extra extra'
      hci (partial_fit i) (hanswer i hi) hchildren
    have set : ns.set i (parentAnswer ps d i)=parentTable ps.length (parentAnswer ps d) (i+1) :=
      parentTable_set ps.length (parentAnswer ps d) j
    change Step (parentBody provider) _ _ _ _
      (parentA C R ps.length ps.length i li left' right' [] (vectorBank C R ps)
        (vectorBank C R (ns.set i (parentAnswer ps d i))) fields' extra') at body
    rw [set] at body
    let b:=parentA C R ps.length ps.length i li left' right' [] (vectorBank C R ps)
      (vectorBank C R (parentTable ps.length (parentAnswer ps d) (i+1))) fields' extra'
    refine ⟨b,body.enlarge (hcost i hi),?_,?_⟩
    · exact parent_index C R ps.length i li left' right' [] (vectorBank C R ps)
        (vectorBank C R (parentTable ps.length (parentAnswer ps d) (i+1))) fields' extra'
    · have he : Function.update b 259 (ZeroPadding.pad R (CompareMachine.word (i+1)))=
          parentA C R ps.length ps.length (i+1) li left' right' [] (vectorBank C R ps)
            (vectorBank C R (parentTable ps.length (parentAnswer ps d) (i+1))) fields' extra' := by
        change Function.update (Fin.addCases (m:=296) (n:=1) (motive:=fun _=>List Bool) _ _) ((259 : Fin 296).castAdd 1) _=_
        rw [PhysicalAppendUpdate.left,update_parent_index]
        rfl
      rw [he]
      exact ⟨ps.length,left',right',fields',extra',hR,(fun _=>rfl),hl',hr',hq',rfl⟩
  obtain ⟨output,run,ready,_⟩:=PhysicalIndexedExists.run_padded (259 : Fin 297) (parentBody provider)
    ps.length F R (parentH (fun _=>0)) rfl (ParentReady C R li ps d Q) input hinput
    (by intro i _ t ht;obtain ⟨ci,l,r,f,e,_,_,_,_,_,rfl⟩:=ht;rfl) step
  exact ⟨output,by simpa only [parents] using run,ready⟩

end
end PCJ9eff70d512234a4c_Fixed.Materializer.VectorBottomUp

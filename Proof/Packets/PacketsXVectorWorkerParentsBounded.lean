import Proof.Packets.PacketsXVectorWorkerChildBounded
import Proof.Packets.PacketsXVectorWorkerParentLoop

/-! Both physical inner loops with a uniform cost and every normalized
arithmetic guard discharged by the literal support/degree census. -/
set_option autoImplicit false
set_option maxHeartbeats 1100000
set_option maxRecDepth 120000
set_option warningAsError true
namespace PCJ9eff70d512234a4c_Fixed.Materializer.VectorBottomUp
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairSource.VerifierDecoding
open NormalizedFiniteTransport Theorem25Completion.CycleBounds SubstitutionCensus
noncomputable section

def parentChildrenFuel (R D N : Nat):=N*(D+1+128*(R+1)^2+2*N+6)+3
def parentBodyFuel (R D N : Nat):=parentChildrenFuel R D N+64*(R+1)^2
def allParentsFuel (R D N : Nat):=N*(parentBodyFuel R D N+2*N+6)+3

theorem commit_cost (R i : Nat) (hi:i≤R) :
    VectorParentCommit.budget R i+2*R+8≤64*(R+1)^2:=by
  unfold VectorParentCommit.budget PacketBank.lookupBudget VectorAccumulator.copyBudget
  have hm:=Nat.mul_le_mul_right R hi
  nlinarith

theorem parent_loop_bounded {s : Nat} (provider : Machine 256 s) (C w d a b li D : Nat)
    (S : Finset Nat) (ps : List (Ring.Poly Nat)) (ds : Nat→Nat→Ring.Poly Nat)
    (Q : (Fin 222→List Bool)→(Fin 32→List Bool)→Prop)
    (input : Fin 297→List Bool)
    (hinput : ParentReady C (commonReserve C w) li ps ds Q 0 input)
    (hS : ∀j∈S,j<C) (hps : ∀P∈ps,Bounded S a P)
    (hd : ∀parent,parent<ps.length→∀child,child<ps.length→Bounded S b (ds parent child))
    (hab:a+b≤d) (hfit:(S.card+1)^d≤2^w) (hw:1≤w) (hN:ps.length+1≤commonReserve C w)
    (provider_run : ∀parent child : Fin ps.length,∀next left right fields extra,
      VectorAccumulator.Fits (commonReserve C w) left→VectorAccumulator.Fits (commonReserve C w) right→Q fields extra→
      ∃fields' extra',Step (delta provider) D (H (fun _=>0))
        (A C (commonReserve C w) child.val parent.val li left right
          (masks C (VectorParentPrefix.value ps (ds parent.val) child.val))
          (vectorBank C (commonReserve C w) ps) next fields extra)
        (H (fun _=>0))
        (A C (commonReserve C w) child.val parent.val li left (masks C (ds parent.val child.val))
          (masks C (VectorParentPrefix.value ps (ds parent.val) child.val))
          (vectorBank C (commonReserve C w) ps) next fields' extra') ∧Q fields' extra') :
    ∃output,Step (parents provider) (allParentsFuel (commonReserve C w) D ps.length)
      (Fin.addCases (parentH (fun _ : Fin 222=>0)) (fun _ : Fin 1=>1))
      (Fin.addCases input (fun _ : Fin 1=>ZeroPadding.pad (commonReserve C w) (CompareMachine.word ps.length)))
      (Fin.addCases (parentH (fun _ : Fin 222=>0)) (fun _ : Fin 1=>1))
      (Fin.addCases output (fun _ : Fin 1=>ZeroPadding.pad (commonReserve C w) (CompareMachine.word ps.length))) ∧
      ParentReady C (commonReserve C w) li ps ds Q ps.length output:=by
  apply parent_loop_run provider C (commonReserve C w) li
    (parentChildrenFuel (commonReserve C w) D ps.length) (parentBodyFuel (commonReserve C w) D ps.length)
    ps ds Q input hinput hN
  · intro i hi
    exact (VectorChildGuardBundle.guards C w d a b S ps (ds i) hS hps (hd i hi) hab hfit hw).prefixFits
      ps.length (Nat.le_refl _)
  · intro i hi
    have bound:=commit_cost (commonReserve C w) i (by omega)
    unfold parentBodyFuel
    omega
  · intro i next left right fields extra hl hr hq
    have start : ChildReady C (commonReserve C w) i.val li ps (ds i.val) next Q 0
        (A C (commonReserve C w) 0 i.val li left right [] (vectorBank C (commonReserve C w) ps) next fields extra):=
      ⟨left,right,fields,extra,hl,hr,hq,rfl⟩
    obtain ⟨output,step,ready⟩:=child_loop_bounded provider C w d a b i.val li D S ps (ds i.val) next Q _ start
      hS hps (hd i.val i.isLt) hab hfit hw (by omega)
      (fun j l r f e hl hr hq=>provider_run i j next l r f e hl hr hq)
    exact ⟨output,by simpa only [parentChildrenFuel,parentH,parentA] using step,ready⟩

end
end PCJ9eff70d512234a4c_Fixed.Materializer.VectorBottomUp

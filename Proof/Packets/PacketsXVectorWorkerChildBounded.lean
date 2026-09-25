import Proof.Packets.PacketsXVectorWorkerChildLoop
import Proof.Packets.PacketsXVectorChildGuardBundle

/-! Uniform resource discharge for the actual ordered child loop, from the
unchanged literal-support and degree census. -/
set_option autoImplicit false
set_option maxHeartbeats 700000
set_option maxRecDepth 120000
set_option warningAsError true
namespace PCJ9eff70d512234a4c_Fixed.Materializer.VectorBottomUp
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairSource.VerifierDecoding
open NormalizedFiniteTransport Theorem25Completion.CycleBounds SubstitutionCensus
noncomputable section

theorem child_loop_bounded {s : Nat} (provider : Machine 256 s) (C w d a b pi li D : Nat)
    (S : Finset Nat) (ps : List (Ring.Poly Nat)) (deltaPoly : Nat→Ring.Poly Nat) (next : List Bool)
    (Q : (Fin 222→List Bool)→(Fin 32→List Bool)→Prop)
    (input : Fin 296→List Bool)
    (hinput : ChildReady C (commonReserve C w) pi li ps deltaPoly next Q 0 input)
    (hS : ∀j∈S,j<C) (hps : ∀P∈ps,Bounded S a P)
    (hd : ∀i,i<ps.length→Bounded S b (deltaPoly i)) (hab : a+b≤d)
    (hfit : (S.card+1)^d≤2^w) (hw : 1≤w) (hN : ps.length≤commonReserve C w)
    (provider_run : ∀i : Fin ps.length,∀left right fields extra,
      VectorAccumulator.Fits (commonReserve C w) left→VectorAccumulator.Fits (commonReserve C w) right→Q fields extra→
      ∃fields' extra',Step (delta provider) D (H (fun _=>0))
        (A C (commonReserve C w) i.val pi li left right (masks C (VectorParentPrefix.value ps deltaPoly i.val))
          (vectorBank C (commonReserve C w) ps) next fields extra) (H (fun _=>0))
        (A C (commonReserve C w) i.val pi li left (masks C (deltaPoly i.val)) (masks C (VectorParentPrefix.value ps deltaPoly i.val))
          (vectorBank C (commonReserve C w) ps) next fields' extra') ∧ Q fields' extra') :
    ∃output,Step (children provider)
      (ps.length*(D+1+128*(commonReserve C w+1)^2+2*ps.length+6)+3)
      (Fin.addCases (H (fun _ : Fin 222=>0)) (fun _ : Fin 1=>1))
      (Fin.addCases input (fun _ : Fin 1=>ZeroPadding.pad (commonReserve C w) (CompareMachine.word ps.length)))
      (Fin.addCases (H (fun _ : Fin 222=>0)) (fun _ : Fin 1=>1))
      (Fin.addCases output (fun _ : Fin 1=>ZeroPadding.pad (commonReserve C w) (CompareMachine.word ps.length))) ∧
      ChildReady C (commonReserve C w) pi li ps deltaPoly next Q ps.length output := by
  have guard:=VectorChildGuardBundle.guards C w d a b S ps deltaPoly hS hps hd hab hfit hw
  apply child_loop_run provider C (commonReserve C w) pi li D (D+1+128*(commonReserve C w+1)^2)
    ps deltaPoly next Q input hinput guard.packet guard.code guard.deltaCode guard.prefixFits guard.term
    guard.mulData guard.mulFuel guard.addData guard.addFuel _ provider_run
  intro i
  have bound:=VectorChildGuardBundle.transaction_budget C (commonReserve C w) i.val ps[i.val] (deltaPoly i.val)
    (VectorParentPrefix.value ps deltaPoly i.val) (guard.code _ (List.getElem_mem i.isLt))
    (guard.deltaCode i.val i.isLt) (by have hi:=i.isLt;omega) (guard.mulFuel i) (guard.addFuel i)
  dsimp only [VectorChildGuardBundle.masks,masks] at bound ⊢
  omega

end
end PCJ9eff70d512234a4c_Fixed.Materializer.VectorBottomUp

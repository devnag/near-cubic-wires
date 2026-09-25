import Proof.Packets.PacketsXComplementPacketStep
import Proof.Packets.PacketsXOrderedPacketFold

/-! A real indexed scan builds the paired positive/negative coordinate bank
used by every truth-table row. The original coordinate bank is retained. -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unusedSimpArgs false
namespace PCJ9eff70d512234a4c_Fixed.Materializer.ComplementPacketBank
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairSource.VerifierDecoding
open NormalizedFiniteTransport Theorem25Completion.CycleBounds
open ComplementPacketStep
abbrev Poly:=Ring.Poly Nat

def pairs (ps : List Poly) : List Poly:=ps.flatMap (fun P=>[P,Ring.add [[]] P])
def emitted (C R : Nat) (ps : List Poly) (n : Nat) :=
  (ps.take n).flatMap (fun P=>entry C R P++entry C R (Ring.add [[]] P))
def prior (ps : List Poly) (old : Poly) (n : Nat) :=
  if n=0 then old else Ring.add [[]] (ps.getD (n-1) [])
noncomputable def machine:=PhysicalIndexedAt.machine (35 : Fin 38) ComplementPacketStep.machine
def budget (C w N : Nat):=N*(128*(commonReserve C w+1)^2+2*N+6)+3

theorem emitted_succ (C R : Nat) (ps : List Poly) (n : Nat) (hn : n<ps.length) :
    emitted C R ps (n+1)=emitted C R ps n++entry C R ps[n]++entry C R (Ring.add [[]] ps[n]) := by
  unfold emitted
  rw [List.take_succ_eq_append_getElem hn]
  simp only [List.flatMap_append,List.flatMap_singleton,List.append_assoc]

theorem emitted_all (C R : Nat) (ps : List Poly) :
    emitted C R ps ps.length=OrderedPacketStep.bank C R (pairs ps) := by
  simp only [emitted,List.take_length,pairs,OrderedPacketStep.bank,PacketVector.bank,
    List.map_flatMap,List.map_cons,List.map_nil,List.flatMap_assoc,List.flatMap_cons,
    List.flatMap_nil,List.append_nil,entry]

theorem prior_count (_C w d : Nat) (S : Finset Nat) (ps : List Poly) (old : Poly)
    (hps : ∀P∈ps,NormalizedIntermediate.Bounded S d P)
    (hfit : (S.card+1)^d≤2^w) (ho : old.length≤2^w)
    (n : Nat) (hn : n≤ps.length) : (prior ps old n).length≤2^w := by
  unfold prior
  split
  · exact ho
  · have hi : n-1<ps.length := by omega
    rw [List.getD_eq_getElem _ _ hi]
    exact (NormalizedIntermediate.census (NormalizedIntermediate.add
      (NormalizedIntermediate.one S d) (hps _ (List.getElem_mem hi)))).trans hfit

theorem update_index (C R i j : Nat) (right : Poly) (ps : List Poly) (out : List Bool) :
    PhysicalIndexedAt.A (35 : Fin 38) R j (A C R i right ps out)=A C R j right ps out := by
  funext k
  fin_cases k <;>simp [PhysicalIndexedAt.A,A,OrderedPacketStep.A,ArithmeticLookup.A,Fin.addCases]

theorem update_heads (out : List Bool) : PhysicalIndexedAt.H (35 : Fin 38) (H out)=H out := by
  apply Function.update_eq_self_iff.mpr
  rfl

theorem step_bound (C w i N : Nat) (hi : i≤N) (hN : N≤2^w) :
    ComplementPacketStep.budget C w i≤128*(commonReserve C w+1)^2 := by
  have hcap:=OrderedPacketFold.driver_fit C w N hN
  have hmul : i*commonReserve C w≤commonReserve C w*commonReserve C w:=
    Nat.mul_le_mul_right _ (by omega)
  unfold ComplementPacketStep.budget ArithmeticLookup.budget PacketBank.lookupBudget
    PacketBank.storeBudget ReusableArithmetic.boundedBudget
  nlinarith

theorem run (C w : Nat) (S : Finset Nat) (d : Nat) (ps : List Poly) (old : Poly) (out : List Bool)
    (hS : ∀j∈S,j<C) (hps : ∀P∈ps,NormalizedIntermediate.Bounded S d P)
    (hfit : (S.card+1)^d≤2^w) (hN : ps.length≤2^w) (ho : old.length≤2^w) (hw : 1≤w) :
    Step machine (budget C w ps.length)
      (Fin.addCases (m:=38) (n:=1) (motive:=fun _=>Nat) (H out) (fun _=>1))
      (Fin.addCases (m:=38) (n:=1) (motive:=fun _=>List Bool)
        (A C (commonReserve C w) 0 old ps out) (fun _=>CompareMachine.word ps.length))
      (Fin.addCases (m:=38) (n:=1) (motive:=fun _=>Nat)
        (H (out++OrderedPacketStep.bank C (commonReserve C w) (pairs ps))) (fun _=>1))
      (Fin.addCases (m:=38) (n:=1) (motive:=fun _=>List Bool)
        (A C (commonReserve C w) ps.length (prior ps old ps.length) ps
          (out++OrderedPacketStep.bank C (commonReserve C w) (pairs ps)))
        (fun _=>CompareMachine.word ps.length)) := by
  let hs : Nat→Fin 38→Nat:=fun i=>H (out++emitted C (commonReserve C w) ps i)
  let states : Nat→Fin 38→List Bool:=fun i=>
    A C (commonReserve C w) 0 (prior ps old i) ps (out++emitted C (commonReserve C w) ps i)
  have work : ∀i,i<ps.length→Step ComplementPacketStep.machine (128*(commonReserve C w+1)^2)
      (PhysicalIndexedAt.H 35 (hs i)) (PhysicalIndexedAt.A 35 (commonReserve C w) i (states i))
      (PhysicalIndexedAt.H 35 (hs (i+1))) (PhysicalIndexedAt.A 35 (commonReserve C w) i (states (i+1))) := by
    intro i hi
    dsimp only [hs,states]
    rw [update_heads,update_heads,update_index,update_index]
    have h:=ComplementPacketStep.run C w S d ps ⟨i,hi⟩ (prior ps old i)
      (out++emitted C (commonReserve C w) ps i) hS hps hfit
      (prior_count C w d S ps old hps hfit ho i (by omega)) hw
    have he : prior ps old (i+1)=Ring.add [[]] ps[i]:=by
      simp only [prior,Nat.add_eq_zero_iff,one_ne_zero,and_false,ite_false,Nat.add_sub_cancel,
        List.getD_eq_getElem _ _ hi]
    rw [he,emitted_succ C (commonReserve C w) ps i hi]
    simpa only [List.append_assoc] using h.enlarge (step_bound C w i ps.length (by omega) hN)
  have result:=PhysicalIndexedAt.run (35 : Fin 38) ComplementPacketStep.machine ps.length
    (128*(commonReserve C w+1)^2) (commonReserve C w) hs states work
  dsimp only [hs,states] at result
  rw [update_heads,update_heads,update_index,update_index,emitted_all] at result
  simpa only [machine,budget,emitted,List.take_zero,List.flatMap_nil,List.append_nil,prior,ite_true] using result

end PCJ9eff70d512234a4c_Fixed.Materializer.ComplementPacketBank

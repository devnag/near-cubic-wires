import Proof.Packets.PacketsXBooleanSelectorRun
import Proof.Packets.PacketsXBooleanSelectorSeek
import Proof.Packets.PacketsXOrderedPacketReset

/-! Resident Boolean-selector transaction. It physically resets the product
one, builds the doubled index and end cursor from the retained length counter,
and executes every bit-controlled factor. The original paired bank, assignment,
and driver are retained, with index and assignment heads returned to zero. -/
set_option autoImplicit false
set_option maxHeartbeats 950000
set_option maxRecDepth 120000
set_option warningAsError true
namespace PCJ9eff70d512234a4c_Fixed.Materializer.BooleanSelectorResident
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairSource.VerifierDecoding
open NormalizedFiniteTransport Theorem25Completion.CycleBounds PairedPacketMeaning

def H : Fin 39→Nat:=Fin.addCases (m:=38) (n:=1) (motive:=fun _=>Nat) (SelectedPairFetch.H 0) (fun _=>1)
def A (C R N : Nat) (left right : Poly) (ps : List Poly) (bits : List Bool) : Fin 39→List Bool:=
  Fin.addCases (m:=38) (n:=1) (motive:=fun _=>List Bool)
    (SelectedPairFetch.A C R 0 left right (ComplementPacketBank.pairs ps) bits) (fun _=>CompareMachine.word N)
noncomputable def reset:=TapeEmbedding.machine 2 OrderedPacketReset.oneMachine
noncomputable def machine:=Composition.machine reset (Composition.machine BooleanSelectorSeek.machine BooleanSelectorRun.machine)
def budget (C w N : Nat):=4*commonReserve C w+12+BooleanSelectorSeek.budget N+BooleanSelectorRun.budget C w N

theorem reset_run (C w N : Nat) (left right : Poly) (ps : List Poly) (bits : List Bool)
    (hr : right.length≤2^w) :
    Step reset (4*commonReserve C w+10) H (A C (commonReserve C w) N left right ps bits)
      H (A C (commonReserve C w) N left [[]] ps bits) := by
  have h:=(OrderedPacketReset.one_run C w 0 left right (ComplementPacketBank.pairs ps) hr).embed
    (![0,1] : Fin 2→Nat) (![bits,CompareMachine.word N] : Fin 2→List Bool)
  refine (h.congr_in ?_ ?_).congr ?_ ?_
  all_goals funext i;fin_cases i <;>rfl

theorem run (C w : Nat) (S : Finset Nat) (d : Nat) (ps : List Poly) (left right : Poly) (bits : List Bool)
    (hS : ∀j∈S,j<C) (hps : ∀P∈ps,NormalizedIntermediate.Bounded S d P)
    (hfit : (S.card+1)^(d*ps.length)≤2^w) (hAtom : (S.card+1)^d≤2^w)
    (hN : ps.length≤2^w) (hl : left.length≤2^w) (hr : right.length≤2^w) (hw : 1≤w) :
    Step machine (budget C w ps.length) H (A C (commonReserve C w) ps.length left right ps bits)
      H (A C (commonReserve C w) ps.length
        (OrderedPacketFold.last (factors ps bits) left ps.length)
        (Normalized.structuralGF2Product (factors ps bits)) ps bits) := by
  have one:=reset_run C w ps.length left right ps bits hr
  have two:=BooleanSelectorSeek.run C (commonReserve C w) ps.length left [[]] (ComplementPacketBank.pairs ps) bits
  have three:=BooleanSelectorRun.run C w S d ps left bits hS hps hfit hAtom hN hl hw
  have whole:=one.seq (two.seq three)
  have cost : (4*commonReserve C w+10)+1+
      (BooleanSelectorSeek.budget ps.length+1+BooleanSelectorRun.budget C w ps.length)=budget C w ps.length:=by
    unfold budget
    omega
  rw [cost] at whole
  exact whole

end PCJ9eff70d512234a4c_Fixed.Materializer.BooleanSelectorResident

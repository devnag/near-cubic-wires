import Proof.Packets.PacketsXOrderedPacketFold
import Proof.Packets.PhysicalBitCallFalse

/-! Read one of two adjacent actual packets using a physically scanned bit.
True selects the first entry, false the second. The resident unary index is
paid down to the first entry in either branch, ready for the next pair. -/
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 120000
set_option warningAsError true
namespace PCJ9eff70d512234a4c_Fixed.Materializer.SelectedPairFetch
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairSource.VerifierDecoding
open NormalizedFiniteTransport Theorem25Completion.CycleBounds
abbrev Poly:=Ring.Poly Nat

def H (pos : Nat) : Fin 38→Nat:=Fin.addCases (m:=37) (n:=1) (motive:=fun _=>Nat)
  (ArithmeticLookup.H 0) (fun _=>pos)
def A (C R index : Nat) (left acc : Poly) (ps : List Poly) (bits : List Bool) : Fin 38→List Bool:=
  Fin.addCases (m:=37) (n:=1) (motive:=fun _=>List Bool)
    (OrderedPacketStep.A C R index left acc ps) (fun _=>bits)
noncomputable def retreat:=PhysicalIndexedAt.retreat (35 : Fin 38)
noncomputable def before:=PhysicalBitCall.machine (37 : Fin 38) retreat
noncomputable def fetch:=TapeEmbedding.machine 1 ArithmeticLookup.machine
noncomputable def after:=PhysicalBitCall.falseMachine (37 : Fin 38) retreat
noncomputable def machine:=Composition.machine before (Composition.machine fetch after)
def chosen (i : Nat) (bit : Bool):Nat:=if bit then 2*i else 2*i+1

theorem update_index (C R i j : Nat) (left acc : Poly) (ps : List Poly) (bits : List Bool) :
    PhysicalIndexedAt.A (35 : Fin 38) R j (A C R i left acc ps bits)=A C R j left acc ps bits := by
  funext k
  fin_cases k <;>simp [PhysicalIndexedAt.A,A,OrderedPacketStep.A,ArithmeticLookup.A,Fin.addCases]

theorem retreat_run (C R index pos : Nat) (left acc : Poly) (ps : List Poly) (bits : List Bool)
    (hi : index+2≤R) :
    Step retreat (2*index+4) (H pos) (A C R (index+1) left acc ps bits)
      (H pos) (A C R index left acc ps bits) := by
  have h:=PhysicalIndexedAt.retreat_run (35 : Fin 38) R index (H pos)
    (A C R index left acc ps bits) hi
  have hh : PhysicalIndexedAt.H (35 : Fin 38) (H pos)=H pos:=by
    apply Function.update_eq_self_iff.mpr
    rfl
  rw [hh,update_index,update_index] at h
  exact h

theorem fetch_run (C w pos : Nat) (ps : List Poly) (j : Fin ps.length) (left acc : Poly) (bits : List Bool)
    (hl : left.length≤2^w) (hps : ∀P∈ps,P.length≤2^w) :
    Step fetch (ArithmeticLookup.budget (commonReserve C w) j.val)
      (H pos) (A C (commonReserve C w) j.val left acc ps bits)
      (H pos) (A C (commonReserve C w) j.val ps[j.val] acc ps bits) :=
  (OrderedPacketStep.fetch C w ps j left acc hl hps).embed (fun _ : Fin 1=>pos) (fun _ : Fin 1=>bits)

theorem run (C w i pos : Nat) (ps : List Poly) (left acc : Poly) (bits : List Bool) (bit : Bool)
    (hb : readTapeBit bits pos=bit) (hi : 2*i+1<ps.length)
    (hR : 2*i+2≤commonReserve C w) (hl : left.length≤2^w) (hps : ∀P∈ps,P.length≤2^w) :
    Step machine (96*(commonReserve C w+1)^2)
      (H pos) (A C (commonReserve C w) (2*i+1) left acc ps bits)
      (H pos) (A C (commonReserve C w) (2*i) (ps.getD (chosen i bit) []) acc ps bits) := by
  have small (j : Nat) (hj : j≤commonReserve C w) :
      ArithmeticLookup.budget (commonReserve C w) j+4*i+11≤96*(commonReserve C w+1)^2 := by
    unfold ArithmeticLookup.budget PacketBank.lookupBudget
    have hm:=Nat.mul_le_mul_right (commonReserve C w) hj
    nlinarith
  cases bit
  · let j : Fin ps.length:=⟨2*i+1,hi⟩
    have hfirst:=PhysicalBitCall.run_false (p:=retreat) (37 : Fin 38) (H pos)
      (A C (commonReserve C w) (2*i+1) left acc ps bits) hb
    have hfetch:=fetch_run C w pos ps j left acc bits hl hps
    have hret:=retreat_run C (commonReserve C w) (2*i) pos ps[j.val] acc ps bits hR
    have hlast:=PhysicalBitCall.false_run (37 : Fin 38) (p:=retreat) hb hret
    have all:=hfirst.seq (hfetch.seq hlast)
    have cost : 2+1+(ArithmeticLookup.budget (commonReserve C w) (2*i+1)+1+(2*(2*i)+4+3))=
      ArithmeticLookup.budget (commonReserve C w) (2*i+1)+4*i+11:=by omega
    rw [cost] at all
    simpa only [machine,before,after,j,chosen,Bool.false_eq_true,ite_false,List.getD_eq_getElem _ _ hi]
      using all.enlarge (small (2*i+1) (by omega))
  · have hi0 : 2*i<ps.length:=by omega
    let j : Fin ps.length:=⟨2*i,hi0⟩
    have hret:=retreat_run C (commonReserve C w) (2*i) pos left acc ps bits hR
    have hfirst:=PhysicalBitCall.run_true (37 : Fin 38) (p:=retreat) hb hret
    have hfetch:=fetch_run C w pos ps j left acc bits hl hps
    have hlast:=PhysicalBitCall.true_skip (p:=retreat) (37 : Fin 38) (H pos)
      (A C (commonReserve C w) (2*i) ps[j.val] acc ps bits) hb
    have all:=hfirst.seq (hfetch.seq hlast)
    have cost : (2*(2*i)+4+3)+1+(ArithmeticLookup.budget (commonReserve C w) (2*i)+1+2)=
      ArithmeticLookup.budget (commonReserve C w) (2*i)+4*i+11:=by omega
    rw [cost] at all
    simpa only [machine,before,after,j,chosen,ite_true,List.getD_eq_getElem _ _ hi0]
      using all.enlarge (small (2*i) (by omega))

end PCJ9eff70d512234a4c_Fixed.Materializer.SelectedPairFetch

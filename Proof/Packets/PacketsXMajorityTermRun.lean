import Proof.Packets.PacketsXMajorityTermRead
import Proof.Packets.PacketsXMajorityTermSelect
import Proof.Packets.PacketsXMajorityTermStore
import Proof.Packets.PacketsXMajorityTermArena
import Proof.Packets.PacketsXCycleMajorityCost

/-! Complete reusable physical majority callback: read the actual assignment,
count/compare, select/multiply, conditionally store one packet, and clear all
private words. Every execution guard comes from finite support and census. -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 120000
set_option warningAsError true
namespace PCJ9eff70d512234a4c_Fixed.Materializer.MajorityTermArena
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairSource.VerifierDecoding
open NormalizedFiniteTransport Theorem25Completion.CycleBounds PairedPacketMeaning

def product (ps : List Poly) (bits : List Bool):=Normalized.structuralGF2Product (factors ps bits)
def accepted (ps : List Poly) (bits : List Bool):Bool:=
  decide ((ps.length+1)/2≤(Theorem25Completion.CycleCellBitCount.marks bits).length)
def term (ps : List Poly) (bits : List Bool):=if accepted ps bits then product ps bits else []
noncomputable def machine:=Composition.machine read (Composition.machine accept
  (Composition.machine select (Composition.machine store clear)))

theorem count_room (C w N : Nat) (hN : N≤2^w) : 4*N+5≤commonReserve C w := by
  have he : 2^w≤2^(8*w):=Nat.pow_le_pow_right (by decide) (by omega)
  have hC : 1≤(C+1)^4:=Nat.one_le_pow _ _ (by omega)
  have hp : 1≤2^(8*w):=Nat.one_le_pow _ _ (by decide)
  unfold commonReserve
  nlinarith

theorem run (C w : Nat) (S : Finset Nat) (d : Nat) (ps : List Poly) (bits out : List Bool)
    (hb : bits.length=ps.length) (hS : ∀j∈S,j<C)
    (hps : ∀P∈ps,NormalizedIntermediate.Bounded S d P)
    (hfit : (S.card+1)^(d*ps.length)≤2^w) (hAtom : (S.card+1)^d≤2^w)
    (hN : ps.length≤2^w) (hw : 1≤w) :
    Step machine (majorityTermBudget C w ps.length)
      (H out) (A C (commonReserve C w) ps [] [] [] 0 false out (frame bits))
      (H (out++OrderedPacketStore.entry C (commonReserve C w) (term ps bits)))
      (A C (commonReserve C w) ps [] [] [] 0 false
        (out++OrderedPacketStore.entry C (commonReserve C w) (term ps bits)) (frame bits)) := by
  have hroom:=count_room C w ps.length hN
  have hbits : bits.length≤commonReserve C w:=by omega
  have hmarks : (Theorem25Completion.CycleCellBitCount.marks bits).length≤bits.length:=List.length_filter_le _ _
  have hfb:=factors_bounded S d ps bits hps
  have hfl:=factors_length ps bits
  have hc : ∀P∈factors ps bits,P.length≤2^w:=fun P hP=>(NormalizedIntermediate.census (hfb P hP)).trans hAtom
  have hprod : (product ps bits).length≤2^w:=
    (NormalizedIntermediate.census (NormalizedIntermediate.product (factors ps bits) hfb)).trans
      (by simpa only [hfl] using hfit)
  have hlast:=OrderedPacketFold.last_count (factors ps bits) ([] : Poly) (2^w) ps.length (by simp) hc
  have hterm : (term ps bits).length≤2^w:=by
    unfold term
    split
    · exact hprod
    · simp
  have one:=read_run C (commonReserve C w) ps [] [] bits 0 false out hbits
  have two:=accept_run C (commonReserve C w) ps [] [] bits false out (frame bits) hb hroom
  have three:=select_run C w S d ps [] [] bits
    (Theorem25Completion.CycleCellBitCount.marks bits).length (accepted ps bits) out (frame bits)
    hS hps hfit hAtom hN (by simp) (by simp) hw
  have four:=store_run C w ps (OrderedPacketFold.last (factors ps bits) [] ps.length)
    (product ps bits) bits (Theorem25Completion.CycleCellBitCount.marks bits).length
    (accepted ps bits) out (frame bits) hprod
  have five:=clear_run C w ps (OrderedPacketFold.last (factors ps bits) [] ps.length)
    (term ps bits) bits (Theorem25Completion.CycleCellBitCount.marks bits).length (accepted ps bits)
    (out++OrderedPacketStore.entry C (commonReserve C w) (term ps bits)) (frame bits)
    hlast hterm hbits (by omega)
  have whole:=one.seq (two.seq (three.seq (four.seq five)))
  rw [hb] at whole
  have cost : (4*ps.length+2)+1+((10*ps.length+21)+1+(BooleanSelectorResident.budget C w ps.length+1+
      ((12*commonReserve C w+28)+1+(2*commonReserve C w+4))))=majorityTermBudget C w ps.length:=by
    unfold majorityTermBudget
    omega
  rw [cost] at whole
  exact whole

end PCJ9eff70d512234a4c_Fixed.Materializer.MajorityTermArena

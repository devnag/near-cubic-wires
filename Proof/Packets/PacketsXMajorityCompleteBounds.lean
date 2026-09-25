import Proof.Packets.PacketsXMajorityCompleteLayout

/-! The physically generated pair and term banks fit the quadratic rewind
capacity. Their bounds follow from the same support/degree census as the
actual majority callbacks. -/
set_option autoImplicit false
set_option maxHeartbeats 700000
set_option warningAsError true
namespace PCJ9eff70d512234a4c_Fixed.Materializer.MajorityComplete
open NearCubicWires NormalizedFiniteTransport Theorem25Completion.CycleBounds PairedPacketMeaning

theorem bank_length (C w : Nat) (ps : List Poly) (hps : ∀P∈ps,P.length≤2^w) :
    (OrderedPacketStep.bank C (commonReserve C w) ps).length=ps.length*(2*commonReserve C w) := by
  unfold OrderedPacketStep.bank
  rw [PacketVector.bank_length _ _ (OrderedPacketStep.bank_fit C w ps hps),List.length_map]
  ring

theorem paired_length (C w : Nat) (S : Finset Nat) (d : Nat) (ps : List Poly)
    (hps : ∀P∈ps,NormalizedIntermediate.Bounded S d P)
    (hfit : (S.card+1)^d≤2^w) :
    (paired C (commonReserve C w) ps).length=4*ps.length*commonReserve C w := by
  unfold paired
  rw [bank_length C w _ (fun P hp=>(NormalizedIntermediate.census
    (pairs_bounded S d ps hps P hp)).trans hfit),pairs_length]
  ring

theorem paired_capacity (C w : Nat) (S : Finset Nat) (d : Nat) (ps : List Poly)
    (hps : ∀P∈ps,NormalizedIntermediate.Bounded S d P)
    (hfit : (S.card+1)^d≤2^w) (hN : ps.length≤2^w) :
    (paired C (commonReserve C w) ps).length≤(commonReserve C w)^2 := by
  rw [paired_length C w S d ps hps hfit]
  have room:=MajorityTermArena.count_room C w ps.length hN
  have hm:=Nat.mul_le_mul_right (commonReserve C w) (by omega : 4*ps.length≤commonReserve C w)
  nlinarith only [hm]

theorem terms_capacity (C w : Nat) (S : Finset Nat) (d : Nat) (ps : List Poly)
    (hps : ∀P∈ps,NormalizedIntermediate.Bounded S d P)
    (hfit : (S.card+1)^(d*ps.length)≤2^w) (hCodes : 2^ps.length≤2^w) :
    (termBank C (commonReserve C w) ps).length≤(commonReserve C w)^2 := by
  unfold termBank
  rw [bank_length C w _ (fun P hp=>(NormalizedIntermediate.census
    (terms_bounded S d ps hps P hp)).trans hfit),terms_length]
  have room:=MajorityTermArena.count_room C w (2^ps.length) hCodes
  have hm:=Nat.mul_le_mul_right (commonReserve C w)
    (by omega : 2*(2^ps.length)≤commonReserve C w)
  nlinarith only [hm]

end PCJ9eff70d512234a4c_Fixed.Materializer.MajorityComplete

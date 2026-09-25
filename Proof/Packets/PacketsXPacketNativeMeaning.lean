import Proof.Packets.PacketsXCycleFlatDockTyped
import Proof.Packets.PacketsXNormalizedFiniteTransport
import Proof.Packets.PacketsXCycleDenseAtomCost

/-! The existing native serializer appends the exact natural-index packet
stream from the common-width mask bank. Its paid cleanup is retained, and
its fuel guard follows from the normalized packet census. -/
set_option autoImplicit false
set_option maxHeartbeats 700000
set_option maxRecDepth 120000
set_option warningAsError true
namespace PCJ9eff70d512234a4c_Fixed.Materializer.PacketNativeMeaning
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.ExtDecompositionBatch
open NormalizedFiniteTransport Theorem25Completion.CycleBounds

theorem serializer_reserve (C w N : Nat) (hN : N≤2^w) :
    N*(C^2+8*C+9)+9≤commonReserve C w := by
  have hc : N≤2^(2*w):=hN.trans (Nat.pow_le_pow_right (by decide) (by omega))
  have h:=packet_reserve_bound C w N hc
  have hp : N*(C^2+8*C+9)+9≤32*(N+1)*(C+1)^2 := by
    nlinarith only [Nat.zero_le (N*C^2),Nat.zero_le (N*C),Nat.zero_le N,Nat.zero_le (C^2),Nat.zero_le C]
  have ht : (N+1)*(C+1)^2≤(N+1)^3*(C+1)^3 :=
    Nat.mul_le_mul (Nat.le_self_pow (by decide) _) (Nat.pow_le_pow_right (by omega) (by decide))
  have hs:=Nat.mul_le_mul_left 32 ht
  have hp2 : 32*(N+1)*(C+1)^2≤8192*(N+1)^3*(C+1)^3 := by
    nlinarith only [hs,Nat.zero_le ((N+1)^3*(C+1)^3)]
  exact hp.trans (hp2.trans h)

theorem run (C w : Nat) (left : List Bool) (leftN : Nat) (P : Ring.Poly Nat) (out : List Bool)
    (hf : Fits C P) (hn : Ring.Normal P) (hc : P.length≤2^w) :
    Step Theorem25Completion.CycleFlatDock.machine
      (2*(P.length*(C^2+8*C+9)+8)+2*commonReserve C w+7)
      (Theorem25Completion.CycleFlatDock.heads out)
      (Theorem25Completion.CycleFlatDock.bank C (commonReserve C w) left leftN (P.map (maskNat C)) out)
      (Theorem25Completion.CycleFlatDock.heads (out++ExtIncidence.stream P))
      (Theorem25Completion.CycleFlatDock.bank C (commonReserve C w) left leftN [] (out++ExtIncidence.stream P)) := by
  have hR : C+3≤commonReserve C w := by
    have h:=(Theorem25Completion.CycleDenseAtomCost.reserve_small C w).1;omega
  have hb : (lift C P).length*(C^2+8*C+9)+9≤commonReserve C w := by
    simpa only [lift,List.length_map] using serializer_reserve C w P.length hc
  have h:=Theorem25Completion.CycleFlatDock.typed_run (commonReserve C w) left leftN (lift C P) out
    (normal_lift C P hf hn).2 hR hb
  have he : (lift C P).map (fun m=>m.map Fin.val)=P:=lift_down C P hf
  rw [he] at h
  have hm : (lift C P).map PhysicalPacketMasks.mask=P.map (maskNat C) := masks_lift C P hf
  rw [hm] at h
  simpa only [lift,List.length_map] using h

end PCJ9eff70d512234a4c_Fixed.Materializer.PacketNativeMeaning

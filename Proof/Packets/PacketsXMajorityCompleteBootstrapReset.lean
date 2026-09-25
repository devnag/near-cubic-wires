import Proof.Packets.PacketsXMajorityCompleteBootstrapResident
import Proof.Packets.PacketsXMajorityCompleteFinalBounds

/-! The final field census discharges every actual erasure length guard.
This is the closed reusable reset following a stored majority result. -/
set_option autoImplicit false
set_option maxHeartbeats 500000
set_option maxRecDepth 120000
set_option warningAsError true
namespace PCJ9eff70d512234a4c_Fixed.Materializer.MajorityComplete.Bootstrap
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch
open NormalizedFiniteTransport Theorem25Completion.CycleBounds PairedPacketMeaning
noncomputable section

theorem final_work_length (C w : Nat) (S : Finset Nat) (d : Nat) (ps : List Poly)
    (hS : ∀j∈S,j<C) (hps : ∀P∈ps,NormalizedIntermediate.Bounded S d P)
    (hfit : (S.card+1)^(d*ps.length)≤2^w) (hAtom : (S.card+1)^d≤2^w)
    (hN : ps.length≤2^w) (hCodes : 2^ps.length≤2^w) (hw : 1≤w) :
    ∀i,(finalWork C (commonReserve C w) ((commonReserve C w)^2) ps i).length≤
      (commonReserve C w)^2 := by
  intro i
  have h:=final_fits C w S d ps hS hps hfit hAtom hN hCodes hw
    (Palette.privatePort i) (Palette.private_not_source i) (Palette.private_not_width i)
  simp only [finalWork,ZeroPadding.pad,List.length_append,List.length_replicate]
  omega

theorem boot_ready_with (palette : Fin 10→List Bool) (C w : Nat) (ps : List Poly)
    (hN : ps.length≤2^w) (hCodes : 2^ps.length≤2^w) (hw : 1≤w)
    (hc : Compatible palette C (commonReserve C w) ps.length ((commonReserve C w)^2)) :
    Step machine (2*(commonReserve C w)^2+6) baseH
      (cold palette ((commonReserve C w)^2) (OrderedPacketStep.bank C (commonReserve C w) ps))
      heads (readyWith palette C (commonReserve C w) ((commonReserve C w)^2) ps) :=
  boot_with palette C (commonReserve C w) ((commonReserve C w)^2) ps
    (palette_fits C w ps.length hN hCodes hw) hc

end
end PCJ9eff70d512234a4c_Fixed.Materializer.MajorityComplete.Bootstrap

import Proof.Packets.PacketsXMajorityCompletePacketRewind
import Proof.Packets.PacketsXMajorityCompletePacketMeaning

/-! Direct application to the genuine row parent. The source row and actual
occurrence atom table are transformed into the exact once-normalized lowered
packet, on tape44 at head0, ready for physical live-assignment relabelling. -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 120000
set_option warningAsError true
namespace PCJ9eff70d512234a4c_Fixed.Materializer.MajorityComplete.PacketRun
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.RepairRepresentation
open NearCubicWires.ExtDecompositionBatch NearCubicWires.SourceInterfaces
open NormalizedFiniteTransport NormalizedIntermediate Theorem25Completion.CycleBounds
noncomputable section
variable {q L : Nat}

theorem actual_rewound_run (C w : Nat) (a : DecompositionAlgorithm)
    (F : Packets.Family q L) (r : Packets.Row F.occurrences L)
    (hchild : PacketMeaning.childCount a F≤C) (hw : 1≤w)
    (hfit : (PacketMeaning.childCount a F+1)^r.degree≤2^w)
    (hfitAtom : PacketMeaning.childCount a F+1≤2^w)
    (hP : SubstitutionInvariant.Good C r.polynomial)
    (hdeg : Ring.Degree r.degree r.polynomial) (hcount : r.polynomial.length≤2^w)
    (left : Ring.Poly Nat) (hl : left.length≤2^w) :
    Step rewound
      (budget C (commonReserve C w) r.polynomial (Packets.lowered a F r)+1+2*commonReserve C w+2)
      (heads []) (coldBank C (commonReserve C w) left r.polynomial
        (atomBank C (commonReserve C w) (PacketMeaning.atoms C a F)) [])
      (heads []) (bank C (commonReserve C w) [] []
        (atomBank C (commonReserve C w) (PacketMeaning.atoms C a F))
        (ExtIncidence.stream (Ring.norm (Packets.lowered a F r)))) := by
  have h:=rewound_run C w r.degree (Finset.range (PacketMeaning.childCount a F))
    (fun j hj=>(Finset.mem_range.mp hj).trans_le hchild) hw
    (by simpa only [Finset.card_range] using hfit)
    (by simpa only [Finset.card_range] using hfitAtom)
    r.polynomial hP hdeg hcount (PacketMeaning.atoms C a F)
    (PacketMeaning.atoms_length C a F) (PacketMeaning.atoms_bounded C a F) left hl
  have he : lowered (PacketMeaning.atoms C a F) r.polynomial=Packets.lowered a F r :=
    PacketMeaning.lowered_exact C a F r hP.1
  rw [he] at h
  exact h

end
end PCJ9eff70d512234a4c_Fixed.Materializer.MajorityComplete.PacketRun

import Proof.Packets.PacketsXMajorityCompletePacketAtomsJoinLayout
import Proof.Rows.SourceDockCore

/-! Physical occurrence atoms, paid polynomial installation, literal
substitution and native packet serialization in one fixed58-tape machine.
The entry row polynomial is retained outside the atom producer. -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 120000
set_option warningAsError true
namespace PCJ9eff70d512234a4c_Fixed.Materializer.MajorityComplete.PacketAtomsJoin
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch NearCubicWires.SourceInterfaces
open NearCubicWires.RepairRepresentation NearCubicWires.RepairSource.VerifierDecoding
open NearCubicWires.RepairSource
open NearCubicWires.RepairOrdinary.RecoveryRootRound
open NormalizedFiniteTransport Theorem25Completion.CycleBounds
noncomputable section
variable {q L : Nat}

def budget (C R count : Nat) (P Q : Ring.Poly Nat) :=
  (PacketAtoms.budget C R count+1+(4*R+5))+1+
    (PacketRun.budget C R P Q+1+2*R+2)
def result (C R : Nat) (a : DecompositionAlgorithm) (F : Packets.Family q L)
    (r : Packets.Row F.occurrences L) : Fin 58→List Bool :=
  install slots (copied C R (CloseoutRowsUniversal.pairs a (Packets.live F) F.occurrences)
    (PacketMeaning.atoms C a F) r.polynomial)
    (PacketRun.bank C R [] [] (PacketRun.atomBank C R (PacketMeaning.atoms C a F))
      (ExtIncidence.stream (Ring.norm (Packets.lowered a F r))))

theorem run (C w : Nat) (a : DecompositionAlgorithm) (F : Packets.Family q L)
    (r : Packets.Row F.occurrences L)
    (hC : 1≤C) (hocc : F.occurrences.length≤C)
    (hchild : PacketMeaning.childCount a F≤C) (hw : 1≤w)
    (hfit : (PacketMeaning.childCount a F+1)^r.degree≤2^w)
    (hfitAtom : PacketMeaning.childCount a F+1≤2^w)
    (hP : SubstitutionInvariant.Good C r.polynomial)
    (hdeg : Ring.Degree r.degree r.polynomial) (hcount : r.polynomial.length≤2^w) :
    Step machine (budget C (commonReserve C w) F.occurrences.length r.polynomial
        (Packets.lowered a F r)) heads
      (input C (commonReserve C w)
        (CloseoutRowsUniversal.pairs a (Packets.live F) F.occurrences) r.polynomial)
      heads (result C (commonReserve C w) a F r) := by
  have hR : 1≤commonReserve C w := by
    have h:=(Theorem25Completion.CycleDenseAtomCost.reserve_small C w).1
    omega
  have hp : PacketVector.Fits (commonReserve C w) (r.polynomial.map (maskNat C)) :=
    (SubstitutionCensus.packet_fits C w _ (SubstitutionCensus.mask_width C _)
      (by simpa only [List.length_map] using hcount)).1
  have atom:=(PacketAtoms.actual_run_of_width C w a F hC hocc hchild hw hfitAtom).embed
    (fun _ : Fin 12=>0) (extras C (commonReserve C w) r.polynomial)
  have moved:=copy_run C (commonReserve C w)
    (CloseoutRowsUniversal.pairs a (Packets.live F) F.occurrences)
    (PacketMeaning.atoms C a F) r.polynomial hR hp
  have packet:=PacketRun.actual_rewound_run C w a F r hchild hw hfit hfitAtom
    hP hdeg hcount [] (by simp)
  have last:=Completion.SourceDock.dock packet slots slots_injective heads
    (copied C (commonReserve C w)
      (CloseoutRowsUniversal.pairs a (Packets.live F) F.occurrences)
      (PacketMeaning.atoms C a F) r.polynomial)
    packet_heads (packet_words C (commonReserve C w) _ _ _ hR)
  rw [Completion.SourceDock.heads_existing slots heads (PacketRun.heads []) packet_heads] at last
  exact (atom.seq moved).seq last

theorem output_word (C R : Nat) (a : DecompositionAlgorithm) (F : Packets.Family q L)
    (r : Packets.Row F.occurrences L) :
    result C R a F r 57=ExtIncidence.stream (Ring.norm (Packets.lowered a F r)) := by
  change install slots _ _ (slots 44)=_
  rw [install_slot slots slots_injective]
  rfl

end
end PCJ9eff70d512234a4c_Fixed.Materializer.MajorityComplete.PacketAtomsJoin

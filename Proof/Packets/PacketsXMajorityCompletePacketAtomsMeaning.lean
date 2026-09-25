import Proof.Packets.PacketsXMajorityCompletePacketAtoms
import Proof.Packets.PacketsXMajorityCompletePacketMeaning
import Proof.CaseAnalysis.RowsUniversalPairs

/-! The normalized dense table is obtained from the actual paired source
cache in occurrence order. Its entries are exactly the atoms in Packets.lowered,
including the empty out-of-range entries. -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 120000
set_option warningAsError true
namespace PCJ9eff70d512234a4c_Fixed.Materializer.MajorityComplete.PacketAtoms
open NearCubicWires NearCubicWires.SourceInterfaces NearCubicWires.RepairRepresentation
open NearCubicWires.RepairOrdinary NearCubicWires.RepairSource
open NearCubicWires.ExtDecompositionBatch NearCubicWires.LocalBitMultitape
open NormalizedFiniteTransport Theorem25Completion.CycleBounds
noncomputable section
variable {q L : Nat}

theorem pair_answer (a : DecompositionAlgorithm) (F : Packets.Family q L) (code : Nat) :
    AddressedAtomsNat.answer
      ((CloseoutRowsUniversal.pairs a (Packets.live F) F.occurrences).getD code ([],[]))=
      PacketMeaning.atom a F code := by
  by_cases hc : code<F.occurrences.length
  · have hp : code<(CloseoutRowsUniversal.pairs a (Packets.live F) F.occurrences).length := by
      rw [CloseoutRowsUniversal.pairs_length];exact hc
    rw [List.getD_eq_getElem _ _ hp]
    unfold AddressedAtomsNat.answer PacketMeaning.atom CloseoutRowsUniversal.atomOfCode
    rw [dif_pos hc]
    exact congrArg Ring.norm (CloseoutRowsUniversal.pairs_residual a (Packets.live F) F.occurrences ⟨code,hc⟩)
  · rw [List.getD_eq_default _ ([],[]) (by rw [CloseoutRowsUniversal.pairs_length];omega)]
    unfold AddressedAtomsNat.answer PacketMeaning.atom CloseoutRowsUniversal.atomOfCode
    rw [dif_neg hc]
    rfl

theorem actual_polynomials (C : Nat) (a : DecompositionAlgorithm) (F : Packets.Family q L) :
    polynomials C (CloseoutRowsUniversal.pairs a (Packets.live F) F.occurrences)=
      PacketMeaning.atoms C a F := by
  apply congrArg List.ofFn
  funext i
  exact pair_answer a F i.val

theorem actual_run (C w : Nat) (a : DecompositionAlgorithm) (F : Packets.Family q L)
    (hocc : F.occurrences.length≤C)
    (hc : ∀p∈CloseoutRowsUniversal.pairs a (Packets.live F) F.occurrences,
      (p.1++p.2).length≤2^(2*w))
    (hf : ∀p∈CloseoutRowsUniversal.pairs a (Packets.live F) F.occurrences,Fits C (p.1++p.2))
    (hd : ∀p∈CloseoutRowsUniversal.pairs a (Packets.live F) F.occurrences,
      ∀m∈p.1++p.2,m.length≤C) :
    Step machine (budget C (commonReserve C w) F.occurrences.length) DenseAtomBoundary.heads
      (IdentityAtomMaterialize.input C (commonReserve C w)
        (CloseoutRowsUniversal.pairs a (Packets.live F) F.occurrences) [] [])
      DenseAtomBoundary.heads
      (AddressedAtomMaterialize.paddedA C (commonReserve C w) id
        (CloseoutRowsUniversal.pairs a (Packets.live F) F.occurrences)
        ((PacketMeaning.atoms C a F).map (List.map (maskNat C))) 0) := by
  have h:=run C w (CloseoutRowsUniversal.pairs a (Packets.live F) F.occurrences)
    (by rw [CloseoutRowsUniversal.pairs_length];exact hocc) hc hf hd
  rw [actual_polynomials,CloseoutRowsUniversal.pairs_length] at h
  exact h

end
end PCJ9eff70d512234a4c_Fixed.Materializer.MajorityComplete.PacketAtoms

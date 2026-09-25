import Proof.Packets.PacketsLowerRun3

set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

namespace NearCubicWires.PacketsConstruction.LowerCore
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairSource.VerifierDecoding
open NearCubicWires.RepairRepresentation
open PCJ9eff70d512234a4c_Fixed PCJ9eff70d512234a4c_Fixed.Materializer
noncomputable section

/-- The core after its metadata: arena boot, raw atoms, load, join. -/
def tailMachine := Composition.machine kbStep (Composition.machine raStep (Composition.machine loadStep joinStep))

def tailCost (C w cap poolLen occLen : ℕ) (P lowered : Ring.Poly ℕ) : ℕ :=
  KitBoot.cost C w + 1 + ((2 * CloseoutRowsRawAtomProducer.budget cap poolLen + 2) + 1 +
    ((1 + 1 + (PacketBank.lookupBudget (PolyKit.reserve C w) 0 + 1 + 1)) + 1 +
      MajorityComplete.PacketAtomsJoin.budget C (PolyKit.reserve C w) occLen P lowered))

theorem cost_split (mcost C w cap poolLen occLen : ℕ) (P lowered : Ring.Poly ℕ) :
    cost mcost C w cap poolLen occLen P lowered = mcost + 1 + tailCost C w cap poolLen occLen P lowered := rfl

variable {q L : ℕ} (a : DecompositionAlgorithm) (F : Packets.Family q L) (row : Packets.Row F.occurrences L)

/-- **The core from its metadata state.** -/
theorem tail_run (Rb C w cap : ℕ) (input : List Bool) (H1 : Fin 302 → ℕ) (A1 : Fin 302 → List Bool)
    (f1 : Facts1 Rb C w F.occurrences.length cap input
      (PacketVector.entry (PolyKit.reserve C w) (row.polynomial.map (NormalizedFiniteTransport.maskNat C)))
      (CloseoutRowsRawAtomMeaning.countWord a
        (RepairSource.CloseoutRowsUniversal.pool (Packets.live F) F.occurrences)) H1 A1)
    (hC : 1 ≤ C) (hocc : F.occurrences.length ≤ C) (hchild : MajorityComplete.PacketMeaning.childCount a F ≤ C)
    (hw : 1 ≤ w) (hfit : (MajorityComplete.PacketMeaning.childCount a F + 1) ^ row.degree ≤ 2 ^ w)
    (hfitAtom : MajorityComplete.PacketMeaning.childCount a F + 1 ≤ 2 ^ w)
    (hP : SubstitutionInvariant.Good C row.polynomial) (hdeg : Ring.Degree row.degree row.polynomial)
    (hcount : row.polynomial.length ≤ 2 ^ w)
    (hc : 64 * (ExtDecompositionBatch.B a (RepairSource.CloseoutRowsUniversal.pool (Packets.live F) F.occurrences)
      + 2) ^ 2 ≤ cap) (hcapRb : cap + 1 ≤ Rb)
    (hlog : CloseoutRowsRawAtomProducer.budget cap
      (RepairSource.CloseoutRowsUniversal.pool (Packets.live F) F.occurrences).length ≤ Rb)
    (hfits : PacketVector.Fits (PolyKit.reserve C w) (row.polynomial.map (NormalizedFiniteTransport.maskNat C)))
    (h2R : 2 * PolyKit.reserve C w ≤ Rb) (hpop : F.occurrences.length + 2 ≤ Rb) :
    ∃ (H : Fin 302 → ℕ) (A : Fin 302 → List Bool),
      Step tailMachine (tailCost C w cap (RepairSource.CloseoutRowsUniversal.pool (Packets.live F) F.occurrences).length
        F.occurrences.length row.polynomial (Packets.lowered a F row)) H1 A1 H A ∧
      A 0 = input ∧ H 0 = 0 ∧
      A 1 = ZeroPadding.pad Rb (PacketVector.entry (PolyKit.reserve C w)
        (row.polynomial.map (NormalizedFiniteTransport.maskNat C))) ∧ H 1 = 0 ∧
      A 2 = ZeroPadding.pad Rb (ExtIncidence.stream (Ring.norm (Packets.lowered a F row))) ∧ H 2 = 0 := by
  obtain ⟨H2, A2, s2, f2⟩ := stage2 Rb C w F.occurrences.length cap input _ _ H1 A1 f1
  obtain ⟨H3, A3, s3, f3⟩ := stage3 a (RepairSource.CloseoutRowsUniversal.pool (Packets.live F) F.occurrences)
    Rb C w F.occurrences.length cap input _ H2 A2 hc hcapRb hlog f2
  obtain ⟨H4, A4, s4, f4⟩ := stage456 Rb C w F.occurrences.length input _
    (row.polynomial.map (NormalizedFiniteTransport.maskNat C)) H3 A3 hfits h2R f3
  obtain ⟨H5, A5, s5, e0, g0, e1, g1, e2, g2⟩ := stage7 a F row Rb C w input H4 A4 hC hocc hchild hw hfit hfitAtom
    hP hdeg hcount (by omega) hpop f4
  exact ⟨H5, A5, s2.seq (s3.seq (s4.seq s5)), e0, g0, e1, g1, e2, g2⟩

end
end NearCubicWires.PacketsConstruction.LowerCore

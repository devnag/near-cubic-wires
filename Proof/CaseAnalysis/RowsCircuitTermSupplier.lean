import Proof.CaseAnalysis.RowsCircuitTermPorts

/-! Both actual circuit programs supply the existing counted term/family
consumer, with original decoder guards and no circuit serialization. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsCircuitTermSupplier
open LocalBitMultitape CloseoutWitness CanonicalWitnessCodec RadixSemantics
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

noncomputable def symmetricFlag (core W L : ℕ) (bits : List Bool) : Bool:=
  match decodeNormalizedSymmetricThresholdCircuit core (value (TermCoefficient.circuitCode bits)) with
  | none=>false
  | some c=>decide (c.wireCount ≤ W ∧ c.descriptionBits ≤ L)
noncomputable def thresholdFlag (core W L : ℕ) (bits : List Bool) : Bool:=
  match decodeNormalizedThresholdThresholdCircuit core (value (TermCoefficient.circuitCode bits)) with
  | none=>false
  | some c=>decide (c.wireCount ≤ W ∧ c.descriptionBits ≤ L)
noncomputable def symmetricNative (core : ℕ) (bits : List Bool):=
  CloseoutRowsCircuitSymmetricRun.native core (TermCoefficient.circuitCode bits)
noncomputable def thresholdNative (core : ℕ) (bits : List Bool):=
  CloseoutRowsCircuitThresholdRun.native core (TermCoefficient.circuitCode bits)

theorem symmetricFlag_iff (core W L : ℕ) (bits : List Bool) : symmetricFlag core W L bits=true ↔
    CloseoutRowsCircuitSymmetricRun.passed core W L (TermCoefficient.circuitCode bits):=by
  rw [CloseoutRowsCircuitMeaning.symmetric_exact]
  cases hd:decodeNormalizedSymmetricThresholdCircuit core (value (TermCoefficient.circuitCode bits)) <;>
    simp [symmetricFlag,hd]

theorem thresholdFlag_iff (core W L : ℕ) (bits : List Bool) : thresholdFlag core W L bits=true ↔
    CloseoutRowsCircuitThresholdRun.passed core W L (TermCoefficient.circuitCode bits):=by
  rw [CloseoutRowsCircuitMeaning.threshold_exact]
  cases hd:decodeNormalizedThresholdThresholdCircuit core (value (TermCoefficient.circuitCode bits)) <;>
    simp [thresholdFlag,hd]

theorem raw_width (bits : List Bool) : (TermCoefficient.circuitCode bits).length=bits.length:=
  (RecoveryFixedUnpair.word_lengths _).1.trans (CompetitorWitnessTriple.word_length bits _)

end NearCubicWires.RepairOrdinary.CloseoutRowsCircuitTermSupplier

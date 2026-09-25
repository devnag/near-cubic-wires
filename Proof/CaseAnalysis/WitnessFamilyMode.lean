import Proof.CaseAnalysis.RowsCircuitTermSupplier
import Proof.CaseAnalysis.CloseoutWitnessFamilyRun

/-! The two actual circuit workers instantiate the whole family ABI.
The predicate is the same public circuit decoder and original wire and
description guards; no worker certificate is an external premise. -/
namespace NearCubicWires.RepairOrdinary.CloseoutWitness.FamilyMode
open LocalBitMultitape CloseoutRowsCircuitTermSupplier
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

def program (sym : Bool) : Σ s,Machine 1703 s:=
  if sym then ⟨CloseoutRowsCircuitSymmetricRun.program.1,CloseoutRowsCircuitSymmetricRun.machine⟩
  else ⟨CloseoutRowsCircuitThresholdRun.program.1,CloseoutRowsCircuitThresholdRun.machine⟩
def machine (sym : Bool) : Machine 1703 (program sym).1:=(program sym).2
def flag (sym : Bool) (core W L : ℕ):=
  if sym then symmetricFlag core W L else thresholdFlag core W L
def native (sym : Bool) (core : ℕ):=
  if sym then symmetricNative core else thresholdNative core

theorem field_width (bits field : List Bool) (hfield : field∈FamilyFields.words bits) : field.length=bits.length:=by
  obtain ⟨_,_,rfl⟩:=List.mem_map.mp hfield
  exact SignedSortKey.binary_length _ _

theorem term_width (field term : List Bool) (hterm : term∈SumHeader.words field) : term.length=field.length:=by
  obtain ⟨_,_,rfl⟩:=List.mem_map.mp hterm
  rw [SignedSortKey.binary_length]
  exact (RecoveryFixedUnpair.word_lengths _).1.trans (CompetitorWitnessTriple.word_length field _)

end
end NearCubicWires.RepairOrdinary.CloseoutWitness.FamilyMode

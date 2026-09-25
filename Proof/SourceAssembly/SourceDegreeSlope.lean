import Proof.SourceAssembly.SourceTraceData
import Proof.SourceAssembly.SourcePrologue
import Proof.SourceAssembly.AdmissionDegree

section
set_option autoImplicit false
set_option maxRecDepth 120000
set_option warningAsError true

open NearCubicWires LocalBitMultitape ExtDecompositionBatch RepairOrdinary RepairRepresentation
open SourceInterfaces RepairSource RepairSource.CloseoutFinal SupplierEstimator SupplierPipeline
open PCJ9eff70d512234a4c_Fixed PCJd4d1d9d7d1fa4313_Production
namespace NearCubicWires.SourceConstruction.TraceData
noncomputable section

/-- **The effective degree at call `j` selects the slope.** For a layout family whose layouts carry AD's uniform degree:
`min (lay j).degree |pool j| = if 3 < lenOf … j then q / (200(K+2)) else 1`. -/
theorem deg_slope {q : Nat} {circuit : BooleanCircuit q} {pcpp : PointwisePCPP circuit}
    (coordinate : Fin (pcpp.systematicBits + pcpp.auxiliaryBits) →
      ComponentwisePolynomial.CircuitPolynomial (C10TotalDecode.Atom pcpp) 1)
    (ph : CloseoutRowsOriginalSchedule.Phase) (ci : Fin (2 ^ pcpp.clauseBits))
    (sources : EightSources) (L target : Nat) (mode : Bool) (selector : CyclicChoice.Laws)
    (lay : LayoutFamily coordinate ph ci sources L target mode selector)
    (hlay : ∀ j, (lay j).degree = Admission.uniformDeg q L) (hL : 1 ≤ L)
    (hu : 1 ≤ q / (200 * (normalizedLiveCount q L + 1 + 1))) (j : Nat) :
    min (lay j).degree (Packets.pool (decompositionOf sources)
        (Packets.request sources L target mode (SourceRequest.FactorLoop.factorsAt coordinate ph ci j))
        (Packets.geometry selector
          (Packets.request sources L target mode (SourceRequest.FactorLoop.factorsAt coordinate ph ci j)))).length =
      if 3 < lenOf coordinate ph ci sources L target mode j then q / (200 * (normalizedLiveCount q L + 1 + 1))
      else 1 := by
  rw [hlay j, Admission.effectiveDegree_eq hL]
  have hU : Admission.uniformDeg q L = q / (200 * (normalizedLiveCount q L + 1 + 1)) := rfl
  have hb := Prologue.exactList_bit (C10SupplierRowInput.childList (decompositionOf sources)
    (Packets.live (Packets.request sources L target mode (SourceRequest.FactorLoop.factorsAt coordinate ph ci j)))
    (Packets.request sources L target mode (SourceRequest.FactorLoop.factorsAt coordinate ph ci j)).occurrences)
  unfold lenOf
  rw [hU]
  by_cases h0 : (C10SupplierRowInput.childList (decompositionOf sources)
      (Packets.live (Packets.request sources L target mode (SourceRequest.FactorLoop.factorsAt coordinate ph ci j)))
      (Packets.request sources L target mode (SourceRequest.FactorLoop.factorsAt coordinate ph ci j)).occurrences).length = 0
  · have hn : ¬ (3 < (exactListWord (C10SupplierRowInput.childList (decompositionOf sources)
        (Packets.live (Packets.request sources L target mode (SourceRequest.FactorLoop.factorsAt coordinate ph ci j)))
        (Packets.request sources L target mode (SourceRequest.FactorLoop.factorsAt coordinate ph ci j)).occurrences)).length) :=
      fun h => hb.mp h (List.length_eq_zero_iff.mp h0)
    rw [if_pos h0, if_neg hn]
    exact min_eq_right hu
  · have hp : 3 < (exactListWord (C10SupplierRowInput.childList (decompositionOf sources)
        (Packets.live (Packets.request sources L target mode (SourceRequest.FactorLoop.factorsAt coordinate ph ci j)))
        (Packets.request sources L target mode (SourceRequest.FactorLoop.factorsAt coordinate ph ci j)).occurrences)).length :=
      hb.mpr (fun h => h0 (by rw [h]; rfl))
    rw [if_neg h0, if_pos hp]

end
end NearCubicWires.SourceConstruction.TraceData
end

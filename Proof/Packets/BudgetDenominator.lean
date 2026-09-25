import Proof.Packets.PacketsMetaPrime
import Proof.SourceAssembly.SourceRequestResidentProducer
import Proof.SourceAssembly.SourceTraceData

set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

namespace NearCubicWires.SourceBudget
open NearCubicWires NearCubicWires.RepairOrdinary NearCubicWires.RepairRepresentation
open NearCubicWires.SupplierPipeline NearCubicWires.SupplierEstimator NearCubicWires.SupplierPrime
open NearCubicWires.SupplierWalkBridge NearCubicWires.SourceInterfaces
open NearCubicWires.RepairSource NearCubicWires.RepairSource.CloseoutFinal
open PCJ9eff70d512234a4c_Fixed PCJd4d1d9d7d1fa4313_Production

/-- **The denominator link at one call's atoms.** -/
theorem denominator_link (sources : EightSources) (L target : ℕ) (mode : Bool) {q : ℕ}
    {circuit : BooleanCircuit q} {pcpp : PointwisePCPP circuit} (atoms : List (C10TotalDecode.Atom pcpp))
    (four : atoms.length ≤ 4) :
    (LiveRows.fraction sources L target mode atoms).2 =
      PacketsGlue.RequestMeta.primeCountOf (decompositionOf sources)
          (SourceRequest.monomialRequest L target mode atoms four) *
        PacketsGlue.RequestMeta.seedCount (decompositionOf sources)
          (SourceRequest.monomialRequest L target mode atoms four) * 2^q := by
  cases mode with
  | true =>
    simp only [LiveRows.fraction, SourceRequest.monomialRequest, if_true, LiveRows.symDenominator,
      PacketsGlue.RequestMeta.primeCountOf, PacketsGlue.RequestMeta.seedCount, Packets.seedList,
      List.length_ofFn, one_mul]
    rfl
  | false =>
    simp only [LiveRows.fraction, SourceRequest.monomialRequest, Bool.false_eq_true, if_false,
      LiveRows.thrDenominator, PacketsGlue.RequestMeta.primeCountOf, PacketsGlue.RequestMeta.seedCount,
      Packets.seedList, List.length_ofFn]
    rfl

theorem denominator_at (sources : EightSources) {q : ℕ} {circuit : BooleanCircuit q} {pcpp : PointwisePCPP circuit}
    (coordinate : Fin (pcpp.systematicBits + pcpp.auxiliaryBits) →
      ComponentwisePolynomial.CircuitPolynomial (C10TotalDecode.Atom pcpp) 1)
    (ph : CloseoutRowsOriginalSchedule.Phase) (ci : Fin (2 ^ pcpp.clauseBits)) (L target : ℕ) (mode : Bool) (j : ℕ) :
    (SourceConstruction.TraceData.fractionOf coordinate ph ci sources L target mode j).2 =
      PacketsGlue.RequestMeta.primeCountOf (decompositionOf sources)
          (SourceRequest.requestAt coordinate ph ci L target mode j) *
        PacketsGlue.RequestMeta.seedCount (decompositionOf sources)
          (SourceRequest.requestAt coordinate ph ci L target mode j) * 2^q :=
  denominator_link sources L target mode _ _

end NearCubicWires.SourceBudget


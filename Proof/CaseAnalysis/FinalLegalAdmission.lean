import Proof.CaseAnalysis.FinalGuardedMachineConsumer
import Proof.CaseAnalysis.WitnessBoundedFamilyDecoded
import Proof.CaseAnalysis.WitnessDyadicGuards
import Proof.CaseAnalysis.WitnessInputCutoff
import Proof.CaseAnalysis.NaturalWireCaps

/-! Paper C.10's honest typed witnesses pass the actual bounded cold flag.
The machine's two natural denominators are exactly 1, matching the frozen
cap1 completeness consumers. A fixed outer onset absorbs the native guard
and padded-arity cutoffs; it does not change the earlier cold cutoff.
This proves admission, not the remaining physical worker/continuation run. -/
namespace NearCubicWires.RepairSource.CloseoutFinal.C10LegalAdmission
open RepairOrdinary RepairOrdinary.CloseoutWitness SourceInterfaces RepairRepresentation
open SelectedRecoveryIntegration CanonicalWitnessCodec SupplierPipeline
open CloseoutLanguage CompetitorRationalGap C10GuardedMachineConsumer C10TotalDecode
open CloseoutWitness.SelectedSource
open private decode_cast from Proof.CaseAnalysis.WitnessDyadicGuards

set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

end
end NearCubicWires.RepairSource.CloseoutFinal.C10LegalAdmission

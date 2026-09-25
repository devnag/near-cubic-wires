import Proof.Packets.BudgetCycRows
import Proof.Packets.BudgetDenominator
import Proof.Packets.BudgetEntryCount
import Proof.Packets.BudgetLift
import Proof.Packets.BudgetPoly
import Proof.Packets.BudgetSeamScalars
import Proof.Packets.BudgetWidthA
import Proof.Packets.SourceResidentOccCount
import Proof.Packets.SrcStartStream
import Proof.SourceAssembly.AdmissionSource
import Proof.SourceAssembly.SourceCacheBound
import Proof.SourceAssembly.SourceClassifierCapacity
import Proof.SourceAssembly.SourceCyclePadRw
import Proof.SourceAssembly.SourceDegreeSlope
import Proof.SourceAssembly.SourceFactorSelCoefBin
import Proof.SourceAssembly.SourceFactorSelCoefValue
import Proof.SourceAssembly.SourceFactorSelHdrBlock
import Proof.SourceAssembly.SourceFactorSelItem4Stages
import Proof.SourceAssembly.SourceFactorSelItem4Top
import Proof.SourceAssembly.SourceFirstCore3
import Proof.SourceAssembly.SourceFirstCore4
import Proof.SourceAssembly.SourceInitLayout
import Proof.SourceAssembly.SourceParityNatural
import Proof.SourceAssembly.SourceParitySymmetricBody
import Proof.SourceAssembly.SourcePoolHeader
import Proof.SourceAssembly.SourceProloguePro3
import Proof.SourceAssembly.SourceRequestCurComp
import Proof.SourceAssembly.SourceRequestCurSpec
import Proof.SourceAssembly.SourceRequestTermSegB
import Proof.SourceAssembly.SourceRestRunD4
import Proof.SourceAssembly.SourceSkelCodeR
import Proof.SourceAssembly.SourceSkelInitMove
import Proof.SourceAssembly.SourceSkelProt
import Proof.SourceAssembly.SourceSkelRestData

set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
namespace NearCubicWires.SourceSkeleton

/-- The source child's hole, restated after hub A (definitionally `SourceGenHoles3`). -/
def SourceGenHoles3A (selector : PCJ9eff70d512234a4c_Fixed.CyclicChoice.Laws)
    (compiler : PCJ9eff70d512234a4c_Fixed.Packets.CompilerLaws) : Prop :=
  SourceGenHoles3 selector compiler

/-- The reduce's producer: the restated hole gives the child's hole. -/
theorem genHoles3_of_A (selector : PCJ9eff70d512234a4c_Fixed.CyclicChoice.Laws)
    (compiler : PCJ9eff70d512234a4c_Fixed.Packets.CompilerLaws) (h : SourceGenHoles3A selector compiler) :
    SourceGenHoles3 selector compiler := h

end NearCubicWires.SourceSkeleton


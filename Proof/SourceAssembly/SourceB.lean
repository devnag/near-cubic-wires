import Proof.Packets.BudgetInitCost
import Proof.Packets.BudgetJ5R
import Proof.Packets.BudgetYFam
import Proof.SourceAssembly.SourceA
import Proof.SourceAssembly.SourceCacheBudget
import Proof.SourceAssembly.SourceFactorSelCoefBridge
import Proof.SourceAssembly.SourceFactorSelCountRead
import Proof.SourceAssembly.SourceFactorSelItem4Top2
import Proof.SourceAssembly.SourceFactorSelWordsHostLay
import Proof.SourceAssembly.SourceFirstSeam4L
import Proof.SourceAssembly.SourcePoolBoot
import Proof.SourceAssembly.SourceRequestCurMoment
import Proof.SourceAssembly.SourceRequestLitInfo
import Proof.SourceAssembly.SourceRequestSelRho
import Proof.SourceAssembly.SourceRequestSymOriginalForward
import Proof.SourceAssembly.SourceSkelFillB
import Proof.SourceAssembly.SourceSkelInitHorner
import Proof.SourceAssembly.SourceSkelLayout
import Proof.SourceAssembly.SourceStepsF6
import Proof.SourceAssembly.SourceStepsHw
import Proof.SourceAssembly.SourceThresholdGate

set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
namespace NearCubicWires.SourceSkeleton

/-- The source hole, restated after hub B (definitionally `SourceGenHoles3A`). -/
def SourceGenHoles3B (selector : PCJ9eff70d512234a4c_Fixed.CyclicChoice.Laws)
    (compiler : PCJ9eff70d512234a4c_Fixed.Packets.CompilerLaws) : Prop :=
  SourceGenHoles3A selector compiler

/-- The reduce's producer: the restated hole gives hub A's hole. -/
theorem genHoles3A_of_B (selector : PCJ9eff70d512234a4c_Fixed.CyclicChoice.Laws)
    (compiler : PCJ9eff70d512234a4c_Fixed.Packets.CompilerLaws) (h : SourceGenHoles3B selector compiler) :
    SourceGenHoles3A selector compiler := h

end NearCubicWires.SourceSkeleton


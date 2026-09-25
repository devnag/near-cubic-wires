import Proof.Foundations.BooleanCircuitSizePadding
import Proof.Foundations.ComponentwiseValidity

/-!
# Executable componentwise-verifier parameters

The imported pointwise PCPP exposes real completeness and soundness constants,
whereas the fixed weak verifier can store and compare only finite rational
codes.  This module makes the one canonical rational choice and proves the
entire numerical reserve once.  Downstream machine code therefore receives
data, not an unproved real-comparison side condition.
-/

namespace NearCubicWires.ComponentwiseVerifierParameters

open NearCubicWires
open NearCubicWires.ComponentwiseValidity
open NearCubicWires.ExecutableInterfaces
open NearCubicWires.SourceInterfaces

/-! ## Bounds derived from the executable PCPP source -/

end NearCubicWires.ComponentwiseVerifierParameters

import Proof.SourceAssembly.SourceRequestSelBackK

set_option autoImplicit false
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace NearCubicWires.SourceRequest.SelLocal
open NearCubicWires LocalBitMultitape ExtDecompositionBatch RepairOrdinary
open NearCubicWires.RepairRepresentation (PCPPRequest PointwisePCPPAlgorithm pcppOutput)
open SourceInterfaces RecoveryRootRound RepairSource.VerifierDecoding
open NearCubicWires.ComponentwiseBranchExtraction NearCubicWires.ComponentwisePolynomial
open NearCubicWires.RepairOrdinary.CloseoutRowsOriginalSchedule (Phase)
open NearCubicWires.SourceRequest.SelFront NearCubicWires.SourceRequest.SelBack
open NearCubicWires.SourceRequest.SelSpec NearCubicWires.SourceRequest.CurSpec
open NearCubicWires.SourceRequest.CurContract NearCubicWires.SourceRequest.CoordBridge NearCubicWires.SourceRequest.TermReader
open NearCubicWires.RepairOrdinary.CloseoutRowsOriginalClause (index negative)
open PCJ6e421fabe2aa4155_SourceLiteralSupport (value)
open NearCubicWires.SourceRequest.LitInfo (litCost)
open NearCubicWires.SourceFactorSel.Modes (kindOf bmOf bitsOf)
noncomputable section

/-- **The local entry bank, the clause-count port `32` at padding `QK`** (S: `QK = 0`) (heads all `0`): the refill clause cache on `0..18` (exact), the witness `frame bits` on `19`, S's
cursor `1^m` on `20`, the residents on `21..32` and `1^b` on `39` (all `pad Rc`), every other fixed port `≥ 33` and the region
blank at `Rc`. -/
structure LocalInK (t : Nat) (mode : Bool) (A : Fin (NF + (19 + 4 * t)) → List Bool) (cache : Fin 19 → List Bool)
    (bits : List Bool) (m q Pw W Ld L target cwid cw D K b Rc QK : Nat) : Prop where
  cache : ∀ j : Fin 19, A (up ⟨j.val, by have := j.isLt; unfold NF; omega⟩) = cache j
  wit : A (up 19) = RepairOrdinary.frame bits
  cur : A (up 20) = ZeroPadding.pad Rc (List.replicate m true)
  tpl : A (up 21) = ZeroPadding.pad Rc (UnaryTemplate.tape q)
  uP : A (up 22) = ZeroPadding.pad Rc (List.replicate Pw true)
  uW : A (up 23) = ZeroPadding.pad Rc (List.replicate W true)
  uL : A (up 24) = ZeroPadding.pad Rc (List.replicate Ld true)
  hdr : ∀ i : Fin 4, A (up ⟨25 + i.val, by have := i.isLt; unfold NF; omega⟩) =
    ZeroPadding.pad Rc (RepairOrdinary.frame (SourceFactorSel.Header.fields mode q L target 0 ⟨i.val, by omega⟩))
  ucwid : A (up 29) = ZeroPadding.pad Rc (List.replicate cwid true)
  ucw : A (up 30) = ZeroPadding.pad Rc (List.replicate cw true)
  uD : A (up 31) = ZeroPadding.pad Rc (List.replicate D true)
  uK : A (up 32) = ZeroPadding.pad QK (List.replicate K true)
  ub : A (up 39) = ZeroPadding.pad Rc (List.replicate b true)
  blank : ∀ k (h : k < NF), 33 ≤ k → k ≠ 39 → A (up ⟨k, h⟩) = List.replicate Rc false
  region : ∀ x, A (Fin.natAdd NF x) = List.replicate Rc false

end
end NearCubicWires.SourceRequest.SelLocal


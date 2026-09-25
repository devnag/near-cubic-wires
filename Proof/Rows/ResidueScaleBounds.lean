import Proof.Rows.ResidueScaleCell

/-! The product emitter's input masters and reserve depend only on width. -/
set_option autoImplicit false
set_option maxHeartbeats 550000
set_option maxRecDepth 120000
set_option warningAsError true
namespace PCJ45bee56da9f34d5a_ResidueScaleBounds
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairSource.CloseoutFinal
open NearCubicWires.RepairSource.VerifierDecoding
open PCJ45bee56da9f34d5a_ResidueScaleCell
noncomputable section

theorem palette_length (a b p w U : Nat) (hU : 1024*(w+1)^2+2≤U) :
    ∀i,(palette a b p w i).length≤U:=by
  intro i;fin_cases i <;>
    simp [palette,PCJ45bee56da9f34d5a_ResidueProductReady.input,
      PCJ45bee56da9f34d5a_ResidueProduct.input,PCJ45bee56da9f34d5a_ResidueProduct.extras,
      HierarchyMultiplyEntry.input14,HierarchyMultiplyEntry.input,Fin.addCases,
      Function.update,frame_length,SignedSortKey.binary_length,CompareMachine.word,
      PCJ45bee56da9f34d5a_ResidueProductBounds.resetCap] <;>nlinarith

theorem run (a b p w U : Nat) (out : List Bool) (hp : 0<p) (hpw : 2*p≤2^w)
    (ha : a<2^w) (hb : b<2^w) (hU : 1024*(w+1)^2+2≤U) :
    Step machine (1024*(w+1)^2+6*U+2*w+19) (heads out 0) (cold (palette a b p w) U out)
      (heads (out++frame (SignedSortKey.binary w ((a*b)%p))) 0)
      (cold (palette a b p w) U (out++frame (SignedSortKey.binary w ((a*b)%p)))):=
  PCJ45bee56da9f34d5a_ResidueScaleCell.run a b p w U out hp hpw ha hb hU (palette_length a b p w U hU)

end
end PCJ45bee56da9f34d5a_ResidueScaleBounds

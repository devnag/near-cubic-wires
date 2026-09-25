import Proof.Rows.NativeScaleEquation
import Proof.Rows.ExpandedThresholdStream

/-! The actual product residues emitted from native fields are exactly the
coefficient frames for the canonical mixed-radix block. -/
set_option autoImplicit false
set_option maxHeartbeats 450000
set_option maxRecDepth 120000
set_option warningAsError true
namespace PCJ45bee56da9f34d5a_NativeScaleMeaning
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairSource.CloseoutFinal
open NearCubicWires.RepairRepresentation NearCubicWires.SupplierPipeline
open SignedSortKey
noncomputable section

theorem scaled_eq (a p : Nat) (factor z : Int) (hp : 0<p)
    (ha : (a : ZMod p)=(factor : ZMod p)) :
    (a*FinalPrimeReduce.intResidue p z)%p=FinalPrimeReduce.intResidue p (factor*z):=by
  apply FinalPrimeReduce.reduced_of_congr
  apply (ZMod.intCast_eq_intCast_iff _ _ _).mp
  simp only [Int.cast_natCast,Int.cast_mul,Nat.cast_mul]
  rw [ha,FinalPrimeReduce.intResidue_cast p hp z]

theorem result_exact (a p w : Nat) (factor : Int) {n : Nat}
    (eq : LabelledEquation (Fin n)) (hp : 0<p)
    (ha : (a : ZMod p)=(factor : ZMod p)) :
    PCJ45bee56da9f34d5a_NativeScaleEquation.result a p w eq=
      (PCJ45bee56da9f34d5a_NativeScaleEquation.weights eq++[-eq.target]).flatMap
        (fun z=>frame (binary w (FinalPrimeReduce.intResidue p (factor*z)))):=by
  rw [PCJ45bee56da9f34d5a_NativeScaleEquation.result_flatMap]
  apply List.flatMap_congr
  intro z _
  rw [scaled_eq a p factor z hp ha]

theorem block_exact (a p w : Nat) (factor : Int) {n : Nat}
    (g : ExactThresholdGate n) (bits : Fin n→Bool) (hp : 0<p)
    (ha : (a : ZMod p)=(factor : ZMod p)) :
    PCJ45bee56da9f34d5a_NativeScaleEquation.result a p w
      ({weights:=g.weight,target:=g.target} : LabelledEquation (Fin n))=
      (PCJ45bee56da9f34d5a_ExpandedThresholdStream.block g bits factor).flatMap
        (fun t=>frame (binary w (FinalPrimeReduce.intResidue p t.1))):=by
  rw [result_exact a p w factor _ hp ha]
  simp only [PCJ45bee56da9f34d5a_NativeScaleEquation.weights,
    PCJ45bee56da9f34d5a_ExpandedThresholdStream.block,List.flatMap_append,
    List.flatMap_cons,List.flatMap_nil,List.append_nil,mul_neg]
  congr 1
  change (List.map (fun z=>frame (binary w (FinalPrimeReduce.intResidue p (factor*z)))) (List.ofFn g.weight)).flatten=_
  change _=(List.map (fun t:Int×Bool=>frame (binary w (FinalPrimeReduce.intResidue p t.1)))
    (List.ofFn (fun j=>(factor*g.weight j,bits j)))).flatten
  simp only [List.map_ofFn]
  rfl
end
end PCJ45bee56da9f34d5a_NativeScaleMeaning

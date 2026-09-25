import Proof.Rows.PowerEquation

/-! The physically updated factor represents the exact canonical power,
including the first factor one and the p=1 residue case. -/
set_option autoImplicit false
set_option warningAsError true
namespace PCJ45bee56da9f34d5a_PowerMeaning
open NearCubicWires NearCubicWires.RepairOrdinary NearCubicWires.RepairRepresentation
open NearCubicWires.RepairSource.CloseoutFinal NearCubicWires.SupplierPipeline
open SignedSortKey
noncomputable section

def factor (B p : Nat) : Nat→Nat
  | 0=>1
  | j+1=>(factor B p j*B)%p

theorem factor_cast (B p j : Nat) : (factor B p j : ZMod p)=(B : ZMod p)^j := by
  induction j with
  | zero=>simp [factor]
  | succ j ih=>simp only [factor,ZMod.natCast_mod,Nat.cast_mul,ih,pow_succ]

theorem block_exact (B p w j : Nat) {n : Nat} (g : ExactThresholdGate n) (bits : Fin n→Bool) (hp : 0 < p) :
    PCJ45bee56da9f34d5a_NativeScaleEquation.result (factor B p j) p w
      ({weights:=g.weight,target:=g.target} : LabelledEquation (Fin n)) =
      (PCJ45bee56da9f34d5a_ExpandedThresholdStream.block g bits ((B : Int)^j)).flatMap
        (fun t=>frame (binary w (FinalPrimeReduce.intResidue p t.1))) := by
  apply PCJ45bee56da9f34d5a_NativeScaleMeaning.block_exact
  · exact hp
  · simpa only [Int.cast_pow,Int.cast_natCast] using factor_cast B p j
end
end PCJ45bee56da9f34d5a_PowerMeaning

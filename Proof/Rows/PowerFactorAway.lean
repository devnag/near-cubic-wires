import Proof.Rows.PowerFactor

/-! The coefficient mapper's actual bank with a retained full-width base and
one isolated product destination. The growing coefficient output stays at64. -/
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 700000
set_option maxRecDepth 120000
namespace PCJ45bee56da9f34d5a_PowerBank
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairOrdinary.RecoveryRootRound
open NearCubicWires.RepairRepresentation NearCubicWires.RepairSource.VerifierDecoding
open SignedSortKey
noncomputable section

attribute [local irreducible] PCJ45bee56da9f34d5a_ResidueScaleCell.palette

theorem cold_factor_away (a a' p w U : Nat) (out : List Bool) (i : Fin 65) (hi : i≠28) :
    PCJ45bee56da9f34d5a_ResidueScaleCell.cold (PCJ45bee56da9f34d5a_ResidueScaleCell.palette a 0 p w) U out i =
      PCJ45bee56da9f34d5a_ResidueScaleCell.cold (PCJ45bee56da9f34d5a_ResidueScaleCell.palette a' 0 p w) U out i := by
  revert hi
  refine Fin.addCases (m:=64) (n:=1) (fun j hj=>?_) (fun j _=>?_) i
  · revert hj
    refine Fin.addCases (m:=63) (n:=1) (fun k hk=>?_) (fun k _=>?_) j
    · revert hk
      refine Fin.addCases (m:=31) (n:=32) (fun k hk=>?_) (fun k _=>?_) k
      · simp only [PCJ45bee56da9f34d5a_ResidueScaleCell.cold,
          NearCubicWires.ExtIncidence.NativeFanout.reusableInput,Fin.addCases_left]
        exact palette_factor_away a a' p w k (by intro h;subst k;exact hk rfl)
      · simp only [PCJ45bee56da9f34d5a_ResidueScaleCell.cold,
          NearCubicWires.ExtIncidence.NativeFanout.reusableInput,Fin.addCases_left,Fin.addCases_right]
    · simp only [PCJ45bee56da9f34d5a_ResidueScaleCell.cold,
        NearCubicWires.ExtIncidence.NativeFanout.reusableInput,Fin.addCases_left,Fin.addCases_right]
  · simp only [PCJ45bee56da9f34d5a_ResidueScaleCell.cold,Fin.addCases_right]

theorem native_factor_away (a a' p w F U : Nat) (source out coefficient : List Bool)
    (i : Fin 91) (hi : i≠28) :
    PCJ45bee56da9f34d5a_NativeScaleInput.bank a p w F U source out coefficient i =
      PCJ45bee56da9f34d5a_NativeScaleInput.bank a' p w F U source out coefficient i := by
  revert hi
  refine Fin.addCases (m:=65) (n:=26) (fun j hj=>?_) (fun j _=>?_) i
  · simp only [PCJ45bee56da9f34d5a_NativeScaleInput.bank,Fin.addCases_left,
      PCJ45bee56da9f34d5a_NativeScaleInput.main]
    by_cases h0:j=0
    · simp only [h0,if_true]
    · simp only [if_neg h0]
      exact cold_factor_away a a' p w U out j (by intro h;subst j;exact hj rfl)
  · simp only [PCJ45bee56da9f34d5a_NativeScaleInput.bank,Fin.addCases_right]

theorem factor_away (a a' B p w F U q : Nat) (source out coefficient temp : List Bool)
    (i : Fin 94) (hi : i≠28) :
    bank a B p w F U q source out coefficient temp i=bank a' B p w F U q source out coefficient temp i := by
  revert hi
  refine Fin.addCases (m:=91) (n:=3) (fun j hj=>?_) (fun j _=>?_) i
  · simp only [bank,Fin.addCases_left,base]
    exact congrArg (ZeroPadding.pad (factorCap U j))
      (native_factor_away a a' p w F U source out coefficient j (by intro h;subst j;exact hj rfl))
  · simp only [bank,Fin.addCases_right]
end
end PCJ45bee56da9f34d5a_PowerBank

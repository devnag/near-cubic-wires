import Proof.Packets.PacketsXWindowCoordinateSubstitute
import Proof.Packets.CycleSubstitutionReusableCost

/-! Reentry state and concrete cost of the whole-coordinate substitution. -/
set_option autoImplicit false
set_option maxHeartbeats 500000
set_option maxRecDepth 120000
set_option warningAsError true
namespace PCJ9eff70d512234a4c_Fixed.Materializer.WindowProvider
open NearCubicWires NearCubicWires.RepairOrdinary NearCubicWires.CanonicalFourfoldRowProgram
open NearCubicWires.ExtDecompositionBatch Theorem25Completion

theorem operands_core (C R : Nat) (left right newLeft newRight : List (List Bool)) (A : Fin 256→ List Bool)
    (ha : ∀i : Fin 34,A (i.castAdd 222)=ReusableArithmetic.state C R left right i) :
    ∀i : Fin 34,operands R newLeft newRight A (i.castAdd 222)=ReusableArithmetic.state C R newLeft newRight i := by
  intro i
  by_cases h25:i=25
  · subst i;rfl
  by_cases h26:i=26
  · subst i;rfl
  by_cases h27:i=27
  · subst i;rfl
  by_cases h28:i=28
  · subst i;rfl
  have ne (j : Fin 34) (hne : i≠j) : i.castAdd 222≠j.castAdd 222:=by
    intro he;apply hne;exact Fin.ext (congrArg (fun k : Fin 256=>k.val) he)
  have n25 : i.castAdd 222≠(25 : Fin 256):=ne 25 h25
  have n26 : i.castAdd 222≠(26 : Fin 256):=ne 26 h26
  have n27 : i.castAdd 222≠(27 : Fin 256):=ne 27 h27
  have n28 : i.castAdd 222≠(28 : Fin 256):=ne 28 h28
  simp only [operands,Function.update_of_ne n25,Function.update_of_ne n26,
    Function.update_of_ne n27,Function.update_of_ne n28,ha]
  exact (state_outside C R left right newLeft newRight i h25 h26 h27 h28).symm

theorem coordinate_output_work (R : Nat) (left right : List (List Bool)) (A : Fin 256→ List Bool) :
    ∀i,Workspace.selected i→ operands R left right (Workspace.cleared R A) i=List.replicate R false := by
  intro i hi
  have hlo : 96≤ i.val:=by unfold Workspace.selected at hi;omega
  have hn (j : Fin 256) (hj:j.val<96) : i≠j:=by intro he;subst i;omega
  simp only [operands,Function.update_of_ne (hn 25 (by decide)),Function.update_of_ne (hn 26 (by decide)),
    Function.update_of_ne (hn 27 (by decide)),Function.update_of_ne (hn 28 (by decide)),Workspace.cleared,if_pos hi]

theorem coordinate_output_retained (R : Nat) (left right : List (List Bool)) (A : Fin 256→ List Bool)
    (i : Fin 256) (hi : 34≤ i.val) (hn : ¬Workspace.selected i) :
    operands R left right (Workspace.cleared R A) i=A i := by
  have ne (j : Fin 256) (hj:j.val<34) : i≠j:=by intro he;subst i;omega
  simp only [operands,Function.update_of_ne (ne 25 (by decide)),Function.update_of_ne (ne 26 (by decide)),
    Function.update_of_ne (ne 27 (by decide)),Function.update_of_ne (ne 28 (by decide)),Workspace.cleared,if_neg hn]

theorem coordinate_substitute_budget (C w count : Nat) (hc : count≤2^w) :
    coordinateSubstituteBudget C (CycleBounds.commonReserve C w) count≤
      4398046511104*(C+1)^9*2^(17*w) := by
  let T:=(C+1)^9*2^(17*w)
  have hT : 1≤ T:=Nat.mul_le_mul (Nat.one_le_pow _ _ (by omega)) (Nat.one_le_two_pow)
  have hR : CycleBounds.commonReserve C w≤65536*T := by
    have h:=Nat.mul_le_mul (Nat.pow_le_pow_right (by omega : 1≤ C+1) (by decide : 4≤9))
      (Nat.pow_le_pow_right (by decide : 1≤2) (show 8*w≤17*w by omega))
    unfold CycleBounds.commonReserve
    dsimp only [T]
    nlinarith only [h]
  have sub:=CycleBounds.substitution_reusable_polynomial C w count hc
  have sub' : SubstitutionCall.totalBudget C (CycleBounds.commonReserve C w) count≤2199023255552*T := by
    simpa only [CycleBounds.commonReserve,CycleCommonReserve.reserve,T,Nat.mul_assoc] using sub
  unfold coordinateSubstituteBudget
  change _≤4398046511104*(C+1)^9*2^(17*w)
  have target : 4398046511104*(C+1)^9*2^(17*w)=4398046511104*T:=by simp only [T,Nat.mul_assoc]
  rw [target]
  omega

end PCJ9eff70d512234a4c_Fixed.Materializer.WindowProvider

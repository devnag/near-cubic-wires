

import Proof.Packets.PacketsXWalkLiteralMastersFanout

/-! The complete fifteen-master producer has a linear paid cost in R. -/
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option warningAsError true
namespace Theorem25Completion.WalkLiteralMasters
open NearCubicWires.RepairOrdinary NearCubicWires.RepairSource.ProjectionNormalization
open Completion

theorem budget_eq (C R root rank depth M : Nat) (mask : List Bool) :
    budget C R root rank depth M mask=30*C+4*R+2*rank+2*depth+2*M+221 := by
  simp only [budget,budget9,budget8,budget7,budget6,budget5,budget4,budget3,budget2,budget1,
    UnaryAffine.budget,DimensionPower.cost,WilliamsUnaryProduct.budget,pow_zero,Nat.mul_one]
  ring

theorem budget_le (C R root rank depth M : Nat) (mask : List Bool)
    (h : Bounds C R root rank depth M mask) : budget C R root rank depth M mask≤64*R := by
  rw [budget_eq]
  have hc:=h.arena
  have hcode:=h.code
  have hr:=h.rank
  have hd:=h.depth
  have hm:=h.population
  omega

end Theorem25Completion.WalkLiteralMasters

import Proof.Packets.VectorAccumulator

/-! Symmetric resident-accumulator transaction for foldr order: the current
left product is added to the old stored accumulator on the right. -/
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 120000
set_option warningAsError true
namespace PCJ9eff70d512234a4c_Fixed.Materializer.VectorAccumulator
open NearCubicWires NearCubicWires.LocalBitMultitape
open NearCubicWires.RepairOrdinary NearCubicWires.ExtDecompositionBatch
open NearCubicWires.RepairSource.VerifierDecoding
noncomputable section

def loadRight := Composition.machine (PhysicalCopyInto.machine (31 : Fin 36) 34 26)
  (PhysicalCopyInto.machine (31 : Fin 36) 35 27)
def saveRight := Composition.machine (PhysicalCopyInto.machine (31 : Fin 36) 26 34)
  (PhysicalCopyInto.machine (31 : Fin 36) 27 35)

theorem load_right_run (B R : Nat) (left right stored : List (List Bool))
    (hl : Fits R right) (hs : Fits R stored) :
    Step loadRight (copyBudget R) heads (tapes B R left right stored)
      heads (tapes B R left stored stored) := by
  let a:=tapes B R left right stored
  have first:=PhysicalCopyInto.run R (31 : Fin 36) 34 26 (by decide) (by decide) (by decide)
    heads a rfl rfl rfl rfl (flat_length R stored hs) (flat_length R right hl)
  have second:=PhysicalCopyInto.run R (31 : Fin 36) 35 27 (by decide) (by decide) (by decide)
    heads (Function.update a 26 (a 34)) rfl rfl rfl rfl
    (count_length R stored hs) (count_length R right hl)
  have h:=first.seq second
  have out : Function.update (Function.update a 26 (a 34)) 27
      ((Function.update a 26 (a 34)) 35)=tapes B R left stored stored := by
    apply update_pair_eq a (tapes B R left stored stored) 26 27 (a 34) ((Function.update a 26 (a 34)) 35) (by decide) rfl rfl
    intro i h26 h27
    exact tapes_right_outside B R left right stored stored i h26 h27
  have fuel : (2*R+2)+1+(2*R+2)=copyBudget R := by unfold copyBudget;omega
  rw [fuel] at h
  exact h.congr rfl out

theorem save_right_run (B R : Nat) (left right stored : List (List Bool))
    (hl : Fits R right) (hs : Fits R stored) :
    Step saveRight (copyBudget R) heads (tapes B R left right stored)
      heads (tapes B R left right right) := by
  let a:=tapes B R left right stored
  have first:=PhysicalCopyInto.run R (31 : Fin 36) 26 34 (by decide) (by decide) (by decide)
    heads a rfl rfl rfl rfl (flat_length R right hl) (flat_length R stored hs)
  have second:=PhysicalCopyInto.run R (31 : Fin 36) 27 35 (by decide) (by decide) (by decide)
    heads (Function.update a 34 (a 26)) rfl rfl rfl rfl
    (count_length R right hl) (count_length R stored hs)
  have h:=first.seq second
  have out : Function.update (Function.update a 34 (a 26)) 35
      ((Function.update a 34 (a 26)) 27)=tapes B R left right right := by
    apply update_pair_eq a (tapes B R left right right) 34 35 (a 26) ((Function.update a 34 (a 26)) 27) (by decide) rfl rfl
    intro i h34 h35
    exact tapes_saved_outside B R left right stored right i h34 h35
  have fuel : (2*R+2)+1+(2*R+2)=copyBudget R := by unfold copyBudget;omega
  rw [fuel] at h
  exact h.congr rfl out

def addRight := TapeEmbedding.machine 2 (ReusableArithmetic.machine NormalizedAddition.machine)
def machineRight := Composition.machine loadRight (Composition.machine addRight saveRight)

theorem run_right (B R : Nat) (product oldRight stored : List (List Bool))
    (hr : Fits R oldRight) (hsfit : Fits R stored)
    (hp : ∀ bits∈product,bits.length=B) (hs : ∀ bits∈stored,bits.length=B)
    (ha : ∀ i,(ReusableArithmetic.data B product stored i).length≤R)
    (hcap : NormalizedAddition.budget B product stored+3≤R) :
    Step machineRight (budget B R product stored) heads (tapes B R product oldRight stored)
      heads (tapes B R product (answer product stored) (answer product stored)) := by
  have first:=load_right_run B R product oldRight stored hr hsfit
  have second:=(ReusableArithmetic.add_run B R product stored hp hs ha hcap).embed
    (fun _ : Fin 2=>0)
    (![ZeroPadding.pad R stored.flatten,ZeroPadding.pad R (CompareMachine.word stored.length)] : Fin 2→List Bool)
  have third:=save_right_run B R product (answer product stored) stored
    (answer_fits B R product stored hp hs ha hcap) hsfit
  exact first.seq (second.seq third)

end
end PCJ9eff70d512234a4c_Fixed.Materializer.VectorAccumulator

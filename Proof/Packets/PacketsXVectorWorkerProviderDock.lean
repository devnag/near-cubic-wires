import Proof.Packets.PacketsXVectorWorkerData

/-! Focus the concrete256-port provider into the full worker while preserving
both vector banks, counters, saved accumulator, and all32 numeric work tapes. -/
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option maxRecDepth 120000
set_option warningAsError true
namespace PCJ9eff70d512234a4c_Fixed.Materializer.VectorBottomUp
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch
noncomputable section

def providerH : Fin 256→Nat:=Fin.addCases (m:=34) (n:=222) (motive:=fun _=>Nat) ReusableArithmetic.heads (fun _=>0)
def providerA (C R : Nat) (left right : List (List Bool)) (fields : Fin 222→List Bool) : Fin 256→List Bool :=
  Fin.addCases (m:=34) (n:=222) (motive:=fun _=>List Bool) (ReusableArithmetic.state C R left right) fields

theorem provider_reconstruct (C R : Nat) (left right : List (List Bool)) (T : Fin 256→List Bool)
    (ht : ∀j : Fin 34,T (j.castAdd 222)=ReusableArithmetic.state C R left right j) :
    T=providerA C R left right (fun j=>T (j.natAdd 34)) := by
  funext i
  refine Fin.addCases (m:=34) (n:=222) (fun j=>?_) (fun j=>?_) i
  · simp only [providerA,Fin.addCases_left];exact ht j
  · simp only [providerA,Fin.addCases_right]

theorem provider_heads (i : Fin 256) : providerH i=H (fun _=>0) (providerSlots i) := by
  change providerH i=(Fin.addCases (m:=264) (n:=32) (motive:=fun _=>Nat)
    (VectorController.H (fun _=>0)) (fun _=>0)) ((i.castAdd 8).castAdd 32)
  rw [Fin.addCases_left]
  change providerH i=(Fin.addCases (m:=256) (n:=8) (motive:=fun _=>Nat) providerH VectorController.extraHeads) (i.castAdd 8)
  rw [Fin.addCases_left]

theorem provider_tapes (C R ci pi li : Nat) (left right acc : List (List Bool)) (previous next : List Bool)
    (fields : Fin 222→List Bool) (extra : Fin 32→List Bool) (i : Fin 256) :
    providerA C R left right fields i=A C R ci pi li left right acc previous next fields extra (providerSlots i) := by
  change providerA C R left right fields i=(Fin.addCases (m:=264) (n:=32) (motive:=fun _=>List Bool)
    (VectorController.A C R ci pi li left right acc previous next fields) extra) ((i.castAdd 8).castAdd 32)
  rw [Fin.addCases_left]
  change providerA C R left right fields i=(Fin.addCases (m:=256) (n:=8) (motive:=fun _=>List Bool)
    (providerA C R left right fields) (VectorController.extraTapes R ci pi li acc previous next)) (i.castAdd 8)
  rw [Fin.addCases_left]

theorem provider_dock {s fuel : Nat} {p : Machine 256 s}
    (C R ci pi li : Nat) (left right left' right' acc : List (List Bool)) (previous next : List Bool)
    (fields : Fin 222→List Bool) (extra : Fin 32→List Bool) (T : Fin 256→List Bool)
    (h : Step p fuel providerH (providerA C R left right fields) providerH T)
    (ht : ∀j : Fin 34,T (j.castAdd 222)=ReusableArithmetic.state C R left' right' j) :
    Step (RecoveryFocus.machine providerSlots p) fuel (H (fun _=>0))
      (A C R ci pi li left right acc previous next fields extra) (H (fun _=>0))
      (A C R ci pi li left' right' acc previous next (fun j=>T (j.natAdd 34)) extra) := by
  have small:=h.congr rfl (provider_reconstruct C R left' right' T ht)
  apply PhysicalFocusBoundary.focus small providerSlots (by intro i j he;exact Fin.ext (congrArg (fun z : Fin 296=>z.val) he))
    (H (fun _=>0)) (H (fun _=>0)) _ _
  · exact provider_heads
  · exact provider_tapes C R ci pi li left right acc previous next fields extra
  · exact provider_heads
  · exact provider_tapes C R ci pi li left' right' acc previous next _ extra
  · intro i away
    refine ⟨rfl,?_⟩
    revert away
    refine Fin.addCases (m:=264) (n:=32) (fun j=>?_) (fun j=>?_) i
    · refine Fin.addCases (m:=256) (n:=8) (fun k=>?_) (fun k=>?_) j
      · intro away;exact False.elim (away k rfl)
      · intro _;simp only [A,VectorController.A,Fin.addCases_left,Fin.addCases_right]
    · intro _;simp only [A,Fin.addCases_right]

end
end PCJ9eff70d512234a4c_Fixed.Materializer.VectorBottomUp

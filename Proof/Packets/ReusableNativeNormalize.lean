import Proof.Packets.ReusableNativeCleanup
import Proof.Packets.NativeNormalizedRetained

/-! Reusable executed native normalization. After actual parsing and parity
normalization the packet is copied to its ready right operand, while the
native source and all private work are physically cleared to retained R-cell
backing. Only the two actual width masters survive beside the result. -/
set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unusedSimpArgs false
namespace PCJ9eff70d512234a4c_Fixed.Materializer.ReusableNative
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairSource.VerifierDecoding

def input (C R : Nat) (P : List (List Nat)) := bank R (padded R (NativeNormalized.A C P []))
def readyData (C R : Nat) (raw : List (List Bool)) (i : Fin 32) : List Bool :=
  if i=13 then ZeroPadding.pad R (UnaryTemplate.tape (2*C+3))
  else if i=24 then ZeroPadding.pad R (UnaryTemplate.tape C)
  else if i=26 then ZeroPadding.pad R raw.flatten
  else if i=27 then ZeroPadding.pad R (CompareMachine.word raw.length)
  else List.replicate R false
def ready (C R : Nat) (raw : List (List Bool)) := bank R (readyData C R raw)
noncomputable def normalize := machine NativeNormalized.machine

theorem local_heads : localHeads=NativeNormalized.H 0 0 1 := by
  funext i;fin_cases i <;> rfl

theorem normalize_run (C R : Nat) (P : List (List Nat))
    (hp : ∀m∈P,∀code∈m,code<C)
    (hdata : ∀i,(NativeNormalized.A C P [] i).length≤R)
    (hfuel : NativeNormalized.budget C P+3≤R) :
    Step normalize (budget (NativeNormalized.budget C P) R) heads (input C R P)
      heads (ready C R (NormalizerOrder.ordered (NativeNormalized.masks C P))) := by
  obtain ⟨r,hr,rs,r20,_,r21,_,r13,r24,_,_⟩ := NativeNormalized.run_retained C P hp
  have raw : Step NativeNormalized.machine (NativeNormalized.budget C P)
      (NativeNormalized.H 0 0 1) (NativeNormalized.A C P []) r.final.heads r.final.tapes :=
    ⟨r,hr,rfl,rfl,rs⟩
  have raw' := raw.congr_in local_heads.symm rfl
  have actual := run raw' hdata hfuel
  apply actual.congr rfl
  funext i
  refine Fin.addCases (m:=32) (n:=4) (fun j=>?_) (fun j=>by simp [bank,ready,Fin.addCases]) i
  simp only [ready,bank,Fin.addCases_left]
  fin_cases j <;> simp [result,cleared,replaced,keep,padded,readyData,Function.update,r20,r21,r13,r24]

end PCJ9eff70d512234a4c_Fixed.Materializer.ReusableNative

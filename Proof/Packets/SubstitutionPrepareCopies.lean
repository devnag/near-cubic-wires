import Proof.Packets.SubstitutionOuterStep
import Proof.Packets.PhysicalCopyPair
import Proof.Packets.PhysicalOneCount

/-! Physical preparation of source, both count drivers, and product one from
the current resident right operand. All destination backing was allocated by
SubstitutionScratch.run, and all operations have ordinary paid receipts. -/
set_option autoImplicit false
set_option maxHeartbeats 350000
set_option maxRecDepth 120000
set_option warningAsError true
namespace PCJ9eff70d512234a4c_Fixed.Materializer.SubstitutionCall
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairSource.VerifierDecoding
abbrev Packet := List (List Bool)

def heads : Fin 44→Nat := Fin.addCases (m:=34) (n:=10) ReusableArithmetic.heads (fun _=>0)
def resident (C R : Nat) (left right : Packet) (atoms : List Bool) : Fin 44→List Bool :=
  Fin.addCases (m:=34) (n:=10) (ReusableArithmetic.state C R left right)
    (fun i=>if i=0 then atoms else List.replicate R false)

def inputCopied (A : Fin 44→List Bool) := Function.update (Function.update A 37 (A 26)) 43 (A 27)
def widthCopied (A : Fin 44→List Bool) := Function.update (Function.update A 35 (A 24)) 38 (A 24)
def oneCount (R : Nat) (A : Fin 44→List Bool) :=
  Function.update A 42 (ZeroPadding.pad R (CompareMachine.word 1))
def productOne (A : Fin 44→List Bool) := Function.update (Function.update A 26 (A 41)) 27 (A 42)
def prepared (C R : Nat) (left right : Packet) (atoms : List Bool) :=
  productOne (oneCount R (widthCopied (inputCopied (resident C R left right atoms))))

noncomputable def copyInput := PhysicalCopyPair.machine (31 : Fin 44) 26 37 27 43
noncomputable def copyWidth := PhysicalCopyPair.machine (31 : Fin 44) 24 35 24 38
noncomputable def makeOne := PhysicalOneCount.into (42 : Fin 44)
noncomputable def resetProduct := PhysicalCopyPair.machine (31 : Fin 44) 41 26 42 27
noncomputable def machine := Composition.machine copyInput
  (Composition.machine copyWidth (Composition.machine makeOne resetProduct))
def budget (R : Nat) := 12*R+22

theorem input_run (C R : Nat) (left right : Packet) (atoms : List Bool) (hr : VectorAccumulator.Fits R right) :
    Step copyInput (4*R+5) heads (resident C R left right atoms) heads
      (inputCopied (resident C R left right atoms)) := by
  apply PhysicalCopyPair.run R (31 : Fin 44) 26 37 27 43 heads (resident C R left right atoms)
    (by decide) (by decide) (by decide) (by decide) rfl rfl rfl rfl rfl rfl
  · exact VectorAccumulator.flat_length R right hr
  · change (List.replicate R false).length=R;simp
  · exact VectorAccumulator.count_length R right hr
  · change (List.replicate R false).length=R;simp

theorem width_run (C R : Nat) (left right : Packet) (atoms : List Bool) (hC : C+2≤R) :
    Step copyWidth (4*R+5) heads (inputCopied (resident C R left right atoms)) heads
      (widthCopied (inputCopied (resident C R left right atoms))) := by
  have hc : (ZeroPadding.pad R (UnaryTemplate.tape C)).length=R := by
    rw [ZeroPadding.pad_length,Nat.max_eq_left (by simpa only [UnaryTemplate.tape_length] using hC)]
  apply PhysicalCopyPair.run R (31 : Fin 44) 24 35 24 38 heads (inputCopied (resident C R left right atoms))
    (by decide) (by decide) (by decide) (by decide) rfl rfl rfl rfl rfl rfl
  · exact hc
  · change (List.replicate R false).length=R;simp
  · exact hc
  · change (List.replicate R false).length=R;simp

theorem one_run (C R : Nat) (left right : Packet) (atoms : List Bool) :
    Step makeOne 4 heads (widthCopied (inputCopied (resident C R left right atoms))) heads
      (oneCount R (widthCopied (inputCopied (resident C R left right atoms)))) :=
  PhysicalOneCount.into_run R (42 : Fin 44) heads _ rfl rfl

theorem reset_run (C R : Nat) (left right : Packet) (atoms : List Bool)
    (hC : C+2≤R) (hr : VectorAccumulator.Fits R right) :
    Step resetProduct (4*R+5) heads
      (oneCount R (widthCopied (inputCopied (resident C R left right atoms)))) heads (prepared C R left right atoms) := by
  apply PhysicalCopyPair.run R (31 : Fin 44) 41 26 42 27 heads
    (oneCount R (widthCopied (inputCopied (resident C R left right atoms))))
    (by decide) (by decide) (by decide) (by decide) rfl rfl rfl rfl rfl rfl
  · change (List.replicate R false).length=R;simp
  · exact VectorAccumulator.flat_length R right hr
  · change (ZeroPadding.pad R (CompareMachine.word 1)).length=R
    rw [ZeroPadding.pad_length,Nat.max_eq_left (by simp [CompareMachine.word];omega)]
  · exact VectorAccumulator.count_length R right hr

theorem run (C R : Nat) (left right : Packet) (atoms : List Bool)
    (hC : C+2≤R) (hr : VectorAccumulator.Fits R right) :
    Step machine (budget R) heads (resident C R left right atoms) heads (prepared C R left right atoms) := by
  have h:=(input_run C R left right atoms hr).seq
    ((width_run C R left right atoms hC).seq ((one_run C R left right atoms).seq (reset_run C R left right atoms hC hr)))
  have hf : (4*R+5)+1+((4*R+5)+1+(4+1+(4*R+5)))=budget R := by unfold budget;omega
  rw [hf] at h
  exact h

end PCJ9eff70d512234a4c_Fixed.Materializer.SubstitutionCall

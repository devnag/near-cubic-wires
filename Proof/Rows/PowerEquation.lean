import Proof.Rows.PowerUpdate
import Proof.Rows.NativeScaleMeaning

/-! Consume the actual coefficient mapper and power update on one shared bank.
Native fields advance once, exact framed coefficients are appended, and the
next block receives its physically computed factor. -/
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 700000
set_option maxRecDepth 120000
namespace PCJ45bee56da9f34d5a_PowerEquation
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairOrdinary.RecoveryRootRound
open NearCubicWires.RepairRepresentation NearCubicWires.RepairSource.VerifierDecoding
open NearCubicWires.RepairSource.CloseoutFinal
open SignedSortKey PCJ45bee56da9f34d5a_PowerBank
noncomputable section
attribute [local irreducible] PCJ45bee56da9f34d5a_NativeScaleEquation.machine

def emit := TapeEmbedding.machine 2 PCJ45bee56da9f34d5a_NativeScaleEquation.machine
def machine := Composition.machine emit PCJ45bee56da9f34d5a_PowerUpdate.machine

theorem emit_run (pre tail out : List Bool) (a B p w F U : Nat) {n : Nat}
    (eq : SupplierPipeline.LabelledEquation (Fin n)) (hp : 0 < p) (hpw : 2*p ≤ 2^w) (ha : a < 2^w)
    (hweights : ∀i,C10NativeResidueCallback.coreBudget false (eq.weights i) w+1 ≤ F)
    (htarget : C10NativeResidueCallback.coreBudget true eq.target w+1 ≤ F)
    (hU : 1024*(w+1)^2+2 ≤ U) :
    Step emit (PCJ45bee56da9f34d5a_NativeScaleEquation.budget n F w U eq.target)
      (heads pre.length out.length 0)
      (bank a B p w F U n (pre++PCJ45bee56da9f34d5a_NativeScaleEquation.source eq++tail) out (List.replicate U false) [])
      (heads (pre.length+(PCJ45bee56da9f34d5a_NativeScaleEquation.source eq).length)
        (out.length+(n+1)*(2*w+1)) 0)
      (bank a B p w F U n (pre++PCJ45bee56da9f34d5a_NativeScaleEquation.source eq++tail)
        (out++PCJ45bee56da9f34d5a_NativeScaleEquation.result a p w eq) (List.replicate U false) []) := by
  have h := ((PCJ45bee56da9f34d5a_NativeScaleEquation.run pre tail out a p w F U eq hp hpw ha hweights htarget hU).pad
    (fun i : Fin 92=>if i=28 then U else 0)).embed (fun _ : Fin 2=>0)
      (![ZeroPadding.pad U (frame (binary w B)),List.replicate U false] : Fin 2→List Bool)
  refine (h.congr_in ?_ ?_).congr ?_ ?_
  · funext i;fin_cases i <;>rfl
  · funext i;fin_cases i <;>first |rfl |exact ZeroPadding.pad_zero _
  · funext i;fin_cases i <;>rfl
  · funext i;fin_cases i <;>first |rfl |exact ZeroPadding.pad_zero _

theorem result_length (a p w : Nat) {n : Nat} (eq : SupplierPipeline.LabelledEquation (Fin n)) :
    (PCJ45bee56da9f34d5a_NativeScaleEquation.result a p w eq).length=(n+1)*(2*w+1) := by
  unfold PCJ45bee56da9f34d5a_NativeScaleEquation.result
  have hc := FinalPrimeModular.blocks_length
    (PCJ45bee56da9f34d5a_NativeScaleWeights.words a p w (PCJ45bee56da9f34d5a_NativeScaleEquation.weights eq))
    w (fun _=>binary_length _ _) 0 n
  rw [List.length_append,hc]
  simp [frame_length,binary_length,Nat.add_mul]

theorem run (pre tail out : List Bool) (a B p w F U : Nat) {n : Nat}
    (eq : SupplierPipeline.LabelledEquation (Fin n)) (hp : 0 < p) (hpw : 2*p ≤ 2^w)
    (ha : a < 2^w) (hB : B < 2^w)
    (hweights : ∀i,C10NativeResidueCallback.coreBudget false (eq.weights i) w+1 ≤ F)
    (htarget : C10NativeResidueCallback.coreBudget true eq.target w+1 ≤ F)
    (hU : 1024*(w+1)^2+2 ≤ U) :
    Step machine (PCJ45bee56da9f34d5a_NativeScaleEquation.budget n F w U eq.target+1+
      (1024*(w+1)^2+10*U+18*w+45)) (heads pre.length out.length 0)
      (bank a B p w F U n (pre++PCJ45bee56da9f34d5a_NativeScaleEquation.source eq++tail) out (List.replicate U false) [])
      (heads (pre.length+(PCJ45bee56da9f34d5a_NativeScaleEquation.source eq).length)
        (out.length+(n+1)*(2*w+1)) 0)
      (bank ((a*B)%p) B p w F U n (pre++PCJ45bee56da9f34d5a_NativeScaleEquation.source eq++tail)
        (out++PCJ45bee56da9f34d5a_NativeScaleEquation.result a p w eq) (List.replicate U false) []) := by
  have first := emit_run pre tail out a B p w F U eq hp hpw ha hweights htarget hU
  have next := PCJ45bee56da9f34d5a_PowerUpdate.run a B p w F U n
    (pre.length+(PCJ45bee56da9f34d5a_NativeScaleEquation.source eq).length)
    (pre++PCJ45bee56da9f34d5a_NativeScaleEquation.source eq++tail)
    (out++PCJ45bee56da9f34d5a_NativeScaleEquation.result a p w eq) hp hpw ha hB hU
  simp only [List.length_append,result_length] at next
  exact first.seq next
end
end PCJ45bee56da9f34d5a_PowerEquation

import Proof.Rows.ResidueScaleBounds
import Proof.Rows.FinalNativeResidueCallback

/-! The native signed field is physically reduced into the product emitter's
right-operand master. The source cursor advances and the native reader returns
its exact next canonical bank. The emitted row prefix stays outside both banks. -/
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 120000
set_option warningAsError true
namespace PCJ45bee56da9f34d5a_NativeScaleInput
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairOrdinary.RecoveryRootRound
open NearCubicWires.RepairSource.CloseoutFinal NearCubicWires.RepairSource.VerifierDecoding
open NearCubicWires.RepairRepresentation
open SignedSortKey
noncomputable section

def main (a p w U : Nat) (out coefficient : List Bool) (i : Fin 65):=
  if i=0 then coefficient else PCJ45bee56da9f34d5a_ResidueScaleCell.cold
    (PCJ45bee56da9f34d5a_ResidueScaleCell.palette a 0 p w) U out i
def extraIndex (i : Fin 26) : Fin 27:=if h:i.val<22 then ⟨i.val,by omega⟩ else ⟨i.val+1,by omega⟩
def extras (F w p : Nat) (source : List Bool) (i : Fin 26):=
  C10NativeResidueCallback.bank F w p source [] (extraIndex i)
def bank (a p w F U : Nat) (source out coefficient : List Bool) : Fin 91→List Bool:=
  Fin.addCases (m:=65) (n:=26) (motive:=fun _=>List Bool) (main a p w U out coefficient) (extras F w p source)
def heads (pos len coefficient : Nat) (i : Fin 91):=
  if i=0 then coefficient else if i=64 then len else if i=65 then pos else 0
def nativeSlots (i : Fin 27) : Fin 91:=if h:i.val=22 then 0 else if h':i.val<22 then ⟨65+i.val,by omega⟩ else ⟨64+i.val,by omega⟩
theorem native_inj : Function.Injective nativeSlots:=by decide
def read (negate : Bool):=RecoveryFocus.machine nativeSlots (C10NativeResidueCallback.machine negate)

theorem read_run (negate : Bool) (pre tail out : List Bool) (z : Int) (a p w F U : Nat)
    (hp : 0<p) (hpw : 2*p≤2^w) (hF : C10NativeResidueCallback.coreBudget negate z w+1≤F) :
    Step (read negate) (2*C10NativeResidueCallback.coreBudget negate z w+2*F+16*w+27)
      (heads pre.length out.length 0) (bank a p w F U (pre++intWord z++tail) out (List.replicate U false))
      (heads (pre.length+(intWord z).length) out.length (2*w+1))
      (bank a p w F U (pre++intWord z++tail) out
        (ZeroPadding.pad U (frame (binary w (FinalPrimeReduce.intResidue p (if negate then -z else z)))))):=by
  let H:=heads pre.length out.length 0
  let A:=bank a p w F U (pre++intWord z++tail) out (List.replicate U false)
  have base:=(C10NativeResidueCallback.run negate pre tail [] z p w F hp hpw hF).pad
    (fun i : Fin 27=>if i=22 then U else 0)
  have h:=base.dock nativeSlots native_inj H A
    (by intro i;fin_cases i <;>rfl)
    (by intro i;fin_cases i <;>first
        | exact (ZeroPadding.pad_zero _).symm
        | (change List.replicate U false=ZeroPadding.pad U ([] : List Bool);simp [ZeroPadding.pad]))
  apply h.congr
  · funext i
    by_cases hi:∃j,nativeSlots j=i
    · obtain ⟨j,rfl⟩:=hi
      rw [dockH_slot nativeSlots native_inj]
      fin_cases j <;>first | rfl | simp [C10NativeResidueReset.head,heads,nativeSlots]
    · rw [dockH_other nativeSlots _ _ _ (by simpa using hi)]
      have h0:i≠0:=fun h=>hi ⟨22,h.symm⟩
      have h65:i≠65:=fun h=>hi ⟨0,h.symm⟩
      simp [H,heads,h0,h65]
  · apply HierarchyAllocation.install_eq nativeSlots native_inj
    · intro i;fin_cases i <;>first
        | exact (ZeroPadding.pad_zero _).symm
        | rfl
    · intro i hi;fin_cases i
      all_goals first
        | rfl
        | exact False.elim (hi 22 rfl)

@[simp] theorem palette_other (a b p w : Nat) (i : Fin 31) (hi : i≠0) :
    PCJ45bee56da9f34d5a_ResidueScaleCell.palette a b p w i=
      PCJ45bee56da9f34d5a_ResidueScaleCell.palette a 0 p w i:=by
  fin_cases i <;>first | rfl | contradiction

theorem main_eq (a b p w U : Nat) (out : List Bool) :
    (fun i : Fin 65=>ZeroPadding.pad (if i=0 then U else 0)
      (PCJ45bee56da9f34d5a_ResidueScaleCell.cold (PCJ45bee56da9f34d5a_ResidueScaleCell.palette a b p w) U out i))=
      main a p w U out (ZeroPadding.pad U (frame (binary w b))):=by
  funext i;fin_cases i <;>
    simp [main,PCJ45bee56da9f34d5a_ResidueScaleCell.cold,
      NearCubicWires.ExtIncidence.NativeFanout.reusableInput,Fin.addCases,ZeroPadding.pad_zero]
  rfl

end
end PCJ45bee56da9f34d5a_NativeScaleInput

import Proof.Rows.NativeCircuitPrepare
import Proof.Rows.PowerEquation

/-! Selected-child locator and scaled coefficient mapper share source65,
arity91, and U cap/log62/63. The growing coefficient stream stays at64. -/
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 450000
set_option maxRecDepth 120000
namespace PCJ45bee56da9f34d5a_SelectedPowerBank
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairOrdinary.RecoveryRootRound
open NearCubicWires.RepairRepresentation NearCubicWires.RepairSource.VerifierDecoding
open NearCubicWires.RepairSource.CloseoutFinal
noncomputable section
attribute [local irreducible] PCJ45bee56da9f34d5a_TopChildReady.machine

def caps (U : Nat) (i : Fin 94):=if i=65 ∨ i=91 then U else 0
def core (a B p w F U n : Nat) (bits out : List Bool) (i : Fin 94):=
 ZeroPadding.pad (caps U i) (PCJ45bee56da9f34d5a_PowerBank.bank a B p w F U n bits out (List.replicate U false) [] i)
def extras (source : List Bool) (index U : Nat):Fin 5→List Bool:=
 ![source,ZeroPadding.pad U (UnaryTemplate.tape index),List.replicate U false,List.replicate U false,List.replicate U false]
def bank (a B p w F U n index : Nat) (source bits out : List Bool):Fin 99→List Bool:=
 Fin.addCases (m:=94) (n:=5) (motive:=fun _=>List Bool) (core a B p w F U n bits out) (extras source index U)
def heads (pos len : Nat):Fin 99→Nat:=
 Fin.addCases (m:=94) (n:=5) (motive:=fun _=>Nat) (PCJ45bee56da9f34d5a_PowerBank.heads pos len 0) ![0,1,0,0,0]
def slots:Fin 9→Fin 99:=![94,96,97,91,95,98,65,62,63]
def locate:=RecoveryFocus.machine slots PCJ45bee56da9f34d5a_TopChildReady.machine

theorem bits_away (a B p w F U n index : Nat) (source bits bits' out : List Bool)
 (i : Fin 99) (hi : i≠65) :bank a B p w F U n index source bits out i=bank a B p w F U n index source bits' out i :=by
 revert hi
 refine Fin.addCases (m:=94) (n:=5) (fun j hj=>?_) (fun _ _=>?_) i
 · simp only [bank,Fin.addCases_left,core]
   apply congrArg (ZeroPadding.pad (caps U j))
   revert hj
   refine Fin.addCases (m:=91) (n:=3) (fun k hk=>?_) (fun _ _=>?_) j
   · simp only [PCJ45bee56da9f34d5a_PowerBank.bank,Fin.addCases_left,PCJ45bee56da9f34d5a_PowerBank.base]
     apply congrArg (ZeroPadding.pad (PCJ45bee56da9f34d5a_PowerBank.factorCap U k))
     revert hk
     refine Fin.addCases (m:=65) (n:=26) (fun _ _=>?_) (fun l hl=>?_) k
     · simp only [PCJ45bee56da9f34d5a_NativeScaleInput.bank,Fin.addCases_left]
     · fin_cases l <;>first | exact False.elim (hl rfl) | rfl
   · simp only [PCJ45bee56da9f34d5a_PowerBank.bank,Fin.addCases_right]
 · simp only [bank,Fin.addCases_right]

theorem at65 (a B p w F U n index : Nat) (source bits out : List Bool) :
 bank a B p w F U n index source bits out 65=ZeroPadding.pad U bits :=by
 change ZeroPadding.pad U (ZeroPadding.pad 0 bits)=_
 rw [ZeroPadding.pad_zero]
theorem at62 (a B p w F U n index : Nat) (source bits out : List Bool) :
 bank a B p w F U n index source bits out 62=List.replicate U true :=by
 change ZeroPadding.pad 0 (ZeroPadding.pad 0 (List.replicate U true))=_
 rw [ZeroPadding.pad_zero,ZeroPadding.pad_zero]
theorem at63 (a B p w F U n index : Nat) (source bits out : List Bool) :
 bank a B p w F U n index source bits out 63=List.replicate (U+1) false :=by
 change ZeroPadding.pad 0 (ZeroPadding.pad 0 (List.replicate (U+1) false))=_
 rw [ZeroPadding.pad_zero,ZeroPadding.pad_zero]


theorem locate_run {n : Nat} (gs : List (ExactThresholdGate n)) (i : Fin gs.length)
 (a B p w F U : Nat) (out : List Bool)
 (hn : n+2≤U) (hp : (PCJ45bee56da9f34d5a_TopChildCursor.payload gs).length≤U)
 (hf : PCJ45bee56da9f34d5a_TopChildCursor.budget gs i.val+1≤U)
 (hg : (exactWord (gs.get i)).length+2≤U) :
 Step locate (PCJ45bee56da9f34d5a_TopChildCursor.budget gs i.val+C10ThresholdSelectedChild.budget (gs.get i) U+4*U+13)
  (heads 0 out.length) (bank a B p w F U n i.val (PCJ45bee56da9f34d5a_TopChildCursor.payload gs) [] out)
  (heads 0 out.length) (bank a B p w F U n i.val (PCJ45bee56da9f34d5a_TopChildCursor.payload gs) (exactWord (gs.get i)) out) :=by
 have hc:=PCJ45bee56da9f34d5a_NativeCircuitPrepare.count_eq n U hn
 have h:=(PCJ45bee56da9f34d5a_TopChildReady.run gs i U hp hf hg).dock slots (by decide)
  (heads 0 out.length) (bank a B p w F U n i.val (PCJ45bee56da9f34d5a_TopChildCursor.payload gs) [] out)
  (by intro j;fin_cases j <;>rfl)
  (by
   intro j;fin_cases j
   all_goals first
    | rfl
    | exact hc.symm
    | exact at65 a B p w F U n i.val _ _ out
    | exact at62 a B p w F U n i.val _ _ out
    | exact at63 a B p w F U n i.val _ _ out)
 apply h.congr
 · exact dockH_existing _ _ _ (by intro j;fin_cases j <;>rfl)
 · apply HierarchyAllocation.install_eq slots (by decide)
   · intro j;fin_cases j
     all_goals first
      | rfl
      | exact hc.symm
      | exact at65 a B p w F U n i.val _ _ out
      | exact at62 a B p w F U n i.val _ _ out
      | exact at63 a B p w F U n i.val _ _ out
   · intro j hj;exact (bits_away a B p w F U n i.val _ _ _ out j (fun he=>hj 6 he.symm)).symm
end
end PCJ45bee56da9f34d5a_SelectedPowerBank

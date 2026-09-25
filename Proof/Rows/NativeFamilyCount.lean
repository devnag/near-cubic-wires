import Proof.Rows.CircuitCountAdvance
import Proof.Rows.NativeFlags

/-! Dock the actual fifth-header count producer into the final circuit-loop
bank, preserving its advancing native source and the gate evaluator masters. -/
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 300000
set_option maxRecDepth 120000
namespace PCJ45bee56da9f34d5a_NativeFamilyCount
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairOrdinary.RecoveryRootRound
open NearCubicWires.RepairRepresentation NearCubicWires.RepairSource.VerifierDecoding
open NearCubicWires.SupplierPipeline
open PCJ45bee56da9f34d5a_UniformMinimumBounds
noncomputable section
attribute [local irreducible] PCJ45bee56da9f34d5a_CircuitCountAdvance.machine

def heads (cursor : Nat) (out : List Bool) (Q count : Nat):Fin 128→Nat:=
 Fin.addCases (m:=127) (n:=1) (motive:=fun _=>Nat)
  (PCJ45bee56da9f34d5a_CircuitFlagBank.heads 0 cursor out Q 0) (fun _=>count)
def bank {q : Nat} (live : Finset (Fin q)) (x : BitInput q) (B Q : Nat) (source out count : List Bool):Fin 128→List Bool:=
 Fin.addCases (m:=127) (n:=1) (motive:=fun _=>List Bool)
  (PCJ45bee56da9f34d5a_CircuitFlagBank.bank live x B source [] [] out (List.replicate (U B q (B+1)) false) Q) (fun _=>count)
def slots :Fin 15→Fin 128:=![124,8,9,105,106,10,11,12,13,14,15,16,17,18,127]
def machine:=RecoveryFocus.machine slots PCJ45bee56da9f34d5a_CircuitCountAdvance.machine

theorem heads_away (cursor cursor' Q count count' : Nat) (out : List Bool) (i : Fin 128)
 (h1 : i≠124) (h2 : i≠127) :heads cursor out Q count i=heads cursor' out Q count' i :=by
 revert h1 h2
 refine Fin.addCases (m:=127) (n:=1) (fun j hj _=>?_) (fun j _ hj=>?_) i
 · simp only [heads,Fin.addCases_left]
   exact PCJ45bee56da9f34d5a_CircuitFlagBank.heads_away 0 cursor cursor' Q 0 out j
    (fun he=>hj (congrArg (fun k :Fin 127=>k.castAdd 1) he))
 · fin_cases j;exact False.elim (hj rfl)

theorem bank_away {q : Nat} (live : Finset (Fin q)) (x : BitInput q) (B Q : Nat)
 (source out count count' : List Bool) (i : Fin 128) (hi : i≠127) :
 bank live x B Q source out count i=bank live x B Q source out count' i :=by
 revert hi
 refine Fin.addCases (m:=127) (n:=1) (fun _ _=>?_) (fun j hj=>?_) i
 · simp only [bank,Fin.addCases_left]
 · fin_cases j;exact False.elim (hj rfl)

theorem run {q : Nat} (live : Finset (Fin q)) (x : BitInput q) (B Q tag L target N : Nat)
 (tail out : List Bool)
 (hc : PCJ45bee56da9f34d5a_CircuitCountCopy.budget tag q L target N+2≤U B q (B+1))
 (hU : PCPPQueryNatural.budget N<U B q (B+1)) :
 Step machine (PCJ45bee56da9f34d5a_CircuitCountAdvance.budget tag q L target N (U B q (B+1)))
  (heads 0 out Q 0) (bank live x B Q (PCJ45bee56da9f34d5a_CircuitCountCopy.source tag q L target N tail)
    out (List.replicate (U B q (B+1)) false))
  (heads ((PCJ45bee56da9f34d5a_CircuitCountCopy.header tag q L target).length+(natWord N).length) out Q 1)
  (bank live x B Q (PCJ45bee56da9f34d5a_CircuitCountCopy.source tag q L target N tail)
    out (ZeroPadding.pad (U B q (B+1)) (CompareMachine.word N))) :=by
 have h:=(PCJ45bee56da9f34d5a_CircuitCountAdvance.run tag q L target N (U B q (B+1)) tail hc hU).dock
  slots (by decide) (heads 0 out Q 0)
  (bank live x B Q (PCJ45bee56da9f34d5a_CircuitCountCopy.source tag q L target N tail)
    out (List.replicate (U B q (B+1)) false))
  (by intro i;fin_cases i <;>rfl) (by intro i;fin_cases i <;>rfl)
 apply h.congr
 · apply PCJ45bee56da9f34d5a_NativeCircuitCount.dock_heads slots (by decide)
   · intro i;fin_cases i <;>rfl
   · intro i hi;exact heads_away _ _ Q 0 1 out i (fun he=>hi 0 he.symm) (fun he=>hi 14 he.symm)
 · apply HierarchyAllocation.install_eq slots (by decide)
   · intro i;fin_cases i <;>rfl
   · intro i hi;exact (bank_away live x B Q _ _ _ _ i (fun he=>hi 14 he.symm)).symm
end
end PCJ45bee56da9f34d5a_NativeFamilyCount

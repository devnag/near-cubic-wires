import Proof.Rows.NativeGateLoop

/-! The original circuit's actual first nat header produces the bottom-loop
count. Reader scratch and its capacity/log reuse the existing gate bank. -/
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 450000
set_option maxRecDepth 120000
namespace PCJ45bee56da9f34d5a_NativeCircuitCount
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairOrdinary.RecoveryRootRound
open NearCubicWires.P1Closure NearCubicWires.RepairRepresentation NearCubicWires.SupplierPipeline
open NearCubicWires.RepairSource.VerifierDecoding
open PCJ45bee56da9f34d5a_FramedGateBank
noncomputable section
attribute [local irreducible] PCJ45bee56da9f34d5a_TopArity.machine

def heads (pos : Nat) (out : List Bool) (Q count : Nat) : Fin 124→Nat :=
 Fin.addCases (m:=123) (n:=1) (motive:=fun _=>Nat)
  (PCJ45bee56da9f34d5a_CountedGateCell.heads (PCJ45bee56da9f34d5a_FramedGateBank.heads pos out) Q) (fun _=>count)
def bank {q : Nat} (live : Finset (Fin q)) (x : BitInput q) (w H R U : Nat)
 (source fields framed out count : List Bool) (Q : Nat) : Fin 124→List Bool :=
 Fin.addCases (m:=123) (n:=1) (motive:=fun _=>List Bool)
  (PCJ45bee56da9f34d5a_CountedGateCell.bank
    (PCJ45bee56da9f34d5a_FramedGateBank.bank live x w H R U source fields framed out) Q) (fun _=>count)
def slots : Fin 13→Fin 124 := ![114,8,9,10,11,12,13,14,15,16,123,106,105]
theorem slots_injective : Function.Injective slots := by decide
def machine := RecoveryFocus.machine slots PCJ45bee56da9f34d5a_TopArity.machine

theorem heads_away (pos Q c c' : Nat) (out : List Bool) (i : Fin 124) (hi : i≠123) :
 heads pos out Q c i=heads pos out Q c' i := by
 revert hi
 refine Fin.addCases (m:=123) (n:=1) (fun j _=>?_) (fun j hj=>?_) i
 · simp only [heads,Fin.addCases_left]
 · fin_cases j;exact False.elim (hj rfl)

theorem bank_away {q : Nat} (live : Finset (Fin q)) (x : BitInput q) (w H R U Q : Nat)
 (source fields framed out count count' : List Bool) (i : Fin 124) (hi : i≠123) :
 bank live x w H R U source fields framed out count Q i=bank live x w H R U source fields framed out count' Q i := by
 revert hi
 refine Fin.addCases (m:=123) (n:=1) (fun j _=>?_) (fun j hj=>?_) i
 · simp only [bank,Fin.addCases_left]
 · fin_cases j;exact False.elim (hj rfl)

theorem dock_heads {t u : Nat} (pick : Fin t→Fin u) (hinj : Function.Injective pick)
 (H : Fin u→Nat) (h : Fin t→Nat) (H' : Fin u→Nat)
 (hon : ∀j,h j=H' (pick j)) (hoff : ∀i,(∀j,pick j≠i)→H i=H' i) : dockH pick H h=H' := by
 funext i
 by_cases he:∃j,pick j=i
 · obtain ⟨j,rfl⟩:=he;exact (dockH_slot pick hinj H h j).trans (hon j)
 · have hn : ∀j,pick j≠i := by intro j hj;exact he ⟨j,hj⟩
   exact (dockH_other pick H h i hn).trans (hoff i hn)

theorem run {q : Nat} (live : Finset (Fin q)) (x : BitInput q) (w H R U Q n : Nat)
 (tail fields framed out : List Bool) (hU : PCPPQueryNatural.budget n<U) :
 Step machine (2*PCPPQueryNatural.budget n+4*U+10)
  (heads 0 out Q 0) (bank live x w H R U (natWord n++tail) fields framed out (List.replicate U false) Q)
  (heads 0 out Q 1) (bank live x w H R U (natWord n++tail) fields framed out (ZeroPadding.pad U (UnaryTemplate.tape n)) Q) := by
 have h:=(PCJ45bee56da9f34d5a_TopArity.run n U tail hU).dock slots slots_injective
  (heads 0 out Q 0) (bank live x w H R U (natWord n++tail) fields framed out (List.replicate U false) Q)
  (by intro i;fin_cases i <;>rfl) (by intro i;fin_cases i <;>rfl)
 apply h.congr
 · apply dock_heads slots slots_injective
   · intro i;fin_cases i <;>rfl
   · intro i hi;exact heads_away 0 Q 0 1 out i (fun he=>hi 10 he.symm)
 · apply HierarchyAllocation.install_eq slots slots_injective
   · intro i;fin_cases i <;>rfl
   · intro i hi;exact (bank_away live x w H R U Q _ _ _ _ _ _ i (fun he=>hi 10 he.symm)).symm
end
end PCJ45bee56da9f34d5a_NativeCircuitCount

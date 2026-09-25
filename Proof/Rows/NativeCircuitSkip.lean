import Proof.Rows.NativeCircuitCount

/-! Skip the actual native bottom-count header and TOP frame after producing
its unary count, then clear the one parser scratch tape. -/
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 450000
set_option maxRecDepth 120000
namespace PCJ45bee56da9f34d5a_NativeCircuitSkip
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairOrdinary.RecoveryRootRound
open NearCubicWires.P1Closure NearCubicWires.RepairRepresentation NearCubicWires.SupplierPipeline
open NearCubicWires.RepairSource.VerifierDecoding
open PCJ45bee56da9f34d5a_NativeCircuitCount
noncomputable section

def fieldSlots : Fin 3→Fin 124 := ![114,8,0]
def frameSlots : Fin 2→Fin 124 := ![114,0]
def eraseSlots : Fin 3→Fin 124 := ![8,105,106]
def field := RecoveryFocus.machine fieldSlots (PCPPQueryField.machine false)
def skipTop := RecoveryFocus.machine frameSlots (CloseoutRowsTupleSeek.frameMachine false)
def erase := RecoveryFocus.machine eraseSlots (RecoveryScratchErase.resetMachine 1)
def dirty (a : Fin 124→List Bool) (scratch : List Bool) :=Function.update a 8 scratch

theorem heads_away (pos pos' Q c : Nat) (out : List Bool) (i : Fin 124) (hi : i≠114) :
 heads pos out Q c i=heads pos' out Q c i := by
 revert hi
 refine Fin.addCases (m:=123) (n:=1) (fun a ha=>?_) (fun _ _=>?_) i
 · revert ha
   refine Fin.addCases (m:=122) (n:=1) (fun b hb=>?_) (fun _ _=>?_) a
   · revert hb
     refine Fin.addCases (m:=114) (n:=8) (fun _ _=>?_) (fun c hc=>?_) b
     · simp only [heads,PCJ45bee56da9f34d5a_CountedGateCell.heads,
         PCJ45bee56da9f34d5a_FramedGateBank.heads,Fin.addCases_left]
     · fin_cases c <;>first | exact False.elim (hc rfl) | rfl
   · simp only [heads,PCJ45bee56da9f34d5a_CountedGateCell.heads,Fin.addCases_left,Fin.addCases_right]
 · simp only [heads,Fin.addCases_right]

theorem field_run {q : Nat} (live : Finset (Fin q)) (x : BitInput q) (w H R U Q n : Nat)
 (tail framed out count : List Bool) :
 Step field (2*natBitLength n+3) (heads 0 out Q 1)
  (bank live x w H R U (natWord n++tail) (List.replicate H false) framed out count Q)
  (heads (natWord n).length out Q 1)
  (dirty (bank live x w H R U (natWord n++tail) (List.replicate H false) framed out count Q)
    (ZeroPadding.pad U (PCJ45bee56da9f34d5a_CircuitCountCopy.scratch n []))) := by
 have small:=(PCJ45bee56da9f34d5a_CircuitCountCopy.field_run false [] tail [] [] n).pad (![0,U,H] : Fin 3→Nat)
 simp only [PCPPQueryField.selected,Bool.false_eq_true,if_false,List.append_nil,List.nil_append,List.length_nil,Nat.zero_add] at small
 have h:=small.dock fieldSlots (by decide) (heads 0 out Q 1)
  (bank live x w H R U (natWord n++tail) (List.replicate H false) framed out count Q)
  (by intro i;fin_cases i <;>rfl)
  (by intro i;fin_cases i <;>first | rfl | exact (ZeroPadding.pad_zero _).symm)
 apply h.congr
 · apply dock_heads fieldSlots (by decide)
   · intro i;fin_cases i <;>rfl
   · intro i hi;exact heads_away 0 (natWord n).length Q 1 out i (fun he=>hi 0 he.symm)
 · apply HierarchyAllocation.install_eq fieldSlots (by decide)
   · intro i;fin_cases i <;>first | rfl | exact (ZeroPadding.pad_zero _).symm
   · intro i hi
     simp only [dirty,Function.update_of_ne (show i≠8 from fun he=>hi 1 he.symm)]

theorem frame_run {q : Nat} (live : Finset (Fin q)) (x : BitInput q) (w H R U Q n : Nat)
 (top tail framed out count scratch : List Bool) :
 Step skipTop (2*top.length+1) (heads (natWord n).length out Q 1)
  (dirty (bank live x w H R U (natWord n++frame top++tail) (List.replicate H false) framed out count Q) scratch)
  (heads ((natWord n).length+(frame top).length) out Q 1)
  (dirty (bank live x w H R U (natWord n++frame top++tail) (List.replicate H false) framed out count Q) scratch) := by
 have small:=(CloseoutRowsTupleSeek.frame_run false (natWord n) top tail []).pad (![0,H] : Fin 2→Nat)
 simp only [CloseoutRowsTupleSeek.selected,Bool.false_eq_true,if_false,List.append_nil] at small
 have h:=small.dock frameSlots (by decide) (heads (natWord n).length out Q 1)
  (dirty (bank live x w H R U (natWord n++frame top++tail) (List.replicate H false) framed out count Q) scratch)
  (by intro i;fin_cases i <;>rfl)
  (by intro i;fin_cases i <;>first | rfl | exact (ZeroPadding.pad_zero _).symm)
 apply h.congr
 · apply dock_heads frameSlots (by decide)
   · intro i;fin_cases i <;>rfl
   · intro i hi;exact heads_away _ _ Q 1 out i (fun he=>hi 0 he.symm)
 · exact install_existing _ _ _ (by intro i;fin_cases i <;>first | rfl | exact (ZeroPadding.pad_zero _).symm)

theorem erase_run {q : Nat} (live : Finset (Fin q)) (x : BitInput q) (w H R U Q pos : Nat)
 (source framed out count scratch : List Bool) (hs : scratch.length≤U) :
 Step erase (2*U+4) (heads pos out Q 1)
  (dirty (bank live x w H R U source (List.replicate H false) framed out count Q) scratch)
  (heads pos out Q 1) (bank live x w H R U source (List.replicate H false) framed out count Q) := by
 have h:=(Step.of_ready (RecoveryScratchErase.erase_ready U (U+1) (![scratch] : Fin 1→List Bool)
  (by intro i;fin_cases i;exact hs))).dock eraseSlots (by decide) (heads pos out Q 1)
  (dirty (bank live x w H R U source (List.replicate H false) framed out count Q) scratch)
  (by intro i;fin_cases i <;>rfl) (by intro i;fin_cases i <;>rfl)
 apply h.congr
 · exact dockH_existing _ _ _ (by intro i;fin_cases i <;>rfl)
 · apply HierarchyAllocation.install_eq eraseSlots (by decide)
   · intro i;fin_cases i <;>simp only [Nat.max_self] <;>rfl
   · intro i hi
     simp only [dirty,Function.update_of_ne (show i≠8 from fun he=>hi 0 he.symm)]
end
end PCJ45bee56da9f34d5a_NativeCircuitSkip

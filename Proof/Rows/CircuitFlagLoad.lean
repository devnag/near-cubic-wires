import Proof.Rows.CircuitFlagBank

/-! Isolate and unwrap one actual circuit frame, preserving the advancing
outer source and using only the fixed local work reserve. -/
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 300000
set_option maxRecDepth 120000
namespace PCJ45bee56da9f34d5a_CircuitFlagLoad
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairOrdinary.RecoveryRootRound
open NearCubicWires.P1Closure NearCubicWires.RepairRepresentation NearCubicWires.SupplierPipeline
open NearCubicWires.RepairSource.VerifierDecoding
open PCJ45bee56da9f34d5a_UniformMinimumBounds PCJ45bee56da9f34d5a_CircuitFlagBank
noncomputable section
attribute [local irreducible] PoolEntryCursor.copy
attribute [local irreducible] Streaming.machine

def copySlots : Fin 3→Fin 127:=![124,125,126]
def unwrapSlots : Fin 3→Fin 127:=![125,114,126]
def copy:=RecoveryFocus.machine copySlots PoolEntryCursor.copy
def unwrap:=RecoveryFocus.machine unwrapSlots Streaming.machine
def machine:=Composition.machine copy unwrap

theorem copy_run {q : Nat} (live : Finset (Fin q)) (x : BitInput q) (B Q : Nat)
 (pre bits tail out : List Bool) (hs : (frame bits).length≤U B q (B+1)) :
 Step copy (4*bits.length+4) (heads 0 pre.length out Q 0)
  (bank live x B (pre++frame bits++tail) [] [] out (List.replicate (U B q (B+1)) false) Q)
  (heads 0 (pre.length+(frame bits).length) out Q 0)
  (bank live x B (pre++frame bits++tail) [] (frame bits) out (List.replicate (U B q (B+1)) false) Q) := by
 have h:=(PoolEntryCursor.copy_run pre bits tail (U B q (B+1)) hs).dock copySlots (by decide)
  (heads 0 pre.length out Q 0)
  (bank live x B (pre++frame bits++tail) [] [] out (List.replicate (U B q (B+1)) false) Q)
  (by intro i;fin_cases i <;>rfl) (by intro i;fin_cases i <;>rfl)
 apply h.congr
 · apply PCJ45bee56da9f34d5a_NativeCircuitCount.dock_heads copySlots (by decide)
   · intro i;fin_cases i <;>rfl
   · intro i hi;exact heads_away _ _ _ Q 0 out i (fun he=>hi 0 he.symm)
 · apply HierarchyAllocation.install_eq copySlots (by decide)
   · intro i;fin_cases i <;>rfl
   · intro i hi;exact (frame_away live x B Q _ _ _ _ _ _ i (fun he=>hi 1 he.symm)).symm

theorem unwrap_run {q : Nat} (live : Finset (Fin q)) (x : BitInput q) (B Q cursor : Nat)
 (source bits out : List Bool) (hs : bits.length≤U B q (B+1)) :
 Step unwrap (4*bits.length+2) (heads 0 cursor out Q 0)
  (bank live x B source [] (frame bits) out (List.replicate (U B q (B+1)) false) Q)
  (heads 0 cursor out Q 0)
  (bank live x B source bits (frame bits) out (List.replicate (U B q (B+1)) false) Q) := by
 obtain ⟨r,hr,ht,hh,_⟩:=UInputFields.unwrap_ready bits
 have small:=(Step.of_run hr (funext hh) ht).pad (fun _=>U B q (B+1))
 have h:=small.dock unwrapSlots (by decide) (heads 0 cursor out Q 0)
  (bank live x B source [] (frame bits) out (List.replicate (U B q (B+1)) false) Q)
  (by intro i;fin_cases i <;>rfl) (by intro i;fin_cases i <;>rfl)
 have hz : ZeroPadding.pad (U B q (B+1)) (List.replicate bits.length false)=List.replicate (U B q (B+1)) false := by
  simp only [ZeroPadding.pad,List.length_replicate,←List.replicate_add,Nat.add_sub_of_le hs]
 apply h.congr
 · exact dockH_existing _ _ _ (by intro i;fin_cases i <;>rfl)
 · apply HierarchyAllocation.install_eq unwrapSlots (by decide)
   · intro i;fin_cases i <;>first | rfl | exact hz.symm
   · intro i hi;exact (raw_away live x B Q _ _ _ _ _ _ i (fun he=>hi 1 he.symm)).symm

theorem run {q : Nat} (live : Finset (Fin q)) (x : BitInput q) (B Q : Nat)
 (pre bits tail out : List Bool) (hs : (frame bits).length≤U B q (B+1)) :
 Step machine (8*bits.length+7) (heads 0 pre.length out Q 0)
  (bank live x B (pre++frame bits++tail) [] [] out (List.replicate (U B q (B+1)) false) Q)
  (heads 0 (pre.length+(frame bits).length) out Q 0)
  (bank live x B (pre++frame bits++tail) bits (frame bits) out (List.replicate (U B q (B+1)) false) Q) := by
 have hb : bits.length≤U B q (B+1) :=by rw [frame_length] at hs;omega
 have h:=(copy_run live x B Q pre bits tail out hs).seq
  (unwrap_run live x B Q (pre.length+(frame bits).length) (pre++frame bits++tail) bits out hb)
 simpa only [machine,show (4*bits.length+4)+1+(4*bits.length+2)=8*bits.length+7 by omega] using h
end
end PCJ45bee56da9f34d5a_CircuitFlagLoad

import Proof.Rows.FramedGateBank

/-! Copy and load a real original gate while retaining the native stream cursor. -/
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 750000
set_option maxRecDepth 120000
namespace PCJ45bee56da9f34d5a_FramedGateLoad
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairOrdinary.RecoveryRootRound
open NearCubicWires.P1Closure NearCubicWires.RepairRepresentation
open PCJ45bee56da9f34d5a_FramedGateBank
noncomputable section
attribute [local irreducible] PoolEntryCursor.copy PCJ45bee56da9f34d5a_NativeGateLoadReady.machine

def copy := RecoveryFocus.machine copySlots PoolEntryCursor.copy
def load := RecoveryFocus.machine loadSlots PCJ45bee56da9f34d5a_NativeGateLoadReady.machine

theorem copy_run {q : Nat} (live : Finset (Fin q)) (x : BitInput q) (w H R U : Nat)
 (pre bits tail out : List Bool) (hf : (frame bits).length≤H) :
 Step copy (4*bits.length+4) (heads pre.length out)
  (bank live x w H R U (pre++frame bits++tail) (List.replicate H false) (List.replicate H false) out)
  (heads (pre.length+(frame bits).length) out)
  (bank live x w H R U (pre++frame bits++tail) (List.replicate H false) (ZeroPadding.pad H (frame bits)) out) := by
 have h:=(PoolEntryCursor.copy_run pre bits tail H hf).dock copySlots copySlots_injective
  (heads pre.length out)
  (bank live x w H R U (pre++frame bits++tail) (List.replicate H false) (List.replicate H false) out)
  (by intro i;fin_cases i <;>rfl) (by intro i;fin_cases i <;>rfl)
 apply h.congr
 · funext i;fin_cases i <;>first
    | exact dockH_slot copySlots copySlots_injective _ _ 0
    | exact dockH_slot copySlots copySlots_injective _ _ 1
    | exact dockH_slot copySlots copySlots_injective _ _ 2
    | exact dockH_other copySlots _ _ _ (by decide)
 · apply HierarchyAllocation.install_eq copySlots copySlots_injective
   · intro i;fin_cases i <;>rfl
   · intro i hi
     by_cases h0:i=0
     · subst i;rfl
     · exact (bank_away live x w H R U _ _ _ _ _ out i h0 (fun he=>hi 1 he.symm)).symm

theorem load_run {q : Nat} (g : NormalizedThresholdGate q) (live : Finset (Fin q)) (x : BitInput q)
 (w H R U pos : Nat) (source out : List Bool) (hH : PoolEntryLoad.budget (strict g)+1≤H) :
 Step load (PoolEntryLoad.budget (strict g)+4*H+10) (heads pos out)
  (bank live x w H R U source (List.replicate H false) (ZeroPadding.pad H (frame (PoolEntryLoad.word (strict g)))) out)
  (heads pos out)
  (bank live x w H R U source (ZeroPadding.pad H (exactWord (strict g))) (ZeroPadding.pad H (frame (PoolEntryLoad.word (strict g)))) out) := by
 have h:=(PCJ45bee56da9f34d5a_NativeGateLoadReady.run (strict g) H hH).dock
  loadSlots loadSlots_injective (heads pos out)
  (bank live x w H R U source (List.replicate H false) (ZeroPadding.pad H (frame (PoolEntryLoad.word (strict g)))) out)
  (by intro i;fin_cases i <;>rfl) (by intro i;fin_cases i <;>rfl)
 apply h.congr
 · exact dockH_existing _ _ _ (by intro i;fin_cases i <;>rfl)
 · apply HierarchyAllocation.install_eq loadSlots loadSlots_injective
   · intro i;fin_cases i <;>rfl
   · intro i hi
     exact (bank_away live x w H R U source _ _ _ _ out i
       (fun he=>hi 5 he.symm) (fun he=>hi 0 he.symm)).symm
end
end PCJ45bee56da9f34d5a_FramedGateLoad

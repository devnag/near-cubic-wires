import Proof.Rows.FramedGateLoad

/-! A real framed original gate is consumed into one residual-constant flag,
with the stream cursor advanced and all isolated gate storage cleared for reuse. -/
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 750000
set_option maxRecDepth 120000
namespace PCJ45bee56da9f34d5a_FramedGateRun
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairOrdinary.RecoveryRootRound
open NearCubicWires.P1Closure NearCubicWires.RepairRepresentation NearCubicWires.SupplierPipeline
open PCJ45bee56da9f34d5a_FramedGateBank PCJ45bee56da9f34d5a_UniformMinimumBounds
open scoped BigOperators
noncomputable section
attribute [local irreducible] PCJ45bee56da9f34d5a_MinimumGateCell.machine

def evaluate := TapeEmbedding.machine 8 PCJ45bee56da9f34d5a_MinimumGateCell.machine
def erase := RecoveryFocus.machine eraseSlots (RecoveryScratchErase.resetMachine 2)
def machine := Composition.machine
 (Composition.machine (Composition.machine PCJ45bee56da9f34d5a_FramedGateLoad.copy PCJ45bee56da9f34d5a_FramedGateLoad.load) evaluate) erase

theorem evaluate_run {q : Nat} (g : NormalizedThresholdGate q) (live : Finset (Fin q)) (x : BitInput q)
 (B w pos : Nat) (source framed out : List Bool) (hw : 0<w)
 (hb : (PCJ45bee56da9f34d5a_FullGateBounds.source g).length≤B)
 (hm : (g.threshold-1).natAbs+(∑i,(g.weight i).natAbs)<2^w) :
 Step evaluate (65536*(B+q+w+1)^2) (heads pos out)
  (bank live x w (H B q w) (R B q w) (U B q w) source (ZeroPadding.pad (H B q w) (exactWord (strict g))) framed out)
  (heads pos (out++[residualConstant g live x]))
  (bank live x w (H B q w) (R B q w) (U B q w) source (ZeroPadding.pad (H B q w) (exactWord (strict g))) framed (out++[residualConstant g live x])) := by
 exact (PCJ45bee56da9f34d5a_UniformMinimumBounds.run g live x out B w hw hb hm).embed
  (extraHeads pos) (extras source framed (H B q w))

theorem erase_run {q : Nat} (live : Finset (Fin q)) (x : BitInput q) (w H R U pos : Nat)
 (source fields framed out : List Bool) (hf : fields.length≤H) (hg : framed.length≤H) :
 Step erase (2*H+4) (heads pos out) (bank live x w H R U source fields framed out)
  (heads pos out) (bank live x w H R U source (List.replicate H false) (List.replicate H false) out) := by
 have h:=(Step.of_ready (RecoveryScratchErase.erase_ready H (H+1) (![fields,framed] : Fin 2→List Bool)
  (by intro i;fin_cases i <;>assumption))).dock eraseSlots eraseSlots_injective (heads pos out)
  (bank live x w H R U source fields framed out)
  (by intro i;fin_cases i <;>rfl) (by intro i;fin_cases i <;>rfl)
 apply h.congr
 · exact dockH_existing _ _ _ (by intro i;fin_cases i <;>rfl)
 · apply HierarchyAllocation.install_eq eraseSlots eraseSlots_injective
   · intro i;fin_cases i <;>simp only [Nat.max_self] <;>rfl
   · intro i hi
     exact (bank_away live x w H R U source fields framed _ _ out i
       (fun he=>hi 0 he.symm) (fun he=>hi 1 he.symm)).symm

theorem load_fits {q : Nat} (g : NormalizedThresholdGate q) (B w : Nat) (hw : 0<w)
 (hb : (PCJ45bee56da9f34d5a_FullGateBounds.source g).length≤B) :
 PoolEntryLoad.budget (strict g)+1≤H B q w ∧ (frame (PoolEntryLoad.word (strict g))).length≤H B q w ∧
 (exactWord (strict g)).length≤H B q w := by
 have hn : natBitLength q≤q+1 := Nat.add_le_add_right (Nat.log_le_self _ _) 1
 have he : (exactWord (strict g)).length≤B := hb
 simp only [PoolEntryLoad.budget,PoolEntryLoad.rawBudget,PoolEntryLoad.word,List.length_append,
   DecompositionSource.natWord_length,frame_length']
 unfold H
 omega

theorem run {q : Nat} (g : NormalizedThresholdGate q) (live : Finset (Fin q)) (x : BitInput q)
 (B w : Nat) (pre tail out : List Bool) (hw : 0<w)
 (hb : (PCJ45bee56da9f34d5a_FullGateBounds.source g).length≤B)
 (hm : (g.threshold-1).natAbs+(∑i,(g.weight i).natAbs)<2^w) :
 Step machine (131072*(B+q+w+1)^2) (heads pre.length out)
  (bank live x w (H B q w) (R B q w) (U B q w)
    (pre++frame (PoolEntryLoad.word (strict g))++tail) (List.replicate (H B q w) false) (List.replicate (H B q w) false) out)
  (heads (pre.length+(frame (PoolEntryLoad.word (strict g))).length) (out++[residualConstant g live x]))
  (bank live x w (H B q w) (R B q w) (U B q w)
    (pre++frame (PoolEntryLoad.word (strict g))++tail) (List.replicate (H B q w) false) (List.replicate (H B q w) false) (out++[residualConstant g live x])) := by
 obtain ⟨hl,hf,he⟩:=load_fits g B w hw hb
 have h1:=PCJ45bee56da9f34d5a_FramedGateLoad.copy_run live x w (H B q w) (R B q w) (U B q w) pre (PoolEntryLoad.word (strict g)) tail out hf
 let src:=pre++frame (PoolEntryLoad.word (strict g))++tail
 let pos:=pre.length+(frame (PoolEntryLoad.word (strict g))).length
 let fld:=ZeroPadding.pad (H B q w) (exactWord (strict g))
 let frm:=ZeroPadding.pad (H B q w) (frame (PoolEntryLoad.word (strict g)))
 have h2:=PCJ45bee56da9f34d5a_FramedGateLoad.load_run g live x w (H B q w) (R B q w) (U B q w) pos src out hl
 have h3:=evaluate_run g live x B w pos src frm out hw hb hm
 have h4:=erase_run live x w (H B q w) (R B q w) (U B q w) pos src fld frm (out++[residualConstant g live x])
   (by simpa only [fld,ZeroPadding.pad_length] using max_le le_rfl he)
   (by simpa only [frm,ZeroPadding.pad_length] using max_le le_rfl hf)
 have h:=((h1.seq h2).seq h3).seq h4
 unfold machine
 apply h.enlarge
 have hs : B+q+w+1≤(B+q+w+1)^2 := Nat.le_self_pow (by decide) _
 have hwords : (PoolEntryLoad.word (strict g)).length≤H B q w := by simp only [frame_length'] at hf;omega
 unfold H at hl hwords ⊢
 nlinarith
end
end PCJ45bee56da9f34d5a_FramedGateRun

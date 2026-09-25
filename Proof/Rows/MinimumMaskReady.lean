import Proof.Rows.MinimumMaskMeaning

/-! Reusable minimizing-mask producer: rewind the retained native source and
input masks, clear only parser scratch, and leave the q-bit answer at head zero. -/
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 650000
set_option maxRecDepth 120000
namespace PCJ45bee56da9f34d5a_MinimumMaskReady
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairOrdinary.RecoveryRootRound
open NearCubicWires.RepairRepresentation NearCubicWires.RepairSource.VerifierDecoding
open StablePartition.Workspace
open PCJ45bee56da9f34d5a_MinimumMaskRun
noncomputable section

def heads : Fin 8→Nat := ![0,0,0,0,0,1,0,0]
def bank (source scratch live x out : List Bool) (q U : Nat) : Fin 8→List Bool :=
  ![source,scratch,live,x,out,CompareMachine.word q,List.replicate U true,List.replicate (U+1) false]
def produce := TapeEmbedding.machine 2 PCJ45bee56da9f34d5a_MinimumMaskRun.machine
def rewindSlots : Fin 7→Fin 8 := ![0,1,2,3,4,6,7]
theorem rewind_injective : Function.Injective rewindSlots := by decide
theorem rewind_pick (i : Fin 8) : RecoveryFocus.pick rewindSlots i = ![some 0,some 1,some 2,some 3,some 4,none,some 5,some 6] i := by
  fin_cases i <;>first
    | exact RecoveryFocus.pick_slot _ rewind_injective 0
    | exact RecoveryFocus.pick_slot _ rewind_injective 1
    | exact RecoveryFocus.pick_slot _ rewind_injective 2
    | exact RecoveryFocus.pick_slot _ rewind_injective 3
    | exact RecoveryFocus.pick_slot _ rewind_injective 4
    | exact RecoveryFocus.pick_slot _ rewind_injective 5
    | exact RecoveryFocus.pick_slot _ rewind_injective 6
    | decide
def clearSlots : Fin 3→Fin 8 := ![1,6,7]
def rewind := RecoveryFocus.machine rewindSlots (PCJ45bee56da9f34d5a_HeaderRewind.machine 5)
def erase := RecoveryFocus.machine clearSlots (RecoveryScratchErase.resetMachine 1)
def machine := Composition.machine (Composition.machine produce rewind) erase

theorem scratch_length (zs : List Int) (backing : List Bool) (U : Nat)
    (hb : backing.length ≤ U) (hz : ∀z∈zs,natBitLength z.natAbs+2 ≤ U) :
    (zs.foldl (fun b z=>PCJ45bee56da9f34d5a_CircuitCountCopy.scratch z.natAbs b) backing).length ≤ U := by
  induction zs generalizing backing with
  | nil => exact hb
  | cons z zs ih =>
    apply ih
    · simp only [PCJ45bee56da9f34d5a_CircuitCountCopy.scratch,overlay_length,UnaryTemplate.tape,
        List.length_append,List.length_cons,List.length_nil,List.length_replicate,max_le_iff]
      have h := hz z (by simp)
      omega
    · intro z hz';exact hz z (by simp [hz'])

theorem run (zs : List Int) (tail live x : List Bool) (F U : Nat)
    (hF : ∀z∈zs,2*natBitLength z.natAbs+5 ≤ F)
    (hFU : F ≤ U) (hs : (stream zs).length ≤ U) (hq : zs.length ≤ U) :
    Step machine (budget zs.length F+4*U+10) heads
      (bank (stream zs++tail) (List.replicate U false) live x (List.replicate U false) zs.length U)
      heads (bank (stream zs++tail) (List.replicate U false) live x
        (ZeroPadding.pad U (output zs live x zs.length)) zs.length U) := by
  let dirty := scratch zs (List.replicate U false) zs.length
  let result := ZeroPadding.pad U (output zs live x zs.length)
  let after := bank (stream zs++tail) dirty live x result zs.length U
  let pos : Fin 8→Nat := ![(stream zs).length,0,zs.length,zs.length,zs.length,1,0,0]
  have first := ((PCJ45bee56da9f34d5a_MinimumMaskRun.run [] tail zs (List.replicate U false) live x [] F hF).pad
    (fun i : Fin 6=>if i=4 then U else 0)).embed (fun _ : Fin 2=>0)
    (![List.replicate U true,List.replicate (U+1) false] : Fin 2→List Bool)
  have first' : Step produce (budget zs.length F) heads
      (bank (stream zs++tail) (List.replicate U false) live x (List.replicate U false) zs.length U) pos after := by
    refine (first.congr_in ?_ ?_).congr ?_ ?_
    · funext i;fin_cases i <;>rfl
    · funext i;fin_cases i <;>simp [bank,PCJ45bee56da9f34d5a_MinimumMaskCell.bank,Fin.addCases,ZeroPadding.pad]
    · funext i;fin_cases i <;>simp [pos,PCJ45bee56da9f34d5a_MinimumMaskCell.heads,Fin.addCases]
    · funext i;fin_cases i <;>first | rfl | exact ZeroPadding.pad_zero _
  have hd : dirty.length ≤ U := by
    dsimp only [dirty,scratch]
    rw [List.take_length]
    apply scratch_length zs _ U (by simp)
    intro z hz
    have h := hF z hz
    omega
  have re := (PCJ45bee56da9f34d5a_HeaderRewind.run 5
    (![ (stream zs).length,0,zs.length,zs.length,zs.length] : Fin 5→Nat)
    (PCJ45bee56da9f34d5a_MinimumMaskCell.bank (stream zs++tail) dirty live x result) U
    (by intro i;fin_cases i <;>simp [hs,hq])).dock rewindSlots (by decide) pos after
    (by intro i;fin_cases i <;>rfl) (by intro i;fin_cases i <;>rfl)
  have middle : Step rewind (2*U+4) pos after heads after := by
    apply re.congr
    · funext i;fin_cases i <;>simp [dockH,rewind_pick,heads,pos]
    · exact install_existing _ _ _ (by intro i;fin_cases i <;>rfl)
  have cl := (Step.of_ready (RecoveryScratchErase.erase_ready U (U+1) (![dirty] : Fin 1→List Bool)
    (by intro i;fin_cases i;exact hd))).dock clearSlots (by decide) heads after
    (by intro i;fin_cases i <;>rfl) (by intro i;fin_cases i <;>rfl)
  have last : Step erase (2*U+4) heads after heads
      (bank (stream zs++tail) (List.replicate U false) live x result zs.length U) := by
    apply cl.congr
    · exact dockH_existing _ _ _ (by intro i;fin_cases i <;>rfl)
    · apply HierarchyAllocation.install_eq clearSlots (by decide)
      · intro i;fin_cases i <;>simp only [Nat.max_self] <;>rfl
      · intro i hi;fin_cases i
        all_goals first | rfl | exact False.elim (hi 0 rfl)
  have all := (first'.seq middle).seq last
  unfold machine
  convert all using 1;omega
end
end PCJ45bee56da9f34d5a_MinimumMaskReady

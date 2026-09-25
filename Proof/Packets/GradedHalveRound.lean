import Proof.PCP.PCPTraversalSplit
import Proof.Packets.PhysicalRepeatStep

/-! An independently checked reusable physical ceiling-halving round. The
construction follows the original WindowHalveRoundK split/erase/copy/erase
sequence, using its authentic primitive workers without importing the unrelated
window-emitter application chain. No schedule or source is assumed. -/
set_option autoImplicit false
set_option maxHeartbeats 500000
set_option maxRecDepth 120000
set_option warningAsError true
namespace PCJ9eff70d512234a4c_Fixed.Materializer.GradedHalveRound
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open RecoveryExecution RecoveryRootRound NearCubicWires.ExtDecompositionBatch
open NearCubicWires.RepairSource.VerifierDecoding
noncomputable section

def halve (n : Nat) := (n+1)/2
 theorem halve_le (n : Nat) : halve n≤n := by unfold halve;omega
 theorem halve_iterate_le (n j : Nat) : halve^[j] n≤n := by
  induction j with
  | zero=>simp
  | succ j ih=>rw [Function.iterate_succ_apply'];exact (halve_le _).trans ih

def layout (C m : Nat) : Fin 6→List Bool:=
  ![ZeroPadding.pad C (List.replicate m true),
    List.replicate C false,List.replicate C false,List.replicate C false,
    List.replicate (C+1) false,List.replicate C true]

def afterSplit (C m : Nat) : Fin 6→List Bool:=
  ![ZeroPadding.pad C (List.replicate m true),
    ZeroPadding.pad C (List.replicate (halve m) true),
    ZeroPadding.pad C (List.replicate (m/2) true),
    List.replicate C false,List.replicate (C+1) false,List.replicate C true]

def afterClear (C m : Nat) : Fin 6→List Bool:=
  ![List.replicate C false,
    ZeroPadding.pad C (List.replicate (halve m) true),
    ZeroPadding.pad C (List.replicate (m/2) true),
    List.replicate C false,List.replicate (C+1) false,List.replicate C true]

def afterCopy (C m : Nat) : Fin 6→List Bool:=
  ![ZeroPadding.pad C (List.replicate (halve m) true),
    ZeroPadding.pad C (List.replicate (halve m) true),
    ZeroPadding.pad C (List.replicate (m/2) true),
    List.replicate C false,List.replicate (C+1) false,List.replicate C true]

/-! ## The reusable erase, in `ClockJoin` form with a round-tripping log -/

def eraseIn (t C : Nat) (backing : Fin t→List Bool) : Fin (t+1+1)→List Bool:=
  Fin.addCases (Fin.addCases backing (fun _ : Fin 1=>List.replicate C true))
    (fun _ : Fin 1=>List.replicate (C+1) false)

def eraseOut (t C : Nat) : Fin (t+1+1)→List Bool:=
  Fin.addCases (Fin.addCases (fun _ : Fin t=>List.replicate C false)
    (fun _ : Fin 1=>List.replicate C true)) (fun _ : Fin 1=>List.replicate (C+1) false)

/-- The published scratch erase, run with a `C+1` log so the log returns to its
own entry shape.  This is `RecoveryScratchErase.erase_ready`, nothing new. -/
theorem erase_clock (t C : Nat) (backing : Fin t→List Bool)
    (hb : ∀ i,(backing i).length ≤ C) :
    ClockJoin.ReadyRun (RecoveryScratchErase.resetMachine t) (2*C+4)
      (eraseIn t C backing) (eraseOut t C):=by
  obtain ⟨r,hr,ht,hh,hs⟩:=RecoveryScratchErase.erase_ready C (C+1) backing hb
  have hmax:max (C+1) (C+1)=C+1:=by omega
  rw [hmax] at ht
  exact ⟨r,hr,ht,hh,hs.le⟩

/-- The published unary copy, run with a `C+1` log so the log returns to its own
entry shape.  This is `PCPUnaryCopy.copy_ready`, nothing new. -/
theorem copy_clock (C n : Nat) (hn : n ≤ C) :
    ClockJoin.ReadyRun PCPUnaryCopy.machine (2*C+4)
      ![ZeroPadding.pad C (List.replicate n true),List.replicate C false,
        List.replicate (C+1) false]
      ![ZeroPadding.pad C (List.replicate n true),
        ZeroPadding.pad C (List.replicate n true),List.replicate (C+1) false]:=by
  obtain ⟨r,hr,ht,hh,hs⟩:=PCPUnaryCopy.copy_ready n C C (C+1)
  have hmax:max (C+1) (n+1)=C+1:=by omega
  rw [hmax] at ht
  exact ClockJoin.enlarge _ (2*n+4) _ _ _ ⟨r,hr,ht,hh,hs.le⟩ (by omega)

/-! ## The four docked stages -/

def splitSlots : Fin 4→Fin 6:=![0,1,2,3]
def clearSlots : Fin 3→Fin 6:=![0,5,4]
def copySlots : Fin 3→Fin 6:=![1,0,4]
def resetSlots : Fin 4→Fin 6:=![1,2,5,4]

theorem splitSlots_injective : Function.Injective splitSlots:=by decide
theorem clearSlots_injective : Function.Injective clearSlots:=by decide
theorem copySlots_injective : Function.Injective copySlots:=by decide
theorem resetSlots_injective : Function.Injective resetSlots:=by decide

noncomputable def splitStage:=RecoveryFocus.machine splitSlots PCPUnarySplit.machine
noncomputable def clearStage:=RecoveryFocus.machine clearSlots (RecoveryScratchErase.resetMachine 1)
noncomputable def copyStage:=RecoveryFocus.machine copySlots PCPUnaryCopy.machine
noncomputable def resetStage:=RecoveryFocus.machine resetSlots (RecoveryScratchErase.resetMachine 2)

theorem split_round (C m : Nat) (hm : m+1 ≤ C) :
    ClockJoin.ReadyRun splitStage (2*C+4) (layout C m) (afterSplit C m):=by
  have h:=(PCPTraversal.padded_split_ready m C C hm).focus splitSlots splitSlots_injective
    (layout C m) (by intro j;fin_cases j <;> rfl)
  have he:install splitSlots (layout C m) (PCPTraversal.splitLocal m C C)=afterSplit C m:=by
    funext i
    fin_cases i
    · change install splitSlots (layout C m) (PCPTraversal.splitLocal m C C) (splitSlots 0)=_
      rw [install_slot _ splitSlots_injective]
      rfl
    · change install splitSlots (layout C m) (PCPTraversal.splitLocal m C C) (splitSlots 1)=_
      rw [install_slot _ splitSlots_injective]
      rfl
    · change install splitSlots (layout C m) (PCPTraversal.splitLocal m C C) (splitSlots 2)=_
      rw [install_slot _ splitSlots_injective]
      rfl
    · change install splitSlots (layout C m) (PCPTraversal.splitLocal m C C) (splitSlots 3)=_
      rw [install_slot _ splitSlots_injective]
      rfl
    · rw [install_other _ _ _ _ (by decide)]
      rfl
    · rw [install_other _ _ _ _ (by decide)]
      rfl
  rw [he] at h
  exact ClockJoin.enlarge _ _ _ _ _ h (by omega)

theorem clear_round (C m : Nat) (hm : m+1 ≤ C) :
    ClockJoin.ReadyRun clearStage (2*C+4) (afterSplit C m) (afterClear C m):=by
  have hb : ∀ i : Fin 1,
      ((fun _ : Fin 1=>ZeroPadding.pad C (List.replicate m true)) i).length ≤ C:=by
    intro _
    simp only [ZeroPadding.pad_length,List.length_replicate]
    omega
  have h:=(erase_clock 1 C (fun _ : Fin 1=>ZeroPadding.pad C (List.replicate m true)) hb).focus
    clearSlots clearSlots_injective (afterSplit C m) (by intro j;fin_cases j <;> rfl)
  have he:install clearSlots (afterSplit C m) (eraseOut 1 C)=afterClear C m:=by
    funext i
    fin_cases i
    · change install clearSlots (afterSplit C m) (eraseOut 1 C) (clearSlots 0)=_
      rw [install_slot _ clearSlots_injective]
      rfl
    · rw [install_other _ _ _ _ (by decide)]
      rfl
    · rw [install_other _ _ _ _ (by decide)]
      rfl
    · rw [install_other _ _ _ _ (by decide)]
      rfl
    · change install clearSlots (afterSplit C m) (eraseOut 1 C) (clearSlots 2)=_
      rw [install_slot _ clearSlots_injective]
      rfl
    · change install clearSlots (afterSplit C m) (eraseOut 1 C) (clearSlots 1)=_
      rw [install_slot _ clearSlots_injective]
      rfl
  rw [he] at h
  exact h

theorem copy_round (C m : Nat) (hm : m+1 ≤ C) :
    ClockJoin.ReadyRun copyStage (2*C+4) (afterClear C m) (afterCopy C m):=by
  have hhalve:halve m ≤ C:=le_trans (halve_le m) (by omega)
  have h:=(copy_clock C (halve m) hhalve).focus copySlots copySlots_injective
    (afterClear C m) (by intro j;fin_cases j <;> rfl)
  have he:install copySlots (afterClear C m)
      ![ZeroPadding.pad C (List.replicate (halve m) true),
        ZeroPadding.pad C (List.replicate (halve m) true),
        List.replicate (C+1) false]=afterCopy C m:=by
    funext i
    fin_cases i
    · change install copySlots (afterClear C m) _ (copySlots 1)=_
      rw [install_slot _ copySlots_injective]
      rfl
    · change install copySlots (afterClear C m) _ (copySlots 0)=_
      rw [install_slot _ copySlots_injective]
      rfl
    · rw [install_other _ _ _ _ (by decide)]
      rfl
    · rw [install_other _ _ _ _ (by decide)]
      rfl
    · change install copySlots (afterClear C m) _ (copySlots 2)=_
      rw [install_slot _ copySlots_injective]
      rfl
    · rw [install_other _ _ _ _ (by decide)]
      rfl
  rw [he] at h
  exact h

theorem reset_round (C m : Nat) (hm : m+1 ≤ C) :
    ClockJoin.ReadyRun resetStage (2*C+4) (afterCopy C m) (layout C (halve m)):=by
  have hb : ∀ i : Fin 2,
      ((![ZeroPadding.pad C (List.replicate (halve m) true),
        ZeroPadding.pad C (List.replicate (m/2) true)] : Fin 2→List Bool) i).length ≤ C:=by
    intro i
    fin_cases i
    · show (ZeroPadding.pad C (List.replicate (halve m) true)).length ≤ C
      simp only [ZeroPadding.pad_length,List.length_replicate]
      have:=halve_le m
      omega
    · show (ZeroPadding.pad C (List.replicate (m/2) true)).length ≤ C
      simp only [ZeroPadding.pad_length,List.length_replicate]
      omega
  have h:=(erase_clock 2 C
    (![ZeroPadding.pad C (List.replicate (halve m) true),
      ZeroPadding.pad C (List.replicate (m/2) true)] : Fin 2→List Bool) hb).focus
    resetSlots resetSlots_injective (afterCopy C m) (by intro j;fin_cases j <;> rfl)
  have he:install resetSlots (afterCopy C m) (eraseOut 2 C)=layout C (halve m):=by
    funext i
    fin_cases i
    · rw [install_other _ _ _ _ (by decide)]
      rfl
    · change install resetSlots (afterCopy C m) (eraseOut 2 C) (resetSlots 0)=_
      rw [install_slot _ resetSlots_injective]
      rfl
    · change install resetSlots (afterCopy C m) (eraseOut 2 C) (resetSlots 1)=_
      rw [install_slot _ resetSlots_injective]
      rfl
    · rw [install_other _ _ _ _ (by decide)]
      rfl
    · change install resetSlots (afterCopy C m) (eraseOut 2 C) (resetSlots 3)=_
      rw [install_slot _ resetSlots_injective]
      rfl
    · change install resetSlots (afterCopy C m) (eraseOut 2 C) (resetSlots 2)=_
      rw [install_slot _ resetSlots_injective]
      rfl
  rw [he] at h
  exact h

/-! ## The round -/

noncomputable def round:=
  Composition.machine (Composition.machine (Composition.machine splitStage clearStage) copyStage)
    resetStage

def roundBudget (C : Nat):=8*C+19

/-- One physical round halves the bank's unary value in place and returns every
other tape to its entry shape. -/
theorem round_run (C m : Nat) (hm : m+1 ≤ C) :
    ClockJoin.ReadyRun round (roundBudget C) (layout C m) (layout C (halve m)):=by
  have h1:=ClockJoin.join _ _ _ _ _ _ _ (split_round C m hm) (clear_round C m hm)
  have h2:=ClockJoin.join _ _ _ _ _ _ _ h1 (copy_round C m hm)
  have h3:=ClockJoin.join _ _ _ _ _ _ _ h2 (reset_round C m hm)
  have he:2*C+4+1+(2*C+4)+1+(2*C+4)+1+(2*C+4)=roundBudget C:=by
    unfold roundBudget
    omega
  rw [he] at h3
  exact h3

/-- The capacity condition survives every iterate, because `halve` contracts. -/
theorem round_iterate_capacity (C n j : Nat) (hn : n+1 ≤ C) : halve^[j] n+1 ≤ C:=by
  have:=halve_iterate_le n j
  omega

end
end PCJ9eff70d512234a4c_Fixed.Materializer.GradedHalveRound

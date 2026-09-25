import Proof.Packets.ReusableNativeCore

/-! Executed scratch clearing and the complete reusable arithmetic cycle. -/
set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unusedSimpArgs false
namespace PCJ9eff70d512234a4c_Fixed.Materializer.ReusableNative
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairOrdinary.RecoveryRootRound

def keep (i : Fin 32) : Bool := decide (i=13 ∨ i=24 ∨ i=26 ∨ i=27)
def scratch : Fin 28 → Fin 32 := ![0,1,2,3,4,5,6,7,8,9,10,11,12,14,15,16,17,18,19,20,21,22,23,25,28,29,30,31]
def eraseSlots (i : Fin 30) : Fin 36 :=
  Fin.addCases (fun j : Fin 28=>(scratch j).castAdd 4) (![34,35] : Fin 2 → Fin 36) i
noncomputable def eraseMachine := RecoveryFocus.machine eraseSlots (RecoveryScratchErase.resetMachine 28)
def cleared (R : Nat) (a : Fin 32 → List Bool) (i : Fin 32) : List Bool :=
  if keep i then a i else List.replicate R false

theorem erase_step (R : Nat) (a : Fin 32 → List Bool) (ha : ∀ i,(a i).length≤R) :
    Step eraseMachine (2*R+4) heads (bank R a) heads (bank R (cleared R a)) := by
  obtain ⟨r,hr,ht,hh,hs⟩ := RecoveryScratchErase.erase_ready R (R+3)
    (fun j : Fin 28=>a (scratch j)) (fun j=>ha (scratch j))
  have small : Step (RecoveryScratchErase.resetMachine 28) (2*R+4)
      (fun _=>0) _ (fun _=>0) _ := ⟨r,hr,funext hh,ht,hs.le⟩
  apply PhysicalFocusBoundary.focus small eraseSlots (by decide) heads heads
    (bank R a) (bank R (cleared R a))
  · intro i;fin_cases i <;>rfl
  · intro i;fin_cases i <;>rfl
  · intro i;fin_cases i <;>rfl
  · intro i;fin_cases i <;>simp [eraseSlots,scratch,bank,cleared,keep,Fin.addCases,Nat.max_eq_left (by omega : R+1≤R+3)]
  · intro i away
    refine ⟨rfl,?_⟩
    fin_cases i <;> try rfl
    all_goals first
      | exact False.elim (away 0 rfl)
      | exact False.elim (away 1 rfl)
      | exact False.elim (away 2 rfl)
      | exact False.elim (away 3 rfl)
      | exact False.elim (away 4 rfl)
      | exact False.elim (away 5 rfl)
      | exact False.elim (away 6 rfl)
      | exact False.elim (away 7 rfl)
      | exact False.elim (away 8 rfl)
      | exact False.elim (away 9 rfl)
      | exact False.elim (away 10 rfl)
      | exact False.elim (away 11 rfl)
      | exact False.elim (away 12 rfl)
      | exact False.elim (away 13 rfl)
      | exact False.elim (away 14 rfl)
      | exact False.elim (away 15 rfl)
      | exact False.elim (away 16 rfl)
      | exact False.elim (away 17 rfl)
      | exact False.elim (away 18 rfl)
      | exact False.elim (away 19 rfl)
      | exact False.elim (away 20 rfl)
      | exact False.elim (away 21 rfl)
      | exact False.elim (away 22 rfl)
      | exact False.elim (away 23 rfl)
      | exact False.elim (away 24 rfl)
      | exact False.elim (away 25 rfl)
      | exact False.elim (away 26 rfl)
      | exact False.elim (away 27 rfl)

def result (R : Nat) (a : Fin 32 → List Bool) : Fin 32 → List Bool :=
  cleared R (replaced (replaced a 20 26) 21 27)

noncomputable def machine {s : Nat} (p : Machine 32 s) :=
  Composition.machine (Composition.machine (Composition.machine (worker p)
    (copyMachine 20 26)) (copyMachine 21 27)) eraseMachine
def budget (fuel R : Nat) := 2*fuel+6*R+17

/-- A literal full-bank reusable transaction. Both copies and the sweep are
paid ordinary executions; all reserved backing remains allocated on exit. -/
theorem run {s fuel R : Nat} {p : Machine 32 s}
    {a b : Fin 32 → List Bool} {h : Fin 32 → Nat}
    (hp : Step p fuel localHeads a h b) (ha : ∀ i,(a i).length≤R) (hcap : fuel+3≤R) :
    Step (machine p) (budget fuel R) heads (bank R (padded R a))
      heads (bank R (result R (padded R b))) := by
  have fits := output_fits hp ha hcap
  have first := worker_step hp hcap
  have second := copy_step R (padded R b) 20 26 (by decide) (fits _) (fits _)
  have third := copy_step R (replaced (padded R b) 20 26) 21 27 (by decide)
    (by simpa [replaced] using fits 21) (by simpa [replaced] using fits 27)
  have fourth := erase_step R (replaced (replaced (padded R b) 20 26) 21 27) (by
    intro i
    by_cases h27 : i=27
    · subst i;simpa [replaced] using (fits 21).le
    by_cases h26 : i=26
    · subst i;simpa [replaced] using (fits 20).le
    simpa [replaced,h27,h26] using (fits i).le)
  have whole := ((first.seq second).seq third).seq fourth
  convert whole using 1 <;> first | rfl | (unfold budget;omega)

end PCJ9eff70d512234a4c_Fixed.Materializer.ReusableNative

import Proof.Packets.PacketsRoot

set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unusedSimpArgs false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false

namespace NearCubicWires.PacketsGlue.WinSum
open NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.RepairOrdinary.RecoveryExecution NearCubicWires.ExtDecompositionBatch
open NearCubicWires.PacketsGlue.CeilSqrt (read_rep write_rep)

def nw : Fin 5 → Option Bool := fun _ => none

def act (q : Fin 22) (w : Fin 5 → Option Bool) (m : Fin 5 → HeadMove) : Option (Action 5 22) :=
  some ⟨q, w, m⟩

def machine : Machine 5 22 where
  descriptionBits := 0
  start := 0
  halted := fun q => q.val == 21
  rule := fun q b =>
    if q.val = 0 then act 1 ![none, none, none, some false, some false] ![.stay, .stay, .stay, .right, .stay]
    else if q.val = 1 then (if b 1 then act 1 ![none, none, none, some true, none] ![.stay, .right, .stay, .right, .stay]
      else act 2 nw ![.stay, .stay, .stay, .left, .stay])
    else if q.val = 2 then (if b 3 then act 2 nw ![.stay, .stay, .stay, .left, .stay]
      else act 3 nw ![.stay, .stay, .stay, .stay, .stay])
    else if q.val = 3 then (if b 0 then act 6 nw ![.right, .stay, .stay, .right, .stay]
      else act 21 nw ![.stay, .stay, .stay, .stay, .stay])
    else if q.val = 4 then (if b 0 then act 7 nw ![.right, .stay, .stay, .right, .stay]
      else act 21 nw ![.stay, .stay, .stay, .stay, .stay])
    else if q.val = 5 then (if b 0 then act 8 nw ![.right, .stay, .stay, .right, .stay]
      else act 21 nw ![.stay, .stay, .stay, .stay, .stay])
    else if q.val = 6 then (if b 3 then act 6 ![none, none, some true, none, none] ![.stay, .stay, .right, .right, .stay]
      else act 9 nw ![.stay, .stay, .stay, .left, .stay])
    else if q.val = 7 then (if b 3 then act 7 ![none, none, some true, none, none] ![.stay, .stay, .right, .right, .stay]
      else act 10 nw ![.stay, .stay, .stay, .left, .stay])
    else if q.val = 8 then (if b 3 then act 8 ![none, none, some true, none, none] ![.stay, .stay, .right, .right, .stay]
      else act 11 nw ![.stay, .stay, .stay, .left, .stay])
    else if q.val = 9 then (if b 3 then act 9 nw ![.stay, .stay, .stay, .left, .stay]
      else act 4 nw ![.stay, .stay, .stay, .stay, .stay])
    else if q.val = 10 then (if b 3 then act 10 nw ![.stay, .stay, .stay, .left, .stay]
      else act 5 nw ![.stay, .stay, .stay, .stay, .stay])
    else if q.val = 11 then (if b 3 then act 11 nw ![.stay, .stay, .stay, .left, .stay]
      else act 12 nw ![.stay, .stay, .stay, .stay, .stay])
    else if q.val = 12 then act 13 nw ![.stay, .stay, .stay, .right, .right]
    else if q.val = 13 then (if b 3 then act 13 ![none, none, none, none, some true] ![.stay, .stay, .stay, .right, .right]
      else act 14 nw ![.stay, .stay, .stay, .left, .stay])
    else if q.val = 14 then act 15 nw ![.stay, .stay, .stay, .stay, .left]
    else if q.val = 15 then (if b 4 then act 15 nw ![.stay, .stay, .stay, .stay, .left]
      else act 16 nw ![.stay, .stay, .stay, .stay, .right])
    else if q.val = 16 then (if b 4 then act 17 nw ![.stay, .stay, .stay, .stay, .right]
      else act 18 nw ![.stay, .stay, .stay, .stay, .stay])
    else if q.val = 17 then (if b 4 then act 16 ![none, none, none, some false, none] ![.stay, .stay, .stay, .left, .right]
      else act 18 nw ![.stay, .stay, .stay, .stay, .stay])
    else if q.val = 18 then act 19 nw ![.stay, .stay, .stay, .stay, .left]
    else if q.val = 19 then (if b 4 then act 19 ![none, none, none, none, some false] ![.stay, .stay, .stay, .stay, .left]
      else act 20 nw ![.stay, .stay, .stay, .stay, .stay])
    else if q.val = 20 then (if b 3 then act 20 nw ![.stay, .stay, .stay, .left, .stay]
      else act 3 nw ![.stay, .stay, .stay, .stay, .stay])
    else none

def cfg (q : Fin 22) (Dt : List Bool) (dh : ℕ) (Rt : List Bool) (rh : ℕ) (Ac : List Bool) (ah : ℕ)
    (H : List Bool) (hh : ℕ) (G : List Bool) (gh : ℕ) : Configuration 5 22 :=
  ⟨q, ![dh, rh, ah, hh, gh], ![Dt, Rt, Ac, H, G]⟩

section Steps
variable (Dt : List Bool) (dh : ℕ) (Rt : List Bool) (rh : ℕ) (Ac : List Bool) (ah : ℕ)
  (H : List Bool) (hh : ℕ) (G : List Bool) (gh : ℕ)

theorem s0 :
    step machine (cfg 0 Dt dh Rt rh Ac ah H hh G gh) = some (cfg 1 Dt dh Rt rh Ac ah (writeTapeBit H hh false) (hh + 1) (writeTapeBit G gh false) gh) := by
  simp [step, machine, cfg, act]
  apply configuration_ext
  · rfl
  · funext i; fin_cases i <;> simp [applyAction, HeadMove.apply]
  · funext i; fin_cases i <;> simp [applyAction, nw]

theorem s1t (h : readTapeBit Rt rh = true) :
    step machine (cfg 1 Dt dh Rt rh Ac ah H hh G gh) = some (cfg 1 Dt dh Rt (rh + 1) Ac ah (writeTapeBit H hh true) (hh + 1) G gh) := by
  simp [step, machine, cfg, act, Configuration.scanned, h]
  apply configuration_ext
  · rfl
  · funext i; fin_cases i <;> simp [applyAction, HeadMove.apply]
  · funext i; fin_cases i <;> simp [applyAction, nw]

theorem s1f (h : readTapeBit Rt rh = false) :
    step machine (cfg 1 Dt dh Rt rh Ac ah H hh G gh) = some (cfg 2 Dt dh Rt rh Ac ah H (hh - 1) G gh) := by
  simp [step, machine, cfg, act, Configuration.scanned, h]
  apply configuration_ext
  · rfl
  · funext i; fin_cases i <;> simp [applyAction, HeadMove.apply]
  · funext i; fin_cases i <;> simp [applyAction, nw]

theorem s2t (h : readTapeBit H hh = true) :
    step machine (cfg 2 Dt dh Rt rh Ac ah H hh G gh) = some (cfg 2 Dt dh Rt rh Ac ah H (hh - 1) G gh) := by
  simp [step, machine, cfg, act, Configuration.scanned, h]
  apply configuration_ext
  · rfl
  · funext i; fin_cases i <;> simp [applyAction, HeadMove.apply]
  · funext i; fin_cases i <;> simp [applyAction, nw]

theorem s2f (h : readTapeBit H hh = false) :
    step machine (cfg 2 Dt dh Rt rh Ac ah H hh G gh) = some (cfg 3 Dt dh Rt rh Ac ah H hh G gh) := by
  simp [step, machine, cfg, act, Configuration.scanned, h]
  apply configuration_ext
  · rfl
  · funext i; fin_cases i <;> simp [applyAction, HeadMove.apply]
  · funext i; fin_cases i <;> simp [applyAction, nw]

theorem s3t (h : readTapeBit Dt dh = true) :
    step machine (cfg 3 Dt dh Rt rh Ac ah H hh G gh) = some (cfg 6 Dt (dh + 1) Rt rh Ac ah H (hh + 1) G gh) := by
  simp [step, machine, cfg, act, Configuration.scanned, h]
  apply configuration_ext
  · rfl
  · funext i; fin_cases i <;> simp [applyAction, HeadMove.apply]
  · funext i; fin_cases i <;> simp [applyAction, nw]

theorem s3f (h : readTapeBit Dt dh = false) :
    step machine (cfg 3 Dt dh Rt rh Ac ah H hh G gh) = some (cfg 21 Dt dh Rt rh Ac ah H hh G gh) := by
  simp [step, machine, cfg, act, Configuration.scanned, h]
  apply configuration_ext
  · rfl
  · funext i; fin_cases i <;> simp [applyAction, HeadMove.apply]
  · funext i; fin_cases i <;> simp [applyAction, nw]

theorem s4t (h : readTapeBit Dt dh = true) :
    step machine (cfg 4 Dt dh Rt rh Ac ah H hh G gh) = some (cfg 7 Dt (dh + 1) Rt rh Ac ah H (hh + 1) G gh) := by
  simp [step, machine, cfg, act, Configuration.scanned, h]
  apply configuration_ext
  · rfl
  · funext i; fin_cases i <;> simp [applyAction, HeadMove.apply]
  · funext i; fin_cases i <;> simp [applyAction, nw]

theorem s4f (h : readTapeBit Dt dh = false) :
    step machine (cfg 4 Dt dh Rt rh Ac ah H hh G gh) = some (cfg 21 Dt dh Rt rh Ac ah H hh G gh) := by
  simp [step, machine, cfg, act, Configuration.scanned, h]
  apply configuration_ext
  · rfl
  · funext i; fin_cases i <;> simp [applyAction, HeadMove.apply]
  · funext i; fin_cases i <;> simp [applyAction, nw]

theorem s5t (h : readTapeBit Dt dh = true) :
    step machine (cfg 5 Dt dh Rt rh Ac ah H hh G gh) = some (cfg 8 Dt (dh + 1) Rt rh Ac ah H (hh + 1) G gh) := by
  simp [step, machine, cfg, act, Configuration.scanned, h]
  apply configuration_ext
  · rfl
  · funext i; fin_cases i <;> simp [applyAction, HeadMove.apply]
  · funext i; fin_cases i <;> simp [applyAction, nw]

theorem s5f (h : readTapeBit Dt dh = false) :
    step machine (cfg 5 Dt dh Rt rh Ac ah H hh G gh) = some (cfg 21 Dt dh Rt rh Ac ah H hh G gh) := by
  simp [step, machine, cfg, act, Configuration.scanned, h]
  apply configuration_ext
  · rfl
  · funext i; fin_cases i <;> simp [applyAction, HeadMove.apply]
  · funext i; fin_cases i <;> simp [applyAction, nw]

theorem s6t (h : readTapeBit H hh = true) :
    step machine (cfg 6 Dt dh Rt rh Ac ah H hh G gh) = some (cfg 6 Dt dh Rt rh (writeTapeBit Ac ah true) (ah + 1) H (hh + 1) G gh) := by
  simp [step, machine, cfg, act, Configuration.scanned, h]
  apply configuration_ext
  · rfl
  · funext i; fin_cases i <;> simp [applyAction, HeadMove.apply]
  · funext i; fin_cases i <;> simp [applyAction, nw]

theorem s6f (h : readTapeBit H hh = false) :
    step machine (cfg 6 Dt dh Rt rh Ac ah H hh G gh) = some (cfg 9 Dt dh Rt rh Ac ah H (hh - 1) G gh) := by
  simp [step, machine, cfg, act, Configuration.scanned, h]
  apply configuration_ext
  · rfl
  · funext i; fin_cases i <;> simp [applyAction, HeadMove.apply]
  · funext i; fin_cases i <;> simp [applyAction, nw]

theorem s7t (h : readTapeBit H hh = true) :
    step machine (cfg 7 Dt dh Rt rh Ac ah H hh G gh) = some (cfg 7 Dt dh Rt rh (writeTapeBit Ac ah true) (ah + 1) H (hh + 1) G gh) := by
  simp [step, machine, cfg, act, Configuration.scanned, h]
  apply configuration_ext
  · rfl
  · funext i; fin_cases i <;> simp [applyAction, HeadMove.apply]
  · funext i; fin_cases i <;> simp [applyAction, nw]

theorem s7f (h : readTapeBit H hh = false) :
    step machine (cfg 7 Dt dh Rt rh Ac ah H hh G gh) = some (cfg 10 Dt dh Rt rh Ac ah H (hh - 1) G gh) := by
  simp [step, machine, cfg, act, Configuration.scanned, h]
  apply configuration_ext
  · rfl
  · funext i; fin_cases i <;> simp [applyAction, HeadMove.apply]
  · funext i; fin_cases i <;> simp [applyAction, nw]

theorem s8t (h : readTapeBit H hh = true) :
    step machine (cfg 8 Dt dh Rt rh Ac ah H hh G gh) = some (cfg 8 Dt dh Rt rh (writeTapeBit Ac ah true) (ah + 1) H (hh + 1) G gh) := by
  simp [step, machine, cfg, act, Configuration.scanned, h]
  apply configuration_ext
  · rfl
  · funext i; fin_cases i <;> simp [applyAction, HeadMove.apply]
  · funext i; fin_cases i <;> simp [applyAction, nw]

theorem s8f (h : readTapeBit H hh = false) :
    step machine (cfg 8 Dt dh Rt rh Ac ah H hh G gh) = some (cfg 11 Dt dh Rt rh Ac ah H (hh - 1) G gh) := by
  simp [step, machine, cfg, act, Configuration.scanned, h]
  apply configuration_ext
  · rfl
  · funext i; fin_cases i <;> simp [applyAction, HeadMove.apply]
  · funext i; fin_cases i <;> simp [applyAction, nw]

theorem s9t (h : readTapeBit H hh = true) :
    step machine (cfg 9 Dt dh Rt rh Ac ah H hh G gh) = some (cfg 9 Dt dh Rt rh Ac ah H (hh - 1) G gh) := by
  simp [step, machine, cfg, act, Configuration.scanned, h]
  apply configuration_ext
  · rfl
  · funext i; fin_cases i <;> simp [applyAction, HeadMove.apply]
  · funext i; fin_cases i <;> simp [applyAction, nw]

theorem s9f (h : readTapeBit H hh = false) :
    step machine (cfg 9 Dt dh Rt rh Ac ah H hh G gh) = some (cfg 4 Dt dh Rt rh Ac ah H hh G gh) := by
  simp [step, machine, cfg, act, Configuration.scanned, h]
  apply configuration_ext
  · rfl
  · funext i; fin_cases i <;> simp [applyAction, HeadMove.apply]
  · funext i; fin_cases i <;> simp [applyAction, nw]

theorem s10t (h : readTapeBit H hh = true) :
    step machine (cfg 10 Dt dh Rt rh Ac ah H hh G gh) = some (cfg 10 Dt dh Rt rh Ac ah H (hh - 1) G gh) := by
  simp [step, machine, cfg, act, Configuration.scanned, h]
  apply configuration_ext
  · rfl
  · funext i; fin_cases i <;> simp [applyAction, HeadMove.apply]
  · funext i; fin_cases i <;> simp [applyAction, nw]

theorem s10f (h : readTapeBit H hh = false) :
    step machine (cfg 10 Dt dh Rt rh Ac ah H hh G gh) = some (cfg 5 Dt dh Rt rh Ac ah H hh G gh) := by
  simp [step, machine, cfg, act, Configuration.scanned, h]
  apply configuration_ext
  · rfl
  · funext i; fin_cases i <;> simp [applyAction, HeadMove.apply]
  · funext i; fin_cases i <;> simp [applyAction, nw]

theorem s11t (h : readTapeBit H hh = true) :
    step machine (cfg 11 Dt dh Rt rh Ac ah H hh G gh) = some (cfg 11 Dt dh Rt rh Ac ah H (hh - 1) G gh) := by
  simp [step, machine, cfg, act, Configuration.scanned, h]
  apply configuration_ext
  · rfl
  · funext i; fin_cases i <;> simp [applyAction, HeadMove.apply]
  · funext i; fin_cases i <;> simp [applyAction, nw]

theorem s11f (h : readTapeBit H hh = false) :
    step machine (cfg 11 Dt dh Rt rh Ac ah H hh G gh) = some (cfg 12 Dt dh Rt rh Ac ah H hh G gh) := by
  simp [step, machine, cfg, act, Configuration.scanned, h]
  apply configuration_ext
  · rfl
  · funext i; fin_cases i <;> simp [applyAction, HeadMove.apply]
  · funext i; fin_cases i <;> simp [applyAction, nw]

theorem s12 :
    step machine (cfg 12 Dt dh Rt rh Ac ah H hh G gh) = some (cfg 13 Dt dh Rt rh Ac ah H (hh + 1) G (gh + 1)) := by
  simp [step, machine, cfg, act]
  apply configuration_ext
  · rfl
  · funext i; fin_cases i <;> simp [applyAction, HeadMove.apply]
  · funext i; fin_cases i <;> simp [applyAction, nw]

theorem s13t (h : readTapeBit H hh = true) :
    step machine (cfg 13 Dt dh Rt rh Ac ah H hh G gh) = some (cfg 13 Dt dh Rt rh Ac ah H (hh + 1) (writeTapeBit G gh true) (gh + 1)) := by
  simp [step, machine, cfg, act, Configuration.scanned, h]
  apply configuration_ext
  · rfl
  · funext i; fin_cases i <;> simp [applyAction, HeadMove.apply]
  · funext i; fin_cases i <;> simp [applyAction, nw]

theorem s13f (h : readTapeBit H hh = false) :
    step machine (cfg 13 Dt dh Rt rh Ac ah H hh G gh) = some (cfg 14 Dt dh Rt rh Ac ah H (hh - 1) G gh) := by
  simp [step, machine, cfg, act, Configuration.scanned, h]
  apply configuration_ext
  · rfl
  · funext i; fin_cases i <;> simp [applyAction, HeadMove.apply]
  · funext i; fin_cases i <;> simp [applyAction, nw]

theorem s14 :
    step machine (cfg 14 Dt dh Rt rh Ac ah H hh G gh) = some (cfg 15 Dt dh Rt rh Ac ah H hh G (gh - 1)) := by
  simp [step, machine, cfg, act]
  apply configuration_ext
  · rfl
  · funext i; fin_cases i <;> simp [applyAction, HeadMove.apply]
  · funext i; fin_cases i <;> simp [applyAction, nw]

theorem s15t (h : readTapeBit G gh = true) :
    step machine (cfg 15 Dt dh Rt rh Ac ah H hh G gh) = some (cfg 15 Dt dh Rt rh Ac ah H hh G (gh - 1)) := by
  simp [step, machine, cfg, act, Configuration.scanned, h]
  apply configuration_ext
  · rfl
  · funext i; fin_cases i <;> simp [applyAction, HeadMove.apply]
  · funext i; fin_cases i <;> simp [applyAction, nw]

theorem s15f (h : readTapeBit G gh = false) :
    step machine (cfg 15 Dt dh Rt rh Ac ah H hh G gh) = some (cfg 16 Dt dh Rt rh Ac ah H hh G (gh + 1)) := by
  simp [step, machine, cfg, act, Configuration.scanned, h]
  apply configuration_ext
  · rfl
  · funext i; fin_cases i <;> simp [applyAction, HeadMove.apply]
  · funext i; fin_cases i <;> simp [applyAction, nw]

theorem s16t (h : readTapeBit G gh = true) :
    step machine (cfg 16 Dt dh Rt rh Ac ah H hh G gh) = some (cfg 17 Dt dh Rt rh Ac ah H hh G (gh + 1)) := by
  simp [step, machine, cfg, act, Configuration.scanned, h]
  apply configuration_ext
  · rfl
  · funext i; fin_cases i <;> simp [applyAction, HeadMove.apply]
  · funext i; fin_cases i <;> simp [applyAction, nw]

theorem s16f (h : readTapeBit G gh = false) :
    step machine (cfg 16 Dt dh Rt rh Ac ah H hh G gh) = some (cfg 18 Dt dh Rt rh Ac ah H hh G gh) := by
  simp [step, machine, cfg, act, Configuration.scanned, h]
  apply configuration_ext
  · rfl
  · funext i; fin_cases i <;> simp [applyAction, HeadMove.apply]
  · funext i; fin_cases i <;> simp [applyAction, nw]

theorem s17t (h : readTapeBit G gh = true) :
    step machine (cfg 17 Dt dh Rt rh Ac ah H hh G gh) = some (cfg 16 Dt dh Rt rh Ac ah (writeTapeBit H hh false) (hh - 1) G (gh + 1)) := by
  simp [step, machine, cfg, act, Configuration.scanned, h]
  apply configuration_ext
  · rfl
  · funext i; fin_cases i <;> simp [applyAction, HeadMove.apply]
  · funext i; fin_cases i <;> simp [applyAction, nw]

theorem s17f (h : readTapeBit G gh = false) :
    step machine (cfg 17 Dt dh Rt rh Ac ah H hh G gh) = some (cfg 18 Dt dh Rt rh Ac ah H hh G gh) := by
  simp [step, machine, cfg, act, Configuration.scanned, h]
  apply configuration_ext
  · rfl
  · funext i; fin_cases i <;> simp [applyAction, HeadMove.apply]
  · funext i; fin_cases i <;> simp [applyAction, nw]

theorem s18 :
    step machine (cfg 18 Dt dh Rt rh Ac ah H hh G gh) = some (cfg 19 Dt dh Rt rh Ac ah H hh G (gh - 1)) := by
  simp [step, machine, cfg, act]
  apply configuration_ext
  · rfl
  · funext i; fin_cases i <;> simp [applyAction, HeadMove.apply]
  · funext i; fin_cases i <;> simp [applyAction, nw]

theorem s19t (h : readTapeBit G gh = true) :
    step machine (cfg 19 Dt dh Rt rh Ac ah H hh G gh) = some (cfg 19 Dt dh Rt rh Ac ah H hh (writeTapeBit G gh false) (gh - 1)) := by
  simp [step, machine, cfg, act, Configuration.scanned, h]
  apply configuration_ext
  · rfl
  · funext i; fin_cases i <;> simp [applyAction, HeadMove.apply]
  · funext i; fin_cases i <;> simp [applyAction, nw]

theorem s19f (h : readTapeBit G gh = false) :
    step machine (cfg 19 Dt dh Rt rh Ac ah H hh G gh) = some (cfg 20 Dt dh Rt rh Ac ah H hh G gh) := by
  simp [step, machine, cfg, act, Configuration.scanned, h]
  apply configuration_ext
  · rfl
  · funext i; fin_cases i <;> simp [applyAction, HeadMove.apply]
  · funext i; fin_cases i <;> simp [applyAction, nw]

theorem s20t (h : readTapeBit H hh = true) :
    step machine (cfg 20 Dt dh Rt rh Ac ah H hh G gh) = some (cfg 20 Dt dh Rt rh Ac ah H (hh - 1) G gh) := by
  simp [step, machine, cfg, act, Configuration.scanned, h]
  apply configuration_ext
  · rfl
  · funext i; fin_cases i <;> simp [applyAction, HeadMove.apply]
  · funext i; fin_cases i <;> simp [applyAction, nw]

theorem s20f (h : readTapeBit H hh = false) :
    step machine (cfg 20 Dt dh Rt rh Ac ah H hh G gh) = some (cfg 3 Dt dh Rt rh Ac ah H hh G gh) := by
  simp [step, machine, cfg, act, Configuration.scanned, h]
  apply configuration_ext
  · rfl
  · funext i; fin_cases i <;> simp [applyAction, HeadMove.apply]
  · funext i; fin_cases i <;> simp [applyAction, nw]

end Steps

/-! ## Tape shapes -/

/-- `false :: 1^a ++ 0^b`: the value `h` (or the halving scratch) with its sentinel. -/
def sh (a b : ℕ) : List Bool := false :: (List.replicate a true ++ List.replicate b false)

/-- A unary value. -/
def rp (n : ℕ) : List Bool := List.replicate n true

theorem read_sh (a b i : ℕ) : readTapeBit (sh a b) i = decide (1 ≤ i ∧ i ≤ a) := by
  cases i with
  | zero => rfl
  | succ i =>
    unfold sh readTapeBit
    simp only [List.getD_cons_succ]
    rw [List.getD_eq_getElem?_getD]
    by_cases h : i < a
    · rw [List.getElem?_append_left (by simpa using h)]
      simp [h] <;> omega
    · rw [List.getElem?_append_right (by simp; omega)]
      simp only [List.length_replicate]
      by_cases h2 : i - a < b
      · simp [h2] <;> omega
      · simp [h2] <;> omega

theorem read_rp (n i : ℕ) : readTapeBit (rp n) i = decide (i < n) := read_rep n i

theorem write_sh_t (a b : ℕ) : writeTapeBit (sh a b) (a + 1) true = sh (a + 1) (b - 1) := by
  have h := NatSum.write_tail (false :: List.replicate a true) b true
  simp only [List.length_cons, List.length_replicate] at h
  unfold sh
  rw [show false :: (List.replicate a true ++ List.replicate b false) =
    (false :: List.replicate a true) ++ List.replicate b false from rfl, h, List.replicate_succ']
  simp only [List.cons_append, List.append_assoc, List.singleton_append, List.nil_append]

theorem write_sh_f (a b : ℕ) : writeTapeBit (sh (a + 1) b) (a + 1) false = sh a (b + 1) := by
  have h := NatSum.write_mid (false :: List.replicate a true) true b false
  simp only [List.length_cons, List.length_replicate] at h
  unfold sh
  have e : false :: (List.replicate (a + 1) true ++ List.replicate b false) =
      (false :: List.replicate a true) ++ true :: List.replicate b false := by
    rw [List.replicate_succ', List.append_assoc, List.singleton_append]; rfl
  rw [e, h, List.replicate_succ]
  rfl

theorem rewind2 (Dt : List Bool) (dh : ℕ) (Rt : List Bool) (rh : ℕ) (Ac : List Bool) (ah : ℕ)
    (a b : ℕ) (G : List Bool) (gh : ℕ) : ∀ p : ℕ, p ≤ a →
    Timed machine (p + 1) (cfg 2 Dt dh Rt rh Ac ah (sh a b) p G gh) (cfg 3 Dt dh Rt rh Ac ah (sh a b) 0 G gh) := by
  intro p
  induction p with
  | zero =>
    intro _
    have h : readTapeBit (sh a b) 0 = false := rfl
    exact Timed.single (p := machine) (by rfl) (s2f Dt dh Rt rh Ac ah (sh a b) 0 G gh h)
  | succ p ih =>
    intro hp
    have h : readTapeBit (sh a b) (p + 1) = true := by rw [read_sh]; simp; omega
    have t1 := Timed.single (p := machine) (by rfl) (s2t Dt dh Rt rh Ac ah (sh a b) (p + 1) G gh h)
    rw [show p + 1 - 1 = p by omega] at t1
    have tt := t1.trans (ih (by omega))
    rw [show 1 + (p + 1) = p + 1 + 1 by omega] at tt
    exact tt

theorem rewind9 (Dt : List Bool) (dh : ℕ) (Rt : List Bool) (rh : ℕ) (Ac : List Bool) (ah : ℕ)
    (a b : ℕ) (G : List Bool) (gh : ℕ) : ∀ p : ℕ, p ≤ a →
    Timed machine (p + 1) (cfg 9 Dt dh Rt rh Ac ah (sh a b) p G gh) (cfg 4 Dt dh Rt rh Ac ah (sh a b) 0 G gh) := by
  intro p
  induction p with
  | zero =>
    intro _
    have h : readTapeBit (sh a b) 0 = false := rfl
    exact Timed.single (p := machine) (by rfl) (s9f Dt dh Rt rh Ac ah (sh a b) 0 G gh h)
  | succ p ih =>
    intro hp
    have h : readTapeBit (sh a b) (p + 1) = true := by rw [read_sh]; simp; omega
    have t1 := Timed.single (p := machine) (by rfl) (s9t Dt dh Rt rh Ac ah (sh a b) (p + 1) G gh h)
    rw [show p + 1 - 1 = p by omega] at t1
    have tt := t1.trans (ih (by omega))
    rw [show 1 + (p + 1) = p + 1 + 1 by omega] at tt
    exact tt

theorem rewind10 (Dt : List Bool) (dh : ℕ) (Rt : List Bool) (rh : ℕ) (Ac : List Bool) (ah : ℕ)
    (a b : ℕ) (G : List Bool) (gh : ℕ) : ∀ p : ℕ, p ≤ a →
    Timed machine (p + 1) (cfg 10 Dt dh Rt rh Ac ah (sh a b) p G gh) (cfg 5 Dt dh Rt rh Ac ah (sh a b) 0 G gh) := by
  intro p
  induction p with
  | zero =>
    intro _
    have h : readTapeBit (sh a b) 0 = false := rfl
    exact Timed.single (p := machine) (by rfl) (s10f Dt dh Rt rh Ac ah (sh a b) 0 G gh h)
  | succ p ih =>
    intro hp
    have h : readTapeBit (sh a b) (p + 1) = true := by rw [read_sh]; simp; omega
    have t1 := Timed.single (p := machine) (by rfl) (s10t Dt dh Rt rh Ac ah (sh a b) (p + 1) G gh h)
    rw [show p + 1 - 1 = p by omega] at t1
    have tt := t1.trans (ih (by omega))
    rw [show 1 + (p + 1) = p + 1 + 1 by omega] at tt
    exact tt

theorem rewind11 (Dt : List Bool) (dh : ℕ) (Rt : List Bool) (rh : ℕ) (Ac : List Bool) (ah : ℕ)
    (a b : ℕ) (G : List Bool) (gh : ℕ) : ∀ p : ℕ, p ≤ a →
    Timed machine (p + 1) (cfg 11 Dt dh Rt rh Ac ah (sh a b) p G gh) (cfg 12 Dt dh Rt rh Ac ah (sh a b) 0 G gh) := by
  intro p
  induction p with
  | zero =>
    intro _
    have h : readTapeBit (sh a b) 0 = false := rfl
    exact Timed.single (p := machine) (by rfl) (s11f Dt dh Rt rh Ac ah (sh a b) 0 G gh h)
  | succ p ih =>
    intro hp
    have h : readTapeBit (sh a b) (p + 1) = true := by rw [read_sh]; simp; omega
    have t1 := Timed.single (p := machine) (by rfl) (s11t Dt dh Rt rh Ac ah (sh a b) (p + 1) G gh h)
    rw [show p + 1 - 1 = p by omega] at t1
    have tt := t1.trans (ih (by omega))
    rw [show 1 + (p + 1) = p + 1 + 1 by omega] at tt
    exact tt

theorem rewind20 (Dt : List Bool) (dh : ℕ) (Rt : List Bool) (rh : ℕ) (Ac : List Bool) (ah : ℕ)
    (a b : ℕ) (G : List Bool) (gh : ℕ) : ∀ p : ℕ, p ≤ a →
    Timed machine (p + 1) (cfg 20 Dt dh Rt rh Ac ah (sh a b) p G gh) (cfg 3 Dt dh Rt rh Ac ah (sh a b) 0 G gh) := by
  intro p
  induction p with
  | zero =>
    intro _
    have h : readTapeBit (sh a b) 0 = false := rfl
    exact Timed.single (p := machine) (by rfl) (s20f Dt dh Rt rh Ac ah (sh a b) 0 G gh h)
  | succ p ih =>
    intro hp
    have h : readTapeBit (sh a b) (p + 1) = true := by rw [read_sh]; simp; omega
    have t1 := Timed.single (p := machine) (by rfl) (s20t Dt dh Rt rh Ac ah (sh a b) (p + 1) G gh h)
    rw [show p + 1 - 1 = p by omega] at t1
    have tt := t1.trans (ih (by omega))
    rw [show 1 + (p + 1) = p + 1 + 1 by omega] at tt
    exact tt

theorem append6 (Dt : List Bool) (dh : ℕ) (Rt : List Bool) (rh : ℕ) (s h z : ℕ) (G : List Bool) (gh : ℕ) :
    ∀ t j : ℕ, j + t = h →
    Timed machine t (cfg 6 Dt dh Rt rh (rp (s + j)) (s + j) (sh h z) (j + 1) G gh)
      (cfg 6 Dt dh Rt rh (rp (s + h)) (s + h) (sh h z) (h + 1) G gh) := by
  intro t
  induction t with
  | zero => intro j hj; rw [show j = h by omega]; exact Timed.refl _ _
  | succ t ih =>
    intro j hj
    have h1 : readTapeBit (sh h z) (j + 1) = true := by rw [read_sh]; simp; omega
    have t1 := Timed.single (p := machine) (by rfl) (s6t Dt dh Rt rh (rp (s + j)) (s + j) (sh h z) (j + 1) G gh h1)
    rw [show writeTapeBit (rp (s + j)) (s + j) true = rp (s + (j + 1)) by unfold rp; rw [write_rep]; rfl] at t1
    have t2 := ih (j + 1) (by omega)
    have tt := t1.trans t2
    rw [show 1 + t = t + 1 by omega] at tt
    exact tt

theorem append7 (Dt : List Bool) (dh : ℕ) (Rt : List Bool) (rh : ℕ) (s h z : ℕ) (G : List Bool) (gh : ℕ) :
    ∀ t j : ℕ, j + t = h →
    Timed machine t (cfg 7 Dt dh Rt rh (rp (s + j)) (s + j) (sh h z) (j + 1) G gh)
      (cfg 7 Dt dh Rt rh (rp (s + h)) (s + h) (sh h z) (h + 1) G gh) := by
  intro t
  induction t with
  | zero => intro j hj; rw [show j = h by omega]; exact Timed.refl _ _
  | succ t ih =>
    intro j hj
    have h1 : readTapeBit (sh h z) (j + 1) = true := by rw [read_sh]; simp; omega
    have t1 := Timed.single (p := machine) (by rfl) (s7t Dt dh Rt rh (rp (s + j)) (s + j) (sh h z) (j + 1) G gh h1)
    rw [show writeTapeBit (rp (s + j)) (s + j) true = rp (s + (j + 1)) by unfold rp; rw [write_rep]; rfl] at t1
    have t2 := ih (j + 1) (by omega)
    have tt := t1.trans t2
    rw [show 1 + t = t + 1 by omega] at tt
    exact tt

theorem append8 (Dt : List Bool) (dh : ℕ) (Rt : List Bool) (rh : ℕ) (s h z : ℕ) (G : List Bool) (gh : ℕ) :
    ∀ t j : ℕ, j + t = h →
    Timed machine t (cfg 8 Dt dh Rt rh (rp (s + j)) (s + j) (sh h z) (j + 1) G gh)
      (cfg 8 Dt dh Rt rh (rp (s + h)) (s + h) (sh h z) (h + 1) G gh) := by
  intro t
  induction t with
  | zero => intro j hj; rw [show j = h by omega]; exact Timed.refl _ _
  | succ t ih =>
    intro j hj
    have h1 : readTapeBit (sh h z) (j + 1) = true := by rw [read_sh]; simp; omega
    have t1 := Timed.single (p := machine) (by rfl) (s8t Dt dh Rt rh (rp (s + j)) (s + j) (sh h z) (j + 1) G gh h1)
    rw [show writeTapeBit (rp (s + j)) (s + j) true = rp (s + (j + 1)) by unfold rp; rw [write_rep]; rfl] at t1
    have t2 := ih (j + 1) (by omega)
    have tt := t1.trans t2
    rw [show 1 + t = t + 1 by omega] at tt
    exact tt

/-! ## The inner loops -/

theorem copyRoot (D ρ : ℕ) : ∀ t j : ℕ, j + t = ρ →
    Timed machine t (cfg 1 (rp D) 0 (rp ρ) j [] 0 (sh j 0) (j + 1) (sh 0 0) 0)
      (cfg 1 (rp D) 0 (rp ρ) ρ [] 0 (sh ρ 0) (ρ + 1) (sh 0 0) 0) := by
  intro t
  induction t with
  | zero => intro j hj; rw [show j = ρ by omega]; exact Timed.refl _ _
  | succ t ih =>
    intro j hj
    have h1 : readTapeBit (rp ρ) j = true := by rw [read_rp]; simp; omega
    have t1 := Timed.single (p := machine) (by rfl) (s1t (rp D) 0 (rp ρ) j [] 0 (sh j 0) (j + 1) (sh 0 0) 0 h1)
    rw [write_sh_t] at t1
    have t2 := ih (j + 1) (by omega)
    have tt := t1.trans t2
    rw [show 1 + t = t + 1 by omega] at tt
    exact tt

theorem copyG (Dt : List Bool) (dh : ℕ) (Rt : List Bool) (rh : ℕ) (Ac : List Bool) (ah : ℕ) (h z g : ℕ) :
    ∀ t j : ℕ, j + t = h →
    Timed machine t (cfg 13 Dt dh Rt rh Ac ah (sh h z) (j + 1) (sh j (g - j)) (j + 1))
      (cfg 13 Dt dh Rt rh Ac ah (sh h z) (h + 1) (sh h (g - h)) (h + 1)) := by
  intro t
  induction t with
  | zero => intro j hj; rw [show j = h by omega]; exact Timed.refl _ _
  | succ t ih =>
    intro j hj
    have h1 : readTapeBit (sh h z) (j + 1) = true := by rw [read_sh]; simp; omega
    have t1 := Timed.single (p := machine) (by rfl)
      (s13t Dt dh Rt rh Ac ah (sh h z) (j + 1) (sh j (g - j)) (j + 1) h1)
    rw [write_sh_t, show g - j - 1 = g - (j + 1) by omega] at t1
    have t2 := ih (j + 1) (by omega)
    have tt := t1.trans t2
    rw [show 1 + t = t + 1 by omega] at tt
    exact tt

theorem rewindG (Dt : List Bool) (dh : ℕ) (Rt : List Bool) (rh : ℕ) (Ac : List Bool) (ah : ℕ)
    (H : List Bool) (hh a b : ℕ) : ∀ p : ℕ, p ≤ a →
    Timed machine (p + 1) (cfg 15 Dt dh Rt rh Ac ah H hh (sh a b) p) (cfg 16 Dt dh Rt rh Ac ah H hh (sh a b) 1) := by
  intro p
  induction p with
  | zero =>
    intro _
    have h : readTapeBit (sh a b) 0 = false := rfl
    exact Timed.single (p := machine) (by rfl) (s15f Dt dh Rt rh Ac ah H hh (sh a b) 0 h)
  | succ p ih =>
    intro hp
    have h : readTapeBit (sh a b) (p + 1) = true := by rw [read_sh]; simp; omega
    have t1 := Timed.single (p := machine) (by rfl) (s15t Dt dh Rt rh Ac ah H hh (sh a b) (p + 1) h)
    rw [show p + 1 - 1 = p by omega] at t1
    have tt := t1.trans (ih (by omega))
    rw [show 1 + (p + 1) = p + 1 + 1 by omega] at tt
    exact tt

theorem pairs (Dt : List Bool) (dh : ℕ) (Rt : List Bool) (rh : ℕ) (Ac : List Bool) (ah : ℕ) (h z b : ℕ) :
    ∀ n t : ℕ, t + n = h / 2 →
    Timed machine (2 * n) (cfg 16 Dt dh Rt rh Ac ah (sh (h - t) (z + t)) (h - t) (sh h b) (2 * t + 1))
      (cfg 16 Dt dh Rt rh Ac ah (sh (h - h / 2) (z + h / 2)) (h - h / 2) (sh h b) (2 * (h / 2) + 1)) := by
  intro n
  induction n with
  | zero => intro t ht; rw [show t = h / 2 by omega]; exact Timed.refl _ _
  | succ n ih =>
    intro t ht
    have h1 : readTapeBit (sh h b) (2 * t + 1) = true := by rw [read_sh]; simp; omega
    have t1 := Timed.single (p := machine) (by rfl)
      (s16t Dt dh Rt rh Ac ah (sh (h - t) (z + t)) (h - t) (sh h b) (2 * t + 1) h1)
    have h2 : readTapeBit (sh h b) (2 * t + 1 + 1) = true := by rw [read_sh]; simp; omega
    have e1 : h - t = (h - (t + 1)) + 1 := by omega
    have t2 := Timed.single (p := machine) (by rfl)
      (s17t Dt dh Rt rh Ac ah (sh (h - (t + 1) + 1) (z + t)) (h - (t + 1) + 1) (sh h b) (2 * t + 1 + 1) h2)
    rw [write_sh_f, show z + t + 1 = z + (t + 1) by omega, show h - (t + 1) + 1 - 1 = h - (t + 1) by omega,
      show 2 * t + 1 + 1 + 1 = 2 * (t + 1) + 1 by omega] at t2
    have t2' : Timed machine 1 (cfg 17 Dt dh Rt rh Ac ah (sh (h - t) (z + t)) (h - t) (sh h b) (2 * t + 1 + 1))
        (cfg 16 Dt dh Rt rh Ac ah (sh (h - (t + 1)) (z + (t + 1))) (h - (t + 1)) (sh h b) (2 * (t + 1) + 1)) := by
      rw [e1]; exact t2
    have t3 := ih (t + 1) (by omega)
    have tt := (t1.trans t2').trans t3
    rw [show 1 + 1 + 2 * n = 2 * (n + 1) by omega] at tt
    exact tt

theorem pairsEnd (Dt : List Bool) (dh : ℕ) (Rt : List Bool) (rh : ℕ) (Ac : List Bool) (ah : ℕ)
    (H : List Bool) (hh h b : ℕ) :
    ∃ e : ℕ, e ≤ 2 ∧ Timed machine e (cfg 16 Dt dh Rt rh Ac ah H hh (sh h b) (2 * (h / 2) + 1))
      (cfg 18 Dt dh Rt rh Ac ah H hh (sh h b) (h + 1)) := by
  rcases Nat.even_or_odd h with ⟨k, hk⟩ | ⟨k, hk⟩
  · have e : 2 * (h / 2) + 1 = h + 1 := by omega
    have hf : readTapeBit (sh h b) (h + 1) = false := by rw [read_sh]; simp
    refine ⟨1, by omega, ?_⟩
    rw [e]
    exact Timed.single (p := machine) (by rfl) (s16f Dt dh Rt rh Ac ah H hh (sh h b) (h + 1) hf)
  · have e : 2 * (h / 2) + 1 = h := by omega
    have ht : readTapeBit (sh h b) h = true := by rw [read_sh]; simp; omega
    have hf : readTapeBit (sh h b) (h + 1) = false := by rw [read_sh]; simp
    refine ⟨2, by omega, ?_⟩
    rw [e]
    have t1 := Timed.single (p := machine) (by rfl) (s16t Dt dh Rt rh Ac ah H hh (sh h b) h ht)
    have t2 := Timed.single (p := machine) (by rfl) (s17f Dt dh Rt rh Ac ah H hh (sh h b) (h + 1) hf)
    exact t1.trans t2

theorem eraseG (Dt : List Bool) (dh : ℕ) (Rt : List Bool) (rh : ℕ) (Ac : List Bool) (ah : ℕ)
    (H : List Bool) (hh b : ℕ) : ∀ p : ℕ,
    Timed machine (p + 1) (cfg 19 Dt dh Rt rh Ac ah H hh (sh p b) p) (cfg 20 Dt dh Rt rh Ac ah H hh (sh 0 (b + p)) 0) := by
  intro p
  induction p generalizing b with
  | zero =>
    have h : readTapeBit (sh 0 b) 0 = false := rfl
    exact Timed.single (p := machine) (by rfl) (s19f Dt dh Rt rh Ac ah H hh (sh 0 b) 0 h)
  | succ p ih =>
    have h : readTapeBit (sh (p + 1) b) (p + 1) = true := by rw [read_sh]; simp
    have t1 := Timed.single (p := machine) (by rfl) (s19t Dt dh Rt rh Ac ah H hh (sh (p + 1) b) (p + 1) h)
    rw [write_sh_f, show p + 1 - 1 = p by omega] at t1
    have tt := t1.trans (ih (b + 1))
    rw [show 1 + (p + 1) = p + 1 + 1 by omega, show b + 1 + p = b + (p + 1) by omega] at tt
    exact tt

theorem tc {n n' : ℕ} {c c' d d' : Configuration 5 22} (h : Timed machine n c d)
    (hn : n = n') (hc : c = c') (hd : d = d') : Timed machine n' c' d' := by
  subst hn hc hd
  exact h

/-- **Halving `h` in place**: `sh h z ↦ sh (h - h/2) (z + h/2)`, the scratch erased. -/
theorem halve (Dt : List Bool) (dh : ℕ) (Rt : List Bool) (rh : ℕ) (Ac : List Bool) (ah : ℕ) (h z g : ℕ) :
    ∃ T g' : ℕ, T ≤ 5 * h + 12 ∧
      Timed machine T (cfg 12 Dt dh Rt rh Ac ah (sh h z) 0 (sh 0 g) 0)
        (cfg 3 Dt dh Rt rh Ac ah (sh (h - h / 2) (z + h / 2)) 0 (sh 0 g') 0) := by
  have t1 := Timed.single (p := machine) (by rfl) (s12 Dt dh Rt rh Ac ah (sh h z) 0 (sh 0 g) 0)
  have t2 := copyG Dt dh Rt rh Ac ah h z g h 0 (by omega)
  have hf : readTapeBit (sh h z) (h + 1) = false := by rw [read_sh]; simp
  have t3 := Timed.single (p := machine) (by rfl)
    (s13f Dt dh Rt rh Ac ah (sh h z) (h + 1) (sh h (g - h)) (h + 1) hf)
  have t4 := Timed.single (p := machine) (by rfl)
    (s14 Dt dh Rt rh Ac ah (sh h z) h (sh h (g - h)) (h + 1))
  have t5 := rewindG Dt dh Rt rh Ac ah (sh h z) h h (g - h) h (le_refl _)
  have t6 := pairs Dt dh Rt rh Ac ah h z (g - h) (h / 2) 0 (by omega)
  obtain ⟨e, he, t7⟩ := pairsEnd Dt dh Rt rh Ac ah (sh (h - h / 2) (z + h / 2)) (h - h / 2) h (g - h)
  have t8 := Timed.single (p := machine) (by rfl)
    (s18 Dt dh Rt rh Ac ah (sh (h - h / 2) (z + h / 2)) (h - h / 2) (sh h (g - h)) (h + 1))
  have t9 := eraseG Dt dh Rt rh Ac ah (sh (h - h / 2) (z + h / 2)) (h - h / 2) (g - h) h
  have t10 := rewind20 Dt dh Rt rh Ac ah (h - h / 2) (z + h / 2) (sh 0 (g - h + h)) 0 (h - h / 2) (le_refl _)
  have a12 := tc t1 rfl rfl (show cfg 13 Dt dh Rt rh Ac ah (sh h z) (0 + 1) (sh 0 g) (0 + 1) =
    cfg 13 Dt dh Rt rh Ac ah (sh h z) (0 + 1) (sh 0 (g - 0)) (0 + 1) by simp)
  have a3 := tc t3 rfl rfl (show cfg 14 Dt dh Rt rh Ac ah (sh h z) (h + 1 - 1) (sh h (g - h)) (h + 1) =
    cfg 14 Dt dh Rt rh Ac ah (sh h z) h (sh h (g - h)) (h + 1) by simp)
  have a4 := tc t4 rfl rfl (show cfg 15 Dt dh Rt rh Ac ah (sh h z) h (sh h (g - h)) (h + 1 - 1) =
    cfg 15 Dt dh Rt rh Ac ah (sh h z) h (sh h (g - h)) h by simp)
  have a6 := tc t6 rfl (show cfg 16 Dt dh Rt rh Ac ah (sh (h - 0) (z + 0)) (h - 0) (sh h (g - h)) (2 * 0 + 1) =
    cfg 16 Dt dh Rt rh Ac ah (sh h z) h (sh h (g - h)) 1 by simp) rfl
  have a8 := tc t8 rfl rfl (show cfg 19 Dt dh Rt rh Ac ah (sh (h - h / 2) (z + h / 2)) (h - h / 2) (sh h (g - h)) (h + 1 - 1) =
    cfg 19 Dt dh Rt rh Ac ah (sh (h - h / 2) (z + h / 2)) (h - h / 2) (sh h (g - h)) h by simp)
  have tt := (((((((((a12.trans t2).trans a3).trans a4).trans t5).trans a6).trans t7).trans a8).trans t9).trans t10)
  refine ⟨_, g - h + h, ?_, tt⟩
  omega

/-! ## One level -/

/-- A level at phase 0 or 1: append `h`, keep it. -/
theorem level01 (D ρ l s h z g : ℕ) (hl : l < D) (v : ℕ) (hv : v < 2) :
    Timed machine (2 * h + 3)
      (cfg ⟨3 + v, by omega⟩ (rp D) l (rp ρ) ρ (rp s) s (sh h z) 0 (sh 0 g) 0)
      (cfg ⟨4 + v, by omega⟩ (rp D) (l + 1) (rp ρ) ρ (rp (s + h)) (s + h) (sh h z) 0 (sh 0 g) 0) := by
  have hD : readTapeBit (rp D) l = true := by rw [read_rp]; simp; omega
  rcases (show v = 0 ∨ v = 1 by omega) with rfl | rfl
  · have t1 := Timed.single (p := machine) (by rfl) (s3t (rp D) l (rp ρ) ρ (rp s) s (sh h z) 0 (sh 0 g) 0 hD)
    have t2 := append6 (rp D) (l + 1) (rp ρ) ρ s h z (sh 0 g) 0 h 0 (by omega)
    have hf : readTapeBit (sh h z) (h + 1) = false := by rw [read_sh]; simp
    have t3 := Timed.single (p := machine) (by rfl) (s6f (rp D) (l + 1) (rp ρ) ρ (rp (s + h)) (s + h) (sh h z) (h + 1) (sh 0 g) 0 hf)
    have t4 := rewind9 (rp D) (l + 1) (rp ρ) ρ (rp (s + h)) (s + h) h z (sh 0 g) 0 h (le_refl _)
    have a1 := tc t1 rfl rfl (show cfg 6 (rp D) (l + 1) (rp ρ) ρ (rp s) s (sh h z) (0 + 1) (sh 0 g) 0 =
      cfg 6 (rp D) (l + 1) (rp ρ) ρ (rp (s + 0)) (s + 0) (sh h z) (0 + 1) (sh 0 g) 0 by simp)
    have a3 := tc t3 rfl rfl (show cfg 9 (rp D) (l + 1) (rp ρ) ρ (rp (s + h)) (s + h) (sh h z) (h + 1 - 1) (sh 0 g) 0 =
      cfg 9 (rp D) (l + 1) (rp ρ) ρ (rp (s + h)) (s + h) (sh h z) h (sh 0 g) 0 by simp)
    exact tc (((a1.trans t2).trans a3).trans t4) (by omega) rfl rfl
  · have t1 := Timed.single (p := machine) (by rfl) (s4t (rp D) l (rp ρ) ρ (rp s) s (sh h z) 0 (sh 0 g) 0 hD)
    have t2 := append7 (rp D) (l + 1) (rp ρ) ρ s h z (sh 0 g) 0 h 0 (by omega)
    have hf : readTapeBit (sh h z) (h + 1) = false := by rw [read_sh]; simp
    have t3 := Timed.single (p := machine) (by rfl) (s7f (rp D) (l + 1) (rp ρ) ρ (rp (s + h)) (s + h) (sh h z) (h + 1) (sh 0 g) 0 hf)
    have t4 := rewind10 (rp D) (l + 1) (rp ρ) ρ (rp (s + h)) (s + h) h z (sh 0 g) 0 h (le_refl _)
    have a1 := tc t1 rfl rfl (show cfg 7 (rp D) (l + 1) (rp ρ) ρ (rp s) s (sh h z) (0 + 1) (sh 0 g) 0 =
      cfg 7 (rp D) (l + 1) (rp ρ) ρ (rp (s + 0)) (s + 0) (sh h z) (0 + 1) (sh 0 g) 0 by simp)
    have a3 := tc t3 rfl rfl (show cfg 10 (rp D) (l + 1) (rp ρ) ρ (rp (s + h)) (s + h) (sh h z) (h + 1 - 1) (sh 0 g) 0 =
      cfg 10 (rp D) (l + 1) (rp ρ) ρ (rp (s + h)) (s + h) (sh h z) h (sh 0 g) 0 by simp)
    exact tc (((a1.trans t2).trans a3).trans t4) (by omega) rfl rfl

/-- A level at phase 2: append `h`, then halve it. -/
theorem level2 (D ρ l s h z g : ℕ) (hl : l < D) :
    ∃ T g' : ℕ, T ≤ 7 * h + 15 ∧ Timed machine T
      (cfg 5 (rp D) l (rp ρ) ρ (rp s) s (sh h z) 0 (sh 0 g) 0)
      (cfg 3 (rp D) (l + 1) (rp ρ) ρ (rp (s + h)) (s + h) (sh (h - h / 2) (z + h / 2)) 0 (sh 0 g') 0) := by
  have hD : readTapeBit (rp D) l = true := by rw [read_rp]; simp; omega
  have t1 := Timed.single (p := machine) (by rfl) (s5t (rp D) l (rp ρ) ρ (rp s) s (sh h z) 0 (sh 0 g) 0 hD)
  have t2 := append8 (rp D) (l + 1) (rp ρ) ρ s h z (sh 0 g) 0 h 0 (by omega)
  have hf : readTapeBit (sh h z) (h + 1) = false := by rw [read_sh]; simp
  have t3 := Timed.single (p := machine) (by rfl) (s8f (rp D) (l + 1) (rp ρ) ρ (rp (s + h)) (s + h) (sh h z) (h + 1) (sh 0 g) 0 hf)
  have t4 := rewind11 (rp D) (l + 1) (rp ρ) ρ (rp (s + h)) (s + h) h z (sh 0 g) 0 h (le_refl _)
  obtain ⟨T5, g', hT5, t5⟩ := halve (rp D) (l + 1) (rp ρ) ρ (rp (s + h)) (s + h) h z g
  have a1 := tc t1 rfl rfl (show cfg 8 (rp D) (l + 1) (rp ρ) ρ (rp s) s (sh h z) (0 + 1) (sh 0 g) 0 =
    cfg 8 (rp D) (l + 1) (rp ρ) ρ (rp (s + 0)) (s + 0) (sh h z) (0 + 1) (sh 0 g) 0 by simp)
  have a3 := tc t3 rfl rfl (show cfg 11 (rp D) (l + 1) (rp ρ) ρ (rp (s + h)) (s + h) (sh h z) (h + 1 - 1) (sh 0 g) 0 =
    cfg 11 (rp D) (l + 1) (rp ρ) ρ (rp (s + h)) (s + h) (sh h z) h (sh 0 g) 0 by simp)
  refine ⟨_, g', ?_, (((a1.trans t2).trans a3).trans t4).trans t5⟩
  omega

/-! ## The levels, then the whole run -/

/-- Round-up halving. -/
def hvf (n : ℕ) : ℕ := n - n / 2

def hs (ρ u : ℕ) : ℕ := hvf^[u] ρ

/-- `Σ_{l<L} h_{⌊l/3⌋}`. -/
def P (ρ L : ℕ) : ℕ := ∑ i ∈ Finset.range L, hs ρ (i / 3)

theorem hs_succ (ρ u : ℕ) : hs ρ (u + 1) = hs ρ u - hs ρ u / 2 := by
  unfold hs; rw [Function.iterate_succ_apply']; rfl

theorem hs_le (ρ : ℕ) : ∀ u, hs ρ u ≤ ρ := by
  intro u
  induction u with
  | zero => simp [hs]
  | succ u ih => rw [hs_succ]; omega

theorem cfgq {q q' : Fin 22} (hq : q.val = q'.val) (Dt : List Bool) (dh : ℕ) (Rt : List Bool) (rh : ℕ)
    (Ac : List Bool) (ah : ℕ) (H : List Bool) (hh : ℕ) (G : List Bool) (gh : ℕ) :
    cfg q Dt dh Rt rh Ac ah H hh G gh = cfg q' Dt dh Rt rh Ac ah H hh G gh := by
  rw [Fin.ext hq]

/-- **All remaining levels.** -/
theorem outer (D ρ : ℕ) : ∀ t l g : ℕ, l + t = D → ∃ T : ℕ, T ≤ t * (7 * ρ + 15) + 1 ∧
    ∃ (H' : List Bool) (hh' : ℕ) (G' : List Bool) (gh' : ℕ), Timed machine T
      (cfg ⟨3 + l % 3, by omega⟩ (rp D) l (rp ρ) ρ (rp (P ρ l)) (P ρ l)
        (sh (hs ρ (l / 3)) (ρ - hs ρ (l / 3))) 0 (sh 0 g) 0)
      (cfg 21 (rp D) D (rp ρ) ρ (rp (P ρ D)) (P ρ D) H' hh' G' gh') := by
  intro t
  induction t with
  | zero =>
    intro l g hl
    have hlD : l = D := by omega
    subst hlD
    have hf : readTapeBit (rp l) l = false := by rw [read_rp]; simp
    refine ⟨1, by omega, sh (hs ρ (l / 3)) (ρ - hs ρ (l / 3)), 0, sh 0 g, 0, ?_⟩
    rcases (show l % 3 = 0 ∨ l % 3 = 1 ∨ l % 3 = 2 by omega) with h | h | h
    · exact tc (Timed.single (p := machine) (by rfl) (s3f (rp l) l (rp ρ) ρ (rp (P ρ l)) (P ρ l)
        (sh (hs ρ (l / 3)) (ρ - hs ρ (l / 3))) 0 (sh 0 g) 0 hf)) rfl (cfgq (by simp [h]) _ _ _ _ _ _ _ _ _ _) rfl
    · exact tc (Timed.single (p := machine) (by rfl) (s4f (rp l) l (rp ρ) ρ (rp (P ρ l)) (P ρ l)
        (sh (hs ρ (l / 3)) (ρ - hs ρ (l / 3))) 0 (sh 0 g) 0 hf)) rfl (cfgq (by simp [h]) _ _ _ _ _ _ _ _ _ _) rfl
    · exact tc (Timed.single (p := machine) (by rfl) (s5f (rp l) l (rp ρ) ρ (rp (P ρ l)) (P ρ l)
        (sh (hs ρ (l / 3)) (ρ - hs ρ (l / 3))) 0 (sh 0 g) 0 hf)) rfl (cfgq (by simp [h]) _ _ _ _ _ _ _ _ _ _) rfl
  | succ t ih =>
    intro l g hl
    have hlD : l < D := by omega
    have hP : P ρ (l + 1) = P ρ l + hs ρ (l / 3) := by unfold P; rw [Finset.sum_range_succ]
    have hle := hs_le ρ (l / 3)
    rcases (show l % 3 = 0 ∨ l % 3 = 1 ∨ l % 3 = 2 by omega) with h | h | h
    · have t1 := level01 D ρ l (P ρ l) (hs ρ (l / 3)) (ρ - hs ρ (l / 3)) g hlD 0 (by omega)
      obtain ⟨T, hT, H', hh', G', gh', t2⟩ := ih (l + 1) g (by omega)
      have e3 : (l + 1) / 3 = l / 3 := by omega
      rw [e3, hP] at t2
      refine ⟨_, ?_, H', hh', G', gh', tc (t1.trans (tc t2 rfl (cfgq (by simp; omega) _ _ _ _ _ _ _ _ _ _) rfl)) rfl
        (cfgq (by simp [h]) _ _ _ _ _ _ _ _ _ _) rfl⟩
      nlinarith
    · have t1 := level01 D ρ l (P ρ l) (hs ρ (l / 3)) (ρ - hs ρ (l / 3)) g hlD 1 (by omega)
      obtain ⟨T, hT, H', hh', G', gh', t2⟩ := ih (l + 1) g (by omega)
      have e3 : (l + 1) / 3 = l / 3 := by omega
      rw [e3, hP] at t2
      refine ⟨_, ?_, H', hh', G', gh', tc (t1.trans (tc t2 rfl (cfgq (by simp; omega) _ _ _ _ _ _ _ _ _ _) rfl)) rfl
        (cfgq (by simp [h]) _ _ _ _ _ _ _ _ _ _) rfl⟩
      nlinarith
    · obtain ⟨T1, g', hT1, t1⟩ := level2 D ρ l (P ρ l) (hs ρ (l / 3)) (ρ - hs ρ (l / 3)) g hlD
      obtain ⟨T, hT, H', hh', G', gh', t2⟩ := ih (l + 1) g' (by omega)
      have e3 : (l + 1) / 3 = l / 3 + 1 := by omega
      rw [e3, hP, hs_succ] at t2
      have e4 : ρ - (hs ρ (l / 3) - hs ρ (l / 3) / 2) = ρ - hs ρ (l / 3) + hs ρ (l / 3) / 2 := by omega
      rw [e4] at t2
      refine ⟨_, ?_, H', hh', G', gh', tc (t1.trans (tc t2 rfl (cfgq (by simp; omega) _ _ _ _ _ _ _ _ _ _) rfl)) rfl
        (cfgq (by simp [h]) _ _ _ _ _ _ _ _ _ _) rfl⟩
      nlinarith

/-- **The run**: from `1^D`, `1^ρ` (all else blank, heads `0`) to `1^(Σ_{l<D} h_{⌊l/3⌋})` on tape 2. -/
theorem run (D ρ : ℕ) : ∃ (n : ℕ) (H1 : Fin 5 → ℕ) (A1 : Fin 5 → List Bool),
    Step machine n (fun _ => 0) ![rp D, rp ρ, [], [], []] H1 A1 ∧
    A1 2 = rp (P ρ D) ∧ n ≤ 2 * ρ + 4 + D * (7 * ρ + 15) + 1 := by
  have t0 := Timed.single (p := machine) (by rfl) (s0 (rp D) 0 (rp ρ) 0 [] 0 [] 0 [] 0)
  have e0 : writeTapeBit ([] : List Bool) 0 false = sh 0 0 := rfl
  rw [e0] at t0
  have t1 := copyRoot D ρ ρ 0 (by omega)
  have hf : readTapeBit (rp ρ) ρ = false := by rw [read_rp]; simp
  have t2 := Timed.single (p := machine) (by rfl) (s1f (rp D) 0 (rp ρ) ρ [] 0 (sh ρ 0) (ρ + 1) (sh 0 0) 0 hf)
  have t3 := rewind2 (rp D) 0 (rp ρ) ρ [] 0 ρ 0 (sh 0 0) 0 ρ (le_refl _)
  obtain ⟨T, hT, H', hh', G', gh', t4⟩ := outer D ρ D 0 0 (by omega)
  have a2 := tc t2 rfl rfl (show cfg 2 (rp D) 0 (rp ρ) ρ [] 0 (sh ρ 0) (ρ + 1 - 1) (sh 0 0) 0 =
    cfg 2 (rp D) 0 (rp ρ) ρ [] 0 (sh ρ 0) ρ (sh 0 0) 0 by simp)
  have a4 := tc t4 rfl (show cfg ⟨3 + 0 % 3, by omega⟩ (rp D) 0 (rp ρ) ρ (rp (P ρ 0)) (P ρ 0)
      (sh (hs ρ (0 / 3)) (ρ - hs ρ (0 / 3))) 0 (sh 0 0) 0 = cfg 3 (rp D) 0 (rp ρ) ρ [] 0 (sh ρ 0) 0 (sh 0 0) 0 by
    simp [P, hs, rp]) rfl
  have e := (((t0.trans t1).trans a2).trans t3).trans a4
  have s := NatAt.Timed.toStep e rfl rfl
  have hh0 : (cfg 0 (rp D) 0 (rp ρ) 0 [] 0 [] 0 [] 0).heads = fun _ => 0 := by
    funext i; fin_cases i <;> rfl
  rw [hh0] at s
  refine ⟨_, _, _, s, rfl, ?_⟩
  omega

end NearCubicWires.PacketsGlue.WinSum

namespace NearCubicWires.PacketsGlue.RequestMeta
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairRepresentation
open NearCubicWires.RepairOrdinary.RecoveryRootRound
open PCJ9eff70d512234a4c_Fixed PCJd4d1d9d7d1fa4313_Production
open NearCubicWires.PacketFamilyParent NearCubicWires.CanonicalFourfoldRowProgram
noncomputable section

def winSumMap : UnaryMap2 (fun D ρ => PacketsGlue.WinSum.P ρ D) where
  extra := 3
  states := 22 + 2
  machine := MaskedReset.machine PacketsGlue.WinSum.machine (fun _ => true)
  cost := fun D ρ => 2 * (2 * ρ + 4 + D * (7 * ρ + 15) + 1) + 2
  run := by
    intro D ρ
    obtain ⟨n, H1, A1, hs, hv, hn⟩ := PacketsGlue.WinSum.run D ρ
    obtain ⟨k, hm⟩ := step_mask0 (hs.enlarge hn) (fun _ => true) (by intro i _; rfl)
    refine ⟨_, _, hm.congr_in ?_ ?_, ?_, ?_⟩
    · funext i; refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;> simp
    · funext i; refine Fin.addCases (fun j => ?_) (fun j => ?_) i
      · simp only [Fin.addCases_left]; fin_cases j <;> rfl
      · simp [unIn2]
    · have hc : (⟨2, by omega⟩ : Fin (3 + 3)) = Fin.castAdd 1 (2 : Fin 5) := rfl
      rw [hc, Fin.addCases_left, hv]; rfl
    · have hc : (⟨2, by omega⟩ : Fin (3 + 3)) = Fin.castAdd 1 (2 : Fin 5) := rfl
      rw [hc, Fin.addCases_left]
      rfl

theorem winSum_cost (x y : ℕ) : winSumMap.cost x y ≤ 32 * (x + y + 3) ^ 2 := by
  change 2 * (2 * y + 4 + x * (7 * y + 15) + 1) + 2 ≤ _
  nlinarith

theorem hs_eq (ρ u : ℕ) : PacketsGlue.WinSum.hs ρ u = (ρ + 2 ^ u - 1) / 2 ^ u := by
  induction u generalizing ρ with
  | zero => simp [PacketsGlue.WinSum.hs]
  | succ q ih =>
    have e : PacketsGlue.WinSum.hs ρ (q + 1) = PacketsGlue.WinSum.hs (PacketsGlue.WinSum.hvf ρ) q := by
      unfold PacketsGlue.WinSum.hs; rw [Function.iterate_succ_apply]
    rw [e, ih]
    have hh : PacketsGlue.WinSum.hvf ρ = (ρ + 1) / 2 := by unfold PacketsGlue.WinSum.hvf; omega
    rw [hh]
    have hq : 1 ≤ 2 ^ q := Nat.one_le_two_pow
    have hsplit : ρ + 2 * 2 ^ q - 1 = (ρ + 1) + 2 * (2 ^ q - 1) := by omega
    have hdiv : (ρ + 2 * 2 ^ q - 1) / 2 = (ρ + 1) / 2 + (2 ^ q - 1) := by
      rw [hsplit, Nat.add_mul_div_left _ _ (by norm_num)]
    rw [Nat.pow_succ, Nat.mul_comm (2 ^ q) 2, ← Nat.div_div_eq_div_mul, hdiv]
    congr 1
    omega

theorem window_hs (a : DecompositionAlgorithm) (r : Request) (l : ℕ) :
    window a r l = 64 + PacketsGlue.WinSum.hs (natCeilSqrt (64 ^ 2 * touch a r)) (l / 3) := by
  unfold window executableGradedWindow
  rw [Nat.ceilDiv_eq_add_pred_div, hs_eq]

/-- `Σ_{l<depth} window_l`. -/
def windowSum (a : DecompositionAlgorithm) (r : Request) : ℕ := ∑ l ∈ Finset.range (depth a r), window a r l

theorem windowSum_eq (a : DecompositionAlgorithm) (r : Request) :
    windowSum a r = PacketsGlue.WinSum.P (natCeilSqrt (64 ^ 2 * touch a r)) (depth a r) + depth a r * 64 := by
  unfold windowSum PacketsGlue.WinSum.P
  simp only [window_hs, Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, smul_eq_mul]
  ring

def windowSumStage (a : DecompositionAlgorithm) : UnaryStage a (windowSum a) :=
  (((depthStage a).pairP (rootStage a) winSumMap 32 2 winSum_cost).pairP
    ((depthStage a).thenMapP (scaleMap 64) (4 * 64 + 12) 2 (scale_cost 64)) addMap2 6 1 add_cost).ofEq
    (fun r => (windowSum_eq a r).symm)

end
end NearCubicWires.PacketsGlue.RequestMeta


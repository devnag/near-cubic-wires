import Proof.Assembly.Bridge

set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

namespace PCJ93d4cfe17dc847a3.Winner
open PCJc4297ab269d8423a_Source PCJ9eff70d512234a4c_Fixed

noncomputable def score (d : MaskData) (j : Nat) : Nat :=
  (State.result d (d.q-j)).1

def word (d : MaskData) (j : Nat) : List Bool :=
  List.ofFn (fun x : Fin d.q => decide (x ∈ CyclicChoice.window d.q d.K j))

def pickStep (d : MaskData) (best : Nat × Nat) (j : Nat) : Nat × Nat :=
  if CyclicChoice.incidenceScore d.support d.K j < best.2 then
    (j, CyclicChoice.incidenceScore d.support d.K j) else best

def pick (d : MaskData) (n : Nat) : Nat × Nat :=
  (List.range n).foldl (pickStep d) (0,CyclicChoice.incidenceScore d.support d.K 0)

noncomputable def scan (d : MaskData) : Nat → Nat × List Bool
  | 0 => (0,Init.bits d.K d.q)
  | n+1 => (max (scan d n).1 (score d n),
      if (scan d n).1 < score d n then word d n else (scan d n).2)

theorem word_zero (d : MaskData) : word d 0 = Init.bits d.K d.q := by
  apply List.ext_getElem
  · simp [word,Init.bits]
  · intro i hi hj
    have hiq : i < d.q := by simpa [word] using hi
    simp [word,Init.bits,CyclicChoice.window,Nat.mod_eq_of_lt hiq]

theorem pick_succ (d : MaskData) (n : Nat) :
    pick d (n+1) = pickStep d (pick d n) n := by
  simp [pick,List.range_succ,List.foldl_append]

theorem pick_one (d : MaskData) : pick d 1 = pick d 0 := by
  simp [pick,pickStep]

theorem invariant (d : MaskData) (n : Nat) (hn : n ≤ d.q) :
    (scan d n).2 = word d (pick d n).1 ∧
    (0 < n → (scan d n).1 + (pick d n).2 = d.m*d.K) := by
  induction n with
  | zero =>
    constructor
    · exact (word_zero d).symm
    · omega
  | succ n ih =>
    have hs := Bridge.score_eq d n (by omega)
    change score d n + CyclicChoice.incidenceScore d.support d.K n = d.m*d.K at hs
    obtain ⟨hw,hb⟩ := ih (by omega)
    by_cases hz : n = 0
    · subst n
      constructor
      · change (if 0 < score d 0 then word d 0 else Init.bits d.K d.q) = word d (pick d 1).1
        rw [pick_one]
        change (if 0 < score d 0 then word d 0 else Init.bits d.K d.q) = word d 0
        split_ifs
        · rfl
        · exact (word_zero d).symm
      · intro _
        simpa [scan,pick,pickStep] using hs
    · have hb' := hb (by omega)
      have he : ((scan d n).1 < score d n) ↔
          CyclicChoice.incidenceScore d.support d.K n < (pick d n).2 := by omega
      rw [scan,pick_succ]
      unfold pickStep
      by_cases hc : (scan d n).1 < score d n
      · simp only [if_pos hc,if_pos (he.mp hc),
          max_eq_right (Nat.le_of_lt hc)]
        exact ⟨trivial,fun _ => hs⟩
      · have hc' : ¬ CyclicChoice.incidenceScore d.support d.K n < (pick d n).2 :=
          fun h => hc (he.mpr h)
        simp only [if_neg hc,if_neg hc',
          max_eq_left (Nat.le_of_not_gt hc)]
        exact ⟨hw,fun _ => hb'⟩

theorem winner_eq (d : MaskData) : (scan d d.q).2 = d.word := by
  exact (invariant d d.q le_rfl).1

theorem length (d : MaskData) (n : Nat) (hn : n ≤ d.q) :
    (scan d n).2.length = d.q := by
  rw [(invariant d n hn).1]
  simp [word]

end PCJ93d4cfe17dc847a3.Winner

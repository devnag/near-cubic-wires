import Proof.Packets.SourceResidentCopies
import Proof.Assembly.Production

set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

namespace NearCubicWires.SourceResident
open NearCubicWires LocalBitMultitape ExtDecompositionBatch
open RepairOrdinary RepairOrdinary.RecoveryExecution RepairOrdinary.RecoveryRootRound
open RepairRepresentation SupplierEstimator SupplierPipeline SourceInterfaces
open PCJ9eff70d512234a4c_Fixed PCJd4d1d9d7d1fa4313_Production
noncomputable section

/-! ## Reading frames and drivers -/

theorem read_mark (w : List Bool) : ∀ (pre post : List Bool) (k : ℕ), k < w.length →
    readTapeBit (pre ++ frame w ++ post) (pre.length + 2 * k) = true := by
  induction w with
  | nil => intro _ _ k hk; simp at hk
  | cons b w ih =>
    intro pre post k hk
    cases k with
    | zero =>
      have e : pre ++ frame (b :: w) ++ post = pre ++ true :: (b :: (frame w ++ post)) := by
        rw [ExtDecompositionBatch.frame_cons]; simp
      rw [e]
      exact Streaming.read_append pre _ true
    | succ k =>
      have e : pre ++ frame (b :: w) ++ post = (pre ++ [true, b]) ++ frame w ++ post := by
        rw [ExtDecompositionBatch.frame_cons]; simp
      have h := ih (pre ++ [true, b]) post k (by simp at hk; omega)
      rw [e]
      simp only [List.length_append, List.length_cons, List.length_nil] at h
      rw [show pre.length + 2 * (k + 1) = pre.length + (0 + 1 + 1) + 2 * k by omega]
      exact h

theorem read_endf (w : List Bool) : ∀ (pre post : List Bool),
    readTapeBit (pre ++ frame w ++ post) (pre.length + 2 * w.length) = false := by
  induction w with
  | nil =>
    intro pre post
    have e : pre ++ frame [] ++ post = pre ++ false :: post := by rw [ExtDecompositionBatch.frame_nil]; simp
    rw [e]
    exact Streaming.read_append pre post false
  | cons b w ih =>
    intro pre post
    have e : pre ++ frame (b :: w) ++ post = (pre ++ [true, b]) ++ frame w ++ post := by
      rw [ExtDecompositionBatch.frame_cons]; simp
    have h := ih (pre ++ [true, b]) post
    rw [e]
    simp only [List.length_append, List.length_cons, List.length_nil] at h
    rw [show pre.length + 2 * (b :: w).length = pre.length + (0 + 1 + 1) + 2 * w.length by simp; omega]
    exact h

theorem read_drv_lt (L z x : ℕ) (h : x < L) :
    readTapeBit (List.replicate L true ++ List.replicate z false) x = true := by
  unfold readTapeBit
  rw [List.getD_eq_getElem _ _ (by simp; omega), List.getElem_append_left (by simp; omega)]
  simp

theorem read_drv_end (L z : ℕ) : readTapeBit (List.replicate L true ++ List.replicate z false) L = false := by
  cases z with
  | zero => simpa using ExtDecompositionBatch.read_replicate_end L true
  | succ z =>
    have := Streaming.read_append (List.replicate L true) (List.replicate z false) false
    simp only [List.length_replicate] at this
    rw [List.replicate_succ]
    exact this

theorem frame_ones (n : ℕ) : frame (List.replicate n true) = List.replicate (2 * n) true ++ [false] := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [List.replicate_succ, ExtDecompositionBatch.frame_cons, ih,
      show 2 * (n + 1) = (2 * n + 1) + 1 by omega, List.replicate_succ, List.replicate_succ]
    rfl

/-! ## The frame counter -/

namespace Cnt

/-- Tape 0 the frames, tape 1 the driver `1^L`, tape 2 the output. State 0 at a marker cell: the driver ended —
write the closing `false` and halt; a `true` marker — skip the pair (state 1); a `false` marker (a frame's end) —
write `true` (state 2 writes the second `true` and steps past it). -/
def machine : Machine 3 4 where
  descriptionBits := 0
  start := 0
  halted := fun q => q.val == 3
  rule := fun q b =>
    if q.val = 0 then some (if b 1 then (if b 0 then ⟨1, ![none, none, none], ![.right, .right, .stay]⟩
        else ⟨2, ![none, none, some true], ![.stay, .stay, .right]⟩)
      else ⟨3, ![none, none, some false], ![.stay, .stay, .stay]⟩)
    else if q.val = 1 then some ⟨0, ![none, none, none], ![.right, .right, .stay]⟩
    else if q.val = 2 then some ⟨0, ![none, none, some true], ![.right, .right, .right]⟩
    else none

def cfg (S D O : List Bool) (q : Fin 4) (p : ℕ) : Configuration 3 4 := ⟨q, ![p, p, O.length], ![S, D, O]⟩

theorem sMark (S D O : List Bool) (p : ℕ) (h0 : readTapeBit S p = true) (h1 : readTapeBit D p = true) :
    step machine (cfg S D O 0 p) = some (cfg S D O 1 (p + 1)) := by
  simp [step, machine, cfg, Configuration.scanned, h0, h1]
  apply configuration_ext
  · rfl
  · funext k; fin_cases k <;> simp [applyAction, HeadMove.apply]
  · funext k; fin_cases k <;> simp [applyAction]

theorem sPay (S D O : List Bool) (p : ℕ) :
    step machine (cfg S D O 1 p) = some (cfg S D O 0 (p + 1)) := by
  simp [step, machine, cfg]
  apply configuration_ext
  · rfl
  · funext k; fin_cases k <;> simp [applyAction, HeadMove.apply]
  · funext k; fin_cases k <;> simp [applyAction]

theorem sEnd (S D O : List Bool) (p : ℕ) (h0 : readTapeBit S p = false) (h1 : readTapeBit D p = true) :
    step machine (cfg S D O 0 p) = some ⟨2, ![p, p, (O ++ [true]).length], ![S, D, O ++ [true]]⟩ := by
  have hw := Streaming.write_append O true
  simp [step, machine, cfg, Configuration.scanned, h0, h1]
  apply configuration_ext
  · rfl
  · funext k; fin_cases k <;> simp [applyAction, HeadMove.apply]
  · funext k; fin_cases k <;> simp [applyAction, hw]

theorem sTwo (S D O : List Bool) (p : ℕ) :
    step machine ⟨2, ![p, p, O.length], ![S, D, O]⟩ = some (cfg S D (O ++ [true]) 0 (p + 1)) := by
  have hw := Streaming.write_append O true
  simp [step, machine, cfg]
  apply configuration_ext
  · rfl
  · funext k; fin_cases k <;> simp [applyAction, HeadMove.apply]
  · funext k; fin_cases k <;> simp [applyAction, hw]

theorem sStop (S D O : List Bool) (p : ℕ) (h1 : readTapeBit D p = false) :
    step machine (cfg S D O 0 p) = some ⟨3, ![p, p, O.length], ![S, D, O ++ [false]]⟩ := by
  have hw := Streaming.write_append O false
  simp [step, machine, cfg, Configuration.scanned, h1]
  apply configuration_ext
  · rfl
  · funext k; fin_cases k <;> simp [applyAction, HeadMove.apply]
  · funext k; fin_cases k <;> simp [applyAction, hw]

/-- Inside one frame: the `true` markers are skipped two cells at a time. -/
theorem pairs (w pre post D O : List Bool) (hD : ∀ x, x < pre.length + (frame w).length → readTapeBit D x = true) :
    ∀ k, k ≤ w.length → Timed machine (2 * k) (cfg (pre ++ frame w ++ post) D O 0 pre.length)
      (cfg (pre ++ frame w ++ post) D O 0 (pre.length + 2 * k)) := by
  intro k
  induction k with
  | zero => intro _; exact Timed.refl _ _
  | succ k ih =>
    intro hk
    have hl := frame_length w
    have t1 := ih (by omega)
    have t2 := Timed.single (p := machine) (by rfl)
      (sMark (pre ++ frame w ++ post) D O (pre.length + 2 * k) (read_mark w pre post k (by omega)) (hD _ (by omega)))
    have t3 := Timed.single (p := machine) (by rfl) (sPay (pre ++ frame w ++ post) D O (pre.length + 2 * k + 1))
    have t := (t1.trans t2).trans t3
    rw [show pre.length + 2 * k + 1 + 1 = pre.length + 2 * (k + 1) by omega] at t
    exact t

/-- One frame: skipped, and `[true, true]` appended to the output. -/
theorem oneFrame (w pre post D O : List Bool)
    (hD : ∀ x, x < pre.length + (frame w).length → readTapeBit D x = true) :
    Timed machine (2 * w.length + 2) (cfg (pre ++ frame w ++ post) D O 0 pre.length)
      (cfg (pre ++ frame w ++ post) D (O ++ [true] ++ [true]) 0 (pre.length + (frame w).length)) := by
  have hl := frame_length w
  have t1 := pairs w pre post D O hD w.length le_rfl
  have t2 := Timed.single (p := machine) (by rfl)
    (sEnd (pre ++ frame w ++ post) D O (pre.length + 2 * w.length) (read_endf w pre post) (hD _ (by omega)))
  have t3 := Timed.single (p := machine) (by rfl)
    (sTwo (pre ++ frame w ++ post) D (O ++ [true]) (pre.length + 2 * w.length))
  have t := (t1.trans t2).trans t3
  rw [show pre.length + 2 * w.length + 1 = pre.length + (frame w).length by omega] at t
  exact t

/-- All frames: `[true, true]` per frame. -/
theorem frames (ws : List (List Bool)) : ∀ (pre post D O : List Bool),
    (∀ x, x < pre.length + (ws.flatMap frame).length → readTapeBit D x = true) →
    Timed machine ((ws.flatMap frame).length + ws.length) (cfg (pre ++ ws.flatMap frame ++ post) D O 0 pre.length)
      (cfg (pre ++ ws.flatMap frame ++ post) D (O ++ List.replicate (2 * ws.length) true) 0
        (pre.length + (ws.flatMap frame).length)) := by
  induction ws with
  | nil => intro pre post D O _; simpa using Timed.refl machine (cfg (pre ++ post) D O 0 pre.length)
  | cons w ws ih =>
    intro pre post D O hD
    have hl := frame_length w
    have e1 : pre ++ (w :: ws).flatMap frame ++ post = pre ++ frame w ++ (ws.flatMap frame ++ post) := by simp
    have e2 : pre ++ (w :: ws).flatMap frame ++ post = (pre ++ frame w) ++ ws.flatMap frame ++ post := by simp
    have hlen : ((w :: ws).flatMap frame).length = (frame w).length + (ws.flatMap frame).length := by simp
    have t1 := oneFrame w pre (ws.flatMap frame ++ post) D O (fun x hx => hD x (by rw [hlen]; omega))
    rw [← e1] at t1
    have t2 := ih (pre ++ frame w) post D (O ++ [true] ++ [true]) (fun x hx => hD x (by
      rw [hlen]; simp only [List.length_append] at hx; omega))
    rw [← e2, List.length_append] at t2
    have t := t1.trans t2
    have eO : O ++ [true] ++ [true] ++ List.replicate (2 * ws.length) true =
        O ++ List.replicate (2 * (w :: ws).length) true := by
      rw [show 2 * (w :: ws).length = 2 * ws.length + 1 + 1 by simp; omega, List.replicate_succ, List.replicate_succ]
      simp
    rw [eO, show pre.length + (frame w).length + (ws.flatMap frame).length = pre.length +
      ((w :: ws).flatMap frame).length by rw [hlen]; omega,
      show 2 * w.length + 2 + ((ws.flatMap frame).length + ws.length) = ((w :: ws).flatMap frame).length +
        (w :: ws).length by rw [hlen, hl]; simp; omega] at t
    exact t

/-- **The count**: from the frames (any zero tail) and the driver `1^L` (any zero tail), the output becomes
`frame (1^N)`, `N` the number of frames. -/
theorem run (ws : List (List Bool)) (tail : List Bool) (z : ℕ) :
    Step machine ((ws.flatMap frame).length + ws.length + 1) (fun _ => 0)
      ![ws.flatMap frame ++ tail, List.replicate (ws.flatMap frame).length true ++ List.replicate z false, []]
      ![(ws.flatMap frame).length, (ws.flatMap frame).length, 2 * ws.length]
      ![ws.flatMap frame ++ tail, List.replicate (ws.flatMap frame).length true ++ List.replicate z false,
        frame (List.replicate ws.length true)] := by
  have t1 := frames ws [] tail (List.replicate (ws.flatMap frame).length true ++ List.replicate z false) []
    (fun x hx => read_drv_lt _ z x (by simp only [List.length_nil, Nat.zero_add] at hx; exact hx))
  simp only [List.nil_append, List.length_nil, Nat.zero_add] at t1
  have t2 := Timed.single (p := machine) (by rfl)
    (sStop (ws.flatMap frame ++ tail) (List.replicate (ws.flatMap frame).length true ++ List.replicate z false)
      (List.replicate (2 * ws.length) true) (ws.flatMap frame).length (read_drv_end _ z))
  have t := t1.trans t2
  obtain ⟨r, hr, hf, _⟩ := t.run (by rfl)
  have hc : cfg (ws.flatMap frame ++ tail) (List.replicate (ws.flatMap frame).length true ++ List.replicate z false) [] 0 0 =
      (⟨machine.start, fun _ => 0, ![ws.flatMap frame ++ tail,
        List.replicate (ws.flatMap frame).length true ++ List.replicate z false, []]⟩ : Configuration 3 4) := by
    apply configuration_ext
    · rfl
    · funext i; fin_cases i <;> rfl
    · funext i; fin_cases i <;> rfl
  rw [hc] at hr
  refine Step.of_run (r := r) hr ?_ ?_
  · rw [hf]; simp
  · rw [hf, frame_ones]

end Cnt

/-- Every frame has at least one cell. -/
theorem count_le_frames (ws : List (List Bool)) : ws.length ≤ (ws.flatMap frame).length := by
  induction ws with
  | nil => simp
  | cons w ws ih => simp only [List.flatMap_cons, List.length_append, frame_length, List.length_cons]; omega

def occM := MaskedReset.machine Cnt.machine (fun _ => true)

/-- Its cost (`L` the frames' length, `N` their number). -/
def occCost (L N : ℕ) : ℕ := 2 * (L + N + 1) + 2

/-- The counter's local bank. -/
def oBank (S D O log : List Bool) : Fin (3 + 1) → List Bool := Fin.addCases ![S, D, O] (fun _ : Fin 1 => log)

theorem occ_local (ws : List (List Bool)) (tail : List Bool) (z : ℕ) :
    ∃ k, k ≤ (ws.flatMap frame).length + ws.length + 1 ∧
      Step occM (occCost (ws.flatMap frame).length ws.length) (fun _ => 0)
        (oBank (ws.flatMap frame ++ tail) (List.replicate (ws.flatMap frame).length true ++ List.replicate z false) [] [])
        (fun _ => 0)
        (oBank (ws.flatMap frame ++ tail) (List.replicate (ws.flatMap frame).length true ++ List.replicate z false)
          (frame (List.replicate ws.length true)) (List.replicate k false)) := by
  obtain ⟨k, hk, st⟩ := mask0 (Cnt.run ws tail z)
  have eH : Fin.addCases (fun _ : Fin 3 => (0 : ℕ)) (fun _ : Fin 1 => 0) = fun _ => 0 := by
    funext i; refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;> simp
  rw [eH] at st
  exact ⟨k, hk, st⟩

theorem occ_run {U : ℕ} (sl : Fin 4 → Fin U) (hsl : Function.Injective sl)
    (H : Fin U → ℕ) (A : Fin U → List Bool) (hH : ∀ j, H (sl j) = 0)
    (ws : List (List Bool)) (Q0 Q1 R : ℕ)
    (h0 : A (sl 0) = ZeroPadding.pad Q0 (ws.flatMap frame))
    (h1 : A (sl 1) = ZeroPadding.pad Q1 (List.replicate (ws.flatMap frame).length true))
    (h2 : A (sl 2) = List.replicate R false) (h3 : A (sl 3) = List.replicate R false)
    (hR : 2 * (ws.flatMap frame).length + 1 ≤ R) :
    ∃ A' : Fin U → List Bool, Step (RecoveryFocus.machine sl occM) (occCost (ws.flatMap frame).length ws.length)
      H A H A' ∧ A' (sl 2) = ZeroPadding.pad R (frame (List.replicate ws.length true)) ∧
      ∀ x, (∀ j, sl j = x → j ≠ 2) → A' x = A x := by
  have hN := count_le_frames ws
  obtain ⟨k, hk, st⟩ := occ_local ws (List.replicate (Q0 - (ws.flatMap frame).length) false)
    (Q1 - (ws.flatMap frame).length)
  have sp := st.pad (Fin.addCases ![0, 0, R] (fun _ : Fin 1 => R))
  have sf := sp.focus sl hsl H A
  have eH : dockH sl H (fun _ => 0) = H := by
    funext x
    by_cases hx : ∃ j, sl j = x
    · obtain ⟨j, rfl⟩ := hx
      rw [dockH_slot _ hsl, hH]
    · simp only [not_exists] at hx
      exact dockH_other _ _ _ _ hx
  have eIn : install sl A (fun i => ZeroPadding.pad (Fin.addCases ![0, 0, R] (fun _ : Fin 1 => R) i)
      (oBank (ws.flatMap frame ++ List.replicate (Q0 - (ws.flatMap frame).length) false)
        (List.replicate (ws.flatMap frame).length true ++ List.replicate (Q1 - (ws.flatMap frame).length) false)
        [] [] i)) = A := by
    apply install_existing
    intro j
    fin_cases j
    · show A (sl 0) = ZeroPadding.pad 0 (ws.flatMap frame ++ List.replicate (Q0 - (ws.flatMap frame).length) false)
      rw [ZeroPadding.pad_zero, h0]
      rfl
    · show A (sl 1) = ZeroPadding.pad 0
        (List.replicate (ws.flatMap frame).length true ++ List.replicate (Q1 - (ws.flatMap frame).length) false)
      rw [ZeroPadding.pad_zero, h1]
      simp [ZeroPadding.pad]
    · show A (sl 2) = ZeroPadding.pad R []
      rw [h2]
      exact (pad_repl R 0 (Nat.zero_le _)).symm
    · show A (sl 3) = ZeroPadding.pad R []
      rw [h3]
      exact (pad_repl R 0 (Nat.zero_le _)).symm
  rw [eH, eIn] at sf
  refine ⟨_, sf, ?_, ?_⟩
  · rw [install_slot _ hsl]
    rfl
  · intro x hx
    by_cases hx' : ∃ j, sl j = x
    · obtain ⟨j, rfl⟩ := hx'
      rw [install_slot _ hsl]
      have hj2 := hx j rfl
      fin_cases j
      · show ZeroPadding.pad 0 (ws.flatMap frame ++ List.replicate (Q0 - (ws.flatMap frame).length) false) = A (sl 0)
        rw [ZeroPadding.pad_zero, h0]
        rfl
      · show ZeroPadding.pad 0
          (List.replicate (ws.flatMap frame).length true ++ List.replicate (Q1 - (ws.flatMap frame).length) false) =
          A (sl 1)
        rw [ZeroPadding.pad_zero, h1]
        simp [ZeroPadding.pad]
      · exact absurd rfl hj2
      · show ZeroPadding.pad R (List.replicate k false) = A (sl 3)
        rw [h3, pad_repl R k (by omega)]
    · simp only [not_exists] at hx'
      exact install_other _ _ _ _ hx'

/-- The support word is one frame per occurrence. -/
theorem support_frames (a : DecompositionAlgorithm) (r : Request) :
    r.supportWord a = ((r.family a).occurrences.map
      (fun (g : SupportedNormalizedGate r.q) => List.ofFn (fun i : Fin r.q => decide (i ∈ g.support)))).flatMap frame := by
  unfold PCJd4d1d9d7d1fa4313_Production.Request.supportWord
  rw [List.flatMap_map]

theorem occ_request {U : ℕ} (sl : Fin 4 → Fin U) (hsl : Function.Injective sl)
    (H : Fin U → ℕ) (A : Fin U → List Bool) (hH : ∀ j, H (sl j) = 0)
    (a : DecompositionAlgorithm) (r : Request) (Q0 Q1 R : ℕ)
    (h0 : A (sl 0) = ZeroPadding.pad Q0 (r.supportWord a))
    (h1 : A (sl 1) = ZeroPadding.pad Q1 (List.replicate (r.supportWord a).length true))
    (h2 : A (sl 2) = List.replicate R false) (h3 : A (sl 3) = List.replicate R false)
    (hR : 2 * (r.supportWord a).length + 1 ≤ R) :
    ∃ A' : Fin U → List Bool, Step (RecoveryFocus.machine sl occM)
      (occCost (r.supportWord a).length (r.family a).occurrences.length) H A H A' ∧
      A' (sl 2) = ZeroPadding.pad R (frame (List.replicate (r.family a).occurrences.length true)) ∧
      ∀ x, (∀ j, sl j = x → j ≠ 2) → A' x = A x := by
  rw [support_frames] at h0 h1 hR
  have h := occ_run sl hsl H A hH _ Q0 Q1 R h0 h1 h2 h3 hR
  rw [List.length_map, ← support_frames] at h
  exact h

end
end NearCubicWires.SourceResident


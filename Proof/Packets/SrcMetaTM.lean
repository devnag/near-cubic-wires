import Proof.Packets.PacketsSetupWords

set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

namespace NearCubicWires.SourceStart.MetaTM
open NearCubicWires LocalBitMultitape RepairOrdinary RepairOrdinary.RecoveryExecution ExtDecompositionBatch

/-! ## 1. The frame-body copier -/

/-- The data bit written for a source bit. -/
def dat (ones b : Bool) : Bool := if ones then true else b

/-- The appended body. -/
def body (ones : Bool) (bits : List Bool) : List Bool := bits.flatMap (fun b => [true, dat ones b])

/-- State 0 reads a marker (`true`: write `true`, go to 1; `false`: stop without writing); state 1 copies the data bit. -/
def bodyM (ones : Bool) : Machine 2 3 where
  descriptionBits := 0
  start := 0
  halted := fun q => q.val == 2
  rule := fun q bits =>
    if q.val = 0 then
      (if bits 0 then some ⟨1, ![none, some true], fun _ => .right⟩ else some ⟨2, fun _ => none, fun _ => .stay⟩)
    else if q.val = 1 then some ⟨0, ![none, some (dat ones (bits 0))], fun _ => .right⟩ else none

def cfg (q : Fin 3) (source : List Bool) (pos : ℕ) (out : List Bool) : Configuration 2 3 :=
  ⟨q, ![pos, out.length], ![source, out]⟩

theorem marker_step (ones : Bool) (pre suffix out : List Bool) :
    step (bodyM ones) (cfg 0 (pre ++ true :: suffix) pre.length out) =
      some (cfg 1 (pre ++ true :: suffix) (pre.length + 1) (out ++ [true])) := by
  simp [step, bodyM, cfg, Configuration.scanned, Streaming.read_append]
  apply configuration_ext
  · rfl
  · funext i
    fin_cases i <;> simp [applyAction, HeadMove.apply]
  · funext i
    fin_cases i <;> simp [applyAction, Streaming.write_append]

theorem stop_step (ones : Bool) (pre suffix out : List Bool) :
    step (bodyM ones) (cfg 0 (pre ++ false :: suffix) pre.length out) =
      some (cfg 2 (pre ++ false :: suffix) pre.length out) := by
  simp [step, bodyM, cfg, Configuration.scanned, Streaming.read_append]
  apply configuration_ext
  · rfl
  · funext i
    fin_cases i <;> simp [applyAction, HeadMove.apply]
  · funext i
    fin_cases i <;> simp [applyAction]

theorem data_step (ones b : Bool) (pre suffix out : List Bool) :
    step (bodyM ones) (cfg 1 (pre ++ b :: suffix) pre.length out) =
      some (cfg 0 (pre ++ b :: suffix) (pre.length + 1) (out ++ [dat ones b])) := by
  simp [step, bodyM, cfg, Configuration.scanned, Streaming.read_append]
  apply configuration_ext
  · rfl
  · funext i
    fin_cases i <;> simp [applyAction, HeadMove.apply]
  · funext i
    fin_cases i <;> simp [applyAction, Streaming.write_append]

theorem body_prefix (ones : Bool) (pre bits suffix out : List Bool) :
    Timed (bodyM ones) (2*bits.length+1)
      (cfg 0 (pre ++ RepairOrdinary.frame bits ++ suffix) pre.length out)
      (cfg 2 (pre ++ RepairOrdinary.frame bits ++ suffix) (pre.length + 2*bits.length) (out ++ body ones bits)) := by
  induction bits generalizing pre out with
  | nil =>
    simpa only [RepairOrdinary.frame, List.length_nil, Nat.mul_zero, Nat.add_zero, body, List.flatMap_nil,
      List.append_nil, List.append_assoc, List.cons_append, List.nil_append, Bool.false_eq_true, ↓reduceIte] using
      Timed.single (by rfl : (bodyM ones).halted (0 : Fin 3) = false) (stop_step ones pre suffix out)
  | cons b bs ih =>
    let source := pre ++ RepairOrdinary.frame (b :: bs) ++ suffix
    have hm : step (bodyM ones) (cfg 0 source pre.length out) = some (cfg 1 source (pre.length + 1) (out ++ [true])) := by
      simpa only [source, RepairOrdinary.frame, List.append_assoc, List.cons_append, ↓reduceIte] using
        marker_step ones pre (b :: RepairOrdinary.frame bs ++ suffix) out
    have hb : step (bodyM ones) (cfg 1 source (pre.length + 1) (out ++ [true])) =
        some (cfg 0 source (pre.length + 2) (out ++ [true, dat ones b])) := by
      have h := data_step ones b (pre ++ [true]) (RepairOrdinary.frame bs ++ suffix) (out ++ [true])
      simpa only [source, RepairOrdinary.frame, List.length_append, List.length_singleton, List.append_assoc,
        List.cons_append, List.nil_append, Nat.add_assoc] using h
    have he : (pre ++ [true, b]) ++ RepairOrdinary.frame bs ++ suffix = source := by
      simp only [source, RepairOrdinary.frame, List.append_assoc, List.cons_append, List.nil_append]
    have htail := ih (pre ++ [true, b]) (out ++ [true, dat ones b])
    rw [he] at htail
    have hp : (pre ++ [true, b]).length = pre.length + 2 := by simp
    rw [hp] at htail
    have h0 := (Timed.single (by rfl : (bodyM ones).halted (0 : Fin 3) = false) hm).trans
      ((Timed.single (by rfl : (bodyM ones).halted (1 : Fin 3) = false) hb).trans htail)
    have htime : 1 + (1 + (2*bs.length+1)) = 2*(b :: bs).length+1 := by simp; omega
    have hpos : pre.length + 2 + 2*bs.length = pre.length + 2*(b :: bs).length := by simp; omega
    have hout : out ++ [true, dat ones b] ++ body ones bs = out ++ body ones (b :: bs) := by
      simp [body, List.append_assoc]
    rw [htime, hpos, hout] at h0
    exact h0

/-- **The frame-body copier as a `Step`**: source head at `pre.length`, output head at its end. -/
theorem body_run (ones : Bool) (pre bits suffix out : List Bool) :
    Step (bodyM ones) (2*bits.length+1) ![pre.length, out.length] ![pre ++ RepairOrdinary.frame bits ++ suffix, out]
      ![pre.length + 2*bits.length, (out ++ body ones bits).length]
      ![pre ++ RepairOrdinary.frame bits ++ suffix, out ++ body ones bits] := by
  obtain ⟨r, hr, hf, hs⟩ := (body_prefix ones pre bits suffix out).run (by rfl)
  exact ⟨r, hr, by rw [hf]; rfl, by rw [hf]; rfl, hs.le⟩

theorem body_false (bits : List Bool) : body false bits ++ [false] = RepairOrdinary.frame bits := by
  induction bits with
  | nil => rfl
  | cons b bs ih =>
    simp only [body, dat, List.flatMap_cons, Bool.false_eq_true, ↓reduceIte, List.cons_append, List.nil_append] at ih ⊢
    rw [RepairOrdinary.frame]
    simp only [List.cons.injEq, true_and]
    exact ih

theorem body_true (bits : List Bool) : body true bits ++ [false] = RepairOrdinary.frame (List.replicate bits.length true) := by
  induction bits with
  | nil => rfl
  | cons b bs ih =>
    simp only [body, dat, List.flatMap_cons, ↓reduceIte, List.cons_append, List.nil_append, List.length_cons,
      List.replicate_succ] at ih ⊢
    rw [RepairOrdinary.frame]
    simp only [List.cons.injEq, true_and]
    exact ih

theorem body_append (ones : Bool) (u v : List Bool) : body ones (u ++ v) = body ones u ++ body ones v := by
  simp [body, List.flatMap_append]

theorem body_length (ones : Bool) (bits : List Bool) : (body ones bits).length = 2*bits.length := by
  induction bits with
  | nil => rfl
  | cons b bs ih =>
    simp only [body, List.flatMap_cons, List.length_append, List.length_cons, List.length_nil] at ih ⊢
    omega

/-! ## 2. `1^b ↦ frame (0^b)` -/

/-- Tape 0 `1^b`, tape 1 the output `frame (0^b)`. -/
def zerosM : Machine 2 3 where
  descriptionBits := 0
  start := 0
  halted := fun q => q.val == 2
  rule := fun q x =>
    if q.val = 0 then some (if x 0 then ⟨1, ![none, some true], ![.stay, .right]⟩
      else ⟨2, ![none, some false], ![.stay, .stay]⟩)
    else if q.val = 1 then some ⟨0, ![none, some false], ![.right, .right]⟩
    else none

/-- The output after `i` cells: `(true, false)^i`. -/
def alt (i : ℕ) : List Bool := (List.replicate i [true, false]).flatten

theorem alt_succ (i : ℕ) : alt (i + 1) = alt i ++ [true, false] := by
  unfold alt
  rw [List.replicate_succ', List.flatten_append]
  simp

theorem alt_length (i : ℕ) : (alt i).length = 2 * i := by
  induction i with
  | zero => rfl
  | succ i ih => rw [alt_succ, List.length_append, ih]; simp; omega

def zcfg (q : Fin 3) (b i : ℕ) (o : List Bool) (ho : ℕ) : Configuration 2 3 :=
  ⟨q, ![i, ho], ![List.replicate b true, o]⟩

theorem z0t (b i : ℕ) (hi : i < b) : step zerosM (zcfg 0 b i (alt i) (2 * i)) =
    some (zcfg 1 b i (alt i ++ [true]) (2 * i + 1)) := by
  have hr : readTapeBit (List.replicate b true) i = true := read_replicate_true b i hi
  have hl : (alt i).length = 2 * i := alt_length i
  simp [step, zerosM, zcfg, Configuration.scanned, hr]
  apply configuration_ext
  · rfl
  · funext k; fin_cases k <;> simp [applyAction, HeadMove.apply]
  · funext k; fin_cases k <;> simp [applyAction]
    rw [← hl]
    exact Streaming.write_append (alt i) true

theorem z1 (b i : ℕ) : step zerosM (zcfg 1 b i (alt i ++ [true]) (2 * i + 1)) =
    some (zcfg 0 b (i + 1) (alt (i + 1)) (2 * (i + 1))) := by
  have hl : (alt i ++ [true]).length = 2 * i + 1 := by rw [List.length_append, alt_length]; rfl
  simp [step, zerosM, zcfg]
  apply configuration_ext
  · rfl
  · funext k; fin_cases k <;> simp [applyAction, HeadMove.apply]; omega
  · funext k; fin_cases k <;> simp [applyAction]
    rw [alt_succ, ← hl, Streaming.write_append]
    simp

theorem z0f (b : ℕ) : step zerosM (zcfg 0 b b (alt b) (2 * b)) =
    some (zcfg 2 b b (alt b ++ [false]) (2 * b)) := by
  have hr : readTapeBit (List.replicate b true) b = false := read_replicate_end b true
  have hl : (alt b).length = 2 * b := alt_length b
  simp [step, zerosM, zcfg, Configuration.scanned, hr]
  apply configuration_ext
  · rfl
  · funext k; fin_cases k <;> simp [applyAction, HeadMove.apply]
  · funext k; fin_cases k <;> simp [applyAction]
    rw [← hl]
    exact Streaming.write_append (alt b) false

theorem zloop (b : ℕ) : ∀ i, i ≤ b →
    Timed zerosM (2 * (b - i)) (zcfg 0 b i (alt i) (2 * i)) (zcfg 0 b b (alt b) (2 * b)) := by
  intro i hi
  induction h : b - i generalizing i with
  | zero =>
    have : i = b := by omega
    subst this
    exact Timed.refl _ _
  | succ k ih =>
    have t1 := Timed.single (p := zerosM) (by simp [zerosM, zcfg]) (z0t b i (by omega))
    have t2 := Timed.single (p := zerosM) (by simp [zerosM, zcfg]) (z1 b i)
    have t3 := ih (i + 1) (by omega) (by omega)
    have t := (t1.trans t2).trans t3
    rw [show 1 + 1 + 2 * k = 2 * (k + 1) by omega] at t
    exact t

theorem frame_zeros (b : ℕ) : RepairOrdinary.frame (List.replicate b false) = alt b ++ [false] := by
  induction b with
  | zero => rfl
  | succ b ih =>
    rw [List.replicate_succ, RepairOrdinary.frame, ih]
    unfold alt
    rw [List.replicate_succ]
    simp

/-- **`1^b ↦ frame (0^b)`**, the source kept. -/
theorem zeros_run (b : ℕ) : ∃ H, Step zerosM (2 * b + 1) ![0, 0] ![List.replicate b true, []] H
    ![List.replicate b true, RepairOrdinary.frame (List.replicate b false)] := by
  have t1 := zloop b 0 (by omega)
  have t2 := Timed.single (p := zerosM) (by simp [zerosM, zcfg]) (z0f b)
  obtain ⟨r, hr, hf, hs⟩ := (t1.trans t2).run (by simp [zerosM, zcfg])
  refine ⟨_, r, ?_, rfl, ?_, by omega⟩
  · have hc : (⟨zerosM.start, ![0, 0], ![List.replicate b true, []]⟩ : Configuration 2 3) =
        zcfg 0 b 0 (alt 0) (2 * 0) := rfl
    rw [hc]
    simpa using hr
  · rw [hf, frame_zeros]; rfl

end NearCubicWires.SourceStart.MetaTM


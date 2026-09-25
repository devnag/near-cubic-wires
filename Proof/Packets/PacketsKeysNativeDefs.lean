import Proof.Packets.PacketsKeysScan

set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unusedSimpArgs false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false

namespace NearCubicWires.PacketsKeys.Native
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.RepairOrdinary.RecoveryExecution NearCubicWires.ExtDecompositionBatch
open NearCubicWires.RepairRepresentation NearCubicWires.PacketsMeta NearCubicWires.PacketsKeys
noncomputable section

/-- The program state. -/
structure NS where
  f0 : ℕ
  out : ℕ
  sp : ℕ
  mp : ℕ
  fl : Bool
  tag : ℕ
  h : ℕ
  nc : ℕ
  sum : ℕ
  prod : ℕ
  b : ℕ
  p2 : ℕ
  k : ℕ
  ct : Fin 8 → TS

/-- The role map. -/
def nv (w : List Bool) (s : NS) : Fin 26 → TS :=
  ![.cells (Setup.ff w) s.f0, .out s.out, .cells (sf w) s.sp, .cells (Setup.mk w) s.mp, .ruler,
    .cells blank 0, .flag s.fl, .reg 0, .reg s.tag, .reg s.h, .reg s.nc, .reg s.sum, .reg s.prod,
    .reg s.b, .reg s.p2, .reg 0, .reg 0, .reg s.k,
    s.ct 0, s.ct 1, s.ct 2, s.ct 3, s.ct 4, s.ct 5, s.ct 6, s.ct 7]

/-- Circuit `c`'s stream and marks slots. -/
def sS (c : Fin 4) : Fin 26 := ⟨18 + 2 * c.val, by omega⟩
def sM (c : Fin 4) : Fin 26 := ⟨19 + 2 * c.val, by omega⟩
def cS (c : Fin 4) : Fin 8 := ⟨2 * c.val, by omega⟩
def cM (c : Fin 4) : Fin 8 := ⟨2 * c.val + 1, by omega⟩

theorem nv_S (w : List Bool) (s : NS) (c : Fin 4) : nv w s (sS c) = s.ct (cS c) := by fin_cases c <;> rfl
theorem nv_M (w : List Bool) (s : NS) (c : Fin 4) : nv w s (sM c) = s.ct (cM c) := by fin_cases c <;> rfl

theorem up_S (w : List Bool) (s : NS) (c : Fin 4) (v : TS) :
    Function.update (nv w s) (sS c) v = nv w { s with ct := Function.update s.ct (cS c) v } := by
  funext i; fin_cases c <;> fin_cases i <;> rfl

/-! ## Instructions in role-map form -/

section Instr
variable {W : ℕ} (w : List Bool) (s : NS)

/-- `tag := natWord` from the stream. -/
theorem readTag (x : ℕ) (hsp : s.mp = s.sp) (hW : natBitLength x ≤ W)
    (hS : ∀ i, i < (natWord x).length → sf w (s.sp + i) = (natWord x).getD i false) :
    LRuns W (ReadNat.at5 (4 : Fin 26) 2 3 5 8) (3 * W + 5) (nv w s)
      (nv w { s with sp := s.sp + (natWord x).length, mp := s.sp + (natWord x).length, tag := x }) := by
  have h := ReadNat.at_run (W := W) (nv w s) (4 : Fin 26) 2 3 5 8 (by decide) s.sp x s.tag (sf w) (Setup.mk w)
    hW hS rfl rfl (by simp [nv, hsp]) rfl rfl
  refine h.congr_out ?_
  funext i; fin_cases i <;> rfl

/-- `h := natWord` from the stream. -/
theorem readH (x : ℕ) (hsp : s.mp = s.sp) (hW : natBitLength x ≤ W)
    (hS : ∀ i, i < (natWord x).length → sf w (s.sp + i) = (natWord x).getD i false) :
    LRuns W (ReadNat.at5 (4 : Fin 26) 2 3 5 9) (3 * W + 5) (nv w s)
      (nv w { s with sp := s.sp + (natWord x).length, mp := s.sp + (natWord x).length, h := x }) := by
  have h := ReadNat.at_run (W := W) (nv w s) (4 : Fin 26) 2 3 5 9 (by decide) s.sp x s.h (sf w) (Setup.mk w)
    hW hS rfl rfl (by simp [nv, hsp]) rfl rfl
  refine h.congr_out ?_
  funext i; fin_cases i <;> rfl

/-- `nc := natWord` from the stream. -/
theorem readN (x : ℕ) (hsp : s.mp = s.sp) (hW : natBitLength x ≤ W)
    (hS : ∀ i, i < (natWord x).length → sf w (s.sp + i) = (natWord x).getD i false) :
    LRuns W (ReadNat.at5 (4 : Fin 26) 2 3 5 10) (3 * W + 5) (nv w s)
      (nv w { s with sp := s.sp + (natWord x).length, mp := s.sp + (natWord x).length, nc := x }) := by
  have h := ReadNat.at_run (W := W) (nv w s) (4 : Fin 26) 2 3 5 10 (by decide) s.sp x s.nc (sf w) (Setup.mk w)
    hW hS rfl rfl (by simp [nv, hsp]) rfl rfl
  refine h.congr_out ?_
  funext i; fin_cases i <;> rfl

/-- `k := k + 1`. -/
theorem incK (hk : s.k + 1 < 2 ^ W) :
    LRuns W (swAt addF true true (4 : Fin 26) 17 7 6) (2 * W + 3) (nv w s)
      (nv w { s with k := s.k + 1, fl := false }) := by
  have h := inc_at (W := W) (nv w s) (4 : Fin 26) 17 7 6 (by decide) s.k 0 s.fl rfl rfl rfl rfl rfl hk
  refine h.congr_out ?_
  funext i; fin_cases i <;> rfl

/-- `k := k - 1`. -/
theorem decK (hk : s.k < 2 ^ W) (h1 : 1 ≤ s.k) :
    LRuns W (swAt subF true true (4 : Fin 26) 17 7 6) (2 * W + 3) (nv w s)
      (nv w { s with k := s.k - 1, fl := false }) := by
  have h := dec_at (W := W) (nv w s) (4 : Fin 26) 17 7 6 (by decide) s.k 0 s.fl rfl rfl rfl rfl rfl hk h1
  refine h.congr_out ?_
  funext i; fin_cases i <;> rfl

/-- `flag := tag < k`. -/
theorem ltTag (ht : s.tag < 2 ^ W) (hk : s.k < 2 ^ W) :
    LRuns W (swAt subF false false (4 : Fin 26) 8 17 6) (2 * W + 3) (nv w s)
      (nv w { s with fl := decide (s.tag < s.k) }) := by
  have h := lt_at (W := W) (nv w s) (4 : Fin 26) 8 17 6 (by decide) s.tag s.k s.fl rfl rfl rfl rfl ht hk
  refine h.congr_out ?_
  funext i; fin_cases i <;> rfl

/-- `prod := prod + 1`. -/
theorem incProd (hp : s.prod + 1 < 2 ^ W) :
    LRuns W (swAt addF true true (4 : Fin 26) 12 7 6) (2 * W + 3) (nv w s)
      (nv w { s with prod := s.prod + 1, fl := false }) := by
  have h := inc_at (W := W) (nv w s) (4 : Fin 26) 12 7 6 (by decide) s.prod 0 s.fl rfl rfl rfl rfl rfl hp
  refine h.congr_out ?_
  funext i; fin_cases i <;> rfl

/-- `b := b + 1`. -/
theorem incB (hb : s.b + 1 < 2 ^ W) :
    LRuns W (swAt addF true true (4 : Fin 26) 13 7 6) (2 * W + 3) (nv w s)
      (nv w { s with b := s.b + 1, fl := false }) := by
  have h := inc_at (W := W) (nv w s) (4 : Fin 26) 13 7 6 (by decide) s.b 0 s.fl rfl rfl rfl rfl rfl hb
  refine h.congr_out ?_
  funext i; fin_cases i <;> rfl

/-- `sum := sum + b`. -/
theorem addSum (h1 : s.sum < 2 ^ W) (h2 : s.b < 2 ^ W) (h3 : s.sum + s.b < 2 ^ W) :
    LRuns W (swAt addF false true (4 : Fin 26) 11 13 6) (2 * W + 3) (nv w s)
      (nv w { s with sum := s.sum + s.b, fl := false }) := by
  have h := add_at (W := W) (nv w s) (4 : Fin 26) 11 13 6 (by decide) s.sum s.b s.fl rfl rfl rfl rfl h1 h2 h3
  refine h.congr_out ?_
  funext i; fin_cases i <;> rfl

/-- `prod := p2`. -/
theorem cpyProd (hp : s.p2 < 2 ^ W) :
    LRuns W (swAt copyF false true (4 : Fin 26) 12 14 6) (2 * W + 3) (nv w s)
      (nv w { s with prod := s.p2, fl := false }) := by
  have h := cpy_at (W := W) (nv w s) (4 : Fin 26) 12 14 6 (by decide) s.prod s.p2 s.fl rfl rfl rfl rfl hp
  refine h.congr_out ?_
  funext i; fin_cases i <;> rfl

/-- `p2 := prod · b`. -/
theorem mulP (hb : s.b < 2 ^ W) (hpb : s.prod * s.b < 2 ^ W) (hW : 1 ≤ W) :
    LRuns W (RecoveryFocus.machine ![(4 : Fin 26), 12, 13, 14, 15, 16, 6, 7] Mul.machine)
      (13 * W * W + 60 * W + 40) (nv w s) (nv w { s with p2 := s.prod * s.b, fl := false }) := by
  have h := Mul.at_run (W := W) (nv w s) (4 : Fin 26) 12 13 14 15 16 6 7 (by decide) s.prod s.b s.p2 0 0 s.fl
    rfl rfl rfl rfl rfl rfl rfl rfl hb hpb hW
  refine h.congr_out ?_
  funext i; fin_cases i <;> rfl

/-- `flag := the stream's bit under its cursor`. -/
theorem peekS :
    LRuns W (RecoveryFocus.machine ![(2 : Fin 26), 6] peek) 1 (nv w s)
      (nv w { s with fl := sf w s.sp }) := by
  have h := (peek_lruns W s.sp (sf w) s.fl).dockK ![(2 : Fin 26), 6] (by decide) (nv w s)
    (by intro j; fin_cases j <;> rfl) [1] (by intro j hj; fin_cases j <;> simp at hj ⊢)
  refine h.congr_out ?_
  funext i; fin_cases i <;> rfl

/-- The emitted register `V` (slot `v`) to the output. -/
theorem emitAt (v : Fin 26) (hinj : Function.Injective ![(4 : Fin 26), 7, v, 6, 1]) (V : ℕ)
    (hV : nv w s v = .reg V) (hVW : V < 2 ^ W) :
    LRuns W (RecoveryFocus.machine ![(4 : Fin 26), 7, v, 6, 1] Emit.machine)
      ((V + 1) * ((2 * W + 3) + (2 * W + 3 + 1 + 1) + 2)) (nv w s)
      (Function.update (Function.update (Function.update (nv w s) v (.reg 0)) 6 (.flag false)) 1
        (.out (s.out + V))) := by
  have h := (Emit.run W V s.out s.fl hVW).dockK ![(4 : Fin 26), 7, v, 6, 1] hinj (nv w s)
    (by
      intro j; fin_cases j
      · rfl
      · rfl
      · exact hV
      · rfl
      · rfl) [4, 3, 2]
    (by intro j hj; fin_cases j <;> simp at hj ⊢)
  exact h

end Instr

/-! ## One circuit block -/

/-- The circuit tapes after `m` blocks: the first `m` pairs spent, the rest blank. -/
def ctAfter (m : ℕ) : Fin 8 → TS := fun j => if j.val < 2 * m then .any else .cells blank 0

theorem ctAfter_S (c : Fin 4) : ctAfter c.val (cS c) = .cells blank 0 := by fin_cases c <;> rfl
theorem ctAfter_M (c : Fin 4) : ctAfter c.val (cM c) = .cells blank 0 := by fin_cases c <;> rfl

/-- The block body: unframe the circuit's payload, read its first number `x`, then
`b := x + 1; sum := sum + b; p2 := prod·b; prod := p2`. -/
def body (c : Fin 4) :=
  Composition.machine (RecoveryFocus.machine ![(2 : Fin 26), sS c, sM c] Unframe.machine)
    (Composition.machine (ReadNat.at5 (4 : Fin 26) (sS c) (sM c) 5 13)
      (Composition.machine (swAt addF true true (4 : Fin 26) 13 7 6)
        (Composition.machine (swAt addF false true (4 : Fin 26) 11 13 6)
          (Composition.machine (RecoveryFocus.machine ![(4 : Fin 26), 12, 13, 14, 15, 16, 6, 7] Mul.machine)
            (swAt copyF false true (4 : Fin 26) 12 14 6)))))

/-- One circuit block: peek; if a circuit frame starts here, run the body. -/
def block (c : Fin 4) := Ite (RecoveryFocus.machine ![(2 : Fin 26), 6] peek) (body c) (nop 26) (6 : Fin 26)

def bodyCost (W m : ℕ) : ℕ :=
  (5 * m + 10) + 1 + ((3 * W + 5) + 1 + ((2 * W + 3) + 1 + ((2 * W + 3) + 1 +
    ((13 * W * W + 60 * W + 40) + 1 + (2 * W + 3)))))

def blockCost (W m : ℕ) : ℕ := 1 + bodyCost W m + 0 + 2

section Block
variable {W : ℕ} (w : List Bool) (s : NS)

theorem unframeC (c : Fin 4) (pay : List Bool)
    (hX : ∀ i, i < (RepairOrdinary.frame pay).length → sf w (s.sp + i) = (RepairOrdinary.frame pay).getD i false)
    (hcs : s.ct (cS c) = .cells blank 0) (hcm : s.ct (cM c) = .cells blank 0) :
    LRuns W (RecoveryFocus.machine ![(2 : Fin 26), sS c, sM c] Unframe.machine) (5 * pay.length + 10) (nv w s)
      (nv w { s with
        sp := s.sp + (RepairOrdinary.frame pay).length,
        ct := Function.update (Function.update s.ct (cS c) (.cells (sf pay) 1)) (cM c)
          (.cells (Setup.mk pay) 1) }) := by
  have hi : Function.Injective ![(2 : Fin 26), sS c, sM c] := by fin_cases c <;> decide
  have h := (Unframe.lruns W s.sp pay (sf w) hX).dockK ![(2 : Fin 26), sS c, sM c] hi (nv w s)
    (by
      intro j; fin_cases j
      · rfl
      · exact (nv_S w s c).trans hcs
      · exact (nv_M w s c).trans hcm) [0, 1, 2]
    (by intro j hj; fin_cases j <;> simp at hj)
  refine h.congr_out ?_
  funext i; fin_cases c <;> fin_cases i <;> rfl

theorem readBC (c : Fin 4) (pay rest : List Bool) (x : ℕ) (hpay : pay = natWord x ++ rest)
    (hW : natBitLength x ≤ W)
    (hcs : s.ct (cS c) = .cells (sf pay) 1) (hcm : s.ct (cM c) = .cells (Setup.mk pay) 1) :
    LRuns W (ReadNat.at5 (4 : Fin 26) (sS c) (sM c) 5 13) (3 * W + 5) (nv w s)
      (nv w { s with
        b := x,
        ct := Function.update (Function.update s.ct (cS c) (.cells (sf pay) (1 + (natWord x).length))) (cM c)
          (.cells (Setup.mk pay) (1 + (natWord x).length)) }) := by
  have hi : Function.Injective ![(4 : Fin 26), sS c, sM c, 5, 13] := by fin_cases c <;> decide
  have hS : ∀ i, i < (natWord x).length → sf pay (1 + i) = (natWord x).getD i false := by
    intro i hi
    rw [Nat.add_comm, sf_succ, hpay, List.getD_append _ _ _ _ hi]
  have h := ReadNat.at_run (W := W) (nv w s) (4 : Fin 26) (sS c) (sM c) 5 13 hi 1 x s.b (sf pay) (Setup.mk pay)
    hW hS rfl ((nv_S w s c).trans hcs) ((nv_M w s c).trans hcm) rfl rfl
  refine h.congr_out ?_
  funext i; fin_cases c <;> fin_cases i <;> rfl

/-- The state after unframing circuit `c`'s payload. -/
def uf (s : NS) (c : Fin 4) (pay : List Bool) : NS :=
  { s with
    sp := s.sp + (RepairOrdinary.frame pay).length,
    ct := Function.update (Function.update s.ct (cS c) (.cells (sf pay) 1)) (cM c) (.cells (Setup.mk pay) 1) }

/-- The state after reading its first number. -/
def rbS (s : NS) (c : Fin 4) (pay : List Bool) (x : ℕ) : NS :=
  { s with
    b := x,
    ct := Function.update (Function.update s.ct (cS c) (.cells (sf pay) (1 + (natWord x).length))) (cM c)
      (.cells (Setup.mk pay) (1 + (natWord x).length)) }

/-- The state after the whole body. -/
def bodyOut (s : NS) (c : Fin 4) (pay : List Bool) (x : ℕ) : NS :=
  { rbS (uf s c pay) c pay x with
    b := x + 1, sum := s.sum + (x + 1), p2 := s.prod * (x + 1), prod := s.prod * (x + 1), fl := false }

theorem body_run (c : Fin 4) (pay rest : List Bool) (x : ℕ) (hpay : pay = natWord x ++ rest)
    (hX : ∀ i, i < (RepairOrdinary.frame pay).length → sf w (s.sp + i) = (RepairOrdinary.frame pay).getD i false)
    (hcs : s.ct (cS c) = .cells blank 0) (hcm : s.ct (cM c) = .cells blank 0)
    (hW : natBitLength x ≤ W) (hW1 : 1 ≤ W)
    (hb : x + 1 < 2 ^ W) (hsum : s.sum + (x + 1) < 2 ^ W) (hprod : s.prod * (x + 1) < 2 ^ W) :
    LRuns W (body c) (bodyCost W pay.length) (nv w s) (nv w (bodyOut s c pay x)) := by
  have e1 := unframeC (W := W) w s c pay hX hcs hcm
  have e2 := readBC (W := W) w (uf s c pay) c pay rest x hpay hW (by fin_cases c <;> rfl) (by fin_cases c <;> rfl)
  have e3 := incB (W := W) w (rbS (uf s c pay) c pay x) hb
  have e4 := addSum (W := W) w { rbS (uf s c pay) c pay x with b := x + 1, fl := false } (by
    show s.sum < 2 ^ W
    omega) hb hsum
  have e5 := mulP (W := W) w { rbS (uf s c pay) c pay x with b := x + 1, sum := s.sum + (x + 1), fl := false }
    hb hprod hW1
  have e6 := cpyProd (W := W) w { rbS (uf s c pay) c pay x with
    b := x + 1, sum := s.sum + (x + 1), p2 := s.prod * (x + 1), fl := false } hprod
  exact e1.seq (e2.seq (e3.seq (e4.seq (e5.seq e6))))

theorem nv_ct_same (s : NS) (ct2 : Fin 8 → TS) (i : Fin 26) (h : i.val < 18) :
    nv w { s with ct := ct2 } i = nv w s i := by
  fin_cases i <;> simp [nv] at h ⊢

theorem nv_slot (s : NS) (j : Fin 8) : nv w s ⟨18 + j.val, by omega⟩ = s.ct j := by
  fin_cases j <;> simp [nv]

theorem weaken_ct (s : NS) (ct2 : Fin 8 → TS) (h : ∀ j H A, TR W (s.ct j) H A → TR W (ct2 j) H A) :
    ∀ i H A, TR W (nv w s i) H A → TR W (nv w { s with ct := ct2 } i) H A := by
  intro i H A hi
  by_cases h18 : i.val < 18
  · rw [nv_ct_same w s ct2 i h18]
    exact hi
  · have hi' : i = ⟨18 + (i.val - 18), by omega⟩ := Fin.ext (by simp; omega)
    have hj : i.val - 18 < 8 := by omega
    rw [hi', nv_slot w { s with ct := ct2 } ⟨i.val - 18, hj⟩]
    rw [hi', nv_slot w s ⟨i.val - 18, hj⟩] at hi
    exact h _ H A hi

theorem ctAfter_mono (m : ℕ) (j : Fin 8) (H : ℕ) (A : List Bool) (h : TR W (ctAfter m j) H A) :
    TR W (ctAfter (m + 1) j) H A := by
  unfold ctAfter at h ⊢
  by_cases h1 : j.val < 2 * (m + 1)
  · rw [if_pos h1]; trivial
  · have h2 : ¬ j.val < 2 * m := by omega
    rw [if_neg h1]; rw [if_neg h2] at h; exact h

/-- **A present circuit.** The frame of `pay = natWord x ++ rest` starts at the stream cursor. -/
theorem block_present (c : Fin 4) (pay rest : List Bool) (x : ℕ) (hpay : pay = natWord x ++ rest)
    (hX : ∀ i, i < (RepairOrdinary.frame pay).length → sf w (s.sp + i) = (RepairOrdinary.frame pay).getD i false)
    (hct : s.ct = ctAfter c.val) (hW : natBitLength x ≤ W) (hW1 : 1 ≤ W)
    (hb : x + 1 < 2 ^ W) (hsum : s.sum + (x + 1) < 2 ^ W) (hprod : s.prod * (x + 1) < 2 ^ W) :
    LRuns W (block c) (blockCost W pay.length) (nv w s)
      (nv w { bodyOut s c pay x with ct := ctAfter (c.val + 1) }) := by
  have hne : 0 < (RepairOrdinary.frame pay).length := by rw [RepairOrdinary.frame_length]; omega
  have hbit : sf w s.sp = true := by
    have := hX 0 hne
    rw [Nat.add_zero] at this
    rw [this, hpay]
    have hl := ReadNat.natWord_length x
    cases hn : natWord x with
    | nil => rw [hn] at hl; simp at hl
    | cons y ys => simp [RepairOrdinary.frame]
  unfold blockCost block
  refine Ite.runs (W := W) (np := bodyCost W pay.length) (nq := 0) _ _ _ (6 : Fin 26) (true) (peekS w s)
    (by simp [nv, hbit]) ?_ (fun h => by simp at h)
  intro _
  have hb1 := body_run (W := W) w { s with fl := sf w s.sp } c pay rest x hpay hX
    (by show s.ct (cS c) = _; rw [hct]; exact ctAfter_S c)
    (by show s.ct (cM c) = _; rw [hct]; exact ctAfter_M c) hW hW1 hb hsum hprod
  refine hb1.weaken (weaken_ct w _ _ ?_)
  intro j H A h
  simp only [bodyOut, rbS, uf] at h
  rw [hct] at h
  fin_cases c <;> fin_cases j <;> first | trivial | exact h

/-- **No circuit here.** The stream reads `false` under its cursor. -/
theorem block_absent (c : Fin 4) (m : ℕ) (hbit : sf w s.sp = false) (hct : s.ct = ctAfter c.val) :
    LRuns W (block c) (blockCost W m) (nv w s) (nv w { s with fl := false, ct := ctAfter (c.val + 1) }) := by
  unfold blockCost block
  refine Ite.runs (W := W) (np := bodyCost W m) (nq := 0) _ _ _ (6 : Fin 26) false (peekS w s) (by simp [nv, hbit])
    (fun h => by simp at h) ?_
  intro _
  have e : ({ s with fl := sf w s.sp } : NS) = { s with fl := false } := by rw [hbit]
  rw [e]
  refine (nop_lruns _).weaken (weaken_ct w { s with fl := false } _ ?_)
  intro j H A h
  have h' : TR W (ctAfter c.val j) H A := by rw [← hct]; exact h
  exact ctAfter_mono c.val j H A h'

end Block

end
end NearCubicWires.PacketsKeys.Native


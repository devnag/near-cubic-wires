import Proof.Packets.PacketsKeysScan

set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unusedSimpArgs false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false

namespace NearCubicWires.PacketsKeys.Pow
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.RepairOrdinary.RecoveryExecution NearCubicWires.ExtDecompositionBatch
open NearCubicWires.PacketsMeta NearCubicWires.PacketsKeys
noncomputable section

/-- A unary word's cells. -/
def u (v : ℕ) : ℕ → Bool := fun j => decide (j < v)

/-! ## Marking the ruler -/

/-- Write `true` under the head and move right (the ruler under construction). -/
def markR : Machine 1 2 := oneStep 1 (fun _ => (fun _ => some true, fun _ => .right))

theorem markR_lruns (W P : ℕ) (hP : 1 ≤ P) : LRuns W markR 1 ![.cells (Ruler.rb P) P] ![.cells (Ruler.rb (P + 1)) (P + 1)] := by
  intro H A hA
  have h0 : H 0 = P ∧ ∀ j, readTapeBit (A 0) j = Ruler.rb P j := hA 0
  refine ⟨_, _, oneStep_run 1 _ H A, ?_⟩
  intro i
  fin_cases i
  refine ⟨by simp [HeadMove.apply, h0.1], fun j => ?_⟩
  simp only [acted]
  have e0 : H ⟨0, by omega⟩ = P := h0.1
  have e1 : ∀ j, readTapeBit (A ⟨0, by omega⟩) j = Ruler.rb P j := h0.2
  rw [read_write, e0, e1]
  unfold Ruler.rb
  by_cases hj : j = P
  · subst hj; simp; omega
  · rw [if_neg hj]; by_cases h1 : 1 ≤ j <;> simp [h1] <;> omega

/-! ## The state -/

structure PS where
  ix : ℕ
  ie : ℕ
  iw : ℕ
  out : ℕ
  dx : ℕ
  de : ℕ
  dw : ℕ
  rl : TS
  fl : Bool
  xr : ℕ
  er : ℕ
  pr : ℕ
  p2 : ℕ

/-- The role map (inputs `x`, `e`, `w` fixed). -/
def pv (x e w : ℕ) (s : PS) : Fin 16 → TS :=
  ![.cells (u x) s.ix, .cells (u e) s.ie, .cells (u w) s.iw, .out s.out, .cells blank s.dx, .cells blank s.de,
    .cells blank s.dw, s.rl, .flag s.fl, .reg 0, .reg s.xr, .reg s.er, .reg s.pr, .reg s.p2, .reg 0, .reg 0]

section Instr
variable {W : ℕ} (x e w : ℕ) (s : PS)

theorem moveRL :
    LRuns W (RecoveryFocus.machine ![(7 : Fin 16)] moveR) 1 (pv x e w { s with rl := .cells blank 0 })
      (pv x e w { s with rl := .cells (Ruler.rb 1) 1 }) := by
  have h := (moveR_lruns W 0 blank).dockK ![(7 : Fin 16)] (by decide) (pv x e w { s with rl := .cells blank 0 })
    (by intro j; fin_cases j; rfl) [0] (by intro j hj; fin_cases j; simp at hj)
  refine h.congr_out ?_
  have hb : Ruler.rb 1 = blank := Setup.rb_one
  rw [hb]
  funext i; fin_cases i <;> rfl

theorem readW (hp : s.dw = s.iw) :
    LRuns W (RecoveryFocus.machine ![(6 : Fin 16), 2, 8] readBit) 1 (pv x e w s)
      (pv x e w { s with dw := s.iw + 1, iw := s.iw + 1, fl := u w s.iw }) := by
  have h := (readBit_lruns W s.iw (u w) blank s.fl).dockK ![(6 : Fin 16), 2, 8] (by decide) (pv x e w s)
    (by intro j; fin_cases j
        · simp [pv, hp]
        · rfl
        · rfl) [0, 1, 2] (by intro j hj; fin_cases j <;> simp at hj)
  refine h.congr_out ?_
  funext i; fin_cases i <;> rfl

theorem readX (hp : s.dx = s.ix) :
    LRuns W (RecoveryFocus.machine ![(4 : Fin 16), 0, 8] readBit) 1 (pv x e w s)
      (pv x e w { s with dx := s.ix + 1, ix := s.ix + 1, fl := u x s.ix }) := by
  have h := (readBit_lruns W s.ix (u x) blank s.fl).dockK ![(4 : Fin 16), 0, 8] (by decide) (pv x e w s)
    (by intro j; fin_cases j
        · simp [pv, hp]
        · rfl
        · rfl) [0, 1, 2] (by intro j hj; fin_cases j <;> simp at hj)
  refine h.congr_out ?_
  funext i; fin_cases i <;> rfl

theorem readE (hp : s.de = s.ie) :
    LRuns W (RecoveryFocus.machine ![(5 : Fin 16), 1, 8] readBit) 1 (pv x e w s)
      (pv x e w { s with de := s.ie + 1, ie := s.ie + 1, fl := u e s.ie }) := by
  have h := (readBit_lruns W s.ie (u e) blank s.fl).dockK ![(5 : Fin 16), 1, 8] (by decide) (pv x e w s)
    (by intro j; fin_cases j
        · simp [pv, hp]
        · rfl
        · rfl) [0, 1, 2] (by intro j hj; fin_cases j <;> simp at hj)
  refine h.congr_out ?_
  funext i; fin_cases i <;> rfl

theorem markRL (P : ℕ) (hP : 1 ≤ P) (hr : s.rl = .cells (Ruler.rb P) P) :
    LRuns W (RecoveryFocus.machine ![(7 : Fin 16)] markR) 1 (pv x e w s)
      (pv x e w { s with rl := .cells (Ruler.rb (P + 1)) (P + 1) }) := by
  have h := (markR_lruns W P hP).dockK ![(7 : Fin 16)] (by decide) (pv x e w s)
    (by intro j; fin_cases j; simp [pv, hr]) [0] (by intro j hj; fin_cases j; simp at hj)
  refine h.congr_out ?_
  funext i; fin_cases i <;> rfl

theorem finishRL (hr : s.rl = .cells (Ruler.rb (W + 1)) (W + 1)) :
    LRuns W (RecoveryFocus.machine ![(7 : Fin 16)] Ruler.finish) (W + 3) (pv x e w s)
      (pv x e w { s with rl := .ruler }) := by
  have h := (Ruler.finish_lruns W).dockK ![(7 : Fin 16)] (by decide) (pv x e w s)
    (by intro j; fin_cases j; simp [pv, hr]) [0] (by intro j hj; fin_cases j; simp at hj)
  refine h.congr_out ?_
  funext i; fin_cases i <;> rfl

theorem incXR (hr : s.rl = .ruler) (h : s.xr + 1 < 2 ^ W) :
    LRuns W (swAt addF true true (7 : Fin 16) 10 9 8) (2 * W + 3) (pv x e w s)
      (pv x e w { s with xr := s.xr + 1, fl := false }) := by
  have hh := inc_at (W := W) (pv x e w s) (7 : Fin 16) 10 9 8 (by decide) s.xr 0 s.fl (by simp [pv, hr]) rfl rfl rfl
    rfl h
  refine hh.congr_out ?_
  funext i; fin_cases i <;> first | rfl | simp [pv, hr]

theorem incER (hr : s.rl = .ruler) (h : s.er + 1 < 2 ^ W) :
    LRuns W (swAt addF true true (7 : Fin 16) 11 9 8) (2 * W + 3) (pv x e w s)
      (pv x e w { s with er := s.er + 1, fl := false }) := by
  have hh := inc_at (W := W) (pv x e w s) (7 : Fin 16) 11 9 8 (by decide) s.er 0 s.fl (by simp [pv, hr]) rfl rfl rfl
    rfl h
  refine hh.congr_out ?_
  funext i; fin_cases i <;> first | rfl | simp [pv, hr]

theorem incPR (hr : s.rl = .ruler) (h : s.pr + 1 < 2 ^ W) :
    LRuns W (swAt addF true true (7 : Fin 16) 12 9 8) (2 * W + 3) (pv x e w s)
      (pv x e w { s with pr := s.pr + 1, fl := false }) := by
  have hh := inc_at (W := W) (pv x e w s) (7 : Fin 16) 12 9 8 (by decide) s.pr 0 s.fl (by simp [pv, hr]) rfl rfl rfl
    rfl h
  refine hh.congr_out ?_
  funext i; fin_cases i <;> first | rfl | simp [pv, hr]

theorem decER (hr : s.rl = .ruler) (h : s.er < 2 ^ W) (h1 : 1 ≤ s.er) :
    LRuns W (swAt subF true true (7 : Fin 16) 11 9 8) (2 * W + 3) (pv x e w s)
      (pv x e w { s with er := s.er - 1, fl := false }) := by
  have hh := dec_at (W := W) (pv x e w s) (7 : Fin 16) 11 9 8 (by decide) s.er 0 s.fl (by simp [pv, hr]) rfl rfl rfl
    rfl h h1
  refine hh.congr_out ?_
  funext i; fin_cases i <;> first | rfl | simp [pv, hr]

/-- `flag := 0 < E`. -/
theorem testER (hr : s.rl = .ruler) (h : s.er < 2 ^ W) :
    LRuns W (swAt subF false false (7 : Fin 16) 9 11 8) (2 * W + 3) (pv x e w s)
      (pv x e w { s with fl := decide (0 < s.er) }) := by
  have hh := lt_at (W := W) (pv x e w s) (7 : Fin 16) 9 11 8 (by decide) 0 s.er s.fl (by simp [pv, hr]) rfl rfl rfl
    (Nat.two_pow_pos W) h
  refine hh.congr_out ?_
  funext i; fin_cases i <;> first | rfl | simp [pv, hr]

theorem mulPX (hr : s.rl = .ruler) (hx : s.xr < 2 ^ W) (hpx : s.pr * s.xr < 2 ^ W) (hW : 1 ≤ W) :
    LRuns W (RecoveryFocus.machine ![(7 : Fin 16), 12, 10, 13, 14, 15, 8, 9] Mul.machine)
      (13 * W * W + 60 * W + 40) (pv x e w s) (pv x e w { s with p2 := s.pr * s.xr, fl := false }) := by
  have hh := Mul.at_run (W := W) (pv x e w s) (7 : Fin 16) 12 10 13 14 15 8 9 (by decide) s.pr s.xr s.p2 0 0 s.fl
    (by simp [pv, hr]) rfl rfl rfl rfl rfl rfl rfl hx hpx hW
  refine hh.congr_out ?_
  funext i; fin_cases i <;> first | rfl | simp [pv, hr]

theorem cpyPR (hr : s.rl = .ruler) (h : s.p2 < 2 ^ W) :
    LRuns W (swAt copyF false true (7 : Fin 16) 12 13 8) (2 * W + 3) (pv x e w s)
      (pv x e w { s with pr := s.p2, fl := false }) := by
  have hh := cpy_at (W := W) (pv x e w s) (7 : Fin 16) 12 13 8 (by decide) s.pr s.p2 s.fl (by simp [pv, hr]) rfl rfl rfl
    h
  refine hh.congr_out ?_
  funext i; fin_cases i <;> first | rfl | simp [pv, hr]

theorem emitPR (hr : s.rl = .ruler) (h : s.pr < 2 ^ W) :
    LRuns W (RecoveryFocus.machine ![(7 : Fin 16), 9, 12, 8, 3] Emit.machine)
      ((s.pr + 1) * ((2 * W + 3) + (2 * W + 3 + 1 + 1) + 2)) (pv x e w s)
      (pv x e w { s with pr := 0, fl := false, out := s.out + s.pr }) := by
  have hh := (Emit.run W s.pr s.out s.fl h).dockK ![(7 : Fin 16), 9, 12, 8, 3] (by decide) (pv x e w s)
    (by intro j; fin_cases j
        · simp [pv, hr]
        · rfl
        · rfl
        · rfl
        · rfl) [4, 3, 2] (by intro j hj; fin_cases j <;> simp at hj ⊢)
  refine hh.congr_out ?_
  funext i; fin_cases i <;> first | rfl | simp [pv, hr]

end Instr

/-! ## The program -/

def rulerLoop := Loop (RecoveryFocus.machine ![(6 : Fin 16), 2, 8] readBit) (RecoveryFocus.machine ![(7 : Fin 16)] markR)
  (8 : Fin 16)
def loadX := Loop (RecoveryFocus.machine ![(4 : Fin 16), 0, 8] readBit) (swAt addF true true (7 : Fin 16) 10 9 8)
  (8 : Fin 16)
def loadE := Loop (RecoveryFocus.machine ![(5 : Fin 16), 1, 8] readBit) (swAt addF true true (7 : Fin 16) 11 9 8)
  (8 : Fin 16)
def powLoop := Loop (swAt subF false false (7 : Fin 16) 9 11 8)
  (Composition.machine (RecoveryFocus.machine ![(7 : Fin 16), 12, 10, 13, 14, 15, 8, 9] Mul.machine)
    (Composition.machine (swAt copyF false true (7 : Fin 16) 12 13 8) (swAt subF true true (7 : Fin 16) 11 9 8)))
  (8 : Fin 16)

def prog :=
  Composition.machine (RecoveryFocus.machine ![(7 : Fin 16)] moveR)
    (Composition.machine rulerLoop
      (Composition.machine (RecoveryFocus.machine ![(7 : Fin 16)] Ruler.finish)
        (Composition.machine loadX
          (Composition.machine loadE
            (Composition.machine (swAt addF true true (7 : Fin 16) 12 9 8)
              (Composition.machine powLoop (RecoveryFocus.machine ![(7 : Fin 16), 9, 12, 8, 3] Emit.machine)))))))

/-- The start state. -/
def s0 : PS where
  ix := 0
  ie := 0
  iw := 0
  out := 0
  dx := 0
  de := 0
  dw := 0
  rl := .cells blank 0
  fl := false
  xr := 0
  er := 0
  pr := 0
  p2 := 0

section Run
variable (x e w : ℕ)

def sR (i : ℕ) : PS := { s0 with iw := i, dw := i, rl := .cells (Ruler.rb (i + 1)) (i + 1), fl := decide (0 < i) }
def tR (w i : ℕ) : PS := { s0 with iw := i + 1, dw := i + 1, rl := .cells (Ruler.rb (i + 1)) (i + 1), fl := decide (i < w) }

theorem ruler_run :
    LRuns w rulerLoop ((w + 1) * (1 + 1 + 2)) (pv x e w (sR 0)) (pv x e w (tR w w)) := by
  refine Loop.runs _ _ _ (fun i => pv x e w (sR i)) (fun i => pv x e w (tR w i)) w (fun i _ => ?_) (fun i _ => rfl)
    (fun i hi => ?_)
  · exact readW (W := w) x e w (sR i) rfl
  · have h := markRL (W := w) x e w (tR w i) (i + 1) (by omega) rfl
    refine h.congr_out ?_
    congr 1
    simp only [tR, sR, s0]
    congr 1
    simp [hi]

def tRX (w : ℕ) : PS := { tR w w with rl := .ruler }

def sX (w i : ℕ) : PS := { tRX w with ix := i, dx := i, xr := i, fl := false }
def tX (x w i : ℕ) : PS := { tRX w with ix := i + 1, dx := i + 1, xr := i, fl := decide (i < x) }

theorem loadX_run (hx : x < 2 ^ w) :
    LRuns w loadX ((x + 1) * (1 + (2 * w + 3) + 2)) (pv x e w (sX w 0)) (pv x e w (tX x w x)) := by
  refine Loop.runs _ _ _ (fun i => pv x e w (sX w i)) (fun i => pv x e w (tX x w i)) x (fun i _ => ?_) (fun i _ => rfl)
    (fun i hi => ?_)
  · exact readX (W := w) x e w (sX w i) rfl
  · exact incXR (W := w) x e w (tX x w i) rfl (by show i + 1 < 2 ^ w; omega)

def tXE (x w : ℕ) : PS := { tX x w x with fl := false }

def sE (x w i : ℕ) : PS := { tXE x w with ie := i, de := i, er := i, fl := false }
def tE (x e w i : ℕ) : PS := { tXE x w with ie := i + 1, de := i + 1, er := i, fl := decide (i < e) }

theorem loadE_run (he : e < 2 ^ w) :
    LRuns w loadE ((e + 1) * (1 + (2 * w + 3) + 2)) (pv x e w (sE x w 0)) (pv x e w (tE x e w e)) := by
  refine Loop.runs _ _ _ (fun i => pv x e w (sE x w i)) (fun i => pv x e w (tE x e w i)) e (fun i _ => ?_)
    (fun i _ => rfl) (fun i hi => ?_)
  · exact readE (W := w) x e w (sE x w i) rfl
  · exact incER (W := w) x e w (tE x e w i) rfl (by show i + 1 < 2 ^ w; omega)

def sP (x e w i : ℕ) : PS := { tE x e w e with er := e - i, pr := x ^ i, p2 := if i = 0 then 0 else x ^ i, fl := false }
def tP (x e w i : ℕ) : PS := { sP x e w i with fl := decide (i < e) }

theorem pow_run (hx : x < 2 ^ w) (he : e < 2 ^ w) (hp : x ^ e < 2 ^ w) (hw : 1 ≤ w) :
    LRuns w powLoop ((e + 1) * ((2 * w + 3) + ((13 * w * w + 60 * w + 40) + 1 + ((2 * w + 3) + 1 + (2 * w + 3))) + 2))
      (pv x e w (sP x e w 0)) (pv x e w (tP x e w e)) := by
  have hmono : ∀ i, i ≤ e → x ^ i < 2 ^ w := by
    intro i hi
    rcases Nat.eq_zero_or_pos x with h0 | h0
    · subst h0; rcases Nat.eq_zero_or_pos i with hi0 | hi0
      · subst hi0; simp; omega
      · rw [Nat.zero_pow hi0]; exact Nat.two_pow_pos w
    · exact lt_of_le_of_lt (Nat.pow_le_pow_right h0 hi) hp
  refine Loop.runs _ _ _ (fun i => pv x e w (sP x e w i)) (fun i => pv x e w (tP x e w i)) e (fun i hi => ?_)
    (fun i _ => rfl) (fun i hi => ?_)
  · have h := testER (W := w) x e w (sP x e w i) rfl (by show e - i < _; omega)
    refine h.congr_out ?_
    congr 1
    simp only [tP, sP]
    congr 1
    by_cases h' : i < e <;> simp [h'] <;> omega
  · have hi1 : x ^ i * x < 2 ^ w := by rw [← pow_succ]; exact hmono (i + 1) hi
    have e1 := mulPX (W := w) x e w (tP x e w i) rfl hx hi1 hw
    have e2 := cpyPR (W := w) x e w { tP x e w i with p2 := x ^ i * x, fl := false } rfl hi1
    have e3 := decER (W := w) x e w { tP x e w i with p2 := x ^ i * x, pr := x ^ i * x, fl := false } rfl
      (by show e - i < _; omega) (by show 1 ≤ e - i; omega)
    refine (e1.seq (e2.seq e3)).congr_out ?_
    congr 1
    try simp [tP, sP, pow_succ, Nat.sub_sub]

theorem prog_run (hx : x < 2 ^ w) (he : e < 2 ^ w) (hp : x ^ e < 2 ^ w) (hw : 1 ≤ w) :
    ∃ s : PS, LRuns w prog
      (1 + 1 + ((w + 1) * (1 + 1 + 2) + 1 + ((w + 3) + 1 + ((x + 1) * (1 + (2 * w + 3) + 2) + 1 +
        ((e + 1) * (1 + (2 * w + 3) + 2) + 1 + ((2 * w + 3) + 1 +
        ((e + 1) * ((2 * w + 3) + ((13 * w * w + 60 * w + 40) + 1 + ((2 * w + 3) + 1 + (2 * w + 3))) + 2) + 1 +
        (x ^ e + 1) * ((2 * w + 3) + (2 * w + 3 + 1 + 1) + 2))))))))
      (pv x e w s0) (pv x e w s) ∧ s.out = x ^ e := by
  have e1 := moveRL (W := w) x e w s0
  have e2 := ruler_run x e w
  have e3 := finishRL (W := w) x e w (tR w w) rfl
  have e4 := loadX_run x e w hx
  have e5 := loadE_run x e w he
  have e6 := incPR (W := w) x e w (tE x e w e) rfl (by show 0 + 1 < _; have := Nat.one_lt_two_pow_iff.mpr (show w ≠ 0 by omega); omega)
  have e7 := pow_run x e w hx he hp hw
  have e8 := emitPR (W := w) x e w (tP x e w e) rfl (hp)
  refine ⟨_, e1.seq (lr_src (e2.seq (lr_src (e3.seq (lr_src (e4.seq (lr_src (e5.seq (lr_src (e6.seq (lr_src (e7.seq e8)
    ?_)) ?_)) ?_)) ?_)) ?_)) ?_), ?_⟩
  all_goals first
    | rfl
    | (simp [tP, sP, tE, tXE, tX, tRX, tR, s0]; done)
    | (congr 1; simp [sP, tE, tXE, tX, tRX, tR, sR, sE, sX, s0])

end Run

end
end NearCubicWires.PacketsKeys.Pow


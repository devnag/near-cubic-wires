import Proof.SourceAssembly.SourceWiring

section
set_option autoImplicit false
set_option maxRecDepth 120000
set_option warningAsError true

open NearCubicWires LocalBitMultitape ExtDecompositionBatch RepairOrdinary RepairOrdinary.RecoveryRootRound
namespace NearCubicWires.SourceConstruction.Prologue
noncomputable section

/-- A zero-head dock that keeps the ambient heads. -/
theorem dockKeep {t u s n : ℕ} {p : Machine t s} {tin tout : Fin t → List Bool}
    (h : Step p n (fun _ => 0) tin (fun _ => 0) tout) (slots : Fin t → Fin u)
    (hi : Function.Injective slots) (H : Fin u → ℕ) (A : Fin u → List Bool)
    (hH : ∀ j, H (slots j) = 0) (hA : ∀ j, A (slots j) = tin j) :
    Step (RecoveryFocus.machine slots p) n H A H (install slots A tout) := by
  have hs := h.dock slots hi H A hH hA
  rwa [BlockPlatform.dockH_existing slots H (fun _ => 0) hH] at hs

/-- A full-length bounded copy reproduces the source. -/
theorem copied_full (w : List Bool) : RecoveryBoundedTapeCopy.copied w w.length = w := by
  apply List.ext_getElem
  · simp
  · intro n h1 h2
    simp [RecoveryBoundedTapeCopy.copied, readTapeBit, List.getD, h2]

/-- The E6 machine: erase the copy, copy the query word, erase the cache word. -/
def restoreMachine {V : ℕ} (src dst drv log : Fin V) :=
  Composition.machine (Composition.machine
    (RecoveryFocus.machine (![dst, drv, log] : Fin (1+1+1) → Fin V) (RecoveryScratchErase.resetMachine 1))
    (RecoveryFocus.machine (![src, dst, drv, log] : Fin 4 → Fin V) RecoveryBoundedTapeCopy.machine))
    (RecoveryFocus.machine (![src, drv, log] : Fin (1+1+1) → Fin V) (RecoveryScratchErase.resetMachine 1))

/-- **E6: copy the query word to the resident tape, restore the cache.** -/
theorem query_restore {V : ℕ} (src dst drv log : Fin V)
    (h1 : src ≠ dst) (h2 : src ≠ drv) (h3 : src ≠ log) (h4 : dst ≠ drv) (h5 : dst ≠ log) (h6 : drv ≠ log)
    (C : ℕ) (w : List Bool) (hw : w.length = C) (H : Fin V → ℕ) (A : Fin V → List Bool)
    (hsrc : A src = w) (hdrv : A drv = List.replicate C true) (hlog : A log = List.replicate (C+1) false)
    (hdst : (A dst).length ≤ C)
    (hHs : H src = 0) (hHd : H dst = 0) (hHv : H drv = 0) (hHl : H log = 0) :
    ∃ A', Step (restoreMachine src dst drv log) ((2*C+4) + 1 + (2*C+4) + 1 + (2*C+4)) H A H A' ∧
      A' src = List.replicate C false ∧ A' dst = w ∧ A' drv = List.replicate C true ∧
      A' log = List.replicate (C+1) false ∧
      (∀ x, x ≠ src → x ≠ dst → x ≠ drv → x ≠ log → A' x = A x) := by
  have hmax : max (C+1) (C+1) = C+1 := max_self _
  -- stage 1: erase the copy
  let s1 : Fin (1+1+1) → Fin V := ![dst, drv, log]
  have i1 : Function.Injective s1 := by
    intro a b h; fin_cases a <;> fin_cases b <;> simp_all [s1]
  have e1 := Step.of_ready (RecoveryScratchErase.erase_ready (t := 1) C (C+1) ![A dst]
    (fun i => by fin_cases i; exact hdst))
  have st1 := dockKeep e1 s1 i1 H A (by intro j; fin_cases j <;> assumption) (by
    intro j; fin_cases j
    · rfl
    · exact hdrv
    · exact hlog)
  set A1 := install s1 A (Fin.addCases (Fin.addCases (fun _ : Fin 1 => List.replicate C false)
      (fun _ : Fin 1 => List.replicate C true))
      (fun _ : Fin 1 => List.replicate (max (C+1) (C+1)) false)) with hA1
  have A1d : A1 dst = List.replicate C false := install_slot s1 i1 A _ 0
  have A1v : A1 drv = List.replicate C true := install_slot s1 i1 A _ 1
  have A1l : A1 log = List.replicate (C+1) false := by
    rw [show A1 log = _ from install_slot s1 i1 A _ 2]
    show List.replicate (max (C+1) (C+1)) false = _
    rw [hmax]
  have A1o : ∀ x, x ≠ dst → x ≠ drv → x ≠ log → A1 x = A x := by
    intro x a b c
    exact install_other s1 A _ x (by intro j; fin_cases j <;> simp [s1] <;> intro h <;> simp_all)
  have A1s : A1 src = w := (A1o src h1 h2 h3).trans hsrc
  -- stage 2: copy
  let s2 : Fin 4 → Fin V := ![src, dst, drv, log]
  have i2 : Function.Injective s2 := by
    intro a b h; fin_cases a <;> fin_cases b <;> simp_all [s2]
  have c0 := RecoveryChildSelection.ReadyRun.pad (RecoveryBoundedTapeCopy.copy_ready w C (C+1)) ![0, C, 0, 0]
  have e2 := Step.of_ready c0
  have st2 := dockKeep e2 s2 i2 H A1 (by
    intro j; fin_cases j <;> assumption) (by
    intro j; fin_cases j
    · show A1 src = _; simp [A1s]
    · show A1 dst = _; simp [A1d, ZeroPadding.pad]
    · show A1 drv = _; simp [A1v]
    · show A1 log = _; simp [A1l])
  set A2 := install s2 A1 (fun i => ZeroPadding.pad ((![0, C, 0, 0] : Fin 4 → ℕ) i)
      ((![w, RecoveryBoundedTapeCopy.copied w C, List.replicate C true,
        List.replicate (max (C+1) (C+1)) false] : Fin 4 → List Bool) i)) with hA2
  have A2s : A2 src = w := by rw [show A2 src = _ from install_slot s2 i2 A1 _ 0]; simp
  have A2d : A2 dst = w := by
    rw [show A2 dst = _ from install_slot s2 i2 A1 _ 1]
    simp only [Matrix.cons_val_one]
    rw [← hw, copied_full]
    simp [ZeroPadding.pad]
  have A2v : A2 drv = List.replicate C true := by
    rw [show A2 drv = _ from install_slot s2 i2 A1 _ 2]; simp
  have A2l : A2 log = List.replicate (C+1) false := by
    rw [show A2 log = _ from install_slot s2 i2 A1 _ 3]
    show ZeroPadding.pad 0 (List.replicate (max (C+1) (C+1)) false) = _
    rw [hmax, ZeroPadding.pad_zero]
  have A2o : ∀ x, x ≠ src → x ≠ dst → x ≠ drv → x ≠ log → A2 x = A1 x := by
    intro x a b c d
    exact install_other s2 A1 _ x (by intro j; fin_cases j <;> simp [s2] <;> intro h <;> simp_all)
  -- stage 3: erase the cache word
  let s3 : Fin (1+1+1) → Fin V := ![src, drv, log]
  have i3 : Function.Injective s3 := by
    intro a b h; fin_cases a <;> fin_cases b <;> simp_all [s3]
  have e3 := Step.of_ready (RecoveryScratchErase.erase_ready (t := 1) C (C+1) ![w]
    (fun i => by fin_cases i; exact hw.le))
  have st3 := dockKeep e3 s3 i3 H A2 (by intro j; fin_cases j <;> assumption) (by
    intro j; fin_cases j
    · exact A2s
    · exact A2v
    · exact A2l)
  set A3 := install s3 A2 (Fin.addCases (Fin.addCases (fun _ : Fin 1 => List.replicate C false)
      (fun _ : Fin 1 => List.replicate C true))
      (fun _ : Fin 1 => List.replicate (max (C+1) (C+1)) false)) with hA3
  refine ⟨A3, (st1.seq st2).seq st3, install_slot s3 i3 A2 _ 0, ?_, install_slot s3 i3 A2 _ 1, ?_, ?_⟩
  · rw [hA3, install_other s3 A2 _ dst (by intro j; fin_cases j <;> simp [s3] <;> intro h <;> simp_all)]
    exact A2d
  · rw [show A3 log = _ from install_slot s3 i3 A2 _ 2]
    show List.replicate (max (C+1) (C+1)) false = _
    rw [hmax]
  · intro x a b c d
    rw [hA3, install_other s3 A2 _ x (by intro j; fin_cases j <;> simp [s3] <;> intro h <;> simp_all),
      A2o x a b c d, A1o x b c d]

/-- A `ClockJoin.ReadyRun` is a zero-head `Step`. -/
theorem step_of_clock {t s n : ℕ} {p : Machine t s} {input output : Fin t → List Bool}
    (h : ClockJoin.ReadyRun p n input output) : Step p n (fun _ => 0) input (fun _ => 0) output := by
  obtain ⟨r, hr, ht, hh, hs⟩ := h
  refine ⟨r, ?_, ?_, ht, hs⟩
  · change runFrom p n (initialConfiguration p input) = some r at hr
    exact hr
  · funext i; exact hh i

/-- A zero-head run, padded tape by tape and docked, keeping the ambient heads. -/
theorem dockPad {t u st n : ℕ} {p : Machine t st} {tin tout : Fin t → List Bool}
    (h : Step p n (fun _ => 0) tin (fun _ => 0) tout) (c : Fin t → ℕ) (sl : Fin t → Fin u)
    (hs : Function.Injective sl) (H : Fin u → ℕ) (A : Fin u → List Bool)
    (hH : ∀ j, H (sl j) = 0) (hA : ∀ j, A (sl j) = ZeroPadding.pad (c j) (tin j)) :
    Step (RecoveryFocus.machine sl p) n H A H (install sl A (fun j => ZeroPadding.pad (c j) (tout j))) :=
  dockKeep (h.pad c) sl hs H A hH hA

/-! ### The F6 denominator pipeline on 66 tapes (`g`)

Tapes `g 0 .. g 58`: blank scratch (`replicate Rc false`). `g 59 = 1^e`, `g 60 = 1^p` (the unary counts),
`g 61 = 1^w`, `g 62 = 1^q` (residents, kept), `g 63 = enc 4`, `g 64, g 65` = the clear's driver `1^Rc`
and log `0^(Rc+2)` (kept). Seven stages: erase `enc 4`; `count_run e` (→ `g 4`); `count_run p` (→ `g 13`);
copy `1^w` (→ `g 19`); copy `1^q` (→ `g 22`); `ClockNormalize` (→ `g 24 = frame (binary w p)`); the engine. -/

def sE : Fin (1+1+1) → Fin 66 := ![63, 64, 65]
def sCe : Fin 10 → Fin 66 := ![59, 0, 1, 2, 3, 4, 5, 6, 7, 8]
def sCp : Fin 10 → Fin 66 := ![60, 9, 10, 11, 12, 13, 14, 15, 16, 17]
def sW : Fin 4 → Fin 66 := ![61, 18, 19, 20]
def sQ : Fin 4 → Fin 66 := ![62, 21, 22, 23]
def sN : Fin 5 → Fin 66 := ![19, 13, 24, 25, 26]
def sD : Fin 37 → Fin 66 := ![4, 24, 19, 22, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42,
  43, 44, 45, 46, 47, 48, 63, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58]

theorem sE_inj : Function.Injective sE := by decide
theorem sCe_inj : Function.Injective sCe := by decide
theorem sCp_inj : Function.Injective sCp := by decide
theorem sW_inj : Function.Injective sW := by decide
theorem sQ_inj : Function.Injective sQ := by decide
theorem sN_inj : Function.Injective sN := by decide
theorem sD_inj : Function.Injective sD := by decide

/-- The F6 denominator machine on the 66-tape local universe. -/
def f6Machine :=
  Composition.machine (Composition.machine (Composition.machine (Composition.machine
  (Composition.machine (Composition.machine
    (RecoveryFocus.machine sE (RecoveryScratchErase.resetMachine 1))
    (RecoveryFocus.machine sCe CloseoutRowsCountBinary.machine))
    (RecoveryFocus.machine sCp CloseoutRowsCountBinary.machine))
    (RecoveryFocus.machine sW ClockUnarySum.machine))
    (RecoveryFocus.machine sQ ClockUnarySum.machine))
    (RecoveryFocus.machine sN ClockNormalize.machine))
    (RecoveryFocus.machine sD CompetitorDenominator.machine)

def f6Cost (Rc e p w q : ℕ) : ℕ :=
  (2*Rc+4) + 1 + CloseoutRowsCountBinary.budget e + 1 + CloseoutRowsCountBinary.budget p + 1 +
    (2*w+6) + 1 + (2*q+6) + 1 + (4*w+4) + 1 +
    CompetitorDenominator.budget (natBitLength e) w q

theorem value_bits (n : ℕ) : RadixSemantics.value (CloseoutRowsCountBinary.bits n) = n := by
  unfold CloseoutRowsCountBinary.bits
  split_ifs with h
  · subst h; rfl
  · exact SignedSortKey.binary_value _ _ (Nat.lt_pow_succ_log_self (by norm_num) n)

theorem bits_pos (n : ℕ) (h : 1 ≤ n) :
    CloseoutRowsCountBinary.bits n = SignedSortKey.binary (natBitLength n) n := by
  unfold CloseoutRowsCountBinary.bits; rw [if_neg (by omega)]

/-- `ClockNormalize.scalar_run` as a zero-head `Step`. -/
theorem scalar_step (w : ℕ) (bits : List Bool) (h : bits.length ≤ w) :
    Step ClockNormalize.machine (4*w+4) (fun _ => 0) (ClockNormalize.input w bits) (fun _ => 0)
      (Fin.addCases (motive := fun _ : Fin (4+1) => List Bool)
        ![List.replicate w true, RepairOrdinary.frame bits,
          RepairOrdinary.frame (SignedSortKey.binary w (RadixSemantics.value bits)), [true]]
        (fun _ : Fin 1 => List.replicate (2*w+1) false)) := by
  obtain ⟨r, hr, h0, h1, h2, h3, h4, hh, hs⟩ := ClockScalarFields.scalar_run w bits h
  refine ⟨r, ?_, funext hh, ?_, le_of_eq hs⟩
  · change runFrom _ _ (initialConfiguration _ _) = some r at hr
    exact hr
  · funext i
    refine Fin.addCases (m := 4) (n := 1) (fun j => ?_) (fun j => ?_) i
    · rw [Fin.addCases_left]; fin_cases j
      · exact h0
      · exact h1
      · exact h2
      · exact h3
    · rw [Fin.addCases_right]; fin_cases j; exact h4

theorem f6_local (Rc e p w q cW cQ : ℕ) (T : Fin 66 → List Bool)
    (hS : ∀ i : Fin 66, i.val < 59 → T i = List.replicate Rc false)
    (h59 : T 59 = ZeroPadding.pad Rc (List.replicate e true))
    (h60 : T 60 = ZeroPadding.pad Rc (List.replicate p true))
    (h61 : T 61 = ZeroPadding.pad cW (List.replicate w true))
    (h62 : T 62 = ZeroPadding.pad cQ (List.replicate q true))
    (h63 : (T 63).length ≤ Rc) (h64 : T 64 = List.replicate Rc true)
    (h65 : T 65 = List.replicate (Rc+2) false)
    (he1 : 1 ≤ e) (hpw : (CloseoutRowsCountBinary.bits p).length ≤ w)
    (hfirst : p * 2^(natBitLength e) < 2^w) (hsecond : p*e*2^(q+1) < 2^w) :
    ∃ T' : Fin 66 → List Bool, Step f6Machine (f6Cost Rc e p w q) (fun _ => 0) T (fun _ => 0) T' ∧
      T' 63 = ZeroPadding.pad Rc (RepairOrdinary.frame (SignedSortKey.binary w (p*e*2^q))) ∧
      T' 61 = T 61 ∧ T' 62 = T 62 ∧ T' 64 = T 64 ∧ T' 65 = T 65 := by
  have blank : ∀ i : Fin 66, i.val < 59 → T i = ZeroPadding.pad Rc [] := by
    intro i hi; rw [hS i hi]; simp [ZeroPadding.pad]
  -- 1. erase enc 4
  have e1 := Step.of_ready (RecoveryScratchErase.erase_ready (t := 1) Rc (Rc+2) ![T 63]
    (fun i => by fin_cases i; exact h63))
  have st1 := dockKeep e1 sE sE_inj (fun _ => 0) T (fun _ => rfl) (by
    intro j; fin_cases j
    · rfl
    · exact h64
    · exact h65)
  set T1 := install sE T (Fin.addCases (Fin.addCases (fun _ : Fin 1 => List.replicate Rc false)
      (fun _ : Fin 1 => List.replicate Rc true))
      (fun _ : Fin 1 => List.replicate (max (Rc+2) (Rc+1)) false)) with hT1
  have T1_63 : T1 63 = List.replicate Rc false := install_slot sE sE_inj T _ 0
  have T1_64 : T1 64 = List.replicate Rc true := install_slot sE sE_inj T _ 1
  have T1_65 : T1 65 = List.replicate (Rc+2) false := by
    rw [show T1 65 = _ from install_slot sE sE_inj T _ 2]
    show List.replicate (max (Rc+2) (Rc+1)) false = _
    rw [max_eq_left (by omega)]
  have T1o : ∀ i, (∀ j, sE j ≠ i) → T1 i = T i := fun i hi => install_other sE T _ i hi
  -- 2. count e
  obtain ⟨oe, hre, -, -, hoe5⟩ := CloseoutRowsCountBinary.count_run e
  have st2 := dockPad (step_of_clock hre) (fun _ => Rc) sCe sCe_inj (fun _ => 0) T1 (fun _ => rfl) (by
    intro j; fin_cases j
    · show T1 59 = _
      rw [T1o 59 (by decide), h59]; simp [CloseoutRowsCountBinary.input]
    all_goals (rw [T1o _ (by decide), blank _ (by decide)]; simp [CloseoutRowsCountBinary.input]))
  set T2 := install sCe T1 (fun j => ZeroPadding.pad ((fun _ => Rc) j) (oe j)) with hT2
  have T2_4 : T2 4 = ZeroPadding.pad Rc (RepairOrdinary.frame (CloseoutRowsCountBinary.bits e)) := by
    rw [show T2 4 = _ from install_slot sCe sCe_inj T1 _ 5]; simp [hoe5]
  have T2o : ∀ i, (∀ j, sCe j ≠ i) → T2 i = T1 i := fun i hi => install_other sCe T1 _ i hi
  -- 3. count p
  obtain ⟨op, hrp, -, -, hop5⟩ := CloseoutRowsCountBinary.count_run p
  have st3 := dockPad (step_of_clock hrp) (fun _ => Rc) sCp sCp_inj (fun _ => 0) T2 (fun _ => rfl) (by
    intro j; fin_cases j
    · show T2 60 = _
      rw [T2o 60 (by decide), T1o 60 (by decide), h60]; simp [CloseoutRowsCountBinary.input]
    all_goals (rw [T2o _ (by decide), T1o _ (by decide), blank _ (by decide)]
               simp [CloseoutRowsCountBinary.input]))
  set T3 := install sCp T2 (fun j => ZeroPadding.pad ((fun _ => Rc) j) (op j)) with hT3
  have T3_13 : T3 13 = ZeroPadding.pad Rc (RepairOrdinary.frame (CloseoutRowsCountBinary.bits p)) := by
    rw [show T3 13 = _ from install_slot sCp sCp_inj T2 _ 5]; simp [hop5]
  have T3o : ∀ i, (∀ j, sCp j ≠ i) → T3 i = T2 i := fun i hi => install_other sCp T2 _ i hi
  -- 4. copy 1^w
  have st4 := dockPad (BlockPlatform.UnaryCalc.copy_step w) ![cW, Rc, Rc, Rc] sW sW_inj (fun _ => 0) T3
    (fun _ => rfl) (by
    intro j; fin_cases j
    · show T3 61 = _
      rw [T3o 61 (by decide), T2o 61 (by decide), T1o 61 (by decide), h61]; rfl
    all_goals (rw [T3o _ (by decide), T2o _ (by decide), T1o _ (by decide), blank _ (by decide)]; rfl))
  set T4 := install sW T3 (fun j => ZeroPadding.pad ((![cW, Rc, Rc, Rc] : Fin 4 → ℕ) j)
    ((![List.replicate w true, [], List.replicate w true, List.replicate (w+2) false] : Fin 4 → List Bool) j))
    with hT4
  have T4_19 : T4 19 = ZeroPadding.pad Rc (List.replicate w true) := install_slot sW sW_inj T3 _ 2
  have T4_61 : T4 61 = T 61 := (install_slot sW sW_inj T3 _ 0).trans h61.symm
  have T4o : ∀ i, (∀ j, sW j ≠ i) → T4 i = T3 i := fun i hi => install_other sW T3 _ i hi
  -- 5. copy 1^q
  have st5 := dockPad (BlockPlatform.UnaryCalc.copy_step q) ![cQ, Rc, Rc, Rc] sQ sQ_inj (fun _ => 0) T4
    (fun _ => rfl) (by
    intro j; fin_cases j
    · show T4 62 = _
      rw [T4o 62 (by decide), T3o 62 (by decide), T2o 62 (by decide), T1o 62 (by decide), h62]; rfl
    all_goals (rw [T4o _ (by decide), T3o _ (by decide), T2o _ (by decide), T1o _ (by decide),
      blank _ (by decide)]; rfl))
  set T5 := install sQ T4 (fun j => ZeroPadding.pad ((![cQ, Rc, Rc, Rc] : Fin 4 → ℕ) j)
    ((![List.replicate q true, [], List.replicate q true, List.replicate (q+2) false] : Fin 4 → List Bool) j))
    with hT5
  have T5_22 : T5 22 = ZeroPadding.pad Rc (List.replicate q true) := install_slot sQ sQ_inj T4 _ 2
  have T5_62 : T5 62 = T 62 := (install_slot sQ sQ_inj T4 _ 0).trans h62.symm
  have T5o : ∀ i, (∀ j, sQ j ≠ i) → T5 i = T4 i := fun i hi => install_other sQ T4 _ i hi
  -- 6. p to width w
  have st6 := dockPad (scalar_step w (CloseoutRowsCountBinary.bits p) hpw) (fun _ => Rc) sN sN_inj
    (fun _ => 0) T5 (fun _ => rfl) (by
    intro j; fin_cases j
    · show T5 19 = _
      rw [T5o 19 (by decide), T4_19]; rfl
    · show T5 13 = _
      rw [T5o 13 (by decide), T4o 13 (by decide), T3_13]; rfl
    all_goals (rw [T5o _ (by decide), T4o _ (by decide), T3o _ (by decide), T2o _ (by decide),
      T1o _ (by decide), blank _ (by decide)]; rfl))
  set T6 := install sN T5 (fun j => ZeroPadding.pad ((fun _ => Rc) j)
    ((Fin.addCases (motive := fun _ : Fin (4+1) => List Bool)
        ![List.replicate w true, RepairOrdinary.frame (CloseoutRowsCountBinary.bits p),
          RepairOrdinary.frame (SignedSortKey.binary w (RadixSemantics.value (CloseoutRowsCountBinary.bits p))),
          [true]]
        (fun _ : Fin 1 => List.replicate (2*w+1) false)) j)) with hT6
  have T6_24 : T6 24 = ZeroPadding.pad Rc (RepairOrdinary.frame (SignedSortKey.binary w p)) := by
    rw [show T6 24 = _ from install_slot sN sN_inj T5 _ 2]
    show ZeroPadding.pad Rc (RepairOrdinary.frame (SignedSortKey.binary w
      (RadixSemantics.value (CloseoutRowsCountBinary.bits p)))) = _
    rw [value_bits]
  have T6_19 : T6 19 = ZeroPadding.pad Rc (List.replicate w true) := install_slot sN sN_inj T5 _ 0
  have T6o : ∀ i, (∀ j, sN j ≠ i) → T6 i = T5 i := fun i hi => install_other sN T5 _ i hi
  -- 7. the engine
  obtain ⟨out, hr7, hout⟩ := CompetitorDenominator.denominator_run (natBitLength e) w q p e
    (Nat.lt_pow_succ_log_self (by norm_num) e) hfirst hsecond
  have st7 := dockPad (step_of_clock hr7) (fun _ => Rc) sD sD_inj (fun _ => 0) T6 (fun _ => rfl) (by
    intro j; fin_cases j
    · show T6 4 = _
      rw [T6o 4 (by decide), T5o 4 (by decide), T4o 4 (by decide), T3o 4 (by decide), T2_4,
        bits_pos e he1]; rfl
    · show T6 24 = _
      rw [T6_24]; rfl
    · show T6 19 = _
      rw [T6_19]; rfl
    · show T6 22 = _
      rw [T6o 22 (by decide), T5_22]; rfl
    rotate_left 22
    · show T6 63 = _
      rw [T6o 63 (by decide), T5o 63 (by decide), T4o 63 (by decide), T3o 63 (by decide),
        T2o 63 (by decide), T1_63]; simp [ZeroPadding.pad, CompetitorDenominator.input]
    all_goals (rw [T6o _ (by decide), T5o _ (by decide), T4o _ (by decide), T3o _ (by decide),
      T2o _ (by decide), T1o _ (by decide), blank _ (by decide)]; rfl))
  refine ⟨_, (((((st1.seq st2).seq st3).seq st4).seq st5).seq st6).seq st7, ?_, ?_, ?_, ?_, ?_⟩
  · show install sD T6 (fun j => ZeroPadding.pad ((fun _ => Rc) j) (out j)) (sD 26) = _
    rw [install_slot sD sD_inj, hout]
  · rw [install_other sD T6 _ 61 (by decide), T6o 61 (by decide), T5o 61 (by decide), T4_61]
  · rw [install_other sD T6 _ 62 (by decide), T6o 62 (by decide), T5_62]
  · rw [install_other sD T6 _ 64 (by decide), T6o 64 (by decide), T5o 64 (by decide), T4o 64 (by decide),
      T3o 64 (by decide), T2o 64 (by decide), T1_64, h64]
  · rw [install_other sD T6 _ 65 (by decide), T6o 65 (by decide), T5o 65 (by decide), T4o 65 (by decide),
      T3o 65 (by decide), T2o 65 (by decide), T1_65, h65]

/-- Erase the destination, then copy the source onto it (driver `1^C`, log `0^K`, `C+1 ≤ K`). -/
def owMachine :=
  Composition.machine
    (RecoveryFocus.machine (![1, 2, 3] : Fin (1+1+1) → Fin 4) (RecoveryScratchErase.resetMachine 1))
    RecoveryBoundedTapeCopy.machine

theorem ow_local (C K : ℕ) (hK : C + 1 ≤ K) (w d : List Bool) (hw : w.length = C) (hd : d.length ≤ C) :
    Step owMachine ((2*C+4) + 1 + (2*C+4)) (fun _ => 0)
      ![w, d, List.replicate C true, List.replicate K false] (fun _ => 0)
      ![w, w, List.replicate C true, List.replicate K false] := by
  have hmax : max K (C+1) = K := max_eq_left hK
  have e1 := Step.of_ready (RecoveryScratchErase.erase_ready (t := 1) C K ![d]
    (fun i => by fin_cases i; exact hd))
  have st1 := dockKeep e1 (![1, 2, 3] : Fin (1+1+1) → Fin 4) (by decide) (fun _ => 0)
    ![w, d, List.replicate C true, List.replicate K false] (fun _ => rfl) (by
      intro j; fin_cases j <;> rfl)
  have mid : install (![1, 2, 3] : Fin (1+1+1) → Fin 4) ![w, d, List.replicate C true, List.replicate K false]
      (Fin.addCases (motive := fun _ => List Bool) (Fin.addCases (motive := fun _ => List Bool)
        (fun _ : Fin 1 => List.replicate C false)
        (fun _ : Fin 1 => List.replicate C true))
        (fun _ : Fin 1 => List.replicate (max K (C+1)) false)) =
      ![w, List.replicate C false, List.replicate C true, List.replicate K false] := by
    funext i; fin_cases i
    · exact install_other _ _ _ _ (by decide)
    · exact install_slot _ (by decide) _ _ 0
    · exact install_slot _ (by decide) _ _ 1
    · refine (install_slot (![1, 2, 3] : Fin (1+1+1) → Fin 4) (by decide) _ _ 2).trans ?_
      show List.replicate (max K (C+1)) false = _
      rw [hmax]; rfl
  rw [mid] at st1
  have c0 := RecoveryChildSelection.ReadyRun.pad (RecoveryBoundedTapeCopy.copy_ready w C K) ![0, C, 0, 0]
  have st2 := Step.of_ready c0
  have eIn : (fun i => ZeroPadding.pad ((![0, C, 0, 0] : Fin 4 → ℕ) i)
      ((![w, [], List.replicate C true, List.replicate K false] : Fin 4 → List Bool) i)) =
      ![w, List.replicate C false, List.replicate C true, List.replicate K false] := by
    funext i; fin_cases i <;> simp [ZeroPadding.pad]
  have eOut : (fun i => ZeroPadding.pad ((![0, C, 0, 0] : Fin 4 → ℕ) i)
      ((![w, RecoveryBoundedTapeCopy.copied w C, List.replicate C true,
        List.replicate (max K (C+1)) false] : Fin 4 → List Bool) i)) =
      ![w, w, List.replicate C true, List.replicate K false] := by
    funext i; fin_cases i
    · simp
    · show ZeroPadding.pad C (RecoveryBoundedTapeCopy.copied w C) = w
      rw [← hw, copied_full]; simp [ZeroPadding.pad]
    · simp
    · show ZeroPadding.pad 0 (List.replicate (max K (C+1)) false) = _
      rw [hmax, ZeroPadding.pad_zero]; rfl
  rw [eIn, eOut] at st2
  exact st1.seq st2

def ow {V' : ℕ} (g : Fin 72 → Fin V') (src dst : Fin 72) : Fin 4 → Fin V' := ![g src, g dst, g 64, g 65]

def f6Full {V : ℕ} (g : Fin 72 → Fin V) :=
  Composition.machine (RecoveryFocus.machine (fun i : Fin 66 => g (Fin.castAdd 6 i)) f6Machine)
    (Composition.machine (Composition.machine
      (RecoveryFocus.machine (ow g 66 69) owMachine) (RecoveryFocus.machine (ow g 67 70) owMachine))
      (RecoveryFocus.machine (ow g 68 71) owMachine))

def f6FullCost (Rc e p w q : ℕ) : ℕ :=
  f6Cost Rc e p w q + 1 + ((((2*Rc+4) + 1 + (2*Rc+4)) + 1 + ((2*Rc+4) + 1 + (2*Rc+4))) + 1 +
    ((2*Rc+4) + 1 + (2*Rc+4)))

theorem f6_run {V : ℕ} (g : Fin 72 → Fin V) (hg : Function.Injective g) (Rc e p w q cW cQ : ℕ)
    (H : Fin V → ℕ) (A : Fin V → List Bool) (hH : ∀ i, H (g i) = 0)
    (hS : ∀ i : Fin 72, i.val < 59 → A (g i) = List.replicate Rc false)
    (h59 : A (g 59) = ZeroPadding.pad Rc (List.replicate e true))
    (h60 : A (g 60) = ZeroPadding.pad Rc (List.replicate p true))
    (h61 : A (g 61) = ZeroPadding.pad cW (List.replicate w true))
    (h62 : A (g 62) = ZeroPadding.pad cQ (List.replicate q true))
    (h63 : (A (g 63)).length ≤ Rc) (h64 : A (g 64) = List.replicate Rc true)
    (h65 : A (g 65) = List.replicate (Rc+2) false)
    (hc : ∀ k : Fin 72, 66 ≤ k.val → k.val < 69 → (A (g k)).length = Rc)
    (hd : ∀ k : Fin 72, 69 ≤ k.val → (A (g k)).length ≤ Rc)
    (he1 : 1 ≤ e) (hpw : (CloseoutRowsCountBinary.bits p).length ≤ w)
    (hfirst : p * 2^(natBitLength e) < 2^w) (hsecond : p*e*2^(q+1) < 2^w) :
    ∃ A' : Fin V → List Bool, Step (f6Full g) (f6FullCost Rc e p w q) H A H A' ∧
      A' (g 63) = ZeroPadding.pad Rc (RepairOrdinary.frame (SignedSortKey.binary w (p*e*2^q))) ∧
      A' (g 69) = A (g 66) ∧ A' (g 70) = A (g 67) ∧ A' (g 71) = A (g 68) ∧
      A' (g 61) = A (g 61) ∧ A' (g 62) = A (g 62) ∧ A' (g 64) = A (g 64) ∧ A' (g 65) = A (g 65) ∧
      (∀ x, (∀ i, g i ≠ x) → A' x = A x) := by
  let g66 : Fin 66 → Fin V := fun i => g (Fin.castAdd 6 i)
  have i66 : Function.Injective g66 := fun a b h => Fin.castAdd_injective _ _ (hg h)
  obtain ⟨T', st, t63, t61, t62, t64, t65⟩ := f6_local Rc e p w q cW cQ (fun i => A (g66 i))
    (fun i hi => hS _ (by simpa using hi)) h59 h60 h61 h62 h63 h64 h65 he1 hpw hfirst hsecond
  have s1 := dockKeep st g66 i66 H A (fun j => hH _) (fun _ => rfl)
  set A1 := install g66 A T' with hA1
  have off66 : ∀ k : Fin 72, 66 ≤ k.val → ∀ j, g66 j ≠ g k := by
    intro k hk j h; have := congrArg Fin.val (hg h); simp at this; omega
  have A1k : ∀ k : Fin 72, 66 ≤ k.val → A1 (g k) = A (g k) := fun k hk => install_other _ _ _ _ (off66 k hk)
  have A1_64 : A1 (g 64) = List.replicate Rc true :=
    (install_slot g66 i66 A T' 64).trans (t64.trans h64)
  have A1_65 : A1 (g 65) = List.replicate (Rc+2) false :=
    (install_slot g66 i66 A T' 65).trans (t65.trans h65)
  -- the three overwrites
  have owInj : ∀ src dst : Fin 72, src.val ≠ dst.val → src.val < 64 ∨ 65 < src.val →
      dst.val < 64 ∨ 65 < dst.val → Function.Injective (ow g src dst) := by
    intro src dst hsd hs hd a b h
    fin_cases a <;> fin_cases b <;> first
      | rfl
      | (exfalso; change g _ = g _ at h; have hv := congrArg Fin.val (hg h); omega)
  have owStep : ∀ (B : Fin V → List Bool) (src dst : Fin 72) (hsd : src.val ≠ dst.val)
      (hs : src.val < 64 ∨ 65 < src.val) (hdd : dst.val < 64 ∨ 65 < dst.val),
      (B (g src)).length = Rc → (B (g dst)).length ≤ Rc → B (g 64) = List.replicate Rc true →
      B (g 65) = List.replicate (Rc+2) false →
      Step (RecoveryFocus.machine (ow g src dst) owMachine) ((2*Rc+4) + 1 + (2*Rc+4)) H B H
        (install (ow g src dst) B ![B (g src), B (g src), List.replicate Rc true,
          List.replicate (Rc+2) false]) := by
    intro B src dst hsd hs hdd hsrc hdst hdrv hlog
    exact dockKeep (ow_local Rc (Rc+2) (by omega) (B (g src)) (B (g dst)) hsrc hdst) (ow g src dst)
      (owInj src dst hsd hs hdd) H B (by intro j; fin_cases j <;> exact hH _) (by
        intro j; fin_cases j
        · rfl
        · rfl
        · exact hdrv
        · exact hlog)
  -- after one overwrite: the values it sets, and its frame
  have owVal : ∀ (B : Fin V → List Bool) (src dst : Fin 72) (hsd : src.val ≠ dst.val)
      (hs : src.val < 64 ∨ 65 < src.val) (hdd : dst.val < 64 ∨ 65 < dst.val),
      let B' := install (ow g src dst) B ![B (g src), B (g src), List.replicate Rc true,
        List.replicate (Rc+2) false]
      B' (g dst) = B (g src) ∧ B' (g src) = B (g src) ∧ B' (g 64) = List.replicate Rc true ∧
        B' (g 65) = List.replicate (Rc+2) false ∧
        (∀ x, x ≠ g src → x ≠ g dst → x ≠ g 64 → x ≠ g 65 → B' x = B x) := by
    intro B src dst hsd hs hdd
    have hi := owInj src dst hsd hs hdd
    refine ⟨install_slot (ow g src dst) hi B _ 1, install_slot (ow g src dst) hi B _ 0,
      install_slot (ow g src dst) hi B _ 2, install_slot (ow g src dst) hi B _ 3, ?_⟩
    intro x a b c d
    exact install_other _ _ _ _ (by intro j; fin_cases j <;> simp [ow] <;> intro h <;> simp_all)
  have ne : ∀ a b : Fin 72, a.val ≠ b.val → g a ≠ g b := fun a b h e => h (congrArg Fin.val (hg e))
  -- overwrite 1: 66 → 69
  have s2 := owStep A1 66 69 (by decide) (Or.inr (by decide)) (Or.inr (by decide))
    (by rw [A1k 66 (by decide)]; exact hc 66 (by decide) (by decide))
    (by rw [A1k 69 (by decide)]; exact hd 69 (by decide)) A1_64 A1_65
  obtain ⟨v1d, v1s, v1a, v1b, v1o⟩ := owVal A1 66 69 (by decide) (Or.inr (by decide)) (Or.inr (by decide))
  set A2 := install (ow g 66 69) A1 ![A1 (g 66), A1 (g 66), List.replicate Rc true,
    List.replicate (Rc+2) false] with hA2
  -- overwrite 2: 67 → 70
  have A2_67 : A2 (g 67) = A (g 67) :=
    (v1o _ (ne _ _ (by decide)) (ne _ _ (by decide)) (ne _ _ (by decide)) (ne _ _ (by decide))).trans
      (A1k 67 (by decide))
  have A2_70 : A2 (g 70) = A (g 70) :=
    (v1o _ (ne _ _ (by decide)) (ne _ _ (by decide)) (ne _ _ (by decide)) (ne _ _ (by decide))).trans
      (A1k 70 (by decide))
  have s3 := owStep A2 67 70 (by decide) (Or.inr (by decide)) (Or.inr (by decide))
    (by rw [A2_67]; exact hc 67 (by decide) (by decide)) (by rw [A2_70]; exact hd 70 (by decide)) v1a v1b
  obtain ⟨v2d, v2s, v2a, v2b, v2o⟩ := owVal A2 67 70 (by decide) (Or.inr (by decide)) (Or.inr (by decide))
  set A3 := install (ow g 67 70) A2 ![A2 (g 67), A2 (g 67), List.replicate Rc true,
    List.replicate (Rc+2) false] with hA3
  -- overwrite 3: 68 → 71
  have A3_68 : A3 (g 68) = A (g 68) :=
    (v2o _ (ne _ _ (by decide)) (ne _ _ (by decide)) (ne _ _ (by decide)) (ne _ _ (by decide))).trans
      ((v1o _ (ne _ _ (by decide)) (ne _ _ (by decide)) (ne _ _ (by decide)) (ne _ _ (by decide))).trans
        (A1k 68 (by decide)))
  have A3_71 : A3 (g 71) = A (g 71) :=
    (v2o _ (ne _ _ (by decide)) (ne _ _ (by decide)) (ne _ _ (by decide)) (ne _ _ (by decide))).trans
      ((v1o _ (ne _ _ (by decide)) (ne _ _ (by decide)) (ne _ _ (by decide)) (ne _ _ (by decide))).trans
        (A1k 71 (by decide)))
  have s4 := owStep A3 68 71 (by decide) (Or.inr (by decide)) (Or.inr (by decide))
    (by rw [A3_68]; exact hc 68 (by decide) (by decide)) (by rw [A3_71]; exact hd 71 (by decide)) v2a v2b
  obtain ⟨v3d, -, v3a, v3b, v3o⟩ := owVal A3 68 71 (by decide) (Or.inr (by decide)) (Or.inr (by decide))
  refine ⟨_, s1.seq ((s2.seq s3).seq s4), ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- enc 4
    rw [v3o _ (ne _ _ (by decide)) (ne _ _ (by decide)) (ne _ _ (by decide)) (ne _ _ (by decide)),
      v2o _ (ne _ _ (by decide)) (ne _ _ (by decide)) (ne _ _ (by decide)) (ne _ _ (by decide)),
      v1o _ (ne _ _ (by decide)) (ne _ _ (by decide)) (ne _ _ (by decide)) (ne _ _ (by decide))]
    exact (install_slot g66 i66 A T' 63).trans t63
  · rw [v3o _ (ne _ _ (by decide)) (ne _ _ (by decide)) (ne _ _ (by decide)) (ne _ _ (by decide)),
      v2o _ (ne _ _ (by decide)) (ne _ _ (by decide)) (ne _ _ (by decide)) (ne _ _ (by decide)), v1d,
      A1k 66 (by decide)]
  · rw [v3o _ (ne _ _ (by decide)) (ne _ _ (by decide)) (ne _ _ (by decide)) (ne _ _ (by decide)), v2d, A2_67]
  · rw [v3d, A3_68]
  · rw [v3o _ (ne _ _ (by decide)) (ne _ _ (by decide)) (ne _ _ (by decide)) (ne _ _ (by decide)),
      v2o _ (ne _ _ (by decide)) (ne _ _ (by decide)) (ne _ _ (by decide)) (ne _ _ (by decide)),
      v1o _ (ne _ _ (by decide)) (ne _ _ (by decide)) (ne _ _ (by decide)) (ne _ _ (by decide))]
    exact (install_slot g66 i66 A T' 61).trans t61
  · rw [v3o _ (ne _ _ (by decide)) (ne _ _ (by decide)) (ne _ _ (by decide)) (ne _ _ (by decide)),
      v2o _ (ne _ _ (by decide)) (ne _ _ (by decide)) (ne _ _ (by decide)) (ne _ _ (by decide)),
      v1o _ (ne _ _ (by decide)) (ne _ _ (by decide)) (ne _ _ (by decide)) (ne _ _ (by decide))]
    exact (install_slot g66 i66 A T' 62).trans t62
  · rw [v3a, h64]
  · rw [v3b, h65]
  · intro x hx
    have n66 := hx 66; have n67 := hx 67; have n68 := hx 68; have n69 := hx 69
    have n70 := hx 70; have n71 := hx 71; have n64 := hx 64; have n65 := hx 65
    rw [v3o x (Ne.symm n68) (Ne.symm n71) (Ne.symm n64) (Ne.symm n65),
      v2o x (Ne.symm n67) (Ne.symm n70) (Ne.symm n64) (Ne.symm n65),
      v1o x (Ne.symm n66) (Ne.symm n69) (Ne.symm n64) (Ne.symm n65)]
    exact install_other g66 A T' x (fun j h => hx _ h)

/-! ## F2: the per-call slope `M2_r`, selected by one bit read off `1^L`

AD's `effectiveDegree_eq`: the effective degree is `uniformDeg` when the child list is nonempty and `1`
when it is empty. The child list is empty iff `L = |exactListWord []| = |natWord 0| = 3`, and otherwise
`L ≥ 4`. So the bit is cell `3` of `lenTape = pad capLen 1^L`, and no new producer is needed. The stage moves
`lenTape`'s head to `3`, switches on the cell (`CloseoutRowsOriginalSwitch`), moves back, and copies the
chosen resident slope onto the per-call `cs 1`. -/

/-- One-step head moves on one ambient tape. -/
def rMove {V : ℕ} (x : Fin V) : Fin V → HeadMove := fun i => if i = x then .right else .stay
def lMove {V : ℕ} (x : Fin V) : Fin V → HeadMove := fun i => if i = x then .left else .stay
def move3 {V : ℕ} (d : Fin V → HeadMove) :=
  Composition.machine (Composition.machine (DecompositionCountPosition.move d)
    (DecompositionCountPosition.move d)) (DecompositionCountPosition.move d)

def slopeMachine {V : ℕ} (lenT big small dst s1 lg : Fin V) :=
  Composition.machine (move3 (rMove lenT)) (CloseoutRowsOriginalSwitch.machine
    (Composition.machine (move3 (lMove lenT))
      (RecoveryFocus.machine ![big, s1, dst, lg] ClockUnarySum.machine))
    (Composition.machine (move3 (lMove lenT))
      (RecoveryFocus.machine ![small, s1, dst, lg] ClockUnarySum.machine)) lenT)

theorem readbit3 (c L : ℕ) :
    readTapeBit (ZeroPadding.pad c (List.replicate L true)) 3 = decide (3 < L) := by
  unfold readTapeBit ZeroPadding.pad
  by_cases h : 3 < L
  · rw [List.getD_eq_getElem?_getD, List.getElem?_append_left (by simp; omega)]
    simp [h]
  · rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by simp; omega)]
    simp only [List.length_replicate, List.getElem?_replicate]
    split_ifs <;> simp [h]

theorem move3_run {V : ℕ} (d : Fin V → HeadMove) (H : Fin V → ℕ) (A : Fin V → List Bool) :
    Step (move3 d) (1 + 1 + 1 + 1 + 1) H A
      (fun i => (d i).apply ((d i).apply ((d i).apply (H i)))) A :=
  ((RowWidth.moveStep d H A).seq (RowWidth.moveStep d _ A)).seq (RowWidth.moveStep d _ A)

/-- **The slope for this call.** `dst` gets `pad Rc (1^M)`, where `M` is the big slope if the child list is
nonempty (`3 < L`) and the small one otherwise; `lenTape`, both residents and every head are kept, and only
`dst`, `s1` and `lg` change. -/
theorem slope_select {V : ℕ} (lenT big small dst s1 lg : Fin V)
    (h1 : big ≠ s1) (h2 : big ≠ dst) (h3 : big ≠ lg) (h4 : small ≠ s1)
    (h5 : small ≠ dst) (h6 : small ≠ lg) (h7 : s1 ≠ dst) (h8 : s1 ≠ lg) (h9 : dst ≠ lg)
    (l1 : lenT ≠ big) (l2 : lenT ≠ small) (l3 : lenT ≠ dst) (l4 : lenT ≠ s1) (l5 : lenT ≠ lg)
    (L capLen Mb Ms cB cS Rc : ℕ) (H : Fin V → ℕ) (A : Fin V → List Bool)
    (hHl : H lenT = 0) (hHb : H big = 0) (hHs : H small = 0) (hHd : H dst = 0) (hH1 : H s1 = 0)
    (hHg : H lg = 0)
    (hlen : A lenT = ZeroPadding.pad capLen (List.replicate L true))
    (hbig : A big = ZeroPadding.pad cB (List.replicate Mb true))
    (hsmall : A small = ZeroPadding.pad cS (List.replicate Ms true))
    (hdst : A dst = ZeroPadding.pad Rc []) (hs1 : A s1 = ZeroPadding.pad Rc [])
    (hlg : A lg = ZeroPadding.pad Rc []) :
    ∃ A' : Fin V → List Bool,
      Step (slopeMachine lenT big small dst s1 lg)
        ((1+1+1+1+1) + 1 + (((1+1+1+1+1) + 1 + (2 * (if 3 < L then Mb else Ms) + 6)) + 2)) H A H A' ∧
      A' dst = ZeroPadding.pad Rc (List.replicate (if 3 < L then Mb else Ms) true) ∧
      (∀ x, x ≠ dst → x ≠ s1 → x ≠ lg → A' x = A x) := by
  classical
  -- the heads after three right moves, and back
  set H3 : Fin V → ℕ := fun i => (rMove lenT i).apply ((rMove lenT i).apply ((rMove lenT i).apply (H i)))
    with hH3
  have H3l : H3 lenT = 3 := by simp [hH3, rMove, HeadMove.apply, hHl]
  have back : (fun i => (lMove lenT i).apply ((lMove lenT i).apply ((lMove lenT i).apply (H3 i)))) = H := by
    funext i
    by_cases hi : i = lenT
    · subst hi; simp [lMove, HeadMove.apply, H3l, hHl]
    · simp [hH3, lMove, rMove, HeadMove.apply, hi]
  have mR := move3_run (rMove lenT) H A
  have mL := move3_run (lMove lenT) H3 A
  rw [back] at mL
  have bit : readTapeBit (A lenT) (H3 lenT) = decide (3 < L) := by rw [H3l, hlen, readbit3]
  -- the copy, from either slope
  have copy : ∀ (src : Fin V) (M cM : ℕ), src ≠ s1 → src ≠ dst → src ≠ lg → H src = 0 →
      A src = ZeroPadding.pad cM (List.replicate M true) →
      Step (RecoveryFocus.machine ![src, s1, dst, lg] ClockUnarySum.machine) (2*M+6) H A H
        (install ![src, s1, dst, lg] A (fun j => ZeroPadding.pad ((![cM, Rc, Rc, Rc] : Fin 4 → ℕ) j)
          ((![List.replicate M true, [], List.replicate M true, List.replicate (M+2) false] :
            Fin 4 → List Bool) j))) := by
    intro src M cM a b c hHsrc hsrc
    have inj : Function.Injective (![src, s1, dst, lg] : Fin 4 → Fin V) := by
      intro u v h; fin_cases u <;> fin_cases v <;> simp_all
    exact dockPad (BlockPlatform.UnaryCalc.copy_step M) ![cM, Rc, Rc, Rc] _ inj H A (by
      intro j; fin_cases j
      · exact hHsrc
      · exact hH1
      · exact hHd
      · exact hHg) (by
      intro j; fin_cases j
      · exact hsrc
      · exact hs1
      · exact hdst
      · exact hlg)
  have outVal : ∀ (src : Fin V) (M cM : ℕ), src ≠ s1 → src ≠ dst → src ≠ lg →
      A src = ZeroPadding.pad cM (List.replicate M true) →
      let A' := install ![src, s1, dst, lg] A (fun j => ZeroPadding.pad ((![cM, Rc, Rc, Rc] : Fin 4 → ℕ) j)
          ((![List.replicate M true, [], List.replicate M true, List.replicate (M+2) false] :
            Fin 4 → List Bool) j))
      A' dst = ZeroPadding.pad Rc (List.replicate M true) ∧
        (∀ x, x ≠ dst → x ≠ s1 → x ≠ lg → A' x = A x) := by
    intro src M cM a b c hsrc
    have inj : Function.Injective (![src, s1, dst, lg] : Fin 4 → Fin V) := by
      intro u v h; fin_cases u <;> fin_cases v <;> simp_all
    refine ⟨install_slot _ inj A _ 2, fun x d1 d2 d3 => ?_⟩
    by_cases hx : x = src
    · subst hx
      exact (install_slot _ inj A _ 0).trans hsrc.symm
    · exact install_other _ _ _ _ (by
        intro j; fin_cases j
        · exact Ne.symm hx
        · exact Ne.symm d2
        · exact Ne.symm d1
        · exact Ne.symm d3)
  by_cases hb : 3 < L
  · simp only [if_pos hb]
    have st := mL.seq (copy big Mb cB h1 h2 h3 hHb hbig)
    have sw := CloseoutRowsOriginalSwitch.true_run _
      (Composition.machine (move3 (lMove lenT))
        (RecoveryFocus.machine ![small, s1, dst, lg] ClockUnarySum.machine)) lenT st
      (by rw [bit]; simp [hb])
    obtain ⟨o1, o2⟩ := outVal big Mb cB h1 h2 h3 hbig
    exact ⟨_, mR.seq sw, o1, o2⟩
  · simp only [if_neg hb]
    have st := mL.seq (copy small Ms cS h4 h5 h6 hHs hsmall)
    have sw := CloseoutRowsOriginalSwitch.false_run
      (Composition.machine (move3 (lMove lenT))
        (RecoveryFocus.machine ![big, s1, dst, lg] ClockUnarySum.machine)) _ lenT st
      (by rw [bit]; simp [hb])
    obtain ⟨o1, o2⟩ := outVal small Ms cS h4 h5 h6 hsmall
    exact ⟨_, mR.seq sw, o1, o2⟩

/-- `|natWord n| = 2·bitlen n + 1 ≥ 3`, and `|natWord 0| = 3`. -/
theorem natWord_len (n : ℕ) : (RepairRepresentation.natWord n).length = 2 * natBitLength n + 1 := by
  simp [RepairRepresentation.natWord, WilliamsPublishedForm.framedNatBits,
    WilliamsPublishedForm.fixedWidthNatBits]
  ring

theorem natBitLength_pos (n : ℕ) : 1 ≤ natBitLength n := by
  unfold natBitLength; omega

/-- **The F2 bit.** The child list is empty iff `|exactListWord gs| ≤ 3`, i.e. iff cell 3 of `1^L` is blank. -/
theorem exactList_bit {n : ℕ} (gs : List (ExactThresholdGate n)) :
    (3 < (RepairRepresentation.exactListWord gs).length) ↔ gs ≠ [] := by
  constructor
  · intro h he; subst he
    have e : (RepairRepresentation.exactListWord ([] : List (ExactThresholdGate n))).length = 3 := by
      rw [RepairRepresentation.exactListWord, List.flatMap_nil, List.append_nil, natWord_len]
      simp [natBitLength]
    omega
  · intro h
    obtain ⟨g, rest, rfl⟩ := List.exists_cons_of_ne_nil h
    have h2 := natBitLength_pos (g :: rest).length
    have h3 : 1 ≤ (RepairRepresentation.exactWord g).length := by
      rw [RepairRepresentation.exactWord, List.length_append]
      simp [RepairRepresentation.intWord]
      omega
    rw [RepairRepresentation.exactListWord, List.flatMap_cons, List.length_append, List.length_append,
      natWord_len]
    omega
end
end NearCubicWires.SourceConstruction.Prologue
end

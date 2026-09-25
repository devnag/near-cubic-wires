import Proof.SourceAssembly.SourceFactorSelCoefPrim

set_option autoImplicit false
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace NearCubicWires.SourceFactorSel.CoefAcc
open NearCubicWires LocalBitMultitape ExtDecompositionBatch RepairOrdinary RepairOrdinary.RecoveryRootRound
open RepairSource.VerifierDecoding RepairOrdinary.RadixSemantics RepairOrdinary.SignedSortKey
open NearCubicWires.SourceFactorSel.CoefPrim
noncomputable section

/-! ## Docking with explicit exit vectors -/

theorem dock_vec {t u s : Nat} {p : Machine t s} {n : Nat} {hin hout : Fin t → Nat}
    {tin tout : Fin t → List Bool} (h : Step p n hin tin hout tout)
    (sl : Fin t → Fin u) (hsl : Function.Injective sl) (H H' : Fin u → Nat) (A A' : Fin u → List Bool)
    (hH : ∀ j, H (sl j) = hin j) (hA : ∀ j, A (sl j) = tin j)
    (hH' : ∀ j, H' (sl j) = hout j) (hA' : ∀ j, A' (sl j) = tout j)
    (hHo : ∀ x, (∀ j, sl j ≠ x) → H' x = H x) (hAo : ∀ x, (∀ j, sl j ≠ x) → A' x = A x) :
    Step (RecoveryFocus.machine sl p) n H A H' A' := by
  have d := h.dock sl hsl H A hH hA
  refine d.congr ?_ ?_
  · funext x
    by_cases hx : ∃ j, sl j = x
    · obtain ⟨j, rfl⟩ := hx
      rw [dockH_slot sl hsl, hH']
    · rw [dockH_other sl H hout x (fun j e => hx ⟨j, e⟩), hHo x (fun j e => hx ⟨j, e⟩)]
  · funext x
    by_cases hx : ∃ j, sl j = x
    · obtain ⟨j, rfl⟩ := hx
      rw [install_slot sl hsl, hA']
    · rw [install_other sl A tout x (fun j e => hx ⟨j, e⟩), hAo x (fun j e => hx ⟨j, e⟩)]

/-! ## The record parse: three `FrameLoad`s, then `Rewind` -/

/-- A factor record, zero padded. -/
def recW (s : Bool) (n d c Qr : Nat) : List Bool :=
  ZeroPadding.pad Qr (frame [s] ++ frame (binary c n) ++ frame (binary c d))

def fl (k : Fin 5) : Machine 5 4 := RecoveryFocus.machine (![0, k, 4] : Fin 3 → Fin 5) FrameLoad.machine
def parse3 := Composition.machine (fl 1) (Composition.machine (fl 2) (fl 3))
def parseM := Rewind.machine parse3
def parseCost (c : Nat) : Nat := 7 + 1 + ((4 * c + 3) + 1 + (4 * c + 3))

theorem fl_inj (k : Fin 5) (h0 : k ≠ 0) (h4 : k ≠ 4) : Function.Injective (![0, k, 4] : Fin 3 → Fin 5) := by
  intro i j hij
  fin_cases i <;> fin_cases j <;> simp_all

theorem parse3_run (s : Bool) (n d c Qr S : Nat) (hS : 2 * c + 1 ≤ S) (hS3 : 3 ≤ S) :
    Step parse3 (parseCost c) (fun _ => 0)
      ![recW s n d c Qr, List.replicate S false, List.replicate S false, List.replicate S false,
        List.replicate S false]
      ![4 * c + 5, 0, 0, 0, 0]
      ![recW s n d c Qr, ZeroPadding.pad S (frame [s]), ZeroPadding.pad S (frame (binary c n)),
        ZeroPadding.pad S (frame (binary c d)), List.replicate S false] := by
  set zs := List.replicate (Qr - (frame [s] ++ frame (binary c n) ++ frame (binary c d)).length) false with hzs
  have hrec : recW s n d c Qr = frame [s] ++ frame (binary c n) ++ frame (binary c d) ++ zs := rfl
  have e1 : ([] : List Bool) ++ frame [s] ++ (frame (binary c n) ++ frame (binary c d) ++ zs) =
      recW s n d c Qr := by rw [hrec]; simp [List.append_assoc]
  have e2 : frame [s] ++ frame (binary c n) ++ (frame (binary c d) ++ zs) = recW s n d c Qr := by
    rw [hrec]; simp [List.append_assoc]
  have e3 : (frame [s] ++ frame (binary c n)) ++ frame (binary c d) ++ zs = recW s n d c Qr := by
    rw [hrec]
  have l1 := load_local [] [s] (frame (binary c n) ++ frame (binary c d) ++ zs) S S (by simp; omega)
  have l2 := load_local (frame [s]) (binary c n) (frame (binary c d) ++ zs) S S (by simp; omega)
  have l3 := load_local (frame [s] ++ frame (binary c n)) (binary c d) zs S S (by simp; omega)
  rw [e1] at l1
  rw [e2] at l2
  rw [e3] at l3
  have s1 : Step (fl 1) (4 * [s].length + 3) (fun _ => 0)
      ![recW s n d c Qr, List.replicate S false, List.replicate S false, List.replicate S false,
        List.replicate S false]
      ![3, 0, 0, 0, 0]
      ![recW s n d c Qr, ZeroPadding.pad S (frame [s]), List.replicate S false, List.replicate S false,
        List.replicate S false] := by
    refine dock_vec l1 _ (fl_inj 1 (by decide) (by decide)) _ _ _ _ ?_ ?_ ?_ ?_ ?_ ?_
    · intro j; fin_cases j <;> rfl
    · intro j; fin_cases j <;> rfl
    · intro j; fin_cases j <;> rfl
    · intro j; fin_cases j <;> rfl
    · intro x hx
      fin_cases x
      · exact absurd rfl (hx 0)
      · exact absurd rfl (hx 1)
      · rfl
      · rfl
      · exact absurd rfl (hx 2)
    · intro x hx
      fin_cases x
      · exact absurd rfl (hx 0)
      · exact absurd rfl (hx 1)
      · rfl
      · rfl
      · exact absurd rfl (hx 2)
  have s2 : Step (fl 2) (4 * (binary c n).length + 3) ![3, 0, 0, 0, 0]
      ![recW s n d c Qr, ZeroPadding.pad S (frame [s]), List.replicate S false, List.replicate S false,
        List.replicate S false]
      ![2 * c + 4, 0, 0, 0, 0]
      ![recW s n d c Qr, ZeroPadding.pad S (frame [s]), ZeroPadding.pad S (frame (binary c n)),
        List.replicate S false, List.replicate S false] := by
    refine dock_vec l2 _ (fl_inj 2 (by decide) (by decide)) _ _ _ _ ?_ ?_ ?_ ?_ ?_ ?_
    · intro j; fin_cases j <;> rfl
    · intro j; fin_cases j <;> rfl
    · intro j
      fin_cases j
      · show 2 * c + 4 = (frame [s]).length + 2 * (binary c n).length + 1
        simp; omega
      · rfl
      · rfl
    · intro j; fin_cases j <;> rfl
    · intro x hx
      fin_cases x
      · exact absurd rfl (hx 0)
      · rfl
      · exact absurd rfl (hx 1)
      · rfl
      · exact absurd rfl (hx 2)
    · intro x hx
      fin_cases x
      · exact absurd rfl (hx 0)
      · rfl
      · exact absurd rfl (hx 1)
      · rfl
      · exact absurd rfl (hx 2)
  have s3 : Step (fl 3) (4 * (binary c d).length + 3) ![2 * c + 4, 0, 0, 0, 0]
      ![recW s n d c Qr, ZeroPadding.pad S (frame [s]), ZeroPadding.pad S (frame (binary c n)),
        List.replicate S false, List.replicate S false]
      ![4 * c + 5, 0, 0, 0, 0]
      ![recW s n d c Qr, ZeroPadding.pad S (frame [s]), ZeroPadding.pad S (frame (binary c n)),
        ZeroPadding.pad S (frame (binary c d)), List.replicate S false] := by
    refine dock_vec l3 _ (fl_inj 3 (by decide) (by decide)) _ _ _ _ ?_ ?_ ?_ ?_ ?_ ?_
    · intro j
      fin_cases j
      · show 2 * c + 4 = (frame [s] ++ frame (binary c n)).length
        simp; omega
      · rfl
      · rfl
    · intro j; fin_cases j <;> rfl
    · intro j
      fin_cases j
      · show 4 * c + 5 = (frame [s] ++ frame (binary c n)).length + 2 * (binary c d).length + 1
        simp; omega
      · rfl
      · rfl
    · intro j; fin_cases j <;> rfl
    · intro x hx
      fin_cases x
      · exact absurd rfl (hx 0)
      · rfl
      · rfl
      · exact absurd rfl (hx 1)
      · exact absurd rfl (hx 2)
    · intro x hx
      fin_cases x
      · exact absurd rfl (hx 0)
      · rfl
      · rfl
      · exact absurd rfl (hx 1)
      · exact absurd rfl (hx 2)
  have hall := s1.seq (s2.seq s3)
  refine hall.enlarge ?_
  simp [parseCost]

theorem parse_local (s : Bool) (n d c Qr S C : Nat) (hS : 2 * c + 1 ≤ S) (hS3 : 3 ≤ S) (hC : parseCost c ≤ C) :
    Step parseM (2 * parseCost c + 2) (fun _ => 0)
      ![recW s n d c Qr, List.replicate S false, List.replicate S false, List.replicate S false,
        List.replicate S false, List.replicate C false] (fun _ => 0)
      ![recW s n d c Qr, ZeroPadding.pad S (frame [s]), ZeroPadding.pad S (frame (binary c n)),
        ZeroPadding.pad S (frame (binary c d)), List.replicate S false, List.replicate C false] := by
  have h := rewind_step (parse3_run s n d c Qr S hS hS3) C hC
  refine (h.congr_in rfl ?_).congr rfl ?_
  · funext i; fin_cases i <;> rfl
  · funext i; fin_cases i <;> rfl

/-- The parse, docked: three new framed fields, everything else (record, counter, log) restored. -/
theorem parse_step {U : Nat} (sl : Fin 6 → Fin U) (hsl : Function.Injective sl) (s : Bool) (n d c Qr S C : Nat)
    (hS : 2 * c + 1 ≤ S) (hS3 : 3 ≤ S) (hC : parseCost c ≤ C) (H : Fin U → Nat) (A : Fin U → List Bool)
    (hH : ∀ j, H (sl j) = 0) (h0 : A (sl 0) = recW s n d c Qr) (h1 : A (sl 1) = List.replicate S false)
    (h2 : A (sl 2) = List.replicate S false) (h3 : A (sl 3) = List.replicate S false)
    (h4 : A (sl 4) = List.replicate S false) (h5 : A (sl 5) = List.replicate C false) :
    Step (RecoveryFocus.machine sl parseM) (2 * parseCost c + 2) H A H
      (Function.update (Function.update (Function.update A (sl 1) (ZeroPadding.pad S (frame [s])))
        (sl 2) (ZeroPadding.pad S (frame (binary c n)))) (sl 3) (ZeroPadding.pad S (frame (binary c d)))) := by
  have hne : ∀ i j : Fin 6, i ≠ j → sl i ≠ sl j := fun i j h e => h (hsl e)
  refine dock_vec (parse_local s n d c Qr S C hS hS3 hC) sl hsl H H A _ hH ?_ hH ?_ (fun _ _ => rfl) ?_
  · intro j; fin_cases j
    · exact h0
    · exact h1
    · exact h2
    · exact h3
    · exact h4
    · exact h5
  · intro j; fin_cases j
    · simp [Function.update_of_ne (hne 0 3 (by decide)), Function.update_of_ne (hne 0 2 (by decide)),
        Function.update_of_ne (hne 0 1 (by decide)), h0]
    · simp [Function.update_of_ne (hne 1 3 (by decide)), Function.update_of_ne (hne 1 2 (by decide))]
    · simp [Function.update_of_ne (hne 2 3 (by decide))]
    · simp
    · simp [Function.update_of_ne (hne 4 3 (by decide)), Function.update_of_ne (hne 4 2 (by decide)),
        Function.update_of_ne (hne 4 1 (by decide)), h4]
    · simp [Function.update_of_ne (hne 5 3 (by decide)), Function.update_of_ne (hne 5 2 (by decide)),
        Function.update_of_ne (hne 5 1 (by decide)), h5]
  · intro x hx
    rw [Function.update_of_ne (fun e => hx 3 e.symm), Function.update_of_ne (fun e => hx 2 e.symm),
      Function.update_of_ne (fun e => hx 1 e.symm)]

/-! ## Binary → unary, docked (dirty scratch) -/

def unaryM {U : Nat} (sl : Fin 7 → Fin U) := RecoveryFocus.machine sl RepairSource.RecoveryProjectionDimension.machine

theorem unary_step {U : Nat} (sl : Fin 7 → Fin U) (hsl : Function.Injective sl) (bits : List Bool) (Q S : Nat)
    (H : Fin U → Nat) (A : Fin U → List Bool) (hH : ∀ j, H (sl j) = 0)
    (h0 : A (sl 0) = ZeroPadding.pad Q (frame bits)) (hs : ∀ j : Fin 7, j ≠ 0 → A (sl j) = List.replicate S false) :
    ∃ A' : Fin U → List Bool, Step (unaryM sl) (RepairSource.RecoveryProjectionDimension.budget bits) H A H A' ∧
      A' (sl 3) = ZeroPadding.pad S (CompareMachine.word (value bits)) ∧
      A' (sl 5) = ZeroPadding.pad S (List.replicate (value bits) true) ∧
      (∀ x, (∀ j, sl j ≠ x) → A' x = A x) := by
  obtain ⟨E', hs', h3, h5⟩ := unary_local bits Q S
  have d := hs'.dock sl hsl H A (fun j => hH j) (by
    intro j; fin_cases j
    · exact h0
    all_goals exact hs _ (by decide))
  rw [dockH_existing sl H (fun _ => 0) hH] at d
  refine ⟨_, d, ?_, ?_, fun x hx => install_other sl A E' x hx⟩
  · rw [install_slot sl hsl]; exact h3
  · rw [install_slot sl hsl]; exact h5

/-! ## One factor -/

def accM :=
  Composition.machine (RecoveryFocus.machine (![0, 8, 9, 10, 11, 7] : Fin 6 → Fin 30) parseM)
  (Composition.machine (unaryM (![8, 12, 13, 14, 15, 16, 17] : Fin 7 → Fin 30))
  (Composition.machine (Count.sumM (3 : Fin 30) 16 6 7)
  (Composition.machine (unaryM (![9, 18, 19, 20, 21, 22, 23] : Fin 7 → Fin 30))
  (Composition.machine (Count.mulM (1 : Fin 30) 20 4 7)
  (Composition.machine (unaryM (![10, 24, 25, 26, 27, 28, 29] : Fin 7 → Fin 30))
  (Count.mulM (2 : Fin 30) 26 5 7))))))

def ub (bits : List Bool) : Nat := RepairSource.RecoveryProjectionDimension.budget bits

def accCost (s : Bool) (n d c Na Da sa : Nat) : Nat :=
  (2 * parseCost c + 2) + 1 + (ub [s] + 1 + ((2 * (sa + s.toNat) + 6) + 1 + (ub (binary c n) + 1 +
    ((2 * (Na * (2 * n + 3) + 2) + 2) + 1 + (ub (binary c d) + 1 + (2 * (Da * (2 * d + 3) + 2) + 2))))))

/-- The size facts one factor needs. -/
structure AccFits (c n d Na Da sa S C : Nat) : Prop where
  s1 : 2 * c + 1 ≤ S
  s3 : 3 ≤ S
  c1 : parseCost c ≤ C
  c2 : sa + 1 + 2 ≤ C
  c3 : Na * (2 * n + 3) + 2 ≤ C
  c4 : Da * (2 * d + 3) + 2 ≤ C

theorem value_flag (s : Bool) : value [s] = s.toNat := by
  cases s <;> rfl

theorem acc_run (s : Bool) (n d c Qr Qa S C Na Da sa : Nat) (hn : n < 2 ^ c) (hd : d < 2 ^ c)
    (E : Fin 30 → List Bool) (h0 : E 0 = recW s n d c Qr)
    (h1 : E 1 = ZeroPadding.pad Qa (List.replicate Na true)) (h2 : E 2 = ZeroPadding.pad Qa (List.replicate Da true))
    (h3 : E 3 = ZeroPadding.pad Qa (List.replicate sa true)) (h7 : E 7 = List.replicate C false)
    (hscr : ∀ j : Fin 30, (j.val = 4 ∨ j.val = 5 ∨ j.val = 6 ∨ 8 ≤ j.val) → E j = List.replicate S false)
    (hf : AccFits c n d Na Da sa S C) :
    ∃ E' : Fin 30 → List Bool, Step accM (accCost s n d c Na Da sa) (fun _ => 0) E (fun _ => 0) E' ∧
      E' 4 = ZeroPadding.pad S (List.replicate (Na * n) true) ∧
      E' 5 = ZeroPadding.pad S (List.replicate (Da * d) true) ∧
      E' 6 = ZeroPadding.pad S (List.replicate (sa + s.toNat) true) ∧
      (∀ j : Fin 30, j.val < 4 → E' j = E j) ∧ E' 7 = E 7 := by
  -- 1. parse
  have p1 := parse_step (![0, 8, 9, 10, 11, 7] : Fin 6 → Fin 30) (by decide) s n d c Qr S C hf.s1 hf.s3 hf.c1
    (fun _ => 0) E (fun _ => rfl) h0 (hscr 8 (by decide)) (hscr 9 (by decide)) (hscr 10 (by decide))
    (hscr 11 (by decide)) h7
  set E1 := Function.update (Function.update (Function.update E (8 : Fin 30) (ZeroPadding.pad S (frame [s])))
    (9 : Fin 30) (ZeroPadding.pad S (frame (binary c n)))) (10 : Fin 30) (ZeroPadding.pad S (frame (binary c d)))
    with hE1
  have k1 : ∀ x : Fin 30, x ≠ 8 → x ≠ 9 → x ≠ 10 → E1 x = E x := by
    intro x a b c'
    rw [hE1, Function.update_of_ne c', Function.update_of_ne b, Function.update_of_ne a]
  -- 2. the sign bit to unary
  obtain ⟨E2, u1, u1a, u1b, u1o⟩ := unary_step (![8, 12, 13, 14, 15, 16, 17] : Fin 7 → Fin 30) (by decide) [s] S S
    (fun _ => 0) E1 (fun _ => rfl) (by simp [E1]) (by
      intro j hj
      fin_cases j
      · exact absurd rfl hj
      all_goals exact (k1 _ (by decide) (by decide) (by decide)).trans (hscr _ (by decide)))
  have k2 : ∀ x : Fin 30, x ≠ 8 → x ≠ 12 → x ≠ 13 → x ≠ 14 → x ≠ 15 → x ≠ 16 → x ≠ 17 → E2 x = E1 x := by
    intro x a1 a2 a3 a4 a5 a6 a7
    apply u1o
    intro j; fin_cases j
    · exact a1.symm
    · exact a2.symm
    · exact a3.symm
    · exact a4.symm
    · exact a5.symm
    · exact a6.symm
    · exact a7.symm
  have u1b' : E2 16 = ZeroPadding.pad S (List.replicate s.toNat true) := by
    rw [← value_flag]; exact u1b
  -- 3. the sign count
  have g3 : E2 3 = ZeroPadding.pad Qa (List.replicate sa true) := by
    rw [k2 3 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
      k1 3 (by decide) (by decide) (by decide)]; exact h3
  have g6 : E2 6 = List.replicate S false := by
    rw [k2 6 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
      k1 6 (by decide) (by decide) (by decide)]; exact hscr 6 (by decide)
  have g7 : E2 7 = List.replicate C false := by
    rw [k2 7 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
      k1 7 (by decide) (by decide) (by decide)]; exact h7
  have hc2 : sa + s.toNat + 2 ≤ C := by
    have := hf.c2; cases s <;> simp only [Bool.toNat_false, Bool.toNat_true] <;> omega
  have s3 := Count.sum_step (3 : Fin 30) 16 6 7 (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) sa s.toNat Qa S S C hc2 (fun _ => 0) E2 (fun _ _ => rfl) g3 u1b' g6 g7
  set E3 := Function.update E2 (6 : Fin 30) (ZeroPadding.pad S (List.replicate (sa + s.toNat) true)) with hE3
  have k3 : ∀ x : Fin 30, x ≠ 6 → E3 x = E2 x := fun x a => by rw [hE3, Function.update_of_ne a]
  -- 4. the numerator magnitude to unary
  have g9 : E3 9 = ZeroPadding.pad S (frame (binary c n)) := by
    rw [k3 9 (by decide), k2 9 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]
    simp [E1]
  obtain ⟨E4, u2, u2a, u2b, u2o⟩ := unary_step (![9, 18, 19, 20, 21, 22, 23] : Fin 7 → Fin 30) (by decide)
    (binary c n) S S (fun _ => 0) E3 (fun _ => rfl) g9 (by
      intro j hj
      fin_cases j
      · exact absurd rfl hj
      all_goals exact (k3 _ (by decide)).trans ((k2 _ (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide)).trans ((k1 _ (by decide) (by decide) (by decide)).trans (hscr _ (by decide)))))
  have k4 : ∀ x : Fin 30, x ≠ 9 → x ≠ 18 → x ≠ 19 → x ≠ 20 → x ≠ 21 → x ≠ 22 → x ≠ 23 → E4 x = E3 x := by
    intro x a1 a2 a3 a4 a5 a6 a7
    apply u2o
    intro j; fin_cases j
    · exact a1.symm
    · exact a2.symm
    · exact a3.symm
    · exact a4.symm
    · exact a5.symm
    · exact a6.symm
    · exact a7.symm
  have u2a' : E4 20 = ZeroPadding.pad S (CompareMachine.word n) := by
    rw [← binary_value c n hn]; exact u2a
  -- 5. numerator product
  have g1 : E4 1 = ZeroPadding.pad Qa (List.replicate Na true) := by
    rw [k4 1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), k3 1 (by decide),
      k2 1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
      k1 1 (by decide) (by decide) (by decide)]; exact h1
  have g4 : E4 4 = List.replicate S false := by
    rw [k4 4 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), k3 4 (by decide),
      k2 4 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
      k1 4 (by decide) (by decide) (by decide)]; exact hscr 4 (by decide)
  have g7' : E4 7 = List.replicate C false := by
    rw [k4 7 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), k3 7 (by decide)]
    exact g7
  have s5 := Count.mul_step (1 : Fin 30) 20 4 7 (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) Na n Qa S S C hf.c3 (fun _ => 0) E4 (fun _ _ => rfl) g1 u2a' g4 g7'
  set E5 := Function.update E4 (4 : Fin 30) (ZeroPadding.pad S (List.replicate (Na * n) true)) with hE5
  have k5 : ∀ x : Fin 30, x ≠ 4 → E5 x = E4 x := fun x a => by rw [hE5, Function.update_of_ne a]
  -- 6. the denominator to unary
  have g10 : E5 10 = ZeroPadding.pad S (frame (binary c d)) := by
    rw [k5 10 (by decide), k4 10 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
      k3 10 (by decide), k2 10 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]
    simp [E1]
  obtain ⟨E6, u3, u3a, u3b, u3o⟩ := unary_step (![10, 24, 25, 26, 27, 28, 29] : Fin 7 → Fin 30) (by decide)
    (binary c d) S S (fun _ => 0) E5 (fun _ => rfl) g10 (by
      intro j hj
      fin_cases j
      · exact absurd rfl hj
      all_goals exact (k5 _ (by decide)).trans ((k4 _ (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide)).trans ((k3 _ (by decide)).trans ((k2 _ (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide)).trans ((k1 _ (by decide) (by decide) (by decide)).trans
        (hscr _ (by decide)))))))
  have k6 : ∀ x : Fin 30, x ≠ 10 → x ≠ 24 → x ≠ 25 → x ≠ 26 → x ≠ 27 → x ≠ 28 → x ≠ 29 → E6 x = E5 x := by
    intro x a1 a2 a3 a4 a5 a6 a7
    apply u3o
    intro j; fin_cases j
    · exact a1.symm
    · exact a2.symm
    · exact a3.symm
    · exact a4.symm
    · exact a5.symm
    · exact a6.symm
    · exact a7.symm
  have u3a' : E6 26 = ZeroPadding.pad S (CompareMachine.word d) := by
    rw [← binary_value c d hd]; exact u3a
  -- 7. denominator product
  have g2 : E6 2 = ZeroPadding.pad Qa (List.replicate Da true) := by
    rw [k6 2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), k5 2 (by decide),
      k4 2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), k3 2 (by decide),
      k2 2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
      k1 2 (by decide) (by decide) (by decide)]; exact h2
  have g5 : E6 5 = List.replicate S false := by
    rw [k6 5 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), k5 5 (by decide),
      k4 5 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), k3 5 (by decide),
      k2 5 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
      k1 5 (by decide) (by decide) (by decide)]; exact hscr 5 (by decide)
  have g7'' : E6 7 = List.replicate C false := by
    rw [k6 7 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), k5 7 (by decide)]
    exact g7'
  have s7 := Count.mul_step (2 : Fin 30) 26 5 7 (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) Da d Qa S S C hf.c4 (fun _ => 0) E6 (fun _ _ => rfl) g2 u3a' g5 g7''
  have hall : Step accM _ (fun _ => 0) E (fun _ => 0) _ := p1.seq (u1.seq (s3.seq (u2.seq (s5.seq (u3.seq s7)))))
  refine ⟨_, hall, ?_, ?_, ?_, ?_, ?_⟩
  · rw [Function.update_of_ne (by decide),
      k6 4 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), hE5,
      Function.update_self]
  · rw [Function.update_self]
  · rw [Function.update_of_ne (by decide),
      k6 6 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), k5 6 (by decide),
      k4 6 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), hE3,
      Function.update_self]
  · intro j hj
    have hne : ∀ c : Fin 30, 4 ≤ c.val → j ≠ c := fun c hc e => by rw [e] at hj; omega
    rw [Function.update_of_ne (hne 5 (by decide)),
      k6 j (hne 10 (by decide)) (hne 24 (by decide)) (hne 25 (by decide)) (hne 26 (by decide)) (hne 27 (by decide))
        (hne 28 (by decide)) (hne 29 (by decide)), k5 j (hne 4 (by decide)),
      k4 j (hne 9 (by decide)) (hne 18 (by decide)) (hne 19 (by decide)) (hne 20 (by decide)) (hne 21 (by decide))
        (hne 22 (by decide)) (hne 23 (by decide)), k3 j (hne 6 (by decide)),
      k2 j (hne 8 (by decide)) (hne 12 (by decide)) (hne 13 (by decide)) (hne 14 (by decide)) (hne 15 (by decide))
        (hne 16 (by decide)) (hne 17 (by decide)), k1 j (hne 8 (by decide)) (hne 9 (by decide)) (hne 10 (by decide))]
  · rw [Function.update_of_ne (by decide), g7'', h7]

end
end NearCubicWires.SourceFactorSel.CoefAcc


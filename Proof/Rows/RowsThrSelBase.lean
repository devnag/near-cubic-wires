import Proof.Rows.RowsBaseJoin
import Proof.Rows.RowsInitBaseParams
import Proof.Rows.RowsThrSelCasc

set_option autoImplicit false
set_option maxRecDepth 120000
set_option warningAsError true

namespace RowsConstruction.ThrSelBase
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairOrdinary.RecoveryRootRound
open NearCubicWires.RepairRepresentation NearCubicWires.RepairSource.VerifierDecoding
open NearCubicWires.SupplierPipeline NearCubicWires.SupplierPrime NearCubicWires.SupplierEstimator
open RowsConstruction.BaseLayout RowsConstruction.KeyStep RowsConstruction.KeyTop RowsConstruction.ThrKey
open RowsConstruction.ThrSel RowsConstruction.ThrSelCasc
noncomputable section

/-! ## 1. The base worker's parameter functions (`base_numeric`) -/

/-- The six constants of the base worker's parameter polynomials (`RowsInitBaseParams.base_numeric_explicit`). -/
def bcD : ℕ := Classical.choose RowsInit.BaseParams.base_numeric_explicit
def bdD : ℕ := Classical.choose (Classical.choose_spec RowsInit.BaseParams.base_numeric_explicit)
def bcU : ℕ := Classical.choose (Classical.choose_spec (Classical.choose_spec RowsInit.BaseParams.base_numeric_explicit))
def bdU : ℕ := Classical.choose (Classical.choose_spec (Classical.choose_spec (Classical.choose_spec
  RowsInit.BaseParams.base_numeric_explicit)))
def bcF : ℕ := Classical.choose (Classical.choose_spec (Classical.choose_spec (Classical.choose_spec
  (Classical.choose_spec RowsInit.BaseParams.base_numeric_explicit))))
def bdF : ℕ := Classical.choose (Classical.choose_spec (Classical.choose_spec (Classical.choose_spec
  (Classical.choose_spec (Classical.choose_spec RowsInit.BaseParams.base_numeric_explicit)))))

/-- The parameter functions: CLOSED polynomials of `T` (so an initializer can write `1^(bU T)`). -/
def bD : ℕ → ℕ := fun T => ThrBaseBounds.DOf bcD bdD T
def bU : ℕ → ℕ := fun T => ThrBaseBounds.UOf' bcD bdD bcU bdU T
def bF : ℕ → ℕ := fun T => ThrBaseBounds.FOf' bcD bdD bcU bdU bcF bdF T

theorem b_poly : ∃ c d, ∀ T : Nat, NearCubicWires.ValidatorPolynomialDomination.PolyBounded (bD T+bU T+bF T) T c d :=
  ThrBaseBounds.baseParams_pb bcD bdD bcU bdU bcF bdF

theorem b_spec :
    ∀ (a : DecompositionAlgorithm) (r : FourfoldRequest NormalizedThresholdThresholdCircuit)
      (four : r.circuits.length ≤ 4) (L target : Nat) (sel : ThresholdRows.Selection a r),
      PCJ45bee56da9f34d5a_FourfoldBaseData.Bounds (PCJ45bee56da9f34d5a_StreamPair.data a r four sel)
        (ThrWidth.T a r four L target) (12*ThrWidth.T a r four L target+17)
        (8*(12*ThrWidth.T a r four L target+17)+12) (bD (ThrWidth.T a r four L target))
        (bU (ThrWidth.T a r four L target)) (ThrWidth.T a r four L target) (bF (ThrWidth.T a r four L target)) ∧
      4*(12*ThrWidth.T a r four L target+19)+3 ≤ bU (ThrWidth.T a r four L target) :=
  Classical.choose_spec (Classical.choose_spec (Classical.choose_spec (Classical.choose_spec (Classical.choose_spec
    (Classical.choose_spec RowsInit.BaseParams.base_numeric_explicit)))))

/-! ## 2. The base worker's bank: census -/

section Census
set_option linter.unnecessarySeqFocus false in
/-- Off the accumulator (9) and the four digit ports (73–76) the base worker's bank depends on neither. -/
theorem bank_other (source : List Bool) (dg dg' : Fin 4 → Nat) (N v w C U a a' : Nat) (k : Fin 82)
    (h9 : k ≠ 9) (hd : ¬ (73 ≤ k.val ∧ k.val < 77)) :
    PCJ45bee56da9f34d5a_FourfoldBaseCell.bank source dg N v w C U a k =
      PCJ45bee56da9f34d5a_FourfoldBaseCell.bank source dg' N v w C U a' k := by
  fin_cases k <;> first
    | exact (h9 (by decide)).elim
    | exact (hd ⟨by decide, by decide⟩).elim
    | (bank_nf PCJ45bee56da9f34d5a_FourfoldBaseCell.bank <;>
        bank_nf PCJ45bee56da9f34d5a_FourfoldBaseCell.bank <;> rfl)

/-- Digit port `73+c` of the base worker's bank. -/
def dk (c : Fin 4) : Fin 82 := ⟨73 + c.val, by omega⟩

theorem bank_digit (source : List Bool) (dg : Fin 4 → Nat) (N v w C U a : Nat) (c : Fin 4) :
    PCJ45bee56da9f34d5a_FourfoldBaseCell.bank source dg N v w C U a (dk c) =
      frame (SignedSortKey.binary v (dg c)) := by
  fin_cases c <;> rfl

theorem heads_one (k : Fin 82) :
    PCJ45bee56da9f34d5a_FourfoldBaseCell.heads 1 k = if 77 ≤ k.val then 1 else 0 := by
  unfold PCJ45bee56da9f34d5a_FourfoldBaseCell.heads
  have := k.isLt
  by_cases h81 : k = 81
  · subst h81; rfl
  · rw [if_neg h81]
    have hk : k.val ≠ 81 := fun e => h81 (Fin.ext e)
    by_cases h77 : 77 ≤ k.val
    · rw [if_pos ⟨h77, by omega⟩, if_pos h77]
    · rw [if_neg (by omega), if_neg h77]

end Census

/-! ## 3. Ports -/

section Ports
variable (NI : Nat) (ib : Fin 82 → Fin NI) (iOne : Fin NI)

/-- The base worker's slot map: digit ports 73–76 on the child-digit masters, everything else on `init`. -/
def bS (k : Fin 82) : Fin (2+rowsWork NI) :=
  if h : 73 ≤ k.val ∧ k.val < 77 then masterPort NI (dPort ⟨k.val - 73, by omega⟩) else initPort NI (ib k)

theorem bS_digit (c : Fin 4) : bS NI ib (dk c) = masterPort NI (dPort c) := by
  unfold bS dk
  rw [dif_pos (by simp; omega)]
  congr 2
  apply Fin.ext
  simp

theorem bS_init (k : Fin 82) (hk : ¬ (73 ≤ k.val ∧ k.val < 77)) : bS NI ib k = initPort NI (ib k) := by
  unfold bS
  rw [dif_neg hk]

theorem bS_injective (hib : Function.Injective ib) : Function.Injective (bS NI ib) := by
  intro x y h
  unfold bS at h
  split_ifs at h with hx hy hy
  · have hv := (masterPort_inj NI _ _).mp h
    have hv' := congrArg Fin.val hv
    rw [dPort_val, dPort_val] at hv'
    simp only at hv'
    exact Fin.ext (by omega)
  · exact absurd h.symm (initPort_ne_master NI _ _)
  · exact absurd h (initPort_ne_master NI _ _)
  · have hv := congrArg Fin.val h
    rw [initPort_val, initPort_val] at hv
    exact hib (Fin.ext (by omega))

/-- The ports that must sit at head 1 for the base worker (its count/cursor ports 77–81). -/
def hot (p : Fin (2+rowsWork NI)) : Prop := ∃ k : Fin 82, 77 ≤ k.val ∧ initPort NI (ib k) = p

instance (p : Fin (2+rowsWork NI)) : Decidable (hot NI ib p) := by
  unfold hot; infer_instance

def mv (dir : HeadMove) : Machine (2+rowsWork NI) 2 :=
  DecompositionCountPosition.move (fun p => if hot NI ib p then dir else HeadMove.stay)

def H1 (p : Fin (2+rowsWork NI)) : ℕ := if hot NI ib p then 1 else 0

theorem mv_right (A : Fin (2+rowsWork NI) → List Bool) :
    Step (mv NI ib HeadMove.right) 1 (fun _ => 0) A (H1 NI ib) A := by
  obtain ⟨r, hr, hf, _⟩ := DecompositionCountPosition.move_run
    (fun p => if hot NI ib p then HeadMove.right else HeadMove.stay) (fun _ => 0) A
  refine Step.of_run hr ?_ (by rw [hf])
  rw [hf]
  funext p
  show (if hot NI ib p then HeadMove.right else HeadMove.stay).apply 0 = H1 NI ib p
  unfold H1
  split <;> rfl

theorem mv_left (A : Fin (2+rowsWork NI) → List Bool) :
    Step (mv NI ib HeadMove.left) 1 (H1 NI ib) A (fun _ => 0) A := by
  obtain ⟨r, hr, hf, _⟩ := DecompositionCountPosition.move_run
    (fun p => if hot NI ib p then HeadMove.left else HeadMove.stay) (H1 NI ib) A
  refine Step.of_run hr ?_ (by rw [hf])
  rw [hf]
  funext p
  show (if hot NI ib p then HeadMove.left else HeadMove.stay).apply (H1 NI ib p) = 0
  unfold H1
  split <;> rfl

theorem H1_bS (hib : Function.Injective ib) (k : Fin 82) :
    H1 NI ib (bS NI ib k) = PCJ45bee56da9f34d5a_FourfoldBaseCell.heads 1 k := by
  rw [heads_one]
  unfold H1
  by_cases hd : 73 ≤ k.val ∧ k.val < 77
  · have hnot : ¬ hot NI ib (bS NI ib k) := by
      intro hx
      obtain ⟨k', _, e⟩ := hx
      unfold bS at e
      rw [dif_pos hd] at e
      exact initPort_ne_master NI _ _ e
    rw [if_neg hnot, if_neg (show ¬ 77 ≤ k.val by omega)]
  · rw [bS_init NI ib k hd]
    by_cases h77 : 77 ≤ k.val
    · rw [if_pos (show hot NI ib (initPort NI (ib k)) from ⟨k, h77, rfl⟩), if_pos h77]
    · have hnot : ¬ hot NI ib (initPort NI (ib k)) := by
        intro hx
        obtain ⟨k', hk', e⟩ := hx
        have hv := congrArg Fin.val e
        rw [initPort_val, initPort_val] at hv
        have hkk : k' = k := hib (Fin.ext (by omega))
        rw [hkk] at hk'
        exact h77 hk'
      rw [if_neg hnot, if_neg h77]

/-- The docked base worker. -/
def dockB := RecoveryFocus.machine (bS NI ib) PCJ45bee56da9f34d5a_FourfoldBaseRun.machine

/-- The scalar copy, docked by a 4-slot map (source, destination, two blank scratch tapes). -/
def srM (s : Fin 4 → Fin (2+rowsWork NI)) := RecoveryFocus.machine s MatrixFrameCopy.machine

def cpS : Fin 4 → Fin (2+rowsWork NI) :=
  ![initPort NI (ib 9), masterPort NI 220, cellPort NI 0, cellPort NI 1]
def rsS : Fin 4 → Fin (2+rowsWork NI) :=
  ![initPort NI iOne, initPort NI (ib 9), cellPort NI 0, cellPort NI 1]

/-- **The base stage** (one fixed machine). -/
def baseW := Composition.machine (mv NI ib HeadMove.right) (Composition.machine (dockB NI ib)
  (Composition.machine (mv NI ib HeadMove.left) (Composition.machine (srM NI (cpS NI ib)) (srM NI (rsS NI ib iOne)))))

end Ports

/-! ## 4. The scalar copy on the work block -/

theorem pad_pad (m n : Nat) (l : List Bool) (h : m ≤ n) : ZeroPadding.pad n (ZeroPadding.pad m l) = ZeroPadding.pad n l := by
  simp only [ZeroPadding.pad, List.length_append, List.length_replicate, List.append_assoc,
    List.replicate_append_replicate]
  congr 2
  omega

theorem pad_rep (m n : Nat) (h : m ≤ n) : ZeroPadding.pad n (List.replicate m false) = List.replicate n false := by
  simp only [ZeroPadding.pad, List.length_replicate, List.replicate_append_replicate]
  congr 1
  omega

theorem sr_step {NI : Nat} (s : Fin 4 → Fin (2+rowsWork NI)) (hs : Function.Injective s)
    (bits backing : List Bool) (U0 P0 P1 R : Nat) (hb : backing.length ≤ 2*bits.length+1) (hU : 4*bits.length+3 ≤ U0)
    (h0 : U0 ≤ P0) (h1 : U0 ≤ P1) (hR : U0 ≤ R) (A : Fin (2+rowsWork NI) → List Bool)
    (a0 : A (s 0) = ZeroPadding.pad P0 (frame bits)) (a1 : A (s 1) = ZeroPadding.pad P1 backing)
    (a2 : A (s 2) = List.replicate R false) (a3 : A (s 3) = List.replicate R false) :
    Step (RecoveryFocus.machine s MatrixFrameCopy.machine) (8*bits.length+8) (fun _ => 0) A (fun _ => 0)
      (Function.update A (s 1) (ZeroPadding.pad P1 (frame bits))) := by
  have base := (PCJ45bee56da9f34d5a_ScalarReplace.run bits backing U0 hb hU).pad ![P0, P1, R, R]
  have ein : (fun i => ZeroPadding.pad (![P0, P1, R, R] i)
      ((![ZeroPadding.pad U0 (frame bits), ZeroPadding.pad U0 backing, List.replicate U0 false,
        List.replicate U0 false] : Fin 4 → List Bool) i)) = fun i => A (s i) := by
    funext i
    fin_cases i
    · show ZeroPadding.pad P0 (ZeroPadding.pad U0 (frame bits)) = A (s 0)
      rw [pad_pad _ _ _ h0, a0]
    · show ZeroPadding.pad P1 (ZeroPadding.pad U0 backing) = A (s 1)
      rw [pad_pad _ _ _ h1, a1]
    · show ZeroPadding.pad R (List.replicate U0 false) = A (s 2)
      rw [pad_rep _ _ hR, a2]
    · show ZeroPadding.pad R (List.replicate U0 false) = A (s 3)
      rw [pad_rep _ _ hR, a3]
  have eout : (fun i => ZeroPadding.pad (![P0, P1, R, R] i)
      ((![ZeroPadding.pad U0 (frame bits), ZeroPadding.pad U0 (frame bits), List.replicate U0 false,
        List.replicate U0 false] : Fin 4 → List Bool) i)) =
      fun i => Function.update (fun i => A (s i)) 1 (ZeroPadding.pad P1 (frame bits)) i := by
    funext i
    fin_cases i
    · show ZeroPadding.pad P0 (ZeroPadding.pad U0 (frame bits)) =
        Function.update (fun i => A (s i)) 1 (ZeroPadding.pad P1 (frame bits)) 0
      rw [Function.update_of_ne (by decide), pad_pad _ _ _ h0, a0]
    · show ZeroPadding.pad P1 (ZeroPadding.pad U0 (frame bits)) =
        Function.update (fun i => A (s i)) 1 (ZeroPadding.pad P1 (frame bits)) 1
      rw [Function.update_self, pad_pad _ _ _ h1]
    · show ZeroPadding.pad R (List.replicate U0 false) =
        Function.update (fun i => A (s i)) 1 (ZeroPadding.pad P1 (frame bits)) 2
      rw [Function.update_of_ne (by decide), pad_rep _ _ hR, a2]
    · show ZeroPadding.pad R (List.replicate U0 false) =
        Function.update (fun i => A (s i)) 1 (ZeroPadding.pad P1 (frame bits)) 3
      rw [Function.update_of_ne (by decide), pad_rep _ _ hR, a3]
  rw [ein, eout] at base
  have d := wdock NI base s hs A (fun _ => rfl)
  rw [SymVerdict.install_update _ hs A _ 1 (fun j hj => by rw [Function.update_of_ne hj])] at d
  rw [Function.update_self] at d
  exact d

/-! ## 5. The base stage on the work block -/

section Base
variable (a : DecompositionAlgorithm) (r : FourfoldRequest NormalizedThresholdThresholdCircuit)
  (four : r.circuits.length ≤ 4) (L target : Nat)

/-- The request's TOP payload stream (the base worker's source; selection-independent). -/
def srcB : List Bool :=
  (r.circuits.map (fun c => PCJ45bee56da9f34d5a_TopChildCursor.payload (ThresholdRows.children a c))).flatMap frame

/-- **The base worker's resident words** (request constants; `init (ib k)` for the 78 non-digit ports). -/
def baseInit (k : Fin 82) : List Bool :=
  PCJ45bee56da9f34d5a_FourfoldBaseCell.bank (srcB a r) (fun _ => 0) r.circuits.length (ThrWidth.T a r four L target)
    (12*ThrWidth.T a r four L target+17) (8*(12*ThrWidth.T a r four L target+17)+12) (bU (ThrWidth.T a r four L target))
    1 k

/-- The cost of the base stage. -/
def baseCost (F w : Nat) : Nat := 1+1+((4*F+27)+1+(1+1+((8*w+8)+1+(8*w+8))))

theorem cpS_injective (NI : Nat) (ib : Fin 82 → Fin NI) : Function.Injective (cpS NI ib) := by
  intro x y h
  have hv := congrArg Fin.val h
  have := (ib 9).isLt
  fin_cases x <;> fin_cases y <;> simp [cpS, masterPort_val, cellPort_val, initPort_val] at hv ⊢ <;> omega

theorem rsS_injective (NI : Nat) (ib : Fin 82 → Fin NI) (iOne : Fin NI) (hone : ib 9 ≠ iOne) :
    Function.Injective (rsS NI ib iOne) := by
  intro x y h
  have hv := congrArg Fin.val h
  have := (ib 9).isLt
  have := iOne.isLt
  have hne : (ib 9).val ≠ iOne.val := fun e => hone (Fin.ext e)
  fin_cases x <;> fin_cases y <;> simp [rsS, cellPort_val, initPort_val] at hv ⊢ <;> omega

theorem data_src (sel : ThresholdRows.Selection a r) :
    (PCJ45bee56da9f34d5a_StreamPair.data a r four sel).words.flatMap frame = srcB a r := by
  rw [ThrBounds.words_eq a r four sel]
  rfl

/-- **The base stage.** On any work bank carrying the selection's child digits on 228–231, the base worker's resident
words on `init`, the constant `scalar U (w+2) 1` at `init iOne`, any framed base at master 220 and blank cells 0–1, the
fixed machine `baseW` writes the canonical base `B(sel)` onto master 220 and changes nothing else. -/
theorem base_step (NI : Nat) (ib : Fin 82 → Fin NI) (iOne : Fin NI) (hib : Function.Injective ib)
    (hone : ib 9 ≠ iOne) (sel : ThresholdRows.Selection a r) (Uf R B0 : Nat) (A : Fin (2+rowsWork NI) → List Bool)
    (hdig : ∀ c, A (masterPort NI (dPort c)) =
      fb (ThrWidth.T a r four L target) ((PCJ45bee56da9f34d5a_StreamPair.data a r four sel).digits c))
    (hini : ∀ k : Fin 82, ¬ (73 ≤ k.val ∧ k.val < 77) → A (initPort NI (ib k)) = baseInit a r four L target k)
    (hon : A (initPort NI iOne) = ZeroPadding.pad (bU (ThrWidth.T a r four L target)) (fb (wT a r four L target) 1))
    (h220 : A (masterPort NI 220) = ZeroPadding.pad Uf (fb (wT a r four L target) B0))
    (hc0 : A (cellPort NI 0) = List.replicate R false) (hc1 : A (cellPort NI 1) = List.replicate R false)
    (hUf : 4*wT a r four L target+3 ≤ Uf) (hR : 4*wT a r four L target+3 ≤ R) :
    Step (baseW NI ib iOne) (baseCost (bF (ThrWidth.T a r four L target)) (wT a r four L target)) (fun _ => 0) A
      (fun _ => 0) (Function.update A (masterPort NI 220)
        (ZeroPadding.pad Uf (fb (wT a r four L target) (PCJ45bee56da9f34d5a_StreamPair.radix a r four sel)))) := by
  set T := ThrWidth.T a r four L target with hT
  set d := PCJ45bee56da9f34d5a_StreamPair.data a r four sel with hd
  set Ub := bU T with hUb
  obtain ⟨hbnd, hfit⟩ := b_spec a r four L target sel
  -- the base worker's entry bank, read from `A`
  have hbank : ∀ k : Fin 82, A (bS NI ib k) =
      PCJ45bee56da9f34d5a_FourfoldBaseCell.bank (d.words.flatMap frame) d.digits d.count T (12*T+17)
        (8*(12*T+17)+12) Ub 1 k := by
    intro k
    by_cases hk : 73 ≤ k.val ∧ k.val < 77
    · obtain ⟨c, hc⟩ : ∃ c : Fin 4, k = dk c := ⟨⟨k.val - 73, by omega⟩, Fin.ext (by simp [dk]; omega)⟩
      subst hc
      rw [bS_digit, bank_digit, hdig]
    · rw [bS_init NI ib k hk, hini k hk, baseInit, ← data_src a r four sel]
      by_cases h9 : k = 9
      · subst h9
        rw [RowsConstruction.BaseJoin.base_port9, RowsConstruction.BaseJoin.base_port9]
      · exact bank_other _ _ _ _ _ _ _ _ _ _ k h9 hk
  -- (1) heads of the count/cursor ports to 1
  have s1 := mv_right NI ib A
  -- (2) the docked base worker
  have run := PCJ45bee56da9f34d5a_FourfoldBaseRun.run d T (12*T+17) (8*(12*T+17)+12) (bD T) Ub T (bF T) hbnd
  have s2 := SymVerdict.focus_at run (bS NI ib) (bS_injective NI ib hib) (H1 NI ib) A (H1_bS NI ib hib) hbank
  rw [dockH_existing _ _ _ (H1_bS NI ib hib)] at s2
  set Bv := 1 + d.values.sum with hBv
  have hrad : Bv = PCJ45bee56da9f34d5a_StreamPair.radix a r four sel := rfl
  rw [SymVerdict.install_update _ (bS_injective NI ib hib) A _ 9 (fun k hk9 => by
    rw [hbank k]
    by_cases hk : 73 ≤ k.val ∧ k.val < 77
    · obtain ⟨c, hc⟩ : ∃ c : Fin 4, k = dk c := ⟨⟨k.val - 73, by omega⟩, Fin.ext (by simp [dk]; omega)⟩
      subst hc
      rw [bank_digit, bank_digit]
    · exact bank_other _ _ _ _ _ _ _ _ _ _ k hk9 hk)] at s2
  rw [bS_init NI ib 9 (by decide), RowsConstruction.BaseJoin.base_port9] at s2
  set A2 := Function.update A (initPort NI (ib 9)) (MatrixScoreWeight.scalar Ub (12*T+17+2) Bv) with hA2
  -- (3) heads back
  have s3 := mv_left NI ib A2
  -- (4) accumulator onto master 220
  have hB : Bv < 2^(wT a r four L target) := by
    rw [hrad]; exact ThrWidth.base_fit a r four L target sel
  have cellA2 : ∀ c : Fin 257, A2 (cellPort NI c) = A (cellPort NI c) := fun c =>
    Function.update_of_ne (fun e => by
      have hv := congrArg Fin.val e
      rw [cellPort_val, initPort_val] at hv
      have := (ib 9).isLt
      omega) _ _
  have s4 := sr_step (cpS NI ib) (cpS_injective NI ib) (SignedSortKey.binary (wT a r four L target) Bv)
    (frame (SignedSortKey.binary (wT a r four L target) B0)) (4*wT a r four L target+3) Ub Uf R
    (by rw [frame_length, SignedSortKey.binary_length, SignedSortKey.binary_length])
    (by rw [SignedSortKey.binary_length]) (by omega) hUf hR A2
    (by show A2 (initPort NI (ib 9)) = _; rw [hA2, Function.update_self]; rfl)
    (by show A2 (masterPort NI 220) = _; rw [hA2, Function.update_of_ne (initPort_ne_master NI _ _).symm, h220])
    (by show A2 (cellPort NI 0) = _; rw [cellA2, hc0])
    (by show A2 (cellPort NI 1) = _; rw [cellA2, hc1])
  rw [show cpS NI ib 1 = masterPort NI 220 from rfl, SignedSortKey.binary_length] at s4
  set A3 := Function.update A2 (masterPort NI 220)
    (ZeroPadding.pad Uf (frame (SignedSortKey.binary (wT a r four L target) Bv))) with hA3
  -- (5) accumulator reset from the resident constant
  have cellA3 : ∀ c : Fin 257, A3 (cellPort NI c) = A (cellPort NI c) := fun c => by
    rw [hA3, Function.update_of_ne (cell_ne_master NI c 220), cellA2]
  have s5 := sr_step (rsS NI ib iOne) (rsS_injective NI ib iOne hone) (SignedSortKey.binary (wT a r four L target) 1)
    (frame (SignedSortKey.binary (wT a r four L target) Bv)) (4*wT a r four L target+3) Ub Ub R
    (by rw [frame_length, SignedSortKey.binary_length, SignedSortKey.binary_length])
    (by rw [SignedSortKey.binary_length]) (by omega) (by omega) hR A3
    (by show A3 (initPort NI iOne) = _
        rw [hA3, Function.update_of_ne (initPort_ne_master NI _ _), hA2,
          Function.update_of_ne (fun e => hone (Fin.ext (by
            have := congrArg Fin.val e; rw [initPort_val, initPort_val] at this; omega))), hon])
    (by show A3 (initPort NI (ib 9)) = _
        rw [hA3, Function.update_of_ne (initPort_ne_master NI _ _), hA2, Function.update_self]; rfl)
    (by show A3 (cellPort NI 0) = _; rw [cellA3, hc0])
    (by show A3 (cellPort NI 1) = _; rw [cellA3, hc1])
  rw [show rsS NI ib iOne 1 = initPort NI (ib 9) from rfl, SignedSortKey.binary_length] at s5
  -- the final bank
  have hA9 : A (initPort NI (ib 9)) = ZeroPadding.pad Ub (frame (SignedSortKey.binary (wT a r four L target) 1)) := by
    rw [hini 9 (by decide), baseInit, RowsConstruction.BaseJoin.base_port9]; rfl
  have efin : Function.update A3 (initPort NI (ib 9))
      (ZeroPadding.pad Ub (frame (SignedSortKey.binary (wT a r four L target) 1))) =
      Function.update A (masterPort NI 220)
        (ZeroPadding.pad Uf (fb (wT a r four L target) (PCJ45bee56da9f34d5a_StreamPair.radix a r four sel))) := by
    rw [hA3, hA2, Function.update_comm (initPort_ne_master NI _ _), Function.update_idem]
    rw [Function.update_eq_self_iff.mpr (by rw [Function.update_of_ne (initPort_ne_master NI _ _), hA9])]
    rfl
  rw [efin] at s5
  have all := s1.seq (s2.seq (s3.seq (s4.seq s5)))
  exact all.enlarge (by unfold baseCost; omega)

end Base

/-! ## 6. `K'`: the whole selection level on the work block -/

/-- **The THR selection level** (one fixed machine): child-digit cascade, then the base stage. -/
def selK (NI : Nat) (ix : Fin 4 → Fin NI) (ib : Fin 82 → Fin NI) (iOne : Fin NI) :=
  Composition.machine (selC NI ix) (baseW NI ib iOne)

/-- Its cost. -/
def selCost (T R F w : Nat) : Nat := cascCost T R + 1 + baseCost F w

section Sel
variable (a : DecompositionAlgorithm) (r : FourfoldRequest NormalizedThresholdThresholdCircuit)
  (four : r.circuits.length ≤ 4) (L target : Nat)

theorem digit_master (R : Nat) (k : RCFive.RowKeys.ThrKey a r L target) (c : Fin 4) :
    thrMasters a r four L target R k (dPort c) =
      fb (ThrWidth.T a r four L target) (KeySucc.dig a r L target k (c4 c)) := by
  rw [← data_digits a r four L target k c]
  have hc : dPort c = ⟨228 + c.val, by omega⟩ := Fin.ext (dPort_val c)
  have h109 : dPort c ≠ 109 := by
    intro e
    have := congrArg Fin.val e
    rw [dPort_val] at this
    simp at this
    omega
  have hkey : dPort c ∈ thrKeySet := by fin_cases c <;> decide
  rw [masters_at a r four L target R k _ h109, keyPad_key _ hkey, hc]
  exact KeySucc.thr_digit_ports a r four _ _ L target _ _ _ _ _ _ _ _ c

theorem master_220 (R : Nat) (k : RCFive.RowKeys.ThrKey a r L target) :
    thrMasters a r four L target R k 220 = ZeroPadding.pad (Uf r.q (ThrWidth.T a r four L target))
      (fb (wT a r four L target) (PCJ45bee56da9f34d5a_StreamPair.radix a r four k.selection)) := by
  rw [masters_at a r four L target R k 220 (by decide), keyPad_key _ (by decide)]
  exact KeySucc.thr_220 a r four _ _ L target _ _ _ _ _ _ _ _

theorem digBank_at (NI : Nat) (A : Fin (2+rowsWork NI) → List Bool) (w : Nat) (e : Fin 4 → ℕ) (c : Fin 4) :
    digBank NI A w e (masterPort NI (dPort c)) = fb w (e c) := by
  have ne : ∀ i k : Fin 254, i ≠ k → masterPort NI i ≠ masterPort NI k := fun i k h ee =>
    h ((masterPort_inj NI i k).mp ee)
  unfold digBank
  fin_cases c
  · show Function.update _ (masterPort NI 231) _ (masterPort NI 228) = _
    rw [Function.update_of_ne (ne 228 231 (by decide)), Function.update_of_ne (ne 228 230 (by decide)),
      Function.update_of_ne (ne 228 229 (by decide)), Function.update_self]
    rfl
  · show Function.update _ (masterPort NI 231) _ (masterPort NI 229) = _
    rw [Function.update_of_ne (ne 229 231 (by decide)), Function.update_of_ne (ne 229 230 (by decide)),
      Function.update_self]
    rfl
  · show Function.update _ (masterPort NI 231) _ (masterPort NI 230) = _
    rw [Function.update_of_ne (ne 230 231 (by decide)), Function.update_self]
    rfl
  · show Function.update _ (masterPort NI 231) _ (masterPort NI 231) = _
    rw [Function.update_self]
    rfl

theorem digBank_off (NI : Nat) (A : Fin (2+rowsWork NI) → List Bool) (w : Nat) (e : Fin 4 → ℕ)
    (p : Fin (2+rowsWork NI)) (hp : ∀ k : Fin 254, k = 228 ∨ k = 229 ∨ k = 230 ∨ k = 231 → p ≠ masterPort NI k) :
    digBank NI A w e p = A p := by
  unfold digBank
  rw [Function.update_of_ne (hp 231 (by decide)), Function.update_of_ne (hp 230 (by decide)),
    Function.update_of_ne (hp 229 (by decide)), Function.update_of_ne (hp 228 (by decide))]

variable (NI : Nat) (pub : Fin 2 → List Bool) (init : Fin NI → List Bool) (rcp : Fin 64 → List Bool) (C cC hF : Nat)

include four in

theorem thr_sel (j : Nat) (hj : j < (KeySucc.keys a r L target).length)
    (h1 : ¬ (KeySucc.keys a r L target)[j].residue.val + 1 < (KeySucc.keys a r L target)[j].prime.val)
    (h2 : ¬ thrSeedIdx a r L target (KeySucc.keys a r L target)[j] + 1 < (thrSeeds a r L target).length)
    (ix : Fin 4 → Fin NI) (ib : Fin 82 → Fin NI) (iOne : Fin NI) (hib : Function.Injective ib) (hone : ib 9 ≠ iOne)
    (hinitD : ∀ c, init (ix c) = fb (ThrWidth.T a r four L target) (bnd a r c))
    (hinitB : ∀ k : Fin 82, ¬ (73 ≤ k.val ∧ k.val < 77) → init (ib k) = baseInit a r four L target k)
    (hinitO : init iOne = ZeroPadding.pad (bU (ThrWidth.T a r four L target)) (fb (wT a r four L target) 1)) :
    ¬ KeySucc.dig a r L target (KeySucc.keys a r L target)[j] 4 + 1 <
        NearCubicWires.PacketsGlue.PrimeCount.pc (KeySucc.cut a r target) →
      Step (selK NI ix ib iOne) (selCost (ThrWidth.T a r four L target) (RT a r four L target)
          (bF (ThrWidth.T a r four L target)) (wT a r four L target)) (fun _ => 0)
        (Bp a r four L target NI pub init rcp C cC hF j 2) (fun _ => 0)
        (thrBase a r four L target NI pub init rcp C cC hF (j+1)) := by
  intro h3
  obtain ⟨k', hk', hdig', hp4, hp5, hp6⟩ := sel_key a r four L target j hj h1 h2 h3
  set T := ThrWidth.T a r four L target with hT
  set kj := (KeySucc.keys a r L target)[j] with hkj
  set A0 := Bp a r four L target NI pub init rcp C cC hF j 2 with hA0
  have hw : wT a r four L target = 12*T+19 := rfl
  
  have hA0m : ∀ i : Fin 254, i ≠ 240 → i ≠ 149 → i ≠ 218 → i ≠ 209 → i ≠ 242 →
      A0 (masterPort NI i) = thrMasters a r four L target (RT a r four L target) kj i := by
    intro i n240 n149 n218 n209 n242
    rw [hA0]
    unfold Bp
    rw [Function.update_of_ne (fun e => n209 ((masterPort_inj NI _ _).mp e)),
      Function.update_of_ne (fun e => n218 ((masterPort_inj NI _ _).mp e)),
      Function.update_of_ne (fun e => n149 ((masterPort_inj NI _ _).mp e)),
      Function.update_of_ne (fun e => n240 ((masterPort_inj NI _ _).mp e))]
    exact B1_master a r four L target NI pub init rcp C cC hF j hj i n242
  have hA0c : ∀ c : Fin 257, A0 (cellPort NI c) =
      PCJ45bee56da9f34d5a_VerdictFinish.bank (fun _ => List.replicate (RT a r four L target) false)
        (RT a r four L target) (List.replicate (2^(thrLive r L)ᶜ.card) false) c := by
    intro c
    rw [hA0]
    unfold Bp
    rw [Function.update_of_ne (cell_ne_master NI c 209), Function.update_of_ne (cell_ne_master NI c 218),
      Function.update_of_ne (cell_ne_master NI c 149), Function.update_of_ne (cell_ne_master NI c 240)]
    exact B1_cell a r four L target NI pub init rcp C cC hF j hj c
  have hA0i : ∀ i : Fin NI, A0 (initPort NI i) = init i := by
    intro i
    rw [hA0]
    unfold Bp B1
    rw [Function.update_of_ne (initPort_ne_master NI i 209), Function.update_of_ne (initPort_ne_master NI i 218),
      Function.update_of_ne (initPort_ne_master NI i 149), Function.update_of_ne (initPort_ne_master NI i 240),
      Function.update_of_ne (initPort_ne_c5 NI i 0), Function.update_of_ne (initPort_ne_master NI i 242)]
    exact (thr_base_rc a r four L target NI pub init rcp C cC hF j).2.1 i
  have hcells : Cells NI (RT a r four L target) A0 :=
    ⟨by rw [hA0c]; rfl, by rw [hA0c]; rfl, by rw [hA0c]; rfl, by rw [hA0c]; rfl, by rw [hA0c]; rfl,
      by rw [hA0c]; rfl⟩
  -- (1) the child-digit cascade
  have hT3 : 3 ≤ T := by have := ThrBounds.header_le a r four L target; omega
  have hRT : 2*(wT a r four L target)+1 ≤ RT a r four L target := wT_fits a r four L target kj
  have hd : ∀ c, A0 (masterPort NI (dPort c)) = fb T (KeySucc.dig a r L target kj (c4 c)) := by
    intro c
    have hne : ∀ z : Fin 254, z = 240 ∨ z = 149 ∨ z = 218 ∨ z = 209 ∨ z = 242 → dPort c ≠ z := by
      intro z hz e
      have hv := congrArg Fin.val e
      rw [dPort_val] at hv
      have := c.isLt
      rcases hz with rfl | rfl | rfl | rfl | rfl <;> simp at hv <;> omega
    rw [hA0m (dPort c) (hne 240 (by simp)) (hne 149 (by simp)) (hne 218 (by simp)) (hne 209 (by simp))
      (hne 242 (by simp)), digit_master a r four L target]
  have hbw : ∀ c, bnd a r c < 2^T := by
    intro c
    unfold bnd bndN
    split
    · dsimp only
      have := ThrWidth.children_length_le a r four L target _ (List.get_mem r.circuits ⟨c.val, by omega⟩)
      exact lt_of_le_of_lt this Nat.lt_two_pow_self
    · exact lt_of_lt_of_le (by omega : 1 < T) (le_of_lt Nat.lt_two_pow_self)
  have s1 := casc_step NI ix T (RT a r four L target) (bnd a r) (fun c => KeySucc.dig a r L target kj (c4 c)) A0
    hcells (by omega) hd (fun c => by rw [hA0i, hinitD]) (fun c => dig_lt_bnd a r four L target kj c) hbw
  rw [← hdig'] at s1
  set A1 := digBank NI A0 T (fun c => KeySucc.dig a r L target k' (c4 c)) with hA1
  -- (2) the base stage
  have hUf : 4*wT a r four L target+3 ≤ Uf r.q T := by
    have hb := (fns_thr a r four L target kj.selection _ rfl kj.prime kj.residue).2.1
    have hcap := hb.capacity
    rw [← hT] at hcap
    have hsq : 12*T+19+1 ≤ (12*T+19+1)^2 := Nat.le_self_pow (by norm_num) _
    rw [hw]
    omega
  have hR4 : 4*wT a r four L target+3 ≤ RT a r four L target := by
    have h1' := thrR_le_res r.q T
    have h2' : Uf r.q T ≤ thrR r.q T := by unfold thrR thrLmax; omega
    show _ ≤ thrRes r.q T
    omega
  have offDig : ∀ p : Fin (2+rowsWork NI), (∀ k : Fin 254, p ≠ masterPort NI k) → A1 p = A0 p := fun p hp =>
    digBank_off NI A0 T _ p (fun k _ => hp k)
  have s2 := base_step a r four L target NI ib iOne hib hone k'.selection (Uf r.q T) (RT a r four L target)
    (PCJ45bee56da9f34d5a_StreamPair.radix a r four kj.selection) A1
    (fun c => by rw [hA1, digBank_at, data_digits a r four L target k' c])
    (fun k hk => by rw [offDig _ (fun z => initPort_ne_master NI _ z), hA0i, hinitB k hk])
    (by rw [offDig _ (fun z => initPort_ne_master NI _ z), hA0i, hinitO])
    (by
      rw [hA1, digBank_off NI A0 T _ _ (fun z hz => by
        intro e
        have := (masterPort_inj NI _ _).mp e
        rcases hz with rfl | rfl | rfl | rfl <;> exact absurd this (by decide)),
        hA0m 220 (by decide) (by decide) (by decide) (by decide) (by decide), master_220])
    (by rw [offDig _ (fun z => cell_ne_master NI 0 z), hcells.c0])
    (by rw [offDig _ (fun z => cell_ne_master NI 1 z), hcells.c1])
    hUf hR4
  -- (3) the target bank
  have hp : k'.prime.val = 2 := by
    rw [← KeySucc.primeAt_dig a r four L target k', hp4]
    exact NearCubicWires.PacketsGlue.RequestMeta.primeAt_zero _ (cut_ge a r target)
  have hr : k'.residue.val = 0 := (KeySucc.dig_res a r four L target k').symm.trans hp6
  have hs : thrSeedIdx a r L target k' = 0 := (KeySucc.dig_seed a r four L target k').symm.trans hp5
  rw [base_succSel a r four L target NI pub init rcp C cC hF j hj k' hk' hp hr hs]
  exact s1.seq s2

end Sel

end
end RowsConstruction.ThrSelBase

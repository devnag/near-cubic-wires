import Proof.SourceAssembly.SourceRequestTermReaderRun

set_option autoImplicit false
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unnecessarySeqFocus false

namespace NearCubicWires.SourceFactorSel.CountRead
open NearCubicWires LocalBitMultitape ExtDecompositionBatch RepairOrdinary RepairOrdinary.RecoveryRootRound
open RadixSemantics CanonicalBinary CanonicalWitnessCodec
open NearCubicWires.SourceRequest.TermSeg NearCubicWires.SourceRequest.TermReader NearCubicWires.SourceRequest.TermBridge

/-- **`J` as the machines see it**: on an admitted witness, the `j`-th sum code exists and its term count is `|ts|`. -/
theorem count_len (bits : List Bool) (j : Nat) (ts : List (ℚ × Nat)) (h : rawTerms bits j = some ts) :
    ∃ hj : j < (sums bits).length,
      (SourceRequest.TermSegB.terms (SignedSortKey.binary bits.length (sums bits)[j])).length = ts.length := by
  unfold rawTerms at h
  cases hF : decodeBalancedList (value (CloseoutWitness.BoundedFields.family bits)) with
  | none => rw [hF] at h; simp at h
  | some cs =>
    rw [hF] at h
    simp only [Option.bind_some] at h
    cases hc : cs[j]? with
    | none => rw [hc] at h; simp at h
    | some cj =>
      rw [hc] at h
      simp only [Option.bind_some] at h
      have hsums : sums bits = cs := atoms_of_decode _ _ hF
      have hjc : j < cs.length := by
        by_contra hn; rw [List.getElem?_eq_none (by omega)] at hc; simp at hc
      have hj : j < (sums bits).length := by rw [hsums]; exact hjc
      have hcj : (sums bits)[j] = cj := by
        have := List.getElem?_eq_getElem hjc; rw [hc] at this
        simp only [hsums]; exact (Option.some.inj this).symm
      refine ⟨hj, ?_⟩
      have hr := rawSum_some cj ts h
      rcases hr with ⟨q, tc, tcs, hT, hB, hM⟩
      have hFlen := family_length bits
      have hcjlt : cj < 2 ^ bits.length := by
        have hmem : cj ∈ (PCPPNativeCanonicalTree.tree (value (CloseoutWitness.BoundedFields.family bits))).atoms := by
          rw [← hcj]; exact List.getElem_mem hj
        have := atom_lt _ _ _ (value_lt _) hmem
        rwa [hFlen] at this
      have hvc : value (SignedSortKey.binary bits.length (sums bits)[j]) = cj := by
        rw [hcj]; exact value_binary _ _ hcjlt
      obtain ⟨_, hq1⟩ := pair_fields _ q tc (by rw [hvc]; exact hT)
      have hterms : SourceRequest.TermSegB.terms (SignedSortKey.binary bits.length (sums bits)[j]) = tcs := by
        unfold SourceRequest.TermSegB.terms SourceRequest.TermSegB.termsCode
        rw [hq1]
        exact atoms_of_decode _ _ hB
      obtain ⟨hlen, _⟩ := mapM_some termOf tcs ts hM
      rw [hterms]
      exact hlen.symm

/-! ## One fixed machine, exact banks (`Fin 379`) -/

/-- Segment A on `0..190`. -/
def cA (i : Fin 191) : Fin 379 := ⟨i.val, by omega⟩
/-- Segment-B core: its input `0` on A's sum-code output `189`, its other tapes on `191..378`. -/
def cB (i : Fin 189) : Fin 379 := if i.val = 0 then ⟨189, by omega⟩ else ⟨190 + i.val, by omega⟩

theorem cB_val (i : Fin 189) : (cB i).val = if i.val = 0 then 189 else 190 + i.val := by
  unfold cB; split <;> rfl

theorem cA_inj : Function.Injective cA := by
  intro a b h
  exact Fin.ext (by have := congrArg Fin.val h; simpa [cA] using this)

theorem cB_inj : Function.Injective cB := by
  intro a b h
  have := congrArg Fin.val h
  rw [cB_val, cB_val] at this
  apply Fin.ext
  split_ifs at this <;> omega

noncomputable def countM :=
  Composition.machine (RecoveryFocus.machine cA machineA) (RecoveryFocus.machine cB SourceRequest.TermSegB.machine)

def countCost (bits : List Bool) (j : Nat) : Nat :=
  costA bits.length j + 1 + SourceRequest.TermSegB.cost bits.length

open RepairSource.VerifierDecoding in
/-- The exact entry: witness on `0`, `word j` on `188`, the two parsers' `[false]` on `1` and `191`, blank elsewhere. -/
def entryC (bits : List Bool) (j : Nat) : Fin 379 → List Bool := fun x =>
  if x.val = 0 then frame bits else if x.val = 188 then CompareMachine.word j
  else if x.val = 1 ∨ x.val = 191 then [false] else []

open RepairSource.VerifierDecoding in
theorem count_exact (bits : List Bool) (j : Nat) (ts : List (ℚ × Nat)) (h : rawTerms bits j = some ts) :
    ∃ X : Fin 379 → List Bool,
      Step countM (countCost bits j) (fun _ => 0) (entryC bits j) (fun _ => 0) X ∧
      X 0 = frame bits ∧ X 188 = CompareMachine.word j ∧ X 369 = List.replicate ts.length true := by
  obtain ⟨hj, hlen⟩ := count_len bits j ts h
  obtain ⟨XA, sA, xa0, xa188, xa189, _⟩ := segA_run bits j hj
  have hEA : ∀ k, entryC bits j (cA k) = entryA bits j k := by
    intro k
    have hk := k.isLt
    unfold entryC entryA
    simp only [cA]
    split_ifs <;> first | rfl | omega
  have dA := NearCubicWires.SourceRequest.TermSeg.dock sA cA cA_inj (fun _ => 0) _ (fun _ => rfl) hEA
  obtain ⟨XB, sB, _, _, xb28⟩ := SourceRequest.TermSegB.core_run (SignedSortKey.binary bits.length (sums bits)[j])
  have hEB : ∀ k, install cA (entryC bits j) XA (cB k) =
      SourceRequest.TermSegB.entry (SignedSortKey.binary bits.length (sums bits)[j]) k := by
    intro k
    have hk := k.isLt
    by_cases h0 : k.val = 0
    · have e : cB k = cA 189 := Fin.ext (by rw [cB_val, if_pos h0]; rfl)
      rw [e, install_slot _ cA_inj, xa189]
      unfold SourceRequest.TermSegB.entry
      rw [if_pos h0]
    · rw [install_other _ _ _ _ (by
        intro m e
        have := congrArg Fin.val e
        rw [cB_val, if_neg h0] at this
        simp only [cA] at this
        omega)]
      unfold entryC SourceRequest.TermSegB.entry
      rw [cB_val, if_neg h0, if_neg h0, if_neg (by omega), if_neg (by omega)]
      by_cases h1 : k.val = 1
      · rw [if_pos (Or.inr (by omega)), if_pos h1]
      · rw [if_neg (by omega), if_neg h1]
  have dB := NearCubicWires.SourceRequest.TermSeg.dock sB cB cB_inj (fun _ => 0) _ (fun _ => rfl) hEB
  have hcl : (SignedSortKey.binary bits.length (sums bits)[j]).length = bits.length := SignedSortKey.binary_length _ _
  rw [hcl] at dB
  refine ⟨_, dA.seq dB, ?_, ?_, ?_⟩
  · rw [install_other _ _ _ _ (by
      intro m e
      have := congrArg Fin.val e
      rw [cB_val] at this
      simp only [Fin.val_zero] at this
      split_ifs at this <;> omega)]
    show install cA _ _ (cA 0) = _
    rw [install_slot _ cA_inj, xa0]
  · rw [install_other _ _ _ _ (by
      intro m e
      have := congrArg Fin.val e
      rw [cB_val] at this
      split_ifs at this <;> simp at this <;> omega)]
    show install cA _ _ (cA 188) = _
    rw [install_slot _ cA_inj, xa188]
  · have e : (369 : Fin 379) = cB (SourceRequest.TermSegB.tS 28) := Fin.ext (by
      rw [cB_val]; simp [SourceRequest.TermSegB.tS])
    rw [e, install_slot _ cB_inj, xb28, hlen]

/-! ## Padded and docked: the `cntT` half of `ReaderRun` -/

def CountRun {U s : Nat} (M : Machine U s) (cost : List Bool → Nat → Nat) (wT jT cntT : Fin U)
    (Scr : Fin U → Prop) : Prop :=
  ∀ (bits : List Bool) (j Rw R : Nat) (ts : List (ℚ × Nat)) (H : Fin U → Nat) (A : Fin U → List Bool),
    rawTerms bits j = some ts →
    A wT = ZeroPadding.pad Rw (RepairOrdinary.frame bits) → H wT = 0 →
    A jT = ZeroPadding.pad R (RepairSource.VerifierDecoding.CompareMachine.word j) → H jT = 0 →
    (∀ x, (Scr x ∨ x = cntT) → A x = List.replicate R false ∧ H x = 0) →
    cost bits j + 1 ≤ R →
    ∃ (H' : Fin U → Nat) (A' : Fin U → List Bool),
      Step M (cost bits j) H A H' A' ∧
      A' cntT = ZeroPadding.pad R (List.replicate ts.length true) ∧ H' cntT = 0 ∧
      (∀ x, ¬ Scr x → x ≠ cntT → A' x = A x ∧ H' x = H x) ∧
      (∀ x, Scr x → (A' x).length ≤ R)

def special (k : Fin 379) : Prop := k.val = 0 ∨ k.val = 188 ∨ k.val = 369

instance (k : Fin 379) : Decidable (special k) := by unfold special; infer_instance

/-- The count reader's scratch in the host layout: every non-port slot. -/
def scr {U : Nat} (slots : Fin 379 → Fin U) (x : Fin U) : Prop := ∃ k, ¬ special k ∧ slots k = x

theorem entry_short (bits : List Bool) (j : Nat) (k : Fin 379) (hk : ¬ special k) :
    entryC bits j k = [] ∨ entryC bits j k = [false] := by
  unfold special at hk
  unfold entryC
  rw [if_neg (by omega), if_neg (by omega)]
  split_ifs
  · exact Or.inr rfl
  · exact Or.inl rfl

/-- **The count reader, docked anywhere, meets `CountRun`.** -/
theorem countRun {U : Nat} (slots : Fin 379 → Fin U) (hinj : Function.Injective slots) :
    CountRun (RecoveryFocus.machine slots countM) countCost (slots 0) (slots 188) (slots 369) (scr slots) := by
  intro bits j Rw R ts H A hraw hw hwH hj hjH hscr hcost
  obtain ⟨X, sX, x0, x188, x369⟩ := count_exact bits j ts hraw
  have hR : 1 ≤ R := by omega
  let cap : Fin 379 → Nat := fun k => if k.val = 0 then Rw else R
  have sp := sX.pad cap
  have hscrK : ∀ k, ¬ special k → A (slots k) = List.replicate R false ∧ H (slots k) = 0 :=
    fun k hk => hscr _ (Or.inl ⟨k, hk, rfl⟩)
  have hA : ∀ k, A (slots k) = ZeroPadding.pad (cap k) (entryC bits j k) := by
    intro k
    by_cases hk : special k
    · have hk' := hk
      unfold special at hk'
      rcases hk' with h | h | h
      · have e : k = 0 := Fin.ext h
        subst e; rw [hw]; rfl
      · have e : k = 188 := Fin.ext h
        subst e; rw [hj]; rfl
      · have e : k = 369 := Fin.ext h
        subst e
        rw [(hscr _ (Or.inr rfl)).1]
        exact (SourceRequest.TermReaderRun.pad_short R hR _ (Or.inl rfl)).symm
    · rw [(hscrK k hk).1]
      have hc : cap k = R := by
        simp only [cap]; unfold special at hk; rw [if_neg (by omega)]
      rw [hc]
      exact (SourceRequest.TermReaderRun.pad_short R hR _ (entry_short bits j k hk)).symm
  have hH : ∀ k, H (slots k) = 0 := by
    intro k
    by_cases hk : special k
    · unfold special at hk
      rcases hk with h | h | h
      · rw [show k = 0 from Fin.ext h]; exact hwH
      · rw [show k = 188 from Fin.ext h]; exact hjH
      · rw [show k = 369 from Fin.ext h]; exact (hscr _ (Or.inr rfl)).2
    · exact (hscrK k hk).2
  have d := NearCubicWires.SourceRequest.TermSeg.dock sp slots hinj H A hH hA
  refine ⟨H, _, d, ?_, hH 369, ?_, ?_⟩
  · rw [install_slot _ hinj, x369]; rfl
  · intro x hx h1
    refine ⟨?_, rfl⟩
    by_cases hr : ∃ k, slots k = x
    · obtain ⟨k, rfl⟩ := hr
      have hk : special k := by
        by_contra hn; exact hx ⟨k, hn, rfl⟩
      rw [install_slot _ hinj, (hA k)]
      have hne369 : k ≠ 369 := fun e => h1 (by rw [e])
      unfold special at hk
      rcases hk with h | h | h
      · rw [show k = 0 from Fin.ext h, x0]; rfl
      · rw [show k = 188 from Fin.ext h, x188]; rfl
      · exact absurd (Fin.ext h) hne369
    · simp only [not_exists] at hr
      exact install_other _ _ _ _ hr
  · intro x hx
    obtain ⟨k, hk, rfl⟩ := hx
    rw [install_slot _ hinj]
    have hc : cap k = R := by
      simp only [cap]; unfold special at hk; rw [if_neg (by omega)]
    rw [hc, ZeroPadding.pad_length]
    have hl := P1Closure.LocalSupport.step_fits sX k R
      (by rcases entry_short bits j k hk with h | h <;> rw [h] <;> simp <;> omega) (by simpa using hcost)
    exact max_le (le_refl R) hl

theorem countCost_le (bits : List Bool) (j : Nat) :
    countCost bits j ≤ 16777216 * (bits.length + j + 2) ^ 3 := by
  unfold countCost costA SourceRequest.TermSeg.cost SourceRequest.TermSegB.cost seekCost
    CloseoutRowsTouching.FrameSeek.budget
  set n := bits.length with hn
  set M := n + j + 2 with hM
  have h1 : n + 1 ≤ M := by omega
  have hj : j ≤ M := by omega
  have p2 : (n + 1) ^ 2 ≤ M ^ 3 := by
    calc (n + 1) ^ 2 ≤ M ^ 2 := Nat.pow_le_pow_left h1 2
      _ ≤ M ^ 3 := Nat.pow_le_pow_right (by omega) (by decide)
  have p3 : (n + 1) ^ 3 ≤ M ^ 3 := Nat.pow_le_pow_left h1 3
  have q : j * (2 * n + 4) ≤ 2 * M ^ 3 := by
    calc j * (2 * n + 4) ≤ M * (2 * M) := Nat.mul_le_mul hj (by omega)
      _ = 2 * M ^ 2 := by ring
      _ ≤ 2 * M ^ 3 := Nat.mul_le_mul_left 2 (Nat.pow_le_pow_right (by omega) (by decide))
  have p1 : M ≤ M ^ 3 := by
    calc M = M ^ 1 := (pow_one M).symm
      _ ≤ M ^ 3 := Nat.pow_le_pow_right (by omega) (by decide)
  omega

end NearCubicWires.SourceFactorSel.CountRead


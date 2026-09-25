import Proof.Packets.SrcMetaRegs
import Proof.Packets.SrcMetaWords

set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

namespace NearCubicWires.SourceStart.MetaAsm
open NearCubicWires LocalBitMultitape ExtDecompositionBatch RepairOrdinary RepairOrdinary.RecoveryRootRound
open RepairRepresentation NearCubicWires.SourceStart.MetaTM NearCubicWires.SourceStart.Regs
noncomputable section

/-! ## 1. A stage with its scratch block anywhere -/

/-! ## 2. The piece machines as heads-`0` local runs -/

/-- A fixed word printed on a blank tape (tape 1 its log). -/
theorem fixed_local (bits : List Bool) :
    Step (HierarchyFixedWord.machine bits) (2*bits.length+2) (fun _ => 0) (fun _ => []) (fun _ => 0)
      ![bits, List.replicate bits.length false] :=
  Step.of_ready (HierarchyFixedWord.word_ready bits)

theorem frameU_local (b : ℕ) : ∃ k, Step (MaskedReset.machine PacketsGlue.FrameUnary.machine (fun _ => true)) (2*(2*b+1)+2)
    (fun _ => 0) (Fin.addCases ![List.replicate b true, []] (fun _ : Fin 1 => [])) (fun _ => 0)
    (Fin.addCases ![List.replicate b true, RepairOrdinary.frame (List.replicate b true)] (fun _ : Fin 1 => List.replicate k false)) := by
  obtain ⟨H, h⟩ := PacketsGlue.FrameUnary.run b
  exact Stages.mask0 (h.congr_in Stages.vec2_zero rfl)

theorem zeros_local (b : ℕ) : ∃ k, Step (MaskedReset.machine zerosM (fun _ => true)) (2*(2*b+1)+2)
    (fun _ => 0) (Fin.addCases ![List.replicate b true, []] (fun _ : Fin 1 => [])) (fun _ => 0)
    (Fin.addCases ![List.replicate b true, RepairOrdinary.frame (List.replicate b false)] (fun _ : Fin 1 => List.replicate k false)) := by
  obtain ⟨H, h⟩ := zeros_run b
  exact Stages.mask0 (h.congr_in Stages.vec2_zero rfl)

theorem count_local (n : ℕ) : ∃ out : Fin 10 → List Bool,
    Step CloseoutRowsCountBinary.machine (CloseoutRowsCountBinary.budget n) (fun _ => 0) (CloseoutRowsCountBinary.input n)
      (fun _ => 0) out ∧ out 5 = RepairOrdinary.frame (CloseoutRowsCountBinary.bits n) := by
  obtain ⟨out, h, _, _, h5⟩ := CloseoutRowsCountBinary.count_run n
  exact ⟨out, CloseoutFinalSelector.step_of_clock h, h5⟩

theorem nat_local (q n : ℕ) (hn : n ≤ q) : ∃ out : Fin 22 → List Bool,
    Step CloseoutRowsEstimatorParity.Natural.machine (CloseoutRowsEstimatorParity.Natural.budget n) (fun _ => 0)
      (CloseoutRowsEstimatorParity.Natural.input q n) (fun _ => 0) out ∧
      out 20 = ZeroPadding.pad (CloseoutRowsEstimatorParity.Capacity.value q) (RepairOrdinary.frame (natWord n)) := by
  obtain ⟨out, h, h20, _, _⟩ := CloseoutRowsEstimatorParity.Natural.native_run q n hn
  exact ⟨out, CloseoutFinalSelector.step_of_clock h, h20⟩

/-! ## 3. Body appends from a list of framed sources -/

/-- One append: `bodyM false` docked on `(src, out)`. -/
def appendM {N : ℕ} (src out : Fin N) : Machine N 3 := RecoveryFocus.machine ![src, out] (bodyM false)

/-- The appends of a list of sources, in order (then a halting machine). -/
def asmM {N : ℕ} (out : Fin N) : List (Fin N) → (st : ℕ) × Machine N st
  | [] => ⟨1, CloseoutRowsOriginalSwitch.stop N⟩
  | j :: js => ⟨3 + (asmM out js).1, Composition.machine (appendM j out) (asmM out js).2⟩

/-- Its cost. -/
def asmCost {N : ℕ} (w : Fin N → List Bool) : List (Fin N) → ℕ
  | [] => 0
  | j :: js => (2*(w j).length+1) + 1 + asmCost w js

theorem asm_run {N : ℕ} (out : Fin N) (w : Fin N → List Bool) :
    ∀ (js : List (Fin N)) (acc : List Bool) (H : Fin N → ℕ) (A : Fin N → List Bool),
      js.Nodup → out ∉ js → H out = acc.length → A out = acc → (∀ j ∈ js, H j = 0 ∧ A j = RepairOrdinary.frame (w j)) →
      ∃ (H' : Fin N → ℕ) (A' : Fin N → List Bool), Step (asmM out js).2 (asmCost w js) H A H' A' ∧
        A' out = acc ++ js.flatMap (fun j => body false (w j)) ∧ H' out = (acc ++ js.flatMap (fun j => body false (w j))).length ∧
        (∀ x, x ∉ js → x ≠ out → A' x = A x ∧ H' x = H x) := by
  intro js
  induction js with
  | nil =>
    intro acc H A _ _ hH hA _
    refine ⟨H, A, Rounds.stop_step H A, by rw [hA]; simp, by rw [hH]; simp, fun _ _ _ => ⟨rfl, rfl⟩⟩
  | cons j js ih =>
    intro acc H A hnd hout hH hA hs
    have hjo : j ≠ out := fun e => hout (e ▸ List.mem_cons_self)
    have hj := hs j List.mem_cons_self
    have hinj : Function.Injective (![j, out] : Fin 2 → Fin N) := by
      intro a b hab
      fin_cases a <;> fin_cases b
      · rfl
      · exact absurd hab hjo
      · exact absurd hab.symm hjo
      · rfl
    have loc := body_run false [] (w j) [] acc
    simp only [List.nil_append, List.append_nil, List.length_nil, Nat.zero_add] at loc
    have d := loc.dock (![j, out] : Fin 2 → Fin N) hinj H A
      (by intro i; fin_cases i; exacts [hj.1, hH]) (by intro i; fin_cases i; exacts [hj.2, hA])
    set H1 := dockH (![j, out] : Fin 2 → Fin N) H ![2*(w j).length, (acc ++ body false (w j)).length]
    set A1 := install (![j, out] : Fin 2 → Fin N) A ![RepairOrdinary.frame (w j), acc ++ body false (w j)]
    have o1 : A1 out = acc ++ body false (w j) := install_slot (![j, out] : Fin 2 → Fin N) hinj A _ 1
    have ho1 : H1 out = (acc ++ body false (w j)).length := dockH_slot (![j, out] : Fin 2 → Fin N) hinj H _ 1
    have fr : ∀ x, x ≠ j → x ≠ out → A1 x = A x ∧ H1 x = H x := by
      intro x h1 h2
      have hn : ∀ i, (![j, out] : Fin 2 → Fin N) i ≠ x := by
        intro i hi; fin_cases i
        · exact h1 hi.symm
        · exact h2 hi.symm
      exact ⟨install_other _ _ _ _ hn, dockH_other _ _ _ _ hn⟩
    have hnd' := (List.nodup_cons.mp hnd)
    obtain ⟨H2, A2, s2, o2, ho2, f2⟩ := ih (acc ++ body false (w j)) H1 A1 hnd'.2
      (fun h => hout (List.mem_cons_of_mem j h)) ho1 o1 (by
        intro k hk
        have hkj : k ≠ j := fun e => hnd'.1 (e ▸ hk)
        have hko : k ≠ out := fun e => hout (List.mem_cons_of_mem j (e ▸ hk))
        rw [(fr k hkj hko).1, (fr k hkj hko).2]
        exact hs k (List.mem_cons_of_mem j hk))
    refine ⟨H2, A2, d.seq s2, ?_, ?_, ?_⟩
    · rw [o2]; simp [List.append_assoc]
    · rw [ho2]; simp [List.append_assoc]
    · intro x hx hxo
      have hxj : x ≠ j := fun e => hx (e ▸ List.mem_cons_self)
      have hxs : x ∉ js := fun h => hx (List.mem_cons_of_mem j h)
      rw [(f2 x hxs hxo).1, (f2 x hxs hxo).2]
      exact fr x hxj hxo

/-! ## 4. The two phases -/

/-- The Field copier appending `frame [] = [false]` from `term` onto `out`. -/
def termM {N : ℕ} (term out : Fin N) : Machine N 3 :=
  RecoveryFocus.machine ![term, out] RepairSource.ProjectionNormalization.Field.machine

theorem term_step {N : ℕ} (term out : Fin N) (hto : term ≠ out) (acc : List Bool) (H : Fin N → ℕ) (A : Fin N → List Bool)
    (hH : H term = 0) (hO : H out = acc.length) (hT : A term = [false]) (hA : A out = acc) :
    ∃ (H' : Fin N → ℕ) (A' : Fin N → List Bool), Step (termM term out) (2*0+1) H A H' A' ∧
      A' out = acc ++ [false] ∧ (∀ x, x ≠ out → A' x = A x) := by
  obtain ⟨r, hr, hf, hs⟩ := RepairSource.ProjectionNormalization.Field.copy_run [] [] [] acc
  have hinj : Function.Injective (![term, out] : Fin 2 → Fin N) := by
    intro a b hab
    fin_cases a <;> fin_cases b
    · rfl
    · exact absurd hab hto
    · exact absurd hab.symm hto
    · rfl
  have loc : Step RepairSource.ProjectionNormalization.Field.machine (2*0+1) ![0, acc.length] ![[false], acc]
      ![1, (acc ++ [false]).length] ![[false], acc ++ [false]] := by
    refine ⟨r, ?_, ?_, ?_, ?_⟩
    · have e : RepairSource.ProjectionNormalization.Field.machine.start = 0 := rfl
      rw [e]
      simpa [RepairSource.ProjectionNormalization.Field.cfg, RepairOrdinary.frame] using hr
    · rw [hf]; simp [RepairSource.ProjectionNormalization.Field.cfg, RepairOrdinary.frame]
    · rw [hf]; simp [RepairSource.ProjectionNormalization.Field.cfg, RepairOrdinary.frame]
    · simp at hs; omega
  have d := loc.dock (![term, out] : Fin 2 → Fin N) hinj H A (by intro i; fin_cases i; exacts [hH, hO])
    (by intro i; fin_cases i; exacts [hT, hA])
  refine ⟨_, _, d, install_slot (![term, out] : Fin 2 → Fin N) hinj A _ 1, ?_⟩
  intro x hx
  by_cases ht : x = term
  · subst ht
    exact (install_slot (![x, out] : Fin 2 → Fin N) hinj A _ 0).trans hT.symm
  · apply install_other
    intro i hi; fin_cases i
    · exact ht hi.symm
    · exact hx hi.symm

/-- Phase A's inner machine on `Fin (m + 2)`: sources `0..m-1`, output `m`, terminator `m+1`. -/
def innerA (m : ℕ) : (st : ℕ) × Machine (m + 2) st :=
  ⟨_, Composition.machine (asmM (⟨m, by omega⟩ : Fin (m+2)) ((List.finRange m).map (Fin.castAdd 2))).2
    (termM (⟨m+1, by omega⟩ : Fin (m+2)) ⟨m, by omega⟩)⟩

/-- Phase A's entry: the framed pieces, an empty output, the terminator `frame [] = [false]`. -/
def tinA (m : ℕ) (w : Fin m → List Bool) (i : Fin (m + 2)) : List Bool :=
  if h : i.val < m then RepairOrdinary.frame (w ⟨i.val, h⟩) else if i.val = m then [] else [false]

/-- Phase A's cost. -/
def costA (m : ℕ) (w : Fin m → List Bool) : ℕ :=
  2*(asmCost (fun i : Fin (m+2) => if h : i.val < m then w ⟨i.val, h⟩ else []) ((List.finRange m).map (Fin.castAdd 2)) + 1 +
    (2*0+1)) + 2

theorem finRange_map_nodup (m : ℕ) : ((List.finRange m).map (Fin.castAdd 2)).Nodup :=
  (List.nodup_finRange m).map (Fin.castAdd_injective m 2)

/-- **Phase A**: from the framed pieces, `frame (w 0 ++ … ++ w (m-1))`'s body and the terminator on the output; heads `0` (masked). -/
theorem phaseA_run (m : ℕ) (w : Fin m → List Bool) : ∃ tout : Fin (m + 2 + 1) → List Bool,
    Step (MaskedReset.machine (innerA m).2 (fun _ => true)) (costA m w) (fun _ => 0)
      (Fin.addCases (tinA m w) (fun _ : Fin 1 => [])) (fun _ => 0) tout ∧
      tout (Fin.castAdd 1 ⟨m, by omega⟩) = (List.finRange m).flatMap (fun i => body false (w i)) ++ [false] := by
  set W : Fin (m+2) → List Bool := fun i => if h : i.val < m then w ⟨i.val, h⟩ else [] with hW
  have hout : (⟨m, by omega⟩ : Fin (m+2)) ∉ (List.finRange m).map (Fin.castAdd 2) := by
    intro h
    obtain ⟨i, _, hi⟩ := List.mem_map.mp h
    have := congrArg Fin.val hi
    simp at this
    omega
  obtain ⟨H1, A1, s1, o1, ho1, f1⟩ := asm_run (⟨m, by omega⟩ : Fin (m+2)) W ((List.finRange m).map (Fin.castAdd 2)) []
    (fun _ => 0) (tinA m w) (finRange_map_nodup m) hout rfl (by simp [tinA]) (by
      intro j hj
      obtain ⟨i, _, rfl⟩ := List.mem_map.mp hj
      refine ⟨rfl, ?_⟩
      simp [tinA, hW, i.isLt])
  have hflat : ((List.finRange m).map (Fin.castAdd 2)).flatMap (fun j => body false (W j)) =
      (List.finRange m).flatMap (fun i => body false (w i)) := by
    rw [List.flatMap_map]
    congr 1
    funext i
    simp [hW, i.isLt]
  have hT : A1 (⟨m+1, by omega⟩ : Fin (m+2)) = [false] := by
    rw [(f1 _ (by
      intro h
      obtain ⟨i, _, hi⟩ := List.mem_map.mp h
      have := congrArg Fin.val hi
      simp at this
      omega) (by intro h; have := congrArg Fin.val h; simp at this)).1]
    simp [tinA]
  have hTH : H1 (⟨m+1, by omega⟩ : Fin (m+2)) = 0 := by
    rw [(f1 _ (by
      intro h
      obtain ⟨i, _, hi⟩ := List.mem_map.mp h
      have := congrArg Fin.val hi
      simp at this
      omega) (by intro h; have := congrArg Fin.val h; simp at this)).2]
  rw [List.nil_append] at o1 ho1
  obtain ⟨H2, A2, s2, o2, _⟩ := term_step (⟨m+1, by omega⟩ : Fin (m+2)) ⟨m, by omega⟩
    (by intro h; have := congrArg Fin.val h; simp at this) _ H1 A1 hTH ho1 hT o1
  obtain ⟨k, hm⟩ := Stages.mask0 (s1.seq s2)
  refine ⟨_, hm.enlarge (le_of_eq ?_), ?_⟩
  · unfold costA; rfl
  · rw [addCases_lt_mask, o2, hflat]
where
  addCases_lt_mask {α : Type} {n : ℕ} (f : Fin n → α) (g : Fin 1 → α) (j : Fin n) :
      Fin.addCases f g (Fin.castAdd 1 j) = f j := Fin.addCases_left j

/-- Phase B's inner machine on `Fin 3`: `0` the source `frame v`, `1` the terminator, `2` the output. -/
def innerB : (st : ℕ) × Machine 3 st :=
  ⟨_, Composition.machine (RecoveryFocus.machine (![0, 2] : Fin 2 → Fin 3) (bodyM true)) (termM (1 : Fin 3) 2)⟩

/-- **Phase B**: `frame v ↦ frame (1^|v|)` on the output, heads `0` (masked). -/
theorem phaseB_run (v : List Bool) : ∃ tout : Fin (3 + 1) → List Bool,
    Step (MaskedReset.machine innerB.2 (fun _ => true)) (2*((2*v.length+1) + 1 + (2*0+1)) + 2) (fun _ => 0)
      (Fin.addCases ![RepairOrdinary.frame v, [false], []] (fun _ : Fin 1 => [])) (fun _ => 0) tout ∧
      tout (Fin.castAdd 1 2) = RepairOrdinary.frame (List.replicate v.length true) ∧
      tout (Fin.castAdd 1 0) = RepairOrdinary.frame v := by
  have loc := body_run true [] v [] []
  simp only [List.nil_append, List.append_nil, List.length_nil, Nat.zero_add] at loc
  have hinj : Function.Injective (![0, 2] : Fin 2 → Fin 3) := by decide
  have d := loc.dock (![0, 2] : Fin 2 → Fin 3) hinj (fun _ => 0) ![RepairOrdinary.frame v, [false], []]
    (by intro i; fin_cases i <;> rfl) (by intro i; fin_cases i <;> rfl)
  set H1 := dockH (![0, 2] : Fin 2 → Fin 3) (fun _ => 0) ![2*v.length, (body true v).length]
  set A1 := install (![0, 2] : Fin 2 → Fin 3) ![RepairOrdinary.frame v, [false], []] ![RepairOrdinary.frame v, body true v]
  have o1 : A1 2 = body true v := install_slot (![0, 2] : Fin 2 → Fin 3) hinj _ _ 1
  have ho1 : H1 2 = (body true v).length := dockH_slot (![0, 2] : Fin 2 → Fin 3) hinj _ _ 1
  have hT : A1 1 = [false] := install_other _ _ _ _ (by decide)
  have hTH : H1 1 = 0 := dockH_other _ _ _ _ (by decide)
  have o0 : A1 0 = RepairOrdinary.frame v := install_slot (![0, 2] : Fin 2 → Fin 3) hinj _ _ 0
  obtain ⟨H2, A2, s2, o2, f2⟩ := term_step (1 : Fin 3) 2 (by decide) _ H1 A1 hTH ho1 hT o1
  obtain ⟨k, hm⟩ := Stages.mask0 (d.seq s2)
  refine ⟨_, hm, ?_, ?_⟩
  · rw [Fin.addCases_left, o2, body_true]
  · rw [Fin.addCases_left, f2 0 (by decide), o0]

end
end NearCubicWires.SourceStart.MetaAsm


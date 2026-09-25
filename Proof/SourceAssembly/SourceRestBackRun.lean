import Proof.SourceAssembly.SourceRestBack

section
set_option autoImplicit false
set_option maxRecDepth 120000
set_option warningAsError true

open NearCubicWires LocalBitMultitape ExtDecompositionBatch RepairOrdinary RepairRepresentation
open RepairOrdinary.RecoveryRootRound RepairSource.VerifierDecoding SourceInterfaces
open PCJ9eff70d512234a4c_Fixed PCJd4d1d9d7d1fa4313_Production PCJc4297ab269d8423a_Source
namespace NearCubicWires.SourceConstruction.Rest
noncomputable section

/-- Close a value (in)equality: `simp`, then `omega` if anything is left. -/
macro "vsimp" : tactic => `(tactic| (first | (simp; done) | (simp; omega) | omega))

/-- Values are distinct tapes. -/
theorem ne_val {V : Nat} {x y : Fin V} (h : x.val ≠ y.val) : x ≠ y := fun e => h (congrArg Fin.val e)

/-- The slope's cost. -/
def slopeCost (L Mb Ms : Nat) : Nat :=
  (1+1+1+1+1) + 1 + (((1+1+1+1+1) + 1 + (2 * (if 3 < L then Mb else Ms) + 6)) + 2)

/-- The first three stages' cost. -/
def stagesCost {a : DecompositionAlgorithm} {vE vP : Request → Nat}
    (se : PacketsGlue.RequestMeta.UnaryStage a vE) (sp : PacketsGlue.RequestMeta.UnaryStage a vP)
    (r : Request) : Nat :=
  (4 * (r.input a).length + 4) + 1 + (se.cost r + 1 + sp.cost r)

/-- The back half's cost. -/
def backCost {a : DecompositionAlgorithm} {vE vP : Request → Nat}
    (se : PacketsGlue.RequestMeta.UnaryStage a vE) (sp : PacketsGlue.RequestMeta.UnaryStage a vP)
    (r : Request) (Rc w q L Mb Ms : Nat) : Nat :=
  stagesCost se sp r + 1 + (Prologue.f6FullCost Rc (vE r) (vP r) w q + 1 + slopeCost L Mb Ms)

section
variable {a : DecompositionAlgorithm} {vE vP : Request → Nat}
  (se : PacketsGlue.RequestMeta.UnaryStage a vE) (sp : PacketsGlue.RequestMeta.UnaryStage a vP)
  {d : SourceConstruction.Dims} {gW : Nat} (e : d.RestExt se.extra sp.extra gW) {V : Nat} (hV : d.U ≤ V)

/-- **Frame the input, then the two metadata stages.** -/
theorem stages_run (r : Request) (Rc cS1 cD1 : Nat) (H : Fin V → Nat) (A : Fin V → List Bool)
    (hs1 : A (d.scr hV 5) = ZeroPadding.pad cS1 (r.input a))
    (hd1 : A (d.scr hV 6) = ZeroPadding.pad cD1 (List.replicate (r.input a).length true))
    (hHs1 : H (d.scr hV 5) = 0) (hHd1 : H (d.scr hV 6) = 0)
    (hlog : 2 * (r.input a).length + 1 ≤ Rc)
    (hblank : ∀ i : Fin (restPc se.extra sp.extra gW),
      (i.val < 61 ∨ (66 ≤ i.val ∧ i.val < 70) ∨ (71 ≤ i.val ∧ i.val < 71 + se.extra + sp.extra)) →
      A (d.pcT e hV i) = List.replicate Rc false)
    (hblankH : ∀ i : Fin (restPc se.extra sp.extra gW), i.val < 71 + se.extra + sp.extra →
      H (d.pcT e hV i) = 0) :
    ∃ (H3 : Fin V → Nat) (A3 : Fin V → List Bool),
      Step (stagesMachine se sp e hV) (stagesCost se sp r) H A H3 A3 ∧
      A3 (d.pcT e hV ⟨59, by unfold restPc; omega⟩) = ZeroPadding.pad Rc (List.replicate (vE r) true) ∧
      A3 (d.pcT e hV ⟨60, by unfold restPc; omega⟩) = ZeroPadding.pad Rc (List.replicate (vP r) true) ∧
      (∀ x : Fin V, x.val ≠ d.B + 19 + 66 → x.val ≠ d.B + 19 + 59 → x.val ≠ d.B + 19 + 60 →
        ¬ (d.B + 19 + 71 ≤ x.val ∧ x.val < d.B + 19 + 71 + se.extra + sp.extra) → A3 x = A x) ∧
      (∀ x : Fin V, ¬ (d.B + 19 + 71 ≤ x.val ∧ x.val < d.B + 19 + 71 + se.extra + sp.extra) → H3 x = H x) := by
  classical
  have hres := e.hres
  set tIn := d.pcT e hV ⟨66, by unfold restPc; omega⟩ with htIn
  set tLog := d.pcT e hV ⟨67, by unfold restPc; omega⟩ with htLog
  have vpc : ∀ i : Fin (restPc se.extra sp.extra gW), (d.pcT e hV i).val = d.B + 19 + i.val := fun _ => rfl
  have vscr : ∀ m : Fin 13, (d.scr hV m).val = d.G + d.R1 + 397 + d.w + d.tc + m.val := fun _ => rfl
  have vB : d.B = d.G + d.R1 + 410 + d.w + d.tc := rfl
  -- 1. frame
  have sF := SLoad.MaskFrame.mask_frame_step (d.scr hV 5) (d.scr hV 6) tIn tLog
    (ne_val (by rw [vscr, vscr]; simp)) (ne_val (by rw [vscr, htIn, vpc]; simp; omega))
    (ne_val (by rw [vscr, htLog, vpc]; simp; omega)) (ne_val (by rw [vscr, htIn, vpc]; simp; omega))
    (ne_val (by rw [vscr, htLog, vpc]; simp; omega)) (ne_val (by rw [htIn, htLog, vpc, vpc]; simp))
    cS1 cD1 Rc Rc (r.input a) hlog H A hHs1 hHd1 (hblankH _ (by simp; omega)) (hblankH _ (by simp; omega))
    hs1 hd1 (hblank _ (Or.inr (Or.inl (by simp)))) (hblank _ (Or.inr (Or.inl (by simp))))
  set A1 := Function.update A tIn (ZeroPadding.pad Rc (RepairOrdinary.frame (r.input a))) with hA1
  have A1o : ∀ x, x ≠ tIn → A1 x = A x := fun x hx => Function.update_of_ne hx _ _
  -- 2. `seedCount`
  obtain ⟨H2, A2, sE, eE0, eEH0, eE1, eEH1, eEf⟩ := stage_run se r (Dims.slE e hV) (Dims.slE_injective e hV) Rc Rc
    H A1 (by
      intro j
      by_cases h0 : j.val = 0
      · rw [show j = ⟨0, by omega⟩ from Fin.ext h0, Dims.slE_zero]; exact hblankH _ (by simp; omega)
      by_cases h1 : j.val = 1
      · rw [show j = ⟨1, by omega⟩ from Fin.ext h1, Dims.slE_one]; exact hblankH _ (by simp; omega)
      · rw [Dims.slE_priv e hV j h0 h1]; exact hblankH _ (by have := j.isLt; simp; omega))
    (by rw [Dims.slE_zero, ← htIn, hA1, Function.update_self])
    (by
      intro j hj0
      by_cases h1 : j.val = 1
      · rw [show j = ⟨1, by omega⟩ from Fin.ext h1, Dims.slE_one,
          A1o _ (ne_val (by rw [htIn, vpc, vpc]; simp))]
        exact hblank _ (Or.inl (by simp))
      · rw [Dims.slE_priv e hV j hj0 h1, A1o _ (ne_val (by rw [htIn, vpc, vpc]; simp; omega))]
        exact hblank _ (Or.inr (Or.inr (by have := j.isLt; simp; omega))))
  -- 3. `primeCount`
  have A2in : A2 tIn = ZeroPadding.pad Rc (RepairOrdinary.frame (r.input a)) := by
    rw [htIn, ← Dims.slE_zero e hV, eE0, Dims.slE_zero, ← htIn, hA1, Function.update_self]
  obtain ⟨H3, A3, sP, eP0, ePH0, eP1, ePH1, ePf⟩ := stage_run sp r (Dims.slP e hV) (Dims.slP_injective e hV) Rc Rc
    H2 A2 (by
      intro j
      by_cases h0 : j.val = 0
      · rw [show j = ⟨0, by omega⟩ from Fin.ext h0, Dims.slP_zero, ← Dims.slE_zero e hV]; exact eEH0
      by_cases h1 : j.val = 1
      · rw [show j = ⟨1, by omega⟩ from Fin.ext h1, Dims.slP_one,
          (eEf _ (Dims.slE_off e hV _ (by rw [vpc]; vsimp) (by rw [vpc]; vsimp) (by rw [vpc]; vsimp))).2]
        exact hblankH _ (by simp; omega)
      · rw [Dims.slP_priv e hV j h0 h1,
          (eEf _ (Dims.slE_off e hV _ (by rw [vpc]; vsimp) (by rw [vpc]; vsimp) (by rw [vpc]; simp; omega))).2]
        exact hblankH _ (by have := j.isLt; simp; omega))
    (by rw [Dims.slP_zero, ← htIn]; exact A2in)
    (by
      intro j hj0
      by_cases h1 : j.val = 1
      · rw [show j = ⟨1, by omega⟩ from Fin.ext h1, Dims.slP_one,
          (eEf _ (Dims.slE_off e hV _ (by rw [vpc]; vsimp) (by rw [vpc]; vsimp) (by rw [vpc]; vsimp))).1,
          A1o _ (ne_val (by rw [htIn, vpc, vpc]; simp))]
        exact hblank _ (Or.inl (by simp))
      · rw [Dims.slP_priv e hV j hj0 h1,
          (eEf _ (Dims.slE_off e hV _ (by rw [vpc]; vsimp) (by rw [vpc]; vsimp) (by rw [vpc]; simp; omega))).1,
          A1o _ (ne_val (by rw [htIn, vpc, vpc]; simp; omega))]
        exact hblank _ (Or.inr (Or.inr (by have := j.isLt; simp; omega))))
  refine ⟨H3, A3, sF.seq (sE.seq sP), ?_, ?_, ?_, ?_⟩
  · rw [(ePf _ (Dims.slP_off e hV _ (by rw [vpc]; vsimp) (by rw [vpc]; vsimp) (by rw [vpc]; vsimp))).1,
      ← Dims.slE_one e hV, eE1]
  · rw [← Dims.slP_one e hV, eP1]
  · intro x h66 h59 h60 hpr
    rw [(ePf x (Dims.slP_off e hV x h66 h60 (by omega))).1,
      (eEf x (Dims.slE_off e hV x h66 h59 (by omega))).1, A1o x (ne_val (by rw [htIn, vpc]; simpa using h66))]
  · intro x hpr
    by_cases h66 : x.val = d.B + 19 + 66
    · have hx : x = Dims.slP e hV ⟨0, by omega⟩ := Fin.ext (by rw [Dims.slP_zero, vpc, h66])
      rw [hx, ePH0, Dims.slP_zero]; exact (hblankH _ (by simp; omega)).symm
    by_cases h60 : x.val = d.B + 19 + 60
    · have hx : x = Dims.slP e hV ⟨1, by omega⟩ := Fin.ext (by rw [Dims.slP_one, vpc, h60])
      rw [hx, ePH1, Dims.slP_one]; exact (hblankH _ (by simp; omega)).symm
    rw [(ePf x (Dims.slP_off e hV x h66 h60 (by omega))).2]
    by_cases h59 : x.val = d.B + 19 + 59
    · have hx : x = Dims.slE e hV ⟨1, by omega⟩ := Fin.ext (by rw [Dims.slE_one, vpc, h59])
      rw [hx, eEH1, Dims.slE_one]; exact (hblankH _ (by simp; omega)).symm
    exact (eEf x (Dims.slE_off e hV x h66 h59 (by omega))).2

theorem f6_step (Rc ee pp w q cW cQ : Nat) (H : Fin V → Nat) (A : Fin V → List Bool)
    (hblank0 : ∀ i : Fin (restPc se.extra sp.extra gW), i.val < 59 → A (d.pcT e hV i) = List.replicate Rc false)
    (h59 : A (d.pcT e hV ⟨59, by unfold restPc; omega⟩) = ZeroPadding.pad Rc (List.replicate ee true))
    (h60 : A (d.pcT e hV ⟨60, by unfold restPc; omega⟩) = ZeroPadding.pad Rc (List.replicate pp true))
    (hblankH : ∀ i : Fin (restPc se.extra sp.extra gW), i.val < 64 → H (d.pcT e hV i) = 0)
    (hcoef : ∀ k : Fin 3, (A (d.pcT e hV ⟨61 + k.val, by unfold restPc; omega⟩)).length = Rc)
    (henc : ∀ k : Fin 13, (k.val < 3 ∨ k.val = 4) → (A (d.encT hV k)).length ≤ Rc)
    (hencH : ∀ k : Fin 13, (k.val < 3 ∨ k.val = 4) → H (d.encT hV k) = 0)
    (hW : A (d.rsT e hV 3) = ZeroPadding.pad cW (List.replicate w true)) (hWH : H (d.rsT e hV 3) = 0)
    (hQ : A (d.rsT e hV 4) = ZeroPadding.pad cQ (List.replicate q true)) (hQH : H (d.rsT e hV 4) = 0)
    (hdrv : A (d.scr hV 11) = List.replicate Rc true) (hdrvH : H (d.scr hV 11) = 0)
    (hlg : A (d.scr hV 12) = List.replicate (Rc+2) false) (hlgH : H (d.scr hV 12) = 0)
    (he1 : 1 ≤ ee) (hpw : (CloseoutRowsCountBinary.bits pp).length ≤ w)
    (hfirst : pp * 2^(natBitLength ee) < 2^w) (hsecond : pp * ee * 2^(q+1) < 2^w) :
    ∃ A4 : Fin V → List Bool,
      Step (Prologue.f6Full (Dims.g e hV)) (Prologue.f6FullCost Rc ee pp w q) H A H A4 ∧
      A4 (d.encT hV 4) = ZeroPadding.pad Rc (RepairOrdinary.frame (SignedSortKey.binary w (pp * ee * 2^q))) ∧
      (∀ k : Fin 3, A4 (d.encT hV ⟨k.val, by omega⟩) = A (d.pcT e hV ⟨61 + k.val, by unfold restPc; omega⟩)) ∧
      (∀ x : Fin V, ¬ (d.B + 19 ≤ x.val ∧ x.val < d.B + 19 + 64) →
        ¬ (d.F + d.rt ≤ x.val ∧ x.val ≤ d.F + d.rt + 4 ∧ x.val ≠ d.F + d.rt + 3) → A4 x = A x) := by
  classical
  have hres := e.hres
  have hH : ∀ i, H (Dims.g e hV i) = 0 := by
    intro i
    have hi := i.isLt
    by_cases hlt : i.val < 61
    · rw [Dims.g_lt61 e hV i hlt]; exact hblankH _ (by simp; omega)
    by_cases h61 : i.val = 61
    · rw [show i = 61 from Fin.ext h61, Dims.g_61]; exact hWH
    by_cases h62 : i.val = 62
    · rw [show i = 62 from Fin.ext h62, Dims.g_62]; exact hQH
    by_cases h63 : i.val = 63
    · rw [show i = 63 from Fin.ext h63, Dims.g_63]; exact hencH 4 (Or.inr rfl)
    by_cases h64 : i.val = 64
    · rw [show i = 64 from Fin.ext h64, Dims.g_64]; exact hdrvH
    by_cases h65 : i.val = 65
    · rw [show i = 65 from Fin.ext h65, Dims.g_65]; exact hlgH
    by_cases h69 : i.val < 69
    · rw [show i = ⟨66 + (i.val - 66), by omega⟩ from Fin.ext (by simp; omega), Dims.g_coef e hV ⟨i.val - 66, by omega⟩]
      exact hblankH _ (by simp; omega)
    · rw [show i = ⟨69 + (i.val - 69), by omega⟩ from Fin.ext (by simp; omega), Dims.g_enc e hV ⟨i.val - 69, by omega⟩]
      exact hencH _ (Or.inl (by simp; omega))
  obtain ⟨A4, s6, f63, f69, f70, f71, f61, f62, f64, f65, f6o⟩ := Prologue.f6_run (Dims.g e hV)
    (Dims.g_injective e hV) Rc ee pp w q cW cQ H A hH
    (by intro i hi; rw [Dims.g_lt61 e hV i (by omega)]; exact hblank0 _ (by simp; omega))
    (by rw [Dims.g_lt61 e hV 59 (by decide)]; exact h59)
    (by rw [Dims.g_lt61 e hV 60 (by decide)]; exact h60)
    (by rw [Dims.g_61]; exact hW) (by rw [Dims.g_62]; exact hQ)
    (by rw [Dims.g_63]; exact henc 4 (Or.inr rfl))
    (by rw [Dims.g_64]; exact hdrv) (by rw [Dims.g_65]; exact hlg)
    (by
      intro k hk1 hk2
      rw [show k = ⟨66 + (k.val - 66), by omega⟩ from Fin.ext (by simp; omega), Dims.g_coef e hV ⟨k.val - 66, by omega⟩]
      exact hcoef _)
    (by
      intro k hk
      rw [show k = ⟨69 + (k.val - 69), by omega⟩ from Fin.ext (by simp; omega), Dims.g_enc e hV ⟨k.val - 69, by omega⟩]
      exact henc _ (Or.inl (by simp; omega)))
    he1 hpw hfirst hsecond
  refine ⟨A4, s6, by rw [← Dims.g_63 e hV]; exact f63, ?_, ?_⟩
  · intro k
    have hk := k.isLt
    rw [← Dims.g_enc e hV k, ← Dims.g_coef e hV k]
    have hk3 : k.val = 0 ∨ k.val = 1 ∨ k.val = 2 := by omega
    rcases hk3 with h | h | h
    · rw [show (⟨69 + k.val, by omega⟩ : Fin 72) = 69 from Fin.ext (by simp [h]),
        show (⟨66 + k.val, by omega⟩ : Fin 72) = 66 from Fin.ext (by simp [h])]
      exact f69
    · rw [show (⟨69 + k.val, by omega⟩ : Fin 72) = 70 from Fin.ext (by simp [h]),
        show (⟨66 + k.val, by omega⟩ : Fin 72) = 67 from Fin.ext (by simp [h])]
      exact f70
    · rw [show (⟨69 + k.val, by omega⟩ : Fin 72) = 71 from Fin.ext (by simp [h]),
        show (⟨66 + k.val, by omega⟩ : Fin 72) = 68 from Fin.ext (by simp [h])]
      exact f71
  · intro x a1 a4
    by_cases g61 : x = d.rsT e hV 3
    · rw [g61, ← Dims.g_61 e hV]; exact f61
    by_cases g62 : x = d.rsT e hV 4
    · rw [g62, ← Dims.g_62 e hV]; exact f62
    by_cases g64 : x = d.scr hV 11
    · rw [g64, ← Dims.g_64 e hV]; exact f64
    by_cases g65 : x = d.scr hV 12
    · rw [g65, ← Dims.g_65 e hV]; exact f65
    exact f6o x (Dims.g_off e hV x a1
      (fun h => g61 (Fin.ext (by rw [h]; rfl))) (fun h => g62 (Fin.ext (by rw [h]; rfl))) a4
      (fun h => g64 (Fin.ext (by rw [h]; rfl)))
      (fun h => g65 (Fin.ext (by rw [h]; simp [SourceConstruction.Dims.scr, SourceConstruction.Dims.scrV]))))

theorem back_run (r : Request) (Rc cS1 cD1 w q cW cQ L capLen Mb Ms cB cS : Nat)
    (H : Fin V → Nat) (A : Fin V → List Bool)
    (hs1 : A (d.scr hV 5) = ZeroPadding.pad cS1 (r.input a))
    (hd1 : A (d.scr hV 6) = ZeroPadding.pad cD1 (List.replicate (r.input a).length true))
    (hHs1 : H (d.scr hV 5) = 0) (hHd1 : H (d.scr hV 6) = 0)
    (hlog : 2 * (r.input a).length + 1 ≤ Rc)
    (hblank : ∀ i : Fin (restPc se.extra sp.extra gW),
      (i.val < 61 ∨ (66 ≤ i.val ∧ i.val < 70) ∨ (71 ≤ i.val ∧ i.val < 71 + se.extra + sp.extra)) →
      A (d.pcT e hV i) = List.replicate Rc false)
    (hblankH : ∀ i : Fin (restPc se.extra sp.extra gW), i.val < 71 + se.extra + sp.extra →
      H (d.pcT e hV i) = 0)
    (hcoef : ∀ k : Fin 3, (A (d.pcT e hV ⟨61 + k.val, by unfold restPc; omega⟩)).length = Rc)
    (henc : ∀ k : Fin 13, (k.val < 3 ∨ k.val = 4) → (A (d.encT hV k)).length ≤ Rc)
    (hencH : ∀ k : Fin 13, (k.val < 3 ∨ k.val = 4) → H (d.encT hV k) = 0)
    (hW : A (d.rsT e hV 3) = ZeroPadding.pad cW (List.replicate w true)) (hWH : H (d.rsT e hV 3) = 0)
    (hQ : A (d.rsT e hV 4) = ZeroPadding.pad cQ (List.replicate q true)) (hQH : H (d.rsT e hV 4) = 0)
    (hdrv : A (d.scr hV 11) = List.replicate Rc true) (hdrvH : H (d.scr hV 11) = 0)
    (hlg : A (d.scr hV 12) = List.replicate (Rc+2) false) (hlgH : H (d.scr hV 12) = 0)
    (hbig : A (d.rsT e hV 0) = ZeroPadding.pad cB (List.replicate Mb true)) (hbigH : H (d.rsT e hV 0) = 0)
    (hsmall : A (d.rsT e hV 1) = ZeroPadding.pad cS (List.replicate Ms true)) (hsmallH : H (d.rsT e hV 1) = 0)
    (hlen : A (Dims.lenTape e.ext hV) = ZeroPadding.pad capLen (List.replicate L true))
    (hlenH : H (Dims.lenTape e.ext hV) = 0)
    (hcs1 : A (Dims.csSlots e.ext hV 1) = ZeroPadding.pad Rc []) (hcs1H : H (Dims.csSlots e.ext hV 1) = 0)
    (he1 : 1 ≤ vE r) (hpw : (CloseoutRowsCountBinary.bits (vP r)).length ≤ w)
    (hfirst : vP r * 2^(natBitLength (vE r)) < 2^w) (hsecond : vP r * vE r * 2^(q+1) < 2^w) :
    ∃ (H' : Fin V → Nat) (A' : Fin V → List Bool),
      Step (backMachine se sp e hV) (backCost se sp r Rc w q L Mb Ms) H A H' A' ∧
      A' (d.encT hV 4) = ZeroPadding.pad Rc (RepairOrdinary.frame (SignedSortKey.binary w (vP r * vE r * 2^q))) ∧
      (∀ k : Fin 3, A' (d.encT hV ⟨k.val, by omega⟩) = A (d.pcT e hV ⟨61 + k.val, by unfold restPc; omega⟩)) ∧
      A' (Dims.csSlots e.ext hV 1) = ZeroPadding.pad Rc (List.replicate (if 3 < L then Mb else Ms) true) ∧
      (∀ x : Fin V, x ≠ Dims.csSlots e.ext hV 1 →
        ¬ (d.B + 19 ≤ x.val ∧ x.val < d.B + 19 + 71 + se.extra + sp.extra) →
        ¬ (d.F + d.rt ≤ x.val ∧ x.val ≤ d.F + d.rt + 4 ∧ x.val ≠ d.F + d.rt + 3) → A' x = A x) ∧
      (∀ x : Fin V, ¬ (d.B + 19 + 71 ≤ x.val ∧ x.val < d.B + 19 + 71 + se.extra + sp.extra) → H' x = H x) := by
  classical
  have hres := e.hres
  have vpc : ∀ i : Fin (restPc se.extra sp.extra gW), (d.pcT e hV i).val = d.B + 19 + i.val := fun _ => rfl
  have vrs : ∀ i : Fin 5, (d.rsT e hV i).val = d.B + 19 + restPc se.extra sp.extra gW + i.val := fun _ => rfl
  have venc : ∀ k : Fin 13, (d.encT hV k).val = d.F + d.rt + k.val := fun _ => rfl
  have vscr : ∀ m : Fin 13, (d.scr hV m).val = d.G + d.R1 + 397 + d.w + d.tc + m.val := fun _ => rfl
  have vG : d.G = d.F + d.rt + 13 := rfl
  have vB : d.B = d.G + d.R1 + 410 + d.w + d.tc := rfl
  have vlen : (Dims.lenTape e.ext hV).val = d.B := rfl
  have vcs1 : (Dims.csSlots e.ext hV 1).val = d.B + 13 := rfl
  have vPc : restPc se.extra sp.extra gW = 71 + se.extra + sp.extra + gW := rfl
  obtain ⟨H3, A3, s3, t59, t60, tA, tH⟩ := stages_run se sp e hV r Rc cS1 cD1 H A hs1 hd1 hHs1 hHd1 hlog
    hblank hblankH
  -- facts at the F6 entry
  have k3 : ∀ x : Fin V, x.val ≠ d.B + 19 + 66 → x.val ≠ d.B + 19 + 59 → x.val ≠ d.B + 19 + 60 →
      ¬ (d.B + 19 + 71 ≤ x.val ∧ x.val < d.B + 19 + 71 + se.extra + sp.extra) → A3 x = A x ∧ H3 x = H x :=
    fun x a1 a2 a3 a4 => ⟨tA x a1 a2 a3 a4, tH x a4⟩
  have kpc : ∀ i : Fin (restPc se.extra sp.extra gW), i.val ≠ 66 → i.val ≠ 59 → i.val ≠ 60 → i.val < 71 →
      A3 (d.pcT e hV i) = A (d.pcT e hV i) ∧ H3 (d.pcT e hV i) = H (d.pcT e hV i) := by
    intro i a1 a2 a3 a4
    exact k3 _ (by rw [vpc]; omega) (by rw [vpc]; omega) (by rw [vpc]; omega) (by rw [vpc]; omega)
  have krs : ∀ i : Fin 5, A3 (d.rsT e hV i) = A (d.rsT e hV i) ∧ H3 (d.rsT e hV i) = H (d.rsT e hV i) := by
    intro i
    exact k3 _ (by rw [vrs]; omega) (by rw [vrs]; omega) (by rw [vrs]; omega) (by rw [vrs]; omega)
  have kenc : ∀ k : Fin 13, A3 (d.encT hV k) = A (d.encT hV k) ∧ H3 (d.encT hV k) = H (d.encT hV k) := by
    intro k
    have := k.isLt
    exact k3 _ (by rw [venc, vB, vG]; omega) (by rw [venc, vB, vG]; omega) (by rw [venc, vB, vG]; omega)
      (by rw [venc, vB, vG]; omega)
  have kscr : ∀ m : Fin 13, A3 (d.scr hV m) = A (d.scr hV m) ∧ H3 (d.scr hV m) = H (d.scr hV m) := by
    intro m
    have := m.isLt
    exact k3 _ (by rw [vscr, vB]; omega) (by rw [vscr, vB]; omega) (by rw [vscr, vB]; omega)
      (by rw [vscr, vB]; omega)
  obtain ⟨A4, s4, u63, u69, uo⟩ := f6_step se sp e hV Rc (vE r) (vP r) w q cW cQ H3 A3
    (by intro i hi; rw [(kpc i (by omega) (by omega) (by omega) (by omega)).1]; exact hblank _ (Or.inl (by omega)))
    t59 t60
    (by
      intro i hi
      by_cases h66 : i.val = 66
      · omega
      by_cases h59 : i.val = 59
      · rw [tH _ (by rw [vpc]; omega)]; exact hblankH _ (by omega)
      by_cases h60 : i.val = 60
      · rw [tH _ (by rw [vpc]; omega)]; exact hblankH _ (by omega)
      rw [(kpc i h66 h59 h60 (by omega)).2]; exact hblankH _ (by omega))
    (by intro k; rw [(kpc _ (by simp; omega) (by simp; omega) (by simp; omega) (by simp; omega)).1]; exact hcoef k)
    (by intro k hk; rw [(kenc k).1]; exact henc k hk)
    (by intro k hk; rw [(kenc k).2]; exact hencH k hk)
    (by rw [(krs 3).1]; exact hW) (by rw [(krs 3).2]; exact hWH)
    (by rw [(krs 4).1]; exact hQ) (by rw [(krs 4).2]; exact hQH)
    (by rw [(kscr 11).1]; exact hdrv) (by rw [(kscr 11).2]; exact hdrvH)
    (by rw [(kscr 12).1]; exact hlg) (by rw [(kscr 12).2]; exact hlgH)
    he1 hpw hfirst hsecond
  -- the slope
  have k4 : ∀ x : Fin V, ¬ (d.B + 19 ≤ x.val ∧ x.val < d.B + 19 + 71 + se.extra + sp.extra) →
      ¬ (d.F + d.rt ≤ x.val ∧ x.val ≤ d.F + d.rt + 4 ∧ x.val ≠ d.F + d.rt + 3) → A4 x = A x ∧ H3 x = H x := by
    intro x a1 a2
    refine ⟨(uo x (by omega) a2).trans (tA x (by omega) (by omega) (by omega) (by omega)), tH x (by omega)⟩
  have p68 : A4 (d.pcT e hV ⟨68, by unfold restPc; omega⟩) = ZeroPadding.pad Rc [] := by
    rw [uo _ (by rw [vpc]; simp) (by rw [vpc, vB, vG]; simp; omega),
      tA _ (by rw [vpc]; simp) (by rw [vpc]; simp) (by rw [vpc]; simp) (by rw [vpc]; simp),
      hblank _ (Or.inr (Or.inl (by simp)))]
    exact (Finish.blank_is_padded Rc).symm
  have p69 : A4 (d.pcT e hV ⟨69, by unfold restPc; omega⟩) = ZeroPadding.pad Rc [] := by
    rw [uo _ (by rw [vpc]; simp) (by rw [vpc, vB, vG]; simp; omega),
      tA _ (by rw [vpc]; simp) (by rw [vpc]; simp) (by rw [vpc]; simp) (by rw [vpc]; simp),
      hblank _ (Or.inr (Or.inl (by simp)))]
    exact (Finish.blank_is_padded Rc).symm
  have h68 : H3 (d.pcT e hV ⟨68, by unfold restPc; omega⟩) = 0 := by
    rw [tH _ (by rw [vpc]; simp)]; exact hblankH _ (by simp; omega)
  have h69 : H3 (d.pcT e hV ⟨69, by unfold restPc; omega⟩) = 0 := by
    rw [tH _ (by rw [vpc]; simp)]; exact hblankH _ (by simp; omega)
  obtain ⟨A5, s5, sl1, slo⟩ := Prologue.slope_select (Dims.lenTape e.ext hV) (d.rsT e hV 0) (d.rsT e hV 1)
    (Dims.csSlots e.ext hV 1) (d.pcT e hV ⟨68, by unfold restPc; omega⟩) (d.pcT e hV ⟨69, by unfold restPc; omega⟩)
    (ne_val (by rw [vrs, vpc]; omega)) (ne_val (by rw [vrs, vcs1]; omega))
    (ne_val (by rw [vrs, vpc]; omega)) (ne_val (by rw [vrs, vpc]; omega))
    (ne_val (by rw [vrs, vcs1]; omega)) (ne_val (by rw [vrs, vpc]; omega))
    (ne_val (by rw [vpc, vcs1]; simp)) (ne_val (by rw [vpc, vpc]; simp))
    (ne_val (by rw [vpc, vcs1]; simp))
    (ne_val (by rw [vlen, vrs]; omega)) (ne_val (by rw [vlen, vrs]; omega)) (ne_val (by rw [vlen, vcs1]; omega))
    (ne_val (by rw [vlen, vpc]; vsimp)) (ne_val (by rw [vlen, vpc]; vsimp))
    L capLen Mb Ms cB cS Rc H3 A4
    (by rw [(k4 _ (by rw [vlen]; omega) (by rw [vlen, vB, vG]; omega)).2]; exact hlenH)
    (by rw [(krs 0).2]; exact hbigH) (by rw [(krs 1).2]; exact hsmallH)
    (by rw [(k4 _ (by rw [vcs1]; omega) (by rw [vcs1, vB, vG]; omega)).2]; exact hcs1H)
    h68 h69
    (by rw [(k4 _ (by rw [vlen]; omega) (by rw [vlen, vB, vG]; omega)).1]; exact hlen)
    (by rw [(k4 _ (by rw [vrs]; omega) (by rw [vrs, vB, vG]; omega)).1]; exact hbig)
    (by rw [(k4 _ (by rw [vrs]; omega) (by rw [vrs, vB, vG]; omega)).1]; exact hsmall)
    (by rw [(k4 _ (by rw [vcs1]; omega) (by rw [vcs1, vB, vG]; omega)).1]; exact hcs1)
    p68 p69
  refine ⟨H3, A5, s3.seq (s4.seq s5), ?_, ?_, sl1, ?_, fun x hx => tH x hx⟩
  · rw [slo _ (ne_val (by rw [venc, vcs1, vB, vG]; simp; omega)) (ne_val (by rw [venc, vpc, vB, vG]; simp; omega))
      (ne_val (by rw [venc, vpc, vB, vG]; simp; omega))]
    exact u63
  · intro k
    have hk := k.isLt
    rw [slo _ (ne_val (by rw [venc, vcs1, vB, vG]; simp; omega)) (ne_val (by rw [venc, vpc, vB, vG]; simp; omega))
      (ne_val (by rw [venc, vpc, vB, vG]; simp; omega)), u69 k,
      tA _ (by rw [vpc]; simp; omega) (by rw [vpc]; simp; omega) (by rw [vpc]; simp; omega)
        (by rw [vpc]; simp; omega)]
  · intro x hx1 hx2 hx3
    rw [slo x hx1 (ne_val (by rw [vpc]; vsimp)) (ne_val (by rw [vpc]; vsimp))]
    exact (k4 x hx2 hx3).1

end

end
end NearCubicWires.SourceConstruction.Rest
end

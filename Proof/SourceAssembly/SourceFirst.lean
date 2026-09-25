import Proof.SourceAssembly.SourceRefillSeam

section
set_option autoImplicit false
set_option maxRecDepth 120000
set_option warningAsError true

open NearCubicWires LocalBitMultitape ExtDecompositionBatch
open RepairOrdinary RepairOrdinary.RecoveryRootRound
open RepairRepresentation SupplierEstimator SupplierPipeline SourceInterfaces
open RepairSource.VerifierDecoding
open NearCubicWires.P1Closure
open PCJ9eff70d512234a4c_Fixed PCJd4d1d9d7d1fa4313_Production PCJc4297ab269d8423a_Source
open NearCubicWires.RepairSource NearCubicWires.RepairSource.CloseoutFinal
open NearCubicWires.SourceRequest NearCubicWires.SourceRequest.FactorLoop
namespace NearCubicWires.SourceConstruction.Rest
noncomputable section

section
variable {a : DecompositionAlgorithm} {vE vP : Request → Nat}
  (se : PacketsGlue.RequestMeta.UnaryStage a vE) (sp : PacketsGlue.RequestMeta.UnaryStage a vP)
  {d : SourceConstruction.Dims} {gW : Nat} (e : d.RestExt se.extra sp.extra gW) {V : Nat} (hV : d.U ≤ V)

theorem back_run70 (r : Request) (Rc cS1 cD1 w q cW cQ L capLen Mb Ms cB cS : Nat)
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
      (∀ x : Fin V, ¬ (d.B + 19 + 71 ≤ x.val ∧ x.val < d.B + 19 + 71 + se.extra + sp.extra) → H' x = H x) ∧
      A' (d.pcT e hV ⟨70, by unfold restPc; omega⟩) = A (d.pcT e hV ⟨70, by unfold restPc; omega⟩) := by
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
  refine ⟨H3, A5, s3.seq (s4.seq s5), ?_, ?_, sl1, ?_, fun x hx => tH x hx, ?_⟩
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
  · have v70 : (d.pcT e hV ⟨70, by unfold restPc; omega⟩).val = d.B + 19 + 70 := rfl
    have v68 : (d.pcT e hV ⟨68, by unfold restPc; omega⟩).val = d.B + 19 + 68 := rfl
    have v69 : (d.pcT e hV ⟨69, by unfold restPc; omega⟩).val = d.B + 19 + 69 := rfl
    rw [slo _ (ne_val (by rw [v70, vcs1]; omega)) (ne_val (by rw [v70, v68]; omega))
        (ne_val (by rw [v70, v69]; omega)),
      uo _ (by rw [v70]; omega) (by rw [v70, vB, vG]; omega),
      tA _ (by rw [v70]; omega) (by rw [v70]; omega) (by rw [v70]; omega) (by rw [v70]; omega)]

end

section concrete
variable (mask : MaskProducer) {selector : CyclicChoice.Laws}
  (packets : PCJc4297ab269d8423a_Source.PacketLibrary selector)
  (rows : PCJc4297ab269d8423a_Source.RowLibrary selector) (sources : EightSources) (res : Nat)
  {gamma : Real} (p : Parameters sources gamma) (k r : Nat)

set_option hygiene false in
local notation "𝔇" => dimsOf mask packets rows sources res p k r

end concrete

end
end NearCubicWires.SourceConstruction.Rest
end

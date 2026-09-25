import Proof.SourceAssembly.SourceFirstSeam3B

section
set_option autoImplicit false
set_option maxRecDepth 120000
set_option warningAsError true

open NearCubicWires LocalBitMultitape ExtDecompositionBatch
open RepairOrdinary RepairOrdinary.RecoveryRootRound
open RepairRepresentation SupplierEstimator SupplierPipeline SourceInterfaces
open RepairSource.VerifierDecoding
open NearCubicWires.P1Closure
namespace NearCubicWires.SourceConstruction.Rest
noncomputable section

section clause
variable {d : SourceConstruction.Dims} {eX pX gW : Nat} {V : Nat}

/-- Every dirty tape lies below `U`. -/
theorem inDirt_lt_U (e : d.RestExt3 eX pX gW) {v : Nat} (h : d.InDirt eX pX gW v) : v < d.U := by
  have hB : d.B = d.G + d.R1 + 410 + d.w + d.tc := rfl
  have hG : d.G = d.F + d.rt + 13 := rfl
  have hU : d.U = d.G + d.prepT := rfl
  have hprep : d.prepT = d.R1 + 410 + d.w + d.tc + d.res := rfl
  have hp : d.pscr = d.R1 + 408 + d.w + d.tc := rfl
  have := e.hres3
  unfold SourceConstruction.Dims.InDirt SourceConstruction.Dims.InClear at h
  unfold restPc at *
  omega

/-- Every `Z` tape lies below `U`. -/
theorem inZ_lt_U (e : d.RestExt3 eX pX gW) {v : Nat} (h : d.InZ eX pX v) : v < d.U := by
  have hB : d.B = d.G + d.R1 + 410 + d.w + d.tc := rfl
  have hU : d.U = d.G + d.prepT := rfl
  have hprep : d.prepT = d.R1 + 410 + d.w + d.tc + d.res := rfl
  have := e.hres3
  unfold SourceConstruction.Dims.InZ at h
  unfold restPc at *
  omega

theorem InvC_of_InvR {e : d.RestExt3 eX pX gW} {hV : d.U ≤ V} {hV1 : d.U ≤ V + 1}
    {Rc Rk : Nat} {K : Fin V → Prop} {K0 : Fin V → List Bool} {KH0 : Fin V → Nat}
    {N w q Mb Ms cW cQ cB cS S Rw B v U0 fuel : Nat} {H : Fin V → Nat} {A : Fin V → List Bool}
    (h : InvR e hV Rc Rk K K0 KH0 N w q Mb Ms cW cQ cB cS S Rw B v U0 fuel H A)
    (hRk : Rc ≤ Rk) (hN : N + 2 ≤ Rc) (hcW : Rc ≤ cW) (hcQ : Rc ≤ cQ) (hcB : Rc ≤ cB) (hcS : Rc ≤ cS)
    (Kc : Fin (V+1) → Prop) (K0' : Fin (V+1) → List Bool) (KH0' : Fin (V+1) → Nat)
    (H1 : Fin (V+1) → Nat) (A1 : Fin (V+1) → List Bool)
    (hA : ∀ x : Fin V, d.F ≤ x.val → A1 x.castSucc = ZeroPadding.pad Rc (A x))
    (hH : ∀ x : Fin V, d.F ≤ x.val → H1 x.castSucc = H x)
    (hcA : (A1 (Fin.last V)).length ≤ Rc) (hcH : H1 (Fin.last V) ≤ Rc)
    (henc : ∀ kk : Fin 13, (kk.val < 3 ∨ kk.val = 4) → (A (Dims.encT (d := d) hV kk)).length ≤ Rc)
    (hKc : ∀ y, Kc y → A1 y = K0' y ∧ H1 y = KH0' y) :
    InvC e hV1 Rc Rk Kc K0' KH0' (Fin.last V) w q Mb Ms cW cQ cB cS S Rw B v U0 H1 A1 := by
  have hB : d.B = d.G + d.R1 + 410 + d.w + d.tc := rfl
  have hG : d.G = d.F + d.rt + 13 := rfl
  have crs : ∀ i : Fin 5, d.rsT e.ext2.ext1 hV1 i = (d.rsT e.ext2.ext1 hV i).castSucc := fun _ => Fin.ext rfl
  have cmT : ∀ i : Fin 5, Dims.mT e.ext2 hV1 i = (Dims.mT e.ext2 hV i).castSucc := fun _ => Fin.ext rfl
  have csc : ∀ m : Fin 13, d.scr hV1 m = (d.scr hV m).castSucc := fun _ => Fin.ext rfl
  have chr : ∀ i : Fin 12, Dims.hrT e hV1 i = (Dims.hrT e hV i).castSucc := fun _ => Fin.ext rfl
  have cen : ∀ kk : Fin 13, Dims.encT (d := d) hV1 kk = (Dims.encT (d := d) hV kk).castSucc := fun _ => Fin.ext rfl
  have rsF : ∀ i : Fin 5, d.F ≤ (d.rsT e.ext2.ext1 hV i).val := fun i => by
    simp only [Dims.rsT]; omega
  have mF : ∀ i : Fin 5, d.F ≤ (Dims.mT e.ext2 hV i).val := fun i => by
    simp only [Dims.mT]; omega
  have scF : ∀ m : Fin 13, d.F ≤ (d.scr hV m).val := fun m => by
    simp only [Dims.scr, Dims.scrV]; omega
  have hrF : ∀ i : Fin 12, d.F ≤ (Dims.hrT e hV i).val := fun i => by
    rw [Dims.hrT_val]; omega
  have enF : ∀ kk : Fin 13, d.F ≤ (Dims.encT (d := d) hV kk).val := fun kk => by
    simp only [Dims.encT]; omega
  -- a dirty or `Z` tape of `V+1` is the image of one of `V`
  have down : ∀ x : Fin (V+1), ∀ hx : x.val < d.U, x = (⟨x.val, by omega⟩ : Fin V).castSucc := fun x hx => Fin.ext rfl
  refine ⟨hKc, ?_, ?_, ?_, ?_, fun i _ => ?_, ?_, ?_, ?_, ?_, ?_, fun i => ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    fun x hx hz => ?_, fun x hx hz => ?_, fun x hz => ?_, fun x hz => ?_, ?_, ?_, hcA, hcH, fun kk hk => ?_,
    fun kk hk => ?_⟩
  · rw [crs, hA _ (rsF 0), h.big]; exact pad_over _ _ hcB _
  · rw [crs, hA _ (rsF 1), h.small]; exact pad_over _ _ hcS _
  · rw [crs, hA _ (rsF 3), h.wv]; exact pad_over _ _ hcW _
  · rw [crs, hA _ (rsF 4), h.qv]; exact pad_over _ _ hcQ _
  · rw [crs, hH _ (rsF i)]; exact h.rsH i
  · rw [cmT, hA _ (mF 0), h.mU]; exact pad_same _ _
  · rw [cmT, hA _ (mF 1), h.mS]; exact pad_same _ _
  · rw [cmT, hA _ (mF 2), h.mR]; exact pad_same _ _
  · rw [cmT, hA _ (mF 3), h.mB]; exact pad_same _ _
  · rw [cmT, hA _ (mF 4), h.mv]; exact pad_same _ _
  · rw [cmT, hH _ (mF i)]; exact h.mH i
  · rw [csc, hA _ (scF 11), h.drv]; exact pad_long _ _ (by simp)
  · rw [csc, hH _ (scF 11)]; exact h.drvH
  · rw [csc, hA _ (scF 12), h.lg]; exact pad_long _ _ (by simp)
  · rw [csc, hH _ (scF 12)]; exact h.lgH
  · rw [chr, hA _ (hrF 10), h.zD]; exact pad_long _ _ (by simp; omega)
  · rw [chr, hH _ (hrF 10)]; exact h.zDH
  · rw [chr, hA _ (hrF 11), h.zL]; exact pad_long _ _ (by simp; omega)
  · rw [chr, hH _ (hrF 11)]; exact h.zLH
  · have hU := inDirt_lt_U e hx
    have hxF : d.F ≤ x.val := by
      unfold SourceConstruction.Dims.InDirt SourceConstruction.Dims.InClear at hx; omega
    rw [down x hU, hA _ hxF, pad_len_max]
    exact max_le le_rfl (h.dirtA _ hx hz)
  · have hU := inDirt_lt_U e hx
    have hxF : d.F ≤ x.val := by
      unfold SourceConstruction.Dims.InDirt SourceConstruction.Dims.InClear at hx; omega
    rw [down x hU, hH _ hxF]
    exact h.dirtH _ hx hz
  · have hU := inZ_lt_U e hz
    have hxF : d.F ≤ x.val := by unfold SourceConstruction.Dims.InZ at hz; omega
    rw [down x hU, hA _ hxF, pad_len_max]
    exact max_le hRk (h.zA _ hz)
  · have hU := inZ_lt_U e hz
    have hxF : d.F ≤ x.val := by unfold SourceConstruction.Dims.InZ at hz; omega
    rw [down x hU, hH _ hxF]
    exact h.zH _ hz
  · rw [crs, hA _ (rsF 2), h.curT, pad_len_max, pad_len_max, tape_len]
    omega
  · rw [crs, hH _ (rsF 2), h.rsH 2]; omega
  · rw [cen, hA _ (enF kk), pad_len_max]
    exact max_le le_rfl (henc kk hk)
  · rw [cen, hH _ (enF kk)]; exact h.encH kk hk

end clause

end
end NearCubicWires.SourceConstruction.Rest
end

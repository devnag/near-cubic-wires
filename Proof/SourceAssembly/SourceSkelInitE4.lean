import Proof.SourceAssembly.SourceSkelInitE3

section
set_option autoImplicit false
set_option maxRecDepth 120000
set_option warningAsError true

open NearCubicWires LocalBitMultitape ExtDecompositionBatch RepairOrdinary
open RepairOrdinary.RecoveryRootRound RepairSource.VerifierDecoding RepairSource.ProjectionNormalization
open NearCubicWires.SupplierEstimator RepairRepresentation
open PCJ1fef9807c6954e94_Native
open NearCubicWires.SourceConstruction NearCubicWires.SourceConstruction.InitRun
namespace NearCubicWires.SourceSkeleton.InitS
noncomputable section

variable {d : Dims} {eX pX gW eR eV X T : Nat} (pl : Place d eX pX gW eR eV X T) {NS : Nat}
  (hh : HeadExt d eX pX gW X NS)

def EncOut2 (Rc b : Nat) (H : Fin T → ℕ) (A : Fin T → List Bool) : Prop :=
  EncOut pl Rc b H A ∧ ∀ kk : Fin 13, kk.val < 3 →
    A (Dims.encT (d := d) pl.hT kk) = List.replicate Rc false ∧ H (Dims.encT (d := d) pl.hT kk) = 0

/-- **Every init state carries `EncOut2`.** -/
theorem encOut2_of_inv {NR NE : Nat}
    {L cS cR q b Rc Vv CP CW CL DP DW DL : Nat} {mode : Bool} {tg : Nat} {val : Nat → Option (List Bool)} {u : Nat}
    {H : Fin T → ℕ} {A : Fin T → List Bool} {H' : Fin T → ℕ} {A' : Fin T → List Bool}
    (hi : InitInv pl hh NR NE L cS cR q b Rc Vv CP CW CL DP DW DL mode tg val u H A H' A') :
    EncOut2 pl Rc b H' A' := by
  refine ⟨encOut_of_inv pl hh hi, fun kk hk => ?_⟩
  obtain ⟨H1, A1, ho, hag⟩ := hi.base
  obtain ⟨hF0, hB0, h11, h12, hU, hJB, hjk, hP⟩ := lay pl.ext
  have hsbB : sb d eX pX gW = d.B + 29 + restPc eX pX gW := rfl
  have hBG : d.B = d.G + d.R1 + 410 + d.w + d.tc := rfl
  have hG : d.G = d.F + d.rt + 13 := rfl
  have hv : (Dims.encT (d := d) pl.hT kk).val = d.F + d.rt + kk.val := rfl
  have hk13 := kk.isLt
  obtain ⟨e1, e2⟩ := hag _ (by rw [hv]; omega) (by rw [hv]; unfold eb; omega)
  rw [e1, e2]
  refine ho.blank _ (by rw [hv]; omega) (by rw [hv]; omega) ?_
  unfold KeptS
  rw [hv]
  omega

theorem entry_initXE3 (e : d.RestExt3 eX pX gW) (NR : Nat) (hNR16 : 16 ≤ NR) (hNR20 : 20 ≤ NR) (hNR : NR ≤ 32) {NE : Nat}
    (hE : ResExt d eX pX gW X NS NE)
    (L C cVc cS cR DP CP DW CW DL CL : Nat) (hN : nsOf DP DW DL ≤ NS) (mode : Bool) (target q b DD CD Dcw Ccw : Nat)
    (hNE : uAll DD Dcw ≤ NE) (MB : List Bool) {sM : Nat} (M : Machine T sM) (mcost wM : Nat)
    (hmeta : MetaRun pl hh NR NE L cS cR q b (Once.Rc eR L C q) (cVc * RuntimeShape.tableClass L eV q) CP CW CL DP DW DL mode target MB
      (uAll DD Dcw + 7) M mcost wM)
    (hK : 2 * normalizedLiveCount q L + 4 ≤ Once.Rc eR L C q)
    (H0 : Fin T → ℕ) (A0 : Fin T → List Bool)
    (hd : A0 (d.scr pl.hT 11) = [])
    (hAr : A0 pl.ar = UnaryTemplate.tape q) (hHr : H0 pl.ar = 0)
    (hAw : A0 pl.wd = List.replicate b true) (hHw : H0 pl.wd = 0)
    (hlowE : ∀ x : Fin T, 278 ≤ x.val → x.val < 284 →
      (A0 x).length ≤ cVc * RuntimeShape.tableClass L eV q ∧ H0 x = 0)
    (hF : ∀ x : Fin T, d.F ≤ x.val → x.val < d.U → A0 x = [] ∧ H0 x = 0)
    (hfit : q + 3 + Dimension.prefixCost eR eV L C cVc q ≤ Once.Rc eR L C q)
    (hVR : cVc * RuntimeShape.tableClass L eV q ≤ Once.Rc eR L C q)
    (hVLR : VLog eV L cVc q ≤ Once.Rc eR L C q) (hRc : 2 ≤ Once.Rc eR L C q)
    (hU0 : U0 L q ≤ Once.Rc eR L C q)
    (hS : cS * (cVc * RuntimeShape.tableClass L eV q + 1) + 2 ≤ Once.Rc eR L C q)
    (hR : cR * (cVc * RuntimeShape.tableClass L eV q + 1) + 2 ≤ Once.Rc eR L C q)
    (hB : cVc * RuntimeShape.tableClass L eV q + 1 + 2 ≤ Once.Rc eR L C q)
    (hv : b + 2 ≤ Once.Rc eR L C q)
    (hcap : CloseoutRowsEstimatorParity.Capacity.value q ≤ Once.Rc eR L C q) (hqR : q ≤ Once.Rc eR L C q)
    (hLw : (frame (natWord L)).length ≤ Once.Rc eR L C q + 2)
    (hTw : (frame (natWord target)).length ≤ Once.Rc eR L C q + 2) (h5 : 5 ≤ Once.Rc eR L C q)
    (hLd : CL*(q+1)^DL + 2 ≤ Once.Rc eR L C q) (hC82 : 82472 ≤ Once.Rc eR L C q)
    (hq2 : 2*q + 1 ≤ Once.Rc eR L C q) (hMs : 2 * InitPost.Ms L q + 5 ≤ Once.Rc eR L C q)
    (Kc : Fin T → Prop) (K0 : Fin T → List Bool) (KH0 : Fin T → Nat) (cnt : Fin T) (hcnt : d.U ≤ cnt.val)
    (hKlow : ∀ x, Kc x → x.val < d.F → x.val ≠ 278 → x.val ≠ 279 → (x.val < 278 ∨ 284 ≤ x.val) ∧ A0 x = K0 x ∧ H0 x = KH0 x)
    (hK278 : ∀ x, Kc x → x.val = 278 → K0 x = List.replicate (cVc * RuntimeShape.tableClass L eV q) true ∧ KH0 x = 0)
    (hK279 : ∀ x, Kc x → x.val = 279 → K0 x = List.replicate (cVc * RuntimeShape.tableClass L eV q) false ∧ KH0 x = 0)
    (hKhigh : ∀ x, Kc x → d.F ≤ x.val → ∃ i, i < NR ∧ x.val = sb d eX pX gW + i ∧
      K0 x = initResVal (Once.Rc eR L C q) q L CP DP CW DW CL DL mode target
        (valAllX mode L q (Once.Rc eR L C q) DD CD Dcw Ccw CL DL b MB) i ∧ KH0 x = 0)
    (hcntA : (A0 cnt).length ≤ Once.Rc eR L C q) (hcntH : H0 cnt ≤ Once.Rc eR L C q) :
    ∃ (Hi : Fin T → ℕ) (Ai : Fin T → List Bool),
      Step (guardAllXE pl hh NR hNR hE L C cVc cS cR DP CP DW CW DL CL hN mode target DD CD Dcw Ccw hNE M)
        (initAllXCostE pl L C cVc cS cR DP CP DW CW DL CL mode target q b DD CD Dcw Ccw mcost + 2) H0 A0 Hi Ai ∧
      Rest.InvC e pl.hT (Once.Rc eR L C q) (Rk (Once.Rc eR L C q)) Kc K0 KH0 cnt b q (Mb L q) (InitPost.Ms L q)
        (Once.Rc eR L C q) (Once.Rc eR L C q) (Once.Rc eR L C q) (Once.Rc eR L C q)
        (cS*(cVc * RuntimeShape.tableClass L eV q+1)) (cR*(cVc * RuntimeShape.tableClass L eV q+1))
        (cVc * RuntimeShape.tableClass L eV q+1) b (U0 L q) Hi Ai ∧
      (∀ x : Fin T, d.F ≤ x.val → x.val < d.U → Once.Rc eR L C q ≤ (Ai x).length) ∧
      (∀ x : Fin T, x.val < d.F → (x.val < 278 ∨ 284 ≤ x.val) → Ai x = A0 x ∧ Hi x = H0 x) ∧
      (∀ x : Fin T, d.U ≤ x.val → Ai x = A0 x ∧ Hi x = H0 x) ∧
      EncOut2 pl (Once.Rc eR L C q) b Hi Ai := by
  obtain ⟨Hi, Ai, s, hi⟩ := initAllX_runE pl hh NR hNR20 hNR hE L C cVc cS cR DP CP DW CW DL CL hN mode target q b DD CD Dcw Ccw
    hNE MB M mcost wM hmeta hK H0 A0 hAr hHr hAw hHw hlowE hF hfit hVR hVLR hRc hU0 hS hR hB hv hcap hqR hLw hTw h5 hLd hC82 hq2 hMs
  have hML := masterW_length L cS cR q b (Once.Rc eR L C q) (cVc * RuntimeShape.tableClass L eV q) hU0 hS hR hB hv
  refine ⟨Hi, Ai, guardAllXE_blank pl hh NR hNR hE L C cVc cS cR DP CP DW CW DL CL hN mode target q b DD CD Dcw Ccw hNE M mcost
      H0 Hi A0 Ai s hd,
    invC_of_init_rwG pl hh e hNR16 hNR hE hi Kc K0 KH0 cnt hcnt hKlow hK278 hK279 hKhigh hcntA hcntH hML hRc
      (valAllX_10 _ _ _ _ _ _ _ _ _ _ _ _) (valAllX_11 _ _ _ _ _ _ _ _ _ _ _ _),
    inv_longG pl hh hE hi hML (slotVal_longX _ _ _ _ _ _ _ _ _ _ _ _), ?_, ?_, encOut2_of_inv pl hh hi⟩
  · obtain ⟨hF0, hB0, h11, h12, hU, hJB, hjk, hP⟩ := lay pl.ext
    have hres := hE.hres
    have hsbB : sb d eX pX gW = d.B + 29 + restPc eX pX gW := rfl
    have hBG : d.B = d.G + d.R1 + 410 + d.w + d.tc := rfl
    have hG : d.G = d.F + d.rt + 13 := rfl
    obtain ⟨H1, A1, ho, hag⟩ := hi.base
    intro x h1 h2
    rw [(hag x (by omega) (by unfold eb; omega)).1, (hag x (by omega) (by unfold eb; omega)).2]
    exact ho.below x h1 h2
  · have hres := hE.hres
    obtain ⟨hF0, hB0, h11, h12, hU, hJB, hjk, hP⟩ := lay pl.ext
    obtain ⟨H1, A1, ho, hag⟩ := hi.base
    intro x h1
    rw [(hag x (by unfold sb; omega) (by unfold eb; omega)).1, (hag x (by unfold sb; omega) (by unfold eb; omega)).2]
    exact ho.above x h1

end
end NearCubicWires.SourceSkeleton.InitS
end


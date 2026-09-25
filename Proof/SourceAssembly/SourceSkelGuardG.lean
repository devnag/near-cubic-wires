import Proof.SourceAssembly.SourceSkelStartGuard

section
set_option autoImplicit false
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unusedVariables false

open NearCubicWires NearCubicWires.ComponentwisePolynomial NearCubicWires.RepairOrdinary.CompetitorRawFieldEmit NearCubicWires.RepairOrdinary.CloseoutRowsOriginalSchedule LocalBitMultitape ExtDecompositionBatch RepairOrdinary RepairRepresentation SourceInterfaces RepairSource RepairSource.CloseoutFinal P1TopDown RepairSource.VerifierDecoding RecoveryRootRound RecoveryExecution CloseoutRowsEstimator CloseoutRowsEstimatorCoefficients CompetitorSelectedCount MatrixScoreBatch CompetitorCountMask SupplierPipeline SupplierEstimator SupplierPrime CanonicalFourfoldRowProgram CloseoutRawRows C10ExternalRowLoop C10ThresholdNaturalRowPrint C10ThresholdParityRow C10ThresholdEstimateRowJoin CloseoutFinalC10RowAnswerWord P1Closure P1TopDownPaidReusable P1TopDownPaidReusableReserves P1TopDownPaidBinaryReserves
open PCJ1fef9807c6954e94_Native
open PCJ9eff70d512234a4c_Fixed PCJd4d1d9d7d1fa4313_Production
open PCJc4297ab269d8423a_Source
open NearCubicWires.SourceConstruction NearCubicWires.SourceConstruction.InitRun
open NearCubicWires.SourceConstruction NearCubicWires.SourceConstruction.InitRun
namespace NearCubicWires.SourceSkeleton.GuardG
open NearCubicWires.SourceSkeleton.EntrySite NearCubicWires.SourceSkeleton.KeptW
open NearCubicWires.SourceSkeleton.ClassR NearCubicWires.SourceSkeleton.Params NearCubicWires.SourceSkeleton.ClassV4
open NearCubicWires.SourceSkeleton.ParamsV4
open NearCubicWires.SourceSkeleton.Fill (XtraW)
open NearCubicWires.SourceSkeleton.FillV5 NearCubicWires.SourceSkeleton.FirstW NearCubicWires.SourceSkeleton.XtraF
noncomputable section

section site
variable (selector : CyclicChoice.Laws) (xtra : XtraW selector) (mask : MaskProducer)
  (packets : PCJc4297ab269d8423a_Source.PacketLibrary selector) (rows : PCJc4297ab269d8423a_Source.RowLibrary selector)
  (sources : EightSources) (gamma : Real) (hg : 0 < gamma) (hh : gamma < 1/2) (p : Parameters sources gamma)

set_option hygiene false in
local notation "𝔮" => C10PartsSchedule.widthAt sources (kW selector mask packets rows sources gamma hg hh p) n
set_option hygiene false in
local notation "𝔏" => LW selector mask packets rows sources gamma hg hh p
set_option hygiene false in
local notation "ℜ" => Once.Rc (hRx4 selector mask packets rows sources gamma hg hh p) (LW selector mask packets rows sources gamma hg hh p) 1 (C10PartsSchedule.widthAt sources (kW selector mask packets rows sources gamma hg hh p) n)
set_option hygiene false in
local notation "𝔙" => SourceBudget.Params.cVcN selector sources gamma hg hh p *
  RuntimeShape.tableClass (LW selector mask packets rows sources gamma hg hh p) (SourceBudget.Params.hVN selector sources gamma hg hh p) (C10PartsSchedule.widthAt sources (kW selector mask packets rows sources gamma hg hh p) n)
set_option hygiene false in
local notation "𝔭𝔩" => plSite selector xtra mask packets rows sources gamma hg hh p mode ph
set_option hygiene false in
local notation "𝔡" => dSite selector xtra mask packets rows sources gamma hg hh p

/-- **The first site entry's one-time init, at the site, with all thirteen encoder banks** (`EncOut2`). -/
theorem entry_initSite2G (mode : Bool) (ph : Phase) (n : ℕ)
    (hn : extraW selector xtra mask packets rows sources gamma hg hh p ≤ n)
    (hxtra : XtraF.xtraF selector mask packets rows sources gamma hg hh p ≤ xtra mask packets rows sources gamma hg hh p)
    (b : ℕ) (hb : b ≤ (C10PartsSchedule.thresholdFloor sources + 1) * (𝔮 + 1)^(SourceSteps.rBsel sources p))
    (hV1 : 1 ≤ SourceBudget.Params.cVcN selector sources gamma hg hh p)
    (H0 : Fin (USite selector xtra mask packets rows sources gamma hg hh p + 1) → ℕ) (A0 : Fin (USite selector xtra mask packets rows sources gamma hg hh p + 1) → List Bool)
    (hd : A0 ((𝔡).scr (𝔭𝔩).hT 11) = [])
    (hAr : A0 (𝔭𝔩).ar = UnaryTemplate.tape 𝔮) (hHr : H0 (𝔭𝔩).ar = 0)
    (hAw : A0 (𝔭𝔩).wd = List.replicate b true) (hHw : H0 (𝔭𝔩).wd = 0)
    (hres : ∀ x : Fin (USite selector xtra mask packets rows sources gamma hg hh p + 1), 278 ≤ x.val → x.val < 284 →
      (A0 x).length ≤ WorkspaceSelectedEntryBudget.envelope sources p (kW selector mask packets rows sources gamma hg hh p) (SourceSteps.rBsel sources p) n + 1 ∧ H0 x = 0)
    (hF : ∀ x : Fin (USite selector xtra mask packets rows sources gamma hg hh p + 1), (𝔡).F ≤ x.val → x.val < (𝔡).U → A0 x = [] ∧ H0 x = 0)
    (Kc : Fin (USite selector xtra mask packets rows sources gamma hg hh p + 1) → Prop) (K0 : Fin (USite selector xtra mask packets rows sources gamma hg hh p + 1) → List Bool) (KH0 : Fin (USite selector xtra mask packets rows sources gamma hg hh p + 1) → Nat)
    (cnt : Fin (USite selector xtra mask packets rows sources gamma hg hh p + 1)) (hcnt : (𝔡).U ≤ cnt.val)
    (hKlow : ∀ x, Kc x → x.val < (𝔡).F → x.val ≠ 278 → x.val ≠ 279 → (x.val < 278 ∨ 284 ≤ x.val) ∧ A0 x = K0 x ∧ H0 x = KH0 x)
    (hK278 : ∀ x, Kc x → x.val = 278 → K0 x = List.replicate 𝔙 true ∧ KH0 x = 0)
    (hK279 : ∀ x, Kc x → x.val = 279 → K0 x = List.replicate 𝔙 false ∧ KH0 x = 0)
    (hKhigh : ∀ x, Kc x → (𝔡).F ≤ x.val → ∃ i, i < initNR ∧
      x.val = InitS.sb (𝔡) (DSite selector mask packets rows sources gamma hg hh p).se.extra (DSite selector mask packets rows sources gamma hg hh p).sp.extra (DSite selector mask packets rows sources gamma hg hh p).gW + i ∧
      K0 x = InitS.initResVal ℜ 𝔮 𝔏 (pC sources gamma hg hh p) (pE sources gamma hg hh p) 1 3
        (ldC sources gamma hg hh p) (ldE sources gamma hg hh p) mode (SourceBudget.Params.tgOf sources gamma hg hh p)
        (InitS.valAllX mode 𝔏 𝔮 ℜ (dE sources gamma hg hh p) (dC sources gamma hg hh p) (cwE sources gamma hg hh p)
          (cwC sources gamma hg hh p) (ldC sources gamma hg hh p) (ldE sources gamma hg hh p) b
          (NearCubicWires.SourceStart.MetaRun.MBof selector sources p packets 𝔏 𝔮)) i ∧ KH0 x = 0)
    (hcntA : (A0 cnt).length ≤ ℜ) (hcntH : H0 cnt ≤ ℜ) :
    ∃ (Hi : Fin (USite selector xtra mask packets rows sources gamma hg hh p + 1) → ℕ) (Ai : Fin (USite selector xtra mask packets rows sources gamma hg hh p + 1) → List Bool),
      Step (initW selector xtra mask packets rows sources gamma hg hh p mode ph)
        (InitS.initAllXCostE (𝔭𝔩) 𝔏 1 (SourceBudget.Params.cVcN selector sources gamma hg hh p) (sC sources gamma hg hh p)
          (rC sources gamma hg hh p) (pE sources gamma hg hh p) (pC sources gamma hg hh p) 3 1 (ldE sources gamma hg hh p)
          (ldC sources gamma hg hh p) mode (SourceBudget.Params.tgOf sources gamma hg hh p) 𝔮 b (dE sources gamma hg hh p)
          (dC sources gamma hg hh p) (cwE sources gamma hg hh p) (cwC sources gamma hg hh p)
          (NearCubicWires.SourceStart.MetaStepGF.metaCostG selector sources p packets 𝔏 𝔮) + 2) H0 A0 Hi Ai ∧
      Rest.InvC (eSite selector xtra mask packets rows sources gamma hg hh p) (𝔭𝔩).hT ℜ (InitS.Rk ℜ) Kc K0 KH0 cnt b 𝔮 (Mb 𝔏 𝔮) (InitPost.Ms 𝔏 𝔮) ℜ ℜ ℜ ℜ
        (sC sources gamma hg hh p * (𝔙 + 1)) (rC sources gamma hg hh p * (𝔙 + 1)) (𝔙 + 1) b (U0 𝔏 𝔮) Hi Ai ∧
      (∀ x : Fin (USite selector xtra mask packets rows sources gamma hg hh p + 1), (𝔡).F ≤ x.val → x.val < (𝔡).U → ℜ ≤ (Ai x).length) ∧
      (∀ x : Fin (USite selector xtra mask packets rows sources gamma hg hh p + 1), x.val < (𝔡).F → (x.val < 278 ∨ 284 ≤ x.val) → Ai x = A0 x ∧ Hi x = H0 x) ∧
      (∀ x : Fin (USite selector xtra mask packets rows sources gamma hg hh p + 1), (𝔡).U ≤ x.val → Ai x = A0 x ∧ Hi x = H0 x) ∧
      InitS.EncOut2 (𝔭𝔩) ℜ b Hi Ai := by
  -- the arity is past every onset
  have hq := qOnW_le_width selector mask packets rows xtra sources gamma hg hh p n hn
  have hxF : XtraF.xtraF selector mask packets rows sources gamma hg hh p ≤ n :=
    le_trans hxtra (le_trans (xtra_le_extraW selector xtra mask packets rows sources gamma hg hh p) hn)
  have hIO : initOnsetW selector mask packets rows sources gamma hg hh p ≤ 𝔮 := by
    refine le_trans ?_ hq
    unfold qOnW
    exact le_trans (le_max_right _ _) (le_trans (le_max_right _ _) (le_trans (le_max_right _ _)
      (le_trans (le_max_right _ _) (le_max_right _ _))))
  obtain ⟨hfit, hVR, hVLR, hRc, hU0, hS, hR, hB, hcap, hqR, hLw, hTw, h5, hLd, hC82, hq2, hMs, hMb⟩ :=
    initWinW selector mask packets rows sources gamma hg hh p 𝔮 hIO
  obtain ⟨hK4, hR1, hbw⟩ := WinW.ext_windowsW selector mask packets rows sources gamma hg hh p 𝔮 hq
  -- the rewind block's residue fits under `V`
  have hwin := xtraF_residue selector mask packets rows sources gamma hg hh p n hxF
  have hpow := ResWin.pow_le_Vv (SourceBudget.Params.cVcN selector sources gamma hg hh p) 𝔏
    (SourceBudget.Params.hVN selector sources gamma hg hh p) 𝔮 hV1
  have hlowE : ∀ x : Fin (USite selector xtra mask packets rows sources gamma hg hh p + 1), 278 ≤ x.val → x.val < 284 → (A0 x).length ≤ 𝔙 ∧ H0 x = 0 := by
    intro x h1 h2
    obtain ⟨hl, hH⟩ := hres x h1 h2
    exact ⟨le_trans hl (le_trans hwin hpow), hH⟩
  
  have hmeta := NearCubicWires.SourceStart.MetaStepGF.meta_stepG (𝔭𝔩) (hhSite selector xtra mask packets rows sources gamma hg hh p) selector sources p packets
    (NR := initNR) (NE := NESite selector mask packets rows sources gamma hg hh p) (by decide) (by decide) (hESite selector xtra mask packets rows sources gamma hg hh p)
    (L := 𝔏) (cS := sC sources gamma hg hh p) (cR := rC sources gamma hg hh p) (q := 𝔮) (b := b) (Rc := ℜ) (Vv := 𝔙)
    (CP := pC sources gamma hg hh p) (CW := 1) (CL := ldC sources gamma hg hh p) (DP := pE sources gamma hg hh p) (DW := 3)
    (DL := ldE sources gamma hg hh p) (mode := mode) (tg := SourceBudget.Params.tgOf sources gamma hg hh p)
    (InitS.uAll (dE sources gamma hg hh p) (cwE sources gamma hg hh p) + 7)
    (by simp only [NESite, initNE, extW]; omega) hR1 hcap (by omega)
  exact InitS.entry_initXE3 (𝔭𝔩) (hhSite selector xtra mask packets rows sources gamma hg hh p) (eSite selector xtra mask packets rows sources gamma hg hh p) initNR (by decide) (by decide) (by decide) (hESite selector xtra mask packets rows sources gamma hg hh p)
    𝔏 1 (SourceBudget.Params.cVcN selector sources gamma hg hh p) (sC sources gamma hg hh p) (rC sources gamma hg hh p)
    (pE sources gamma hg hh p) (pC sources gamma hg hh p) 3 1 (ldE sources gamma hg hh p) (ldC sources gamma hg hh p) (le_refl _)
    mode (SourceBudget.Params.tgOf sources gamma hg hh p) 𝔮 b (dE sources gamma hg hh p) (dC sources gamma hg hh p)
    (cwE sources gamma hg hh p) (cwC sources gamma hg hh p) (hNESite selector mask packets rows sources gamma hg hh p) _ _ _ _ hmeta hK4 H0 A0
    hd hAr hHr hAw hHw hlowE hF hfit hVR hVLR hRc hU0 hS hR hB (hbw b hb) hcap hqR hLw hTw h5 hLd hC82 hq2 hMs
    Kc K0 KH0 cnt hcnt hKlow hK278 hK279 hKhigh hcntA hcntH

theorem encWords_of_encOut2G (mode : Bool) (ph : Phase) (Rc b : ℕ) (H : Fin (USite selector xtra mask packets rows sources gamma hg hh p + 1) → ℕ)
    (A : Fin (USite selector xtra mask packets rows sources gamma hg hh p + 1) → List Bool) (h : InitS.EncOut2 (𝔭𝔩) Rc b H A) :
    SourceSteps.EncWords (d := 𝔡) (𝔭𝔩).hT Rc b H A := by
  obtain ⟨⟨e3, e7, e8, e9, e10, a2, a4, a5, eOld⟩, e012⟩ := h
  let en0 : CloseoutRowsEstimatorCoefficients.Stream.Entry := ⟨⟨0, 0, 0⟩, 0, 0⟩
  refine ⟨fun kk => ?_, fun en old => ⟨(e3 en old).1, (e7 en old).1, (e8 en old).1, (e9 en old).1, (e10 en old).1⟩,
    fun en xs => ⟨(a2 en xs).1, (a4 en xs).1, (a5 en xs).1⟩, ⟨[], by simp, ?_⟩⟩
  · have hk := kk.isLt
    by_cases h0 : kk.val < 3
    · exact (e012 kk h0).2
    · by_cases h4 : kk.val = 4 ∨ kk.val = 5
      · exact (eOld kk h4).2
      · have hc : kk = 3 ∨ kk = 6 ∨ kk = 7 ∨ kk = 8 ∨ kk = 9 ∨ kk = 10 ∨ kk = 11 ∨ kk = 12 := by
          have : kk.val = 3 ∨ kk.val = 6 ∨ kk.val = 7 ∨ kk.val = 8 ∨ kk.val = 9 ∨ kk.val = 10 ∨ kk.val = 11 ∨ kk.val = 12 := by
            omega
          rcases this with h | h | h | h | h | h | h | h
          · exact Or.inl (Fin.ext h)
          · exact Or.inr (Or.inl (Fin.ext h))
          · exact Or.inr (Or.inr (Or.inl (Fin.ext h)))
          · exact Or.inr (Or.inr (Or.inr (Or.inl (Fin.ext h))))
          · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (Fin.ext h)))))
          · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (Fin.ext h))))))
          · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (Fin.ext h)))))))
          · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Fin.ext h)))))))
        rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
        · exact (e3 en0 []).2
        · exact (e7 en0 []).2
        · exact (e8 en0 []).2
        · exact (e9 en0 []).2
        · exact (e10 en0 []).2
        · exact (a2 en0 []).2
        · exact (a4 en0 []).2
        · exact (a5 en0 []).2
  · rw [(eOld 5 (Or.inr rfl)).1]
    simp [ZeroPadding.pad]

/-- The site's query tapes on the first universe. -/
abbrev c15SG (mode : Bool) : Fin (USite selector xtra mask packets rows sources gamma hg hh p + 1) := cacheSite selector xtra mask packets rows sources gamma hg hh p _ (Nat.le_succ _) mode 15
abbrev c17SG (mode : Bool) : Fin (USite selector xtra mask packets rows sources gamma hg hh p + 1) := cacheSite selector xtra mask packets rows sources gamma hg hh p _ (Nat.le_succ _) mode 17
abbrev c18SG (mode : Bool) : Fin (USite selector xtra mask packets rows sources gamma hg hh p + 1) := cacheSite selector xtra mask packets rows sources gamma hg hh p _ (Nat.le_succ _) mode 18
abbrev q284SG : Fin (USite selector xtra mask packets rows sources gamma hg hh p + 1) := q284Site selector xtra mask packets rows sources gamma hg hh p _ (Nat.le_succ _)

def KcSiteG (mode : Bool) (x : Fin (USite selector xtra mask packets rows sources gamma hg hh p + 1)) : Prop :=
  KSite selector xtra mask packets rows sources gamma hg hh p _ (Nat.le_succ _) mode x ∧ x ≠ c15SG selector xtra mask packets rows sources gamma hg hh p mode ∧ x ≠ q284SG selector xtra mask packets rows sources gamma hg hh p

/-- **The entry kept words at the site** (`K0Site` at the init's strip words and `Vv = VvOf`). -/
def K0SG (mode : Bool) (n b : ℕ) (frameW qW : List Bool) (cdW : Fin 19 → List Bool) (NC : ℕ) : Fin (USite selector xtra mask packets rows sources gamma hg hh p + 1) → List Bool :=
  K0Site selector xtra mask packets rows sources gamma hg hh p _ (Nat.le_succ _) mode frameW qW cdW (StartGuard.resWSite selector mask packets rows sources gamma hg hh p mode n b) 𝔙 NC

/-- A tape of the entry kept set below `F` other than the rewind pair lies off the whole block `278..284`. -/
theorem kc_lowG (mode : Bool) (x : Fin (USite selector xtra mask packets rows sources gamma hg hh p + 1)) (hx : KcSiteG selector xtra mask packets rows sources gamma hg hh p mode x) (hF : x.val < (𝔡).F)
    (h8 : x.val ≠ 278) (h9 : x.val ≠ 279) : x.val < 278 ∨ 285 ≤ x.val := by
  obtain ⟨hk, -, hq⟩ := hx
  obtain ⟨hFn, ho, hB, hU, hres, hx25⟩ := site_nums selector xtra mask packets rows sources gamma hg hh p
  rcases hk with h | h | h | h | h | h
  · rcases h with h | h | ⟨j, hj⟩ | h
    · left; omega
    · exact absurd (Fin.ext (by rw [h]; rfl)) hq
    · have hc := cache_nums selector xtra mask packets rows sources gamma hg hh p mode j
      rw [← hj, cacheSite_val]; omega
    · unfold Dims.HiRes at h; omega
  · omega
  · omega
  · omega
  · omega
  · rw [h]; right; show 285 ≤ PCJda54a286946142d3_BranchPhases.offset sources p (kSite selector xtra mask packets rows sources gamma hg hh p) (rSite selector xtra mask packets rows sources gamma hg hh p) + 53; omega

/-- A tape of the entry kept set at or above `F` is a strip slot `sb + i`, `i < 22`. -/
theorem kc_highG (mode : Bool) (x : Fin (USite selector xtra mask packets rows sources gamma hg hh p + 1)) (hx : KcSiteG selector xtra mask packets rows sources gamma hg hh p mode x) (hF : (𝔡).F ≤ x.val) :
    ∃ i, i < initNR ∧ x.val = InitS.sb (𝔡) (DSite selector mask packets rows sources gamma hg hh p).se.extra (DSite selector mask packets rows sources gamma hg hh p).sp.extra (DSite selector mask packets rows sources gamma hg hh p).gW + i := by
  obtain ⟨hk, -, -⟩ := hx
  obtain ⟨hFn, ho, hB, hU, hres, hx25⟩ := site_nums selector xtra mask packets rows sources gamma hg hh p
  have hsb : InitS.sb (𝔡) (DSite selector mask packets rows sources gamma hg hh p).se.extra (DSite selector mask packets rows sources gamma hg hh p).sp.extra (DSite selector mask packets rows sources gamma hg hh p).gW =
      (𝔡).B + 29 + restPc (DSite selector mask packets rows sources gamma hg hh p).se.extra (DSite selector mask packets rows sources gamma hg hh p).sp.extra (DSite selector mask packets rows sources gamma hg hh p).gW := rfl
  rw [hsb]
  rcases hk with h | h | h | h | h | h
  · rcases h with h | h | ⟨j, hj⟩ | h
    · omega
    · omega
    · have hc := cache_nums selector xtra mask packets rows sources gamma hg hh p mode j
      rw [← hj, cacheSite_val] at hF; omega
    · unfold Dims.HiRes at h; exact ⟨x.val - ((𝔡).B + 29 + restPc (DSite selector mask packets rows sources gamma hg hh p).se.extra (DSite selector mask packets rows sources gamma hg hh p).sp.extra (DSite selector mask packets rows sources gamma hg hh p).gW), by
        show _ < 22; omega, by omega⟩
  · omega
  · omega
  · exact ⟨12, by decide, by omega⟩
  · exact ⟨x.val - ((𝔡).B + 29 + restPc (DSite selector mask packets rows sources gamma hg hh p).se.extra (DSite selector mask packets rows sources gamma hg hh p).sp.extra (DSite selector mask packets rows sources gamma hg hh p).gW), by show _ < 22; omega, by omega⟩
  · rw [h] at hF; change PCJda54a286946142d3_BranchPhases.offset sources p (kSite selector xtra mask packets rows sources gamma hg hh p) (rSite selector xtra mask packets rows sources gamma hg hh p) + 1155 ≤ PCJda54a286946142d3_BranchPhases.offset sources p (kSite selector xtra mask packets rows sources gamma hg hh p) (rSite selector xtra mask packets rows sources gamma hg hh p) + 53 at hF; omega

/-- The strip words of the entry kept set (`entry_initXE`'s `hKhigh`). -/
theorem k0s_highG (mode : Bool) (n b : ℕ) (frameW qW : List Bool) (cdW : Fin 19 → List Bool) (NC : ℕ)
    (x : Fin (USite selector xtra mask packets rows sources gamma hg hh p + 1)) (hx : KcSiteG selector xtra mask packets rows sources gamma hg hh p mode x) (hxF : (𝔡).F ≤ x.val) :
    ∃ i, i < initNR ∧ x.val = InitS.sb (𝔡) (DSite selector mask packets rows sources gamma hg hh p).se.extra (DSite selector mask packets rows sources gamma hg hh p).sp.extra (DSite selector mask packets rows sources gamma hg hh p).gW + i ∧
      K0SG selector xtra mask packets rows sources gamma hg hh p mode n b frameW qW cdW NC x = StartGuard.resWSite selector mask packets rows sources gamma hg hh p mode n b i := by
  obtain ⟨i, hi, hxv⟩ := kc_highG selector xtra mask packets rows sources gamma hg hh p mode x hx hxF
  refine ⟨i, hi, hxv, ?_⟩
  have hs := K0Site_strip selector xtra mask packets rows sources gamma hg hh p _ (Nat.le_succ _) mode frameW qW cdW (StartGuard.resWSite selector mask packets rows sources gamma hg hh p mode n b) 𝔙 NC x hxF
  have hsb : InitS.sb (𝔡) (DSite selector mask packets rows sources gamma hg hh p).se.extra (DSite selector mask packets rows sources gamma hg hh p).sp.extra (DSite selector mask packets rows sources gamma hg hh p).gW =
      (𝔡).B + 29 + restPc (DSite selector mask packets rows sources gamma hg hh p).se.extra (DSite selector mask packets rows sources gamma hg hh p).sp.extra (DSite selector mask packets rows sources gamma hg hh p).gW := rfl
  have hi' : x.val - ((𝔡).B + 29 + restPc (DSite selector mask packets rows sources gamma hg hh p).se.extra (DSite selector mask packets rows sources gamma hg hh p).sp.extra (DSite selector mask packets rows sources gamma hg hh p).gW) = i := by omega
  unfold K0SG
  rw [hs, hi']

/-- The rewind words of the entry kept set. -/
theorem k0s_rewG (mode : Bool) (n b : ℕ) (frameW qW : List Bool) (cdW : Fin 19 → List Bool) (NC : ℕ)
    (x : Fin (USite selector xtra mask packets rows sources gamma hg hh p + 1)) :
    (x.val = 278 → K0SG selector xtra mask packets rows sources gamma hg hh p mode n b frameW qW cdW NC x = List.replicate 𝔙 true) ∧
      (x.val = 279 → K0SG selector xtra mask packets rows sources gamma hg hh p mode n b frameW qW cdW NC x = List.replicate 𝔙 false) := by
  have hr1 : (Dims.rewind2Slots (eSite selector xtra mask packets rows sources gamma hg hh p).ext2.ext1.ext (Nat.le_succ (USite selector xtra mask packets rows sources gamma hg hh p)) 1).val = 278 := rfl
  have hr2 : (Dims.rewind2Slots (eSite selector xtra mask packets rows sources gamma hg hh p).ext2.ext1.ext (Nat.le_succ (USite selector xtra mask packets rows sources gamma hg hh p)) 2).val = 279 := rfl
  have hrew := K0Site_rew selector xtra mask packets rows sources gamma hg hh p _ (Nat.le_succ _) mode frameW qW cdW (StartGuard.resWSite selector mask packets rows sources gamma hg hh p mode n b) 𝔙 NC
  refine ⟨fun h8 => ?_, fun h9 => ?_⟩
  · have e : x = Dims.rewind2Slots (eSite selector xtra mask packets rows sources gamma hg hh p).ext2.ext1.ext (Nat.le_succ (USite selector xtra mask packets rows sources gamma hg hh p)) 1 := Fin.ext (by rw [h8, hr1])
    rw [e]; exact hrew.1
  · have e : x = Dims.rewind2Slots (eSite selector xtra mask packets rows sources gamma hg hh p).ext2.ext1.ext (Nat.le_succ (USite selector xtra mask packets rows sources gamma hg hh p)) 2 := Fin.ext (by rw [h9, hr2])
    rw [e]; exact hrew.2

/-- **A later entry's guard at the site**: the guard skips, and every fact carries over. -/
theorem guardLaterSiteG (mode : Bool) (ph : Phase) (n : ℕ)
    (hn : extraW selector xtra mask packets rows sources gamma hg hh p ≤ n)
    (Kc : Fin (USite selector xtra mask packets rows sources gamma hg hh p + 1) → Prop) (K0 : Fin (USite selector xtra mask packets rows sources gamma hg hh p + 1) → List Bool) (KH0 : Fin (USite selector xtra mask packets rows sources gamma hg hh p + 1) → ℕ)
    (b q' Mb Ms S Rw B U0 : ℕ) (H0 : Fin (USite selector xtra mask packets rows sources gamma hg hh p + 1) → ℕ) (A0 : Fin (USite selector xtra mask packets rows sources gamma hg hh p + 1) → List Bool)
    (hL : InitS.LaterEntry (𝔭𝔩) (eSite selector xtra mask packets rows sources gamma hg hh p) ℜ (InitS.Rk ℜ) Kc K0 KH0 (Fin.last _) b q' Mb Ms S Rw B U0 H0 A0) :
    Step (initW selector xtra mask packets rows sources gamma hg hh p mode ph) (0 + 2) H0 A0 H0 A0 := by
  have hq := qOnW_le_width selector mask packets rows xtra sources gamma hg hh p n hn
  obtain ⟨-, hR1, -⟩ := WinW.ext_windowsW selector mask packets rows sources gamma hg hh p 𝔮 hq
  exact InitS.entry_skipXE (𝔭𝔩) (hhSite selector xtra mask packets rows sources gamma hg hh p) initNR (by decide) (hESite selector xtra mask packets rows sources gamma hg hh p)
    𝔏 1 (SourceBudget.Params.cVcN selector sources gamma hg hh p) (sC sources gamma hg hh p) (rC sources gamma hg hh p)
    (pE sources gamma hg hh p) (pC sources gamma hg hh p) 3 1 (ldE sources gamma hg hh p) (ldC sources gamma hg hh p) (le_refl _)
    mode (SourceBudget.Params.tgOf sources gamma hg hh p) (dE sources gamma hg hh p) (dC sources gamma hg hh p)
    (cwE sources gamma hg hh p) (cwC sources gamma hg hh p) (hNESite selector mask packets rows sources gamma hg hh p) _ ℜ hR1 H0 A0 hL.1 hL.2.1

end site

end
end NearCubicWires.SourceSkeleton.GuardG
end


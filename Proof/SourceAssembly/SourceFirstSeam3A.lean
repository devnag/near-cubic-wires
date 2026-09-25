import Proof.SourceAssembly.SourceFirstFront3

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
open PCJ1fef9807c6954e94_Native PCJ515eaa990d75455b_FamilyInit
open NearCubicWires.RepairSource NearCubicWires.RepairSource.CloseoutFinal
open NearCubicWires.SourceRequest NearCubicWires.SourceRequest.FactorLoop
namespace NearCubicWires.SourceConstruction.Rest
noncomputable section
attribute [local irreducible] P1TopDownPaidPayload.tapes

theorem pad_tape0 (Rc : Nat) (h : 2 ≤ Rc) : ZeroPadding.pad Rc (UnaryTemplate.tape 0) = List.replicate Rc false := by
  have ht : UnaryTemplate.tape 0 = List.replicate 2 false := by simp [UnaryTemplate.tape]
  rw [ht]; exact pad_blank 2 Rc h

section concrete
variable (mask : MaskProducer) {selector : CyclicChoice.Laws}
  (packets : PCJc4297ab269d8423a_Source.PacketLibrary selector)
  (rows : PCJc4297ab269d8423a_Source.RowLibrary selector) (sources : EightSources) (res : Nat)
  {gamma : Real} (p : Parameters sources gamma) (k r : Nat)

set_option hygiene false in
local notation "𝔇" => dimsOf mask packets rows sources res p k r

/-- **The first prologue's front on the virtual bank** (part A1): after the outer clear of `Z` (real, at `Rk`), the
front `clear (clr2) ; clear (clrCur) ; E6` runs on the bank whose `Z` is blank at `Rc`; exported: the front's exit facts
and its frame back to the init's exit. -/
theorem first_front3_run {vE vP : Request → Nat}
    (se : PacketsGlue.RequestMeta.UnaryStage (decompositionOf sources) vE)
    (sp : PacketsGlue.RequestMeta.UnaryStage (decompositionOf sources) vP) {gW : Nat}
    (e : (𝔇).RestExt3 se.extra sp.extra gW) {V : Nat} (hV : (𝔇).U ≤ V)
    {q : Nat} (Rc Rk : Nat)
    (cnt c15 q284 c17 c18 : Fin V) (hcnt : cnt.val = (𝔇).U)
    (hlow : c15.val < (𝔇).F ∧ q284.val < (𝔇).F ∧ c17.val < (𝔇).F ∧ c18.val < (𝔇).F)
    (h1 : c15 ≠ q284) (h2 : c15 ≠ c17) (h3 : c15 ≠ c18) (h4 : q284 ≠ c17) (h5 : q284 ≠ c18) (h6 : c17 ≠ c18)
    (C : Nat) (wq : List Bool) (hwq : wq.length = C)
    (Hi : Fin V → Nat) (Ai : Fin V → List Bool)
    (K : Fin V → Prop) (K0 : Fin V → List Bool) (KH0 : Fin V → Nat)
    (Kc : Fin V → Prop) (w Mb Ms cW cQ cB cS S Rw B v U0 : Nat)
    (hC : InvC e hV Rc Rk Kc K0 KH0 cnt w q Mb Ms cW cQ cB cS S Rw B v U0 Hi Ai)
    (hKpos : ∀ x, K x → x.val < (𝔇).F ∨
      ((𝔇).B + 29 + restPc se.extra sp.extra gW ≤ x.val ∧ x ≠ Dims.hrT e hV 10 ∧ x ≠ Dims.hrT e hV 11))
    (hKsub : ∀ x, K x → x ≠ c15 → x ≠ q284 → Kc x) (hKcnt : ∀ x, K x → x ≠ cnt)
    (hK15 : K c15 → K0 c15 = List.replicate C false ∧ KH0 c15 = 0)
    (hK284 : K q284 → K0 q284 = wq ∧ KH0 q284 = 0)
    (hq : Ai c15 = wq) (hq17 : Ai c17 = List.replicate C true) (hq18 : Ai c18 = List.replicate (C+1) false)
    (h284 : (Ai q284).length ≤ C)
    (hH15 : Hi c15 = 0) (hH284 : Hi q284 = 0) (hH17 : Hi c17 = 0) (hH18 : Hi c18 = 0) :
    ∃ (Hf : Fin V → Nat) (Af : Fin V → List Bool),
      Step (firstFront se sp e.ext2 hV cnt c15 q284 c17 c18) ((4*Rc+7) + 1 + ((4*Rc+7) + 1 + ((2*C+4) + 1 + (2*C+4) + 1 + (2*C+4)))) (dockH (Dims.clrZ e hV) Hi (fun _ => 0))
        ((𝔇).virtZ se.extra sp.extra Rc (install (Dims.clrZ e hV) Ai (PCJ6e421fabe2aa4155_SourceClear.join (fun _ => List.replicate Rk false) (List.replicate Rk true) (List.replicate (Rk+2) false)))) Hf Af ∧
      (∀ x : Fin V, (𝔇).InClear se.extra sp.extra gW x.val → Af x = List.replicate Rc false ∧ Hf x = 0) ∧
      Af ((𝔇).rsT e.ext2.ext1 hV 2) = List.replicate Rc false ∧ Hf ((𝔇).rsT e.ext2.ext1 hV 2) = 0 ∧
      Af cnt = List.replicate Rc false ∧ Hf cnt = 0 ∧
      Af ((𝔇).scr hV 11) = List.replicate Rc true ∧ Hf ((𝔇).scr hV 11) = 0 ∧
      Af ((𝔇).scr hV 12) = List.replicate (Rc+2) false ∧ Hf ((𝔇).scr hV 12) = 0 ∧
      Af (Dims.hrT e hV 10) = List.replicate Rk true ∧ Hf (Dims.hrT e hV 10) = 0 ∧
      Af (Dims.hrT e hV 11) = List.replicate (Rk+2) false ∧ Hf (Dims.hrT e hV 11) = 0 ∧
      (∀ x, K x → Af x = K0 x ∧ Hf x = KH0 x) ∧
      (∀ i : Fin 5, i ≠ 2 → Af ((𝔇).rsT e.ext2.ext1 hV i) = Ai ((𝔇).rsT e.ext2.ext1 hV i) ∧
        Hf ((𝔇).rsT e.ext2.ext1 hV i) = Hi ((𝔇).rsT e.ext2.ext1 hV i)) ∧
      (∀ i : Fin 5, Af (Dims.mT e.ext2 hV i) = Ai (Dims.mT e.ext2 hV i) ∧
        Hf (Dims.mT e.ext2 hV i) = Hi (Dims.mT e.ext2 hV i)) ∧
      (∀ i : Fin 5, Af (Dims.rfT e.ext2 hV i) = Ai (Dims.rfT e.ext2 hV i) ∧
        Hf (Dims.rfT e.ext2 hV i) = Hi (Dims.rfT e.ext2 hV i)) ∧
      (∀ kk : Fin 13, Af (Dims.encT (d := 𝔇) hV kk) = Ai (Dims.encT (d := 𝔇) hV kk) ∧
        Hf (Dims.encT (d := 𝔇) hV kk) = Hi (Dims.encT (d := 𝔇) hV kk)) ∧
      (∀ x : Fin V, ¬ (𝔇).InClear se.extra sp.extra gW x.val → x ≠ (𝔇).scr hV 11 → x ≠ (𝔇).scr hV 12 →
        x ≠ (𝔇).rsT e.ext2.ext1 hV 2 → x ≠ cnt → x ≠ c15 → x ≠ q284 → x ≠ Dims.hrT e hV 10 → x ≠ Dims.hrT e hV 11 →
        Af x = Ai x ∧ Hf x = Hi x) := by
  classical
  have vG : (𝔇).G = (𝔇).F + (𝔇).rt + 13 := rfl
  have vB : (𝔇).B = (𝔇).G + (𝔇).R1 + 410 + (𝔇).w + (𝔇).tc := rfl
  have vp : (𝔇).pscr = (𝔇).R1 + 408 + (𝔇).w + (𝔇).tc := rfl
  have vPc : restPc se.extra sp.extra gW = 71 + se.extra + sp.extra + gW := rfl
  have vU : (𝔇).U = (𝔇).G + (𝔇).prepT := rfl
  have vprep : (𝔇).prepT = (𝔇).R1 + 410 + (𝔇).w + (𝔇).tc + (𝔇).res := rfl
  have hres2 := e.ext2.hres2
  have hres3 := e.hres3
  have hF := e.ext2.ext1.ext.hF
  have vrs : ∀ i : Fin 5, ((𝔇).rsT e.ext2.ext1 hV i).val = (𝔇).B + 19 + restPc se.extra sp.extra gW + i.val :=
    fun _ => rfl
  have vmT : ∀ i : Fin 5, (Dims.mT e.ext2 hV i).val = (𝔇).B + 19 + restPc se.extra sp.extra gW + 5 + i.val :=
    fun _ => rfl
  have vrf : ∀ i : Fin 5, (Dims.rfT e.ext2 hV i).val = (𝔇).B + 14 + i.val := fun _ => rfl
  have vscr : ∀ m : Fin 13, ((𝔇).scr hV m).val = (𝔇).G + (𝔇).R1 + 397 + (𝔇).w + (𝔇).tc + m.val := fun _ => rfl
  have vhr : ∀ i : Fin 12, (Dims.hrT e hV i).val = (𝔇).B + 29 + restPc se.extra sp.extra gW + i.val := fun _ => rfl
  have venc : ∀ kk : Fin 13, (Dims.encT (d := 𝔇) hV kk).val = (𝔇).F + (𝔇).rt + kk.val := fun _ => rfl
  have hiZ : ∀ x : Fin V, (x.val < (𝔇).B + 19 ∨ (𝔇).B + 19 + restPc se.extra sp.extra gW ≤ x.val) →
      ¬ (𝔇).InZ se.extra sp.extra x.val := by
    intro x hx hz; unfold SourceConstruction.Dims.InZ at hz; rw [vPc] at hx; omega
  have cntZ : ¬ (𝔇).InZ se.extra sp.extra cnt.val := hiZ cnt (Or.inr (by rw [hcnt, vU, vprep]; omega))
  have cnt10 : cnt ≠ Dims.hrT e hV 10 := ne_val (by rw [hcnt, vhr, vU, vprep]; omega)
  have cnt11 : cnt ≠ Dims.hrT e hV 11 := ne_val (by rw [hcnt, vhr, vU, vprep]; omega)
  -- 2. the virtual bank
  obtain ⟨Hc, hHc⟩ : ∃ Hc : Fin V → Nat, Hc = dockH (Dims.clrZ e hV) Hi (fun _ => 0) := ⟨_, rfl⟩
  obtain ⟨VV, hVV⟩ : ∃ VV : Fin V → List Bool,
      VV = (𝔇).virtZ se.extra sp.extra Rc (install (Dims.clrZ e hV) Ai (PCJ6e421fabe2aa4155_SourceClear.join (fun _ => List.replicate Rk false) (List.replicate Rk true) (List.replicate (Rk+2) false))) := ⟨_, rfl⟩
  have HcOff : ∀ x : Fin V, ¬ (𝔇).InZ se.extra sp.extra x.val → x ≠ Dims.hrT e hV 10 → x ≠ Dims.hrT e hV 11 →
      Hc x = Hi x := by
    intro x h1 h2 h3; rw [hHc]; exact dockH_other _ Hi _ x (Dims.clrZ_off e hV x h1 h2 h3)
  have VVOff : ∀ x : Fin V, ¬ (𝔇).InZ se.extra sp.extra x.val → x ≠ Dims.hrT e hV 10 → x ≠ Dims.hrT e hV 11 →
      VV x = Ai x := by
    intro x h1 h2 h3; rw [hVV]; simp only [SourceConstruction.Dims.virtZ, if_neg h1]
    exact install_other _ Ai _ x (Dims.clrZ_off e hV x h1 h2 h3)
  have VVZ : ∀ x : Fin V, (𝔇).InZ se.extra sp.extra x.val → VV x = List.replicate Rc false := by
    intro x hz; rw [hVV]; simp only [SourceConstruction.Dims.virtZ, if_pos hz]
  have HcZ : ∀ x : Fin V, (𝔇).InZ se.extra sp.extra x.val → Hc x = 0 := by
    intro x hz
    obtain ⟨kk, hk⟩ := Dims.clrZ_cover e hV x hz
    rw [hHc, ← hk, dockH_slot _ (Dims.clrZ_injective e hV)]
  -- low and high value facts
  have lowOff : ∀ x : Fin V, x.val < (𝔇).F → ¬ (𝔇).InZ se.extra sp.extra x.val ∧ x ≠ Dims.hrT e hV 10 ∧
      x ≠ Dims.hrT e hV 11 := fun x hx =>
    ⟨hiZ x (Or.inl (by omega)), ne_val (by rw [vhr]; omega), ne_val (by rw [vhr]; omega)⟩
  -- 3. the front on the virtual bank
  obtain ⟨Hf, Af, sFr, fClr, fcT, fcTH, fcA, fcH, fdrv, fdrvH, flg, flgH, f284, f284H, f15, f15H, fFr⟩ :=
    first_front_run hV se sp e.ext2 cnt c15 q284 c17 c18 hcnt hlow h1 h2 h3 h4 h5 h6 Rc C wq hwq Hc VV
      (fun x hx => by
        by_cases hz : (𝔇).InZ se.extra sp.extra x.val
        · rw [VVZ x hz]; simp
        · rw [VVOff x hz (clear_ne_hrT e hV hx 10) (clear_ne_hrT e hV hx 11)]
          exact hC.dirtA x (Or.inl hx) hz)
      (fun x hx => by
        by_cases hz : (𝔇).InZ se.extra sp.extra x.val
        · rw [HcZ x hz]; omega
        · rw [HcOff x hz (clear_ne_hrT e hV hx 10) (clear_ne_hrT e hV hx 11)]
          exact hC.dirtH x (Or.inl hx) hz)
      (by rw [VVOff _ (hiZ _ (Or.inr (by rw [vrs]; omega))) (Ne.symm (Dims.hrT_ne_rsT e hV 10 2))
          (Ne.symm (Dims.hrT_ne_rsT e hV 11 2))]; exact hC.curA)
      (by rw [HcOff _ (hiZ _ (Or.inr (by rw [vrs]; omega))) (Ne.symm (Dims.hrT_ne_rsT e hV 10 2))
          (Ne.symm (Dims.hrT_ne_rsT e hV 11 2))]; exact hC.curH)
      (by rw [VVOff _ cntZ cnt10 cnt11]; exact hC.cntA) (by rw [HcOff _ cntZ cnt10 cnt11]; exact hC.cntH)
      (by rw [VVOff _ (hiZ _ (Or.inl (by rw [vscr]; omega))) (Ne.symm (Dims.hrT_ne_scr e hV 10 11))
          (Ne.symm (Dims.hrT_ne_scr e hV 11 11))]; exact hC.drv)
      (by rw [HcOff _ (hiZ _ (Or.inl (by rw [vscr]; omega))) (Ne.symm (Dims.hrT_ne_scr e hV 10 11))
          (Ne.symm (Dims.hrT_ne_scr e hV 11 11))]; exact hC.drvH)
      (by rw [VVOff _ (hiZ _ (Or.inl (by rw [vscr]; omega))) (Ne.symm (Dims.hrT_ne_scr e hV 10 12))
          (Ne.symm (Dims.hrT_ne_scr e hV 11 12))]; exact hC.lg)
      (by rw [HcOff _ (hiZ _ (Or.inl (by rw [vscr]; omega))) (Ne.symm (Dims.hrT_ne_scr e hV 10 12))
          (Ne.symm (Dims.hrT_ne_scr e hV 11 12))]; exact hC.lgH)
      (by obtain ⟨z1, z2, z3⟩ := lowOff c15 hlow.1; rw [VVOff _ z1 z2 z3]; exact hq)
      (by obtain ⟨z1, z2, z3⟩ := lowOff c17 hlow.2.2.1; rw [VVOff _ z1 z2 z3]; exact hq17)
      (by obtain ⟨z1, z2, z3⟩ := lowOff c18 hlow.2.2.2; rw [VVOff _ z1 z2 z3]; exact hq18)
      (by obtain ⟨z1, z2, z3⟩ := lowOff q284 hlow.2.1; rw [VVOff _ z1 z2 z3]; exact h284)
      (by obtain ⟨z1, z2, z3⟩ := lowOff c15 hlow.1; rw [HcOff _ z1 z2 z3]; exact hH15)
      (by obtain ⟨z1, z2, z3⟩ := lowOff q284 hlow.2.1; rw [HcOff _ z1 z2 z3]; exact hH284)
      (by obtain ⟨z1, z2, z3⟩ := lowOff c17 hlow.2.2.1; rw [HcOff _ z1 z2 z3]; exact hH17)
      (by obtain ⟨z1, z2, z3⟩ := lowOff c18 hlow.2.2.2; rw [HcOff _ z1 z2 z3]; exact hH18)
  -- the front's frame back to the init's exit (off `Z`, off the outer driver/log)
  have fKeep : ∀ x : Fin V, ¬ (𝔇).InClear se.extra sp.extra gW x.val → x ≠ (𝔇).scr hV 11 → x ≠ (𝔇).scr hV 12 →
      x ≠ (𝔇).rsT e.ext2.ext1 hV 2 → x ≠ cnt → x ≠ c15 → x ≠ q284 → x ≠ Dims.hrT e hV 10 → x ≠ Dims.hrT e hV 11 →
      Af x = Ai x ∧ Hf x = Hi x := by
    intro x a1 a2 a3 a4 a5 a6 a7 a8 a9
    have hz : ¬ (𝔇).InZ se.extra sp.extra x.val := fun hz => a1 (Dims.InZ_clear hz)
    obtain ⟨b1, b2⟩ := fFr x a1 a2 a3 a4 a5 a6 a7
    exact ⟨b1.trans (VVOff x hz a8 a9), b2.trans (HcOff x hz a8 a9)⟩
  -- facts at the front's exit for the core
  have hiC : ∀ x : Fin V, (x.val < (𝔇).F ∨ ((𝔇).F + (𝔇).rt ≤ x.val ∧ x.val < (𝔇).G) ∨
      (𝔇).B + 19 + restPc se.extra sp.extra gW ≤ x.val) → ¬ (𝔇).InClear se.extra sp.extra gW x.val := by
    intro x hx; unfold SourceConstruction.Dims.InClear; omega
  have lowF : ∀ x : Fin V, x.val < (𝔇).F → x ≠ c15 → x ≠ q284 → Af x = Ai x ∧ Hf x = Hi x := by
    intro x hx a6 a7
    exact fKeep x (hiC x (Or.inl hx)) (ne_val (by rw [vscr]; omega)) (ne_val (by rw [vscr]; omega))
      (ne_val (by rw [vrs]; omega)) (ne_val (by rw [hcnt, vU, vprep]; omega)) a6 a7
      (ne_val (by rw [vhr]; omega)) (ne_val (by rw [vhr]; omega))
  have highF : ∀ x : Fin V, (𝔇).B + 19 + restPc se.extra sp.extra gW ≤ x.val →
      x ≠ (𝔇).rsT e.ext2.ext1 hV 2 → x ≠ cnt → x ≠ Dims.hrT e hV 10 → x ≠ Dims.hrT e hV 11 → Af x = Ai x ∧ Hf x = Hi x := by
    intro x hx a4 a5 a8 a9
    exact fKeep x (hiC x (Or.inr (Or.inr hx))) (ne_val (by rw [vscr]; omega)) (ne_val (by rw [vscr]; omega))
      a4 a5 (ne_val (by omega)) (ne_val (by omega)) a8 a9
  have encF : ∀ kk : Fin 13, Af (Dims.encT (d := 𝔇) hV kk) = Ai (Dims.encT (d := 𝔇) hV kk) ∧
      Hf (Dims.encT (d := 𝔇) hV kk) = Hi (Dims.encT (d := 𝔇) hV kk) := by
    intro kk
    have := kk.isLt
    exact fKeep _ (hiC _ (Or.inr (Or.inl ⟨by rw [venc]; omega, by rw [venc]; omega⟩)))
      (ne_val (by rw [venc, vscr]; omega)) (ne_val (by rw [venc, vscr]; omega)) (ne_val (by rw [venc, vrs]; omega))
      (ne_val (by rw [venc, hcnt, vU, vprep]; omega)) (ne_val (by rw [venc]; omega)) (ne_val (by rw [venc]; omega))
      (ne_val (by rw [venc, vhr]; omega)) (ne_val (by rw [venc, vhr]; omega))
  have rfF : ∀ i : Fin 5, Af (Dims.rfT e.ext2 hV i) = Ai (Dims.rfT e.ext2 hV i) ∧
      Hf (Dims.rfT e.ext2 hV i) = Hi (Dims.rfT e.ext2 hV i) := by
    intro i
    have := i.isLt
    exact fKeep _ (by unfold SourceConstruction.Dims.InClear; rw [vrf]; omega)
      (ne_val (by rw [vrf, vscr]; omega)) (ne_val (by rw [vrf, vscr]; omega)) (ne_val (by rw [vrf, vrs]; omega))
      (ne_val (by rw [vrf, hcnt, vU, vprep]; omega)) (ne_val (by rw [vrf]; omega)) (ne_val (by rw [vrf]; omega))
      (ne_val (by rw [vrf, vhr]; omega)) (ne_val (by rw [vrf, vhr]; omega))
  have rsF : ∀ i : Fin 5, i ≠ 2 → Af ((𝔇).rsT e.ext2.ext1 hV i) = Ai ((𝔇).rsT e.ext2.ext1 hV i) ∧
      Hf ((𝔇).rsT e.ext2.ext1 hV i) = Hi ((𝔇).rsT e.ext2.ext1 hV i) := by
    intro i hi
    exact highF _ (by rw [vrs]; omega)
      (fun h => hi (Dims.rsT_injective e.ext2.ext1 hV h)) (ne_val (by rw [vrs, hcnt, vU, vprep]; have := i.isLt; omega))
      (Ne.symm (Dims.hrT_ne_rsT e hV 10 i))
      (Ne.symm (Dims.hrT_ne_rsT e hV 11 i))
  have mF : ∀ i : Fin 5, Af (Dims.mT e.ext2 hV i) = Ai (Dims.mT e.ext2 hV i) ∧
      Hf (Dims.mT e.ext2 hV i) = Hi (Dims.mT e.ext2 hV i) := by
    intro i
    exact highF _ (by rw [vmT]; omega)
      (ne_val (by rw [vmT, vrs]; omega)) (ne_val (by rw [vmT, hcnt, vU, vprep]; have := i.isLt; omega))
      (Ne.symm (Dims.hrT_ne_mT e hV 10 i)) (Ne.symm (Dims.hrT_ne_mT e hV 11 i))
  have hKf : ∀ x, K x → Af x = K0 x ∧ Hf x = KH0 x := by
    intro x hx
    by_cases e15 : x = c15
    · subst e15; rw [f15, f15H]; exact ⟨(hK15 hx).1.symm, (hK15 hx).2.symm⟩
    by_cases e284 : x = q284
    · subst e284; rw [f284, f284H]; exact ⟨(hK284 hx).1.symm, (hK284 hx).2.symm⟩
    rcases hKpos x hx with hl | ⟨hh, h10, h11⟩
    · rw [(lowF x hl e15 e284).1, (lowF x hl e15 e284).2]; exact hC.kept x (hKsub x hx e15 e284)
    · rw [(highF x (by omega) (ne_val (by rw [vrs]; omega)) (hKcnt x hx) h10 h11).1,
        (highF x (by omega) (ne_val (by rw [vrs]; omega)) (hKcnt x hx) h10 h11).2]
      exact hC.kept x (hKsub x hx e15 e284)
  have VV10 : VV (Dims.hrT e hV 10) = List.replicate Rk true := by
    rw [hVV]; simp only [SourceConstruction.Dims.virtZ, if_neg (Dims.hrT_notZ e hV 10)]
    rw [← Dims.clrZ_driver e hV, install_slot _ (Dims.clrZ_injective e hV), PCJ6e421fabe2aa4155_SourceClear.join,
      Fin.addCases_left, Fin.addCases_right]
  have VV11 : VV (Dims.hrT e hV 11) = List.replicate (Rk+2) false := by
    rw [hVV]; simp only [SourceConstruction.Dims.virtZ, if_neg (Dims.hrT_notZ e hV 11)]
    rw [← Dims.clrZ_log e hV, install_slot _ (Dims.clrZ_injective e hV), PCJ6e421fabe2aa4155_SourceClear.join,
      Fin.addCases_right]
  have Hc10 : Hc (Dims.hrT e hV 10) = 0 := by
    rw [hHc, ← Dims.clrZ_driver e hV, dockH_slot _ (Dims.clrZ_injective e hV)]
  have Hc11 : Hc (Dims.hrT e hV 11) = 0 := by
    rw [hHc, ← Dims.clrZ_log e hV, dockH_slot _ (Dims.clrZ_injective e hV)]
  have hrF : ∀ i : Fin 12, Af (Dims.hrT e hV i) = VV (Dims.hrT e hV i) ∧ Hf (Dims.hrT e hV i) = Hc (Dims.hrT e hV i) :=
    fun i => fFr _ (Dims.hrT_notClear e hV i) (Dims.hrT_ne_scr e hV i 11) (Dims.hrT_ne_scr e hV i 12)
      (Dims.hrT_ne_rsT e hV i 2) (ne_val (by rw [vhr, hcnt, vU, vprep]; omega)) (ne_val (by rw [vhr]; omega))
      (ne_val (by rw [vhr]; omega))
  subst hHc hVV
  exact ⟨Hf, Af, sFr, fClr, fcT, fcTH, fcA, fcH, fdrv, fdrvH, flg, flgH,
    (hrF 10).1.trans VV10, (hrF 10).2.trans Hc10, (hrF 11).1.trans VV11, (hrF 11).2.trans Hc11,
    hKf, rsF, mF, rfF, encF, fKeep⟩

end concrete

end
end NearCubicWires.SourceConstruction.Rest
end

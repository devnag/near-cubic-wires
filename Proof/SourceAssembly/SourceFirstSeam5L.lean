import Proof.SourceAssembly.SourceFirstSeam4L
import Proof.SourceAssembly.SourceFirstCore5

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

section concrete
variable (mask : MaskProducer) {selector : CyclicChoice.Laws}
  (packets : PCJc4297ab269d8423a_Source.PacketLibrary selector)
  (rows : PCJc4297ab269d8423a_Source.RowLibrary selector) (sources : EightSources) (res : Nat)
  {gamma : Real} (p : Parameters sources gamma) (k r : Nat)

set_option hygiene false in
local notation "𝔇" => dimsOf mask packets rows sources res p k r

theorem first_pro5_runL {vE vP : Request → Nat}
    (se : PacketsGlue.RequestMeta.UnaryStage (decompositionOf sources) vE)
    (sp : PacketsGlue.RequestMeta.UnaryStage (decompositionOf sources) vP) {gW : Nat}
    (e : (𝔇).RestExt3 se.extra sp.extra gW) {V : Nat} (hV : (𝔇).U ≤ V)
    {si : Nat} (initM : Machine V si) {s7 : Nat} (g7M : Machine V s7) (g7cost : Nat → Nat)
    {q : Nat} {circuit : BooleanCircuit q} {pcpp : PointwisePCPP circuit}
    (coordinate : Fin (pcpp.systematicBits + pcpp.auxiliaryBits) →
      ComponentwisePolynomial.CircuitPolynomial (C10TotalDecode.Atom pcpp) 1)
    (ph : CloseoutRowsOriginalSchedule.Phase) (ci : Fin (2 ^ pcpp.clauseBits))
    (L target : Nat) (mode : Bool) (Rc Rk b : Nat)
    (layoutAt : ∀ m : Nat, Packets.Layout (decompositionOf sources)
      ((requestAt coordinate ph ci L target mode m).family (decompositionOf sources))
      (geometryOf selector (decompositionOf sources) (requestAt coordinate ph ci L target mode m)))
    (capsAt : Nat → RowCaps)
    (K : Fin V → Prop) (K0 : Fin V → List Bool) (KH0 : Fin V → Nat)
    (hG7 : ResidentRunH g7M g7cost mask (packets (decompositionOf sources)) (rows (decompositionOf sources) (printerOf sources))
      ((𝔇).maskSlots hV) ((𝔇).pslots hV) ((𝔇).slot hV) ((𝔇).ret hV) ((𝔇).scr hV 0) ((𝔇).scr hV 1)
      ((𝔇).familySlots hV) ((𝔇).poolSlots hV) (Dims.rewind2Slots e.ext2.ext1.ext hV)
      ((𝔇).scr hV 5) ((𝔇).scr hV 6) ((𝔇).scr hV 7) ((𝔇).scr hV 8) ((𝔇).scr hV 9) ((𝔇).scr hV 10)
      (Dims.lenTape e.ext2.ext1.ext hV) coordinate ph ci L target mode Rc b
      ((𝔇).pcT e.ext2.ext1 hV ⟨70, by unfold restPc; omega⟩)
      (fun i => (𝔇).pcT e.ext2.ext1 hV ⟨61 + i.val, by have := i.isLt; unfold restPc; omega⟩) layoutAt capsAt
      (Dims.Rpad (d := 𝔇) (eX := se.extra) (pX := sp.extra) (gW := gW) (V := V) Rc)
      (RestIn4 (𝔇) se.extra sp.extra gW Rc ((𝔇).pcT e.ext2.ext1 hV ⟨64, by unfold restPc; omega⟩) K K0 KH0)
      (fun x => OutV (𝔇) se.extra sp.extra gW x.val))
    (cnt c15 q284 c17 c18 : Fin V) (hcnt : cnt.val = (𝔇).U)
    (hlow : c15.val < (𝔇).F ∧ q284.val < (𝔇).F ∧ c17.val < (𝔇).F ∧ c18.val < (𝔇).F)
    (h1 : c15 ≠ q284) (h2 : c15 ≠ c17) (h3 : c15 ≠ c18) (h4 : q284 ≠ c17) (h5 : q284 ≠ c18) (h6 : c17 ≠ c18)
    (C : Nat) (wq : List Bool) (hwq : wq.length = C)
    (icost : Nat) (H0 Hi : Fin V → Nat) (A0 Ai : Fin V → List Bool) (hinit : Step initM icost H0 A0 Hi Ai)
    (Kc : Fin V → Prop) (w Mb Ms cW cQ cB cS S Rw B v U0 : Nat)
    (hC : InvC e hV Rc Rk Kc K0 KH0 cnt w q Mb Ms cW cQ cB cS S Rw B v U0 Hi Ai)
    (hRk : Rc ≤ Rk) (hRc4 : 4 ≤ Rc)
    (hSl : S + 2 ≤ Rc) (hRl : Rw + 2 ≤ Rc) (hBl : B + 2 ≤ Rc) (hvl : v + 2 ≤ Rc) (hUl : U0 ≤ Rc)
    (hMb : Mb ≤ Rc) (hMs : Ms ≤ Rc)
    (hKpos : ∀ x, K x → x.val < (𝔇).F ∨
      ((𝔇).B + 29 + restPc se.extra sp.extra gW ≤ x.val ∧ x ≠ Dims.hrT e hV 10 ∧ x ≠ Dims.hrT e hV 11))
    (hKsub : ∀ x, K x → x ≠ c15 → x ≠ q284 → Kc x) (hKcnt : ∀ x, K x → x ≠ cnt)
    (hK15 : K c15 → K0 c15 = List.replicate C false ∧ KH0 c15 = 0)
    (hK284 : K q284 → K0 q284 = wq ∧ KH0 q284 = 0)
    (hq : Ai c15 = wq) (hq17 : Ai c17 = List.replicate C true) (hq18 : Ai c18 = List.replicate (C+1) false)
    (h284 : (Ai q284).length ≤ C)
    (hH15 : Hi c15 = 0) (hH284 : Hi q284 = 0) (hH17 : Hi c17 = 0) (hH18 : Hi c18 = 0)
    (hN : (RepairSource.VerifierDecoding.CompareMachine.word (monomials coordinate ph ci).length).length ≤ Rc)
    (hlog : 2 * ((requestAt coordinate ph ci L target mode 0).input (decompositionOf sources)).length + 1 ≤ Rc)
    (he1 : 1 ≤ vE (requestAt coordinate ph ci L target mode 0))
    (hpw : (CloseoutRowsCountBinary.bits (vP (requestAt coordinate ph ci L target mode 0))).length ≤ w)
    (hfirst : vP (requestAt coordinate ph ci L target mode 0) * 2^(natBitLength (vE (requestAt coordinate ph ci L target mode 0))) < 2^w)
    (hsecond : vP (requestAt coordinate ph ci L target mode 0) * vE (requestAt coordinate ph ci L target mode 0) * 2^(q+1) < 2^w) :
    ∃ (H3 : Fin V → Nat) (A3 : Fin V → List Bool) (Av3 : Fin V → List Bool),
      Step (firstPro3 se sp e hV initM g7M cnt c15 q284 c17 c18) (icost + 1 + ((4*Rk+7) + 1 + (((4*Rc+7) + 1 + ((4*Rc+7) + 1 + ((2*C+4) + 1 + (2*C+4) + 1 + (2*C+4)))) + 1 + ((g7cost 0 + 1 + backCost se sp (requestAt coordinate ph ci L target mode 0) Rc w q (exactListWord (PCJ38fbfed565f64139_Cached.cacheArgs (decompositionOf sources) ((requestAt coordinate ph ci L target mode 0).family (decompositionOf sources))).gs).length Mb Ms) + 1 + (refreshCost Rc + 1 + ((2*Rc+4) + 1 + 1))))))
        H0 A0 H3 (fun y => ZeroPadding.pad ((𝔇).capZ se.extra sp.extra Rk y) (A3 y)) ∧
      (∀ x, A3 x = ZeroPadding.pad (Dims.Rpad (d := 𝔇) (eX := se.extra) (pX := sp.extra) (gW := gW) (V := V) Rc x)
        (Av3 x)) ∧
      Nonempty (Resident mask (packets (decompositionOf sources)) (rows (decompositionOf sources) (printerOf sources))
        ((𝔇).maskSlots hV) ((𝔇).pslots hV) ((𝔇).slot hV) ((𝔇).ret hV) ((𝔇).scr hV 0) ((𝔇).scr hV 1)
        ((𝔇).familySlots hV) ((𝔇).poolSlots hV) (Dims.rewind2Slots e.ext2.ext1.ext hV)
        ((𝔇).scr hV 5) ((𝔇).scr hV 6) ((𝔇).scr hV 7) ((𝔇).scr hV 8) ((𝔇).scr hV 9) ((𝔇).scr hV 10)
        (Dims.lenTape e.ext2.ext1.ext hV) (requestAt coordinate ph ci L target mode 0) (layoutAt 0) (capsAt 0) H3 Av3) ∧
      A3 (Dims.encT (d := 𝔇) hV 4) = ZeroPadding.pad Rc (RepairOrdinary.frame (SignedSortKey.binary w
        (vP (requestAt coordinate ph ci L target mode 0) * vE (requestAt coordinate ph ci L target mode 0) * 2^q))) ∧
      (∀ hm : 0 < (monomials coordinate ph ci).length, ∀ i : Fin 3,
        A3 (Dims.encT (d := 𝔇) hV ⟨i.val, by omega⟩) =
        ZeroPadding.pad Rc (RepairOrdinary.frame (CloseoutRowsEstimatorCoefficients.Stream.recordFields b
          (CloseoutFinalC10SupplierCalls.coefficientEstimate ((monomials coordinate ph ci)[0]).coefficient)
          0 0 ⟨i.val, by omega⟩))) ∧
      A3 (Dims.csSlots e.ext2.ext1.ext hV 1) = ZeroPadding.pad Rc (List.replicate (if 3 < (exactListWord (PCJ38fbfed565f64139_Cached.cacheArgs (decompositionOf sources) ((requestAt coordinate ph ci L target mode 0).family (decompositionOf sources))).gs).length then Mb else Ms) true) ∧
      A3 (Dims.csSlots e.ext2.ext1.ext hV 2) = ZeroPadding.pad Rc (List.replicate U0 true) ∧
      A3 (Dims.drvSlots e.ext2.ext1.ext hV 0) = ZeroPadding.pad Rc (UnaryTemplate.tape S) ∧
      A3 (Dims.drvSlots e.ext2.ext1.ext hV 1) = ZeroPadding.pad Rc (UnaryTemplate.tape Rw) ∧
      A3 (Dims.drvSlots e.ext2.ext1.ext hV 2) = ZeroPadding.pad Rc (UnaryTemplate.tape B) ∧
      A3 (Dims.drvSlots e.ext2.ext1.ext hV 4) = ZeroPadding.pad Rc (UnaryTemplate.tape v) ∧
      (∀ kk : Fin 16, 4 ≤ kk.val → A3 (Dims.csSlots e.ext2.ext1.ext hV kk) = ZeroPadding.pad Rc []) ∧
      (∀ kk : Fin 16, kk.val ≠ 0 → kk.val ≠ 3 → H3 (Dims.csSlots e.ext2.ext1.ext hV kk) = 0) ∧
      (∀ kk : Fin 7, (kk = 0 ∨ kk = 1 ∨ kk = 2 ∨ kk = 4) → H3 (Dims.drvSlots e.ext2.ext1.ext hV kk) = 1) ∧
      (∀ i : Fin (𝔇).rt, A3 (Dims.natSlots hV i) = List.replicate Rc false ∧ H3 (Dims.natSlots hV i) = 0) ∧
      (A3 ((𝔇).rsT e.ext2.ext1 hV 2) = ZeroPadding.pad Rc (UnaryTemplate.tape 0) ∧ H3 ((𝔇).rsT e.ext2.ext1 hV 2) = 0) ∧
      (A3 cnt = ZeroPadding.pad Rc (RepairSource.VerifierDecoding.CompareMachine.word (monomials coordinate ph ci).length) ∧
        H3 cnt = 1) ∧
      (A3 ((𝔇).scr hV 11) = List.replicate Rc true ∧ H3 ((𝔇).scr hV 11) = 0 ∧
        A3 ((𝔇).scr hV 12) = List.replicate (Rc+2) false ∧ H3 ((𝔇).scr hV 12) = 0) ∧
      (A3 (Dims.hrT e hV 10) = List.replicate Rk true ∧ H3 (Dims.hrT e hV 10) = 0 ∧
        A3 (Dims.hrT e hV 11) = List.replicate (Rk+2) false ∧ H3 (Dims.hrT e hV 11) = 0) ∧
      (∀ x, K x → A3 x = K0 x ∧ H3 x = KH0 x) ∧
      (∀ x : Fin V, ¬ (𝔇).InClear se.extra sp.extra gW x.val → x ≠ (𝔇).scr hV 11 → x ≠ (𝔇).scr hV 12 →
        ¬ OutV (𝔇) se.extra sp.extra gW x.val → x ≠ (𝔇).rsT e.ext2.ext1 hV 2 →
        ¬ ((𝔇).F + (𝔇).rt ≤ x.val ∧ x.val ≤ (𝔇).F + (𝔇).rt + 4 ∧ x.val ≠ (𝔇).F + (𝔇).rt + 3) →
        (∀ i, Dims.rfT e.ext2 hV i ≠ x) → x ≠ cnt → x ≠ c15 → x ≠ q284 →
        x ≠ Dims.hrT e hV 10 → x ≠ Dims.hrT e hV 11 → A3 x = Ai x ∧ H3 x = Hi x) ∧
      (∀ x : Fin V, (𝔇).InDirt se.extra sp.extra gW x.val → ¬ (𝔇).InZ se.extra sp.extra x.val →
        (A3 x).length ≤ Rc ∧ H3 x ≤ g7cost 0 + 1) ∧
      (∀ x : Fin V, (𝔇).InZ se.extra sp.extra x.val → (A3 x).length ≤ max Rc ((g7cost 0 + 1 + backCost se sp (requestAt coordinate ph ci L target mode 0) Rc w q (exactListWord (PCJ38fbfed565f64139_Cached.cacheArgs (decompositionOf sources) ((requestAt coordinate ph ci L target mode 0).family (decompositionOf sources))).gs).length Mb Ms) + 1) ∧ H3 x ≤ (g7cost 0 + 1 + backCost se sp (requestAt coordinate ph ci L target mode 0) Rc w q (exactListWord (PCJ38fbfed565f64139_Cached.cacheArgs (decompositionOf sources) ((requestAt coordinate ph ci L target mode 0).family (decompositionOf sources))).gs).length Mb Ms)) ∧
      (∀ kk : Fin 13, H3 (Dims.encT (d := 𝔇) hV kk) = Hi (Dims.encT (d := 𝔇) hV kk)) ∧
      (∀ x : Fin V, (Ai x).length ≤ (ZeroPadding.pad ((𝔇).capZ se.extra sp.extra Rk x) (A3 x)).length) ∧
      (∀ i : Fin 3, (A3 (Dims.encT (d := 𝔇) hV ⟨i.val, by omega⟩)).length ≤ Rc) := by
  revert hlog he1 hpw hfirst hsecond
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
  -- the masters
  let M : Fin 5 → List Bool := ![ZeroPadding.pad Rc (List.replicate U0 true), ZeroPadding.pad Rc (UnaryTemplate.tape S),
    ZeroPadding.pad Rc (UnaryTemplate.tape Rw), ZeroPadding.pad Rc (UnaryTemplate.tape B),
    ZeroPadding.pad Rc (UnaryTemplate.tape v)]
  have hMl : ∀ i, (M i).length = Rc := by
    intro i
    fin_cases i
    · exact pad_len_exact _ _ (by simp; omega)
    · exact pad_len_exact _ _ (by rw [tape_len]; omega)
    · exact pad_len_exact _ _ (by rw [tape_len]; omega)
    · exact pad_len_exact _ _ (by rw [tape_len]; omega)
    · exact pad_len_exact _ _ (by rw [tape_len]; omega)
  -- 1. the outer clear (real) of `Z`, and the front on the virtual bank (part A1)
  have outerStep : Step (RecoveryFocus.machine (Dims.clrZ e hV)
      (PCJ6e421fabe2aa4155_SourceClear.machine (71 + se.extra + sp.extra))) (4*Rk+7) Hi Ai
      (dockH (Dims.clrZ e hV) Hi (fun _ => 0)) (install (Dims.clrZ e hV) Ai (PCJ6e421fabe2aa4155_SourceClear.join (fun _ => List.replicate Rk false) (List.replicate Rk true) (List.replicate (Rk+2) false))) := by
    refine Refill.clear_on (Dims.clrZ e hV) (Dims.clrZ_injective e hV) Rk Hi Ai (fun kk => ?_) (fun kk => ?_)
      ?_ ?_ ?_ ?_
    · exact hC.zH _ (Dims.clrZ_in e hV kk)
    · exact hC.zA _ (Dims.clrZ_in e hV kk)
    · rw [Dims.clrZ_driver e hV]; exact hC.zDH
    · rw [Dims.clrZ_log e hV]; exact hC.zLH
    · rw [Dims.clrZ_driver e hV]; exact hC.zD
    · rw [Dims.clrZ_log e hV]; exact hC.zL
  obtain ⟨Hf, Af, sFr, fClr, fcT, fcTH, fcA, fcH, fdrv, fdrvH, flg, flgH, fz10, fz10H, fz11, fz11H, hKf, rsF, mF, rfF,
      encF, fKeep⟩ := first_front3_run mask packets rows sources res p k r se sp e hV Rc Rk cnt c15 q284 c17 c18 hcnt hlow
    h1 h2 h3 h4 h5 h6 C wq hwq Hi Ai K K0 KH0 Kc w Mb Ms cW cQ cB cS S Rw B v U0 hC hKpos hKsub hKcnt hK15 hK284
    hq hq17 hq18 h284 hH15 hH284 hH17 hH18
  have hiC : ∀ x : Fin V, (x.val < (𝔇).F ∨ ((𝔇).F + (𝔇).rt ≤ x.val ∧ x.val < (𝔇).G) ∨
      (𝔇).B + 19 + restPc se.extra sp.extra gW ≤ x.val) → ¬ (𝔇).InClear se.extra sp.extra gW x.val := by
    intro x hx; unfold SourceConstruction.Dims.InClear; omega
  have hMv : ∀ i, Af (Dims.mT e.ext2 hV i) = M i := by
    intro i
    rw [(mF i).1]
    fin_cases i
    · exact hC.mU
    · exact hC.mS
    · exact hC.mR
    · exact hC.mB
    · exact hC.mv
  -- 4. the core on the virtual bank (`first_core_run3`, no window)
  intro hlog he1 hpw hfirst hsecond
  obtain ⟨H3, A3, Av3, sCo, hM3, ⟨res3⟩, e4, e02, ecs1, ecs1H, fv, f0, f14, bl3, kcA, kcH, cFr, dirt3, dirtZ3, encH3, e02L⟩ :=
    first_core_run5 mask packets rows sources res p k r se sp e.ext2 hV g7M g7cost coordinate ph ci L target mode Rc b
      layoutAt capsAt K K0 KH0 hG7 w cW cQ Mb Ms cB cS M hMl cnt hcnt Hf Af
      fClr hKf
      (fun kk hk => by rw [(encF kk).1]; exact hC.encA kk hk)
      (fun kk hk => by rw [(encF kk).2]; exact hC.encH kk hk)
      (by rw [(rsF 3 (by decide)).1]; exact hC.wv) (by rw [(rsF 3 (by decide)).2]; exact hC.rsH 3 (by decide))
      (by rw [(rsF 4 (by decide)).1]; exact hC.qv) (by rw [(rsF 4 (by decide)).2]; exact hC.rsH 4 (by decide))
      fdrv fdrvH flg flgH
      (by rw [(rsF 0 (by decide)).1]; exact hC.big) (by rw [(rsF 0 (by decide)).2]; exact hC.rsH 0 (by decide))
      (by rw [(rsF 1 (by decide)).1]; exact hC.small) (by rw [(rsF 1 (by decide)).2]; exact hC.rsH 1 (by decide))
      hMv (fun i => by rw [(mF i).2]; exact hC.mH i)
      (fun i => by
        rw [(rfF i).1]; exact hC.dirtA _ (Or.inr (by rw [vrf]; omega)) (hiZ _ (Or.inl (by rw [vrf]; omega))))
      (fun i => by
        rw [(rfF i).2]; exact hC.dirtH _ (Or.inr (by rw [vrf]; omega)) (hiZ _ (Or.inl (by rw [vrf]; omega))))
      fcA fcH hN hlog he1 hpw hfirst hsecond hMb hMs
  clear hlog he1 hpw hfirst hsecond
  -- 5. the virtual front ; core, lifted by `Step.pad`, after the real outer clear and the init
  have sV : Step (Composition.machine (firstFront se sp e.ext2 hV cnt c15 q284 c17 c18)
      (firstCore se sp e.ext2 hV g7M cnt)) (((4*Rc+7) + 1 + ((4*Rc+7) + 1 + ((2*C+4) + 1 + (2*C+4) + 1 + (2*C+4)))) + 1 + ((g7cost 0 + 1 + backCost se sp (requestAt coordinate ph ci L target mode 0) Rc w q (exactListWord (PCJ38fbfed565f64139_Cached.cacheArgs (decompositionOf sources) ((requestAt coordinate ph ci L target mode 0).family (decompositionOf sources))).gs).length Mb Ms) + 1 + (refreshCost Rc + 1 + ((2*Rc+4) + 1 + 1)))) (dockH (Dims.clrZ e hV) Hi (fun _ => 0))
      ((𝔇).virtZ se.extra sp.extra Rc (install (Dims.clrZ e hV) Ai (PCJ6e421fabe2aa4155_SourceClear.join (fun _ => List.replicate Rk false) (List.replicate Rk true) (List.replicate (Rk+2) false)))) H3 A3 := sFr.seq sCo
  have sL := (sV.pad ((𝔇).capZ se.extra sp.extra Rk)).congr_in rfl (outer_exit_pad e hV Rc Rk hRk Ai)
  have s0 := outerStep
  have mono : ∀ x : Fin V, (Ai x).length ≤ (ZeroPadding.pad ((𝔇).capZ se.extra sp.extra Rk x) (A3 x)).length :=
    fun x => CloseoutFinalC10WorkerEmitShape.Step_length_le (s0.seq sL) x
  have sAll : Step (firstPro3 se sp e hV initM g7M cnt c15 q284 c17 c18)
      (icost + 1 + ((4*Rk+7) + 1 + (((4*Rc+7) + 1 + ((4*Rc+7) + 1 + ((2*C+4) + 1 + (2*C+4) + 1 + (2*C+4)))) + 1 + ((g7cost 0 + 1 + backCost se sp (requestAt coordinate ph ci L target mode 0) Rc w q (exactListWord (PCJ38fbfed565f64139_Cached.cacheArgs (decompositionOf sources) ((requestAt coordinate ph ci L target mode 0).family (decompositionOf sources))).gs).length Mb Ms) + 1 + (refreshCost Rc + 1 + ((2*Rc+4) + 1 + 1)))))) H0 A0 H3
      (fun y => ZeroPadding.pad ((𝔇).capZ se.extra sp.extra Rk y) (A3 y)) := hinit.seq (s0.seq sL)
  -- 6. the exports
  have csHigh : ∀ kk : Fin 16, 4 ≤ kk.val → (Dims.csSlots e.ext2.ext1.ext hV kk).val = (𝔇).B + (kk.val - 3) := by
    intro kk hk
    simp only [Dims.csSlots, Dims.csV]
    split_ifs <;> omega
  have cKeep : ∀ x : Fin V, ¬ (𝔇).InClear se.extra sp.extra gW x.val → x ≠ (𝔇).scr hV 11 → x ≠ (𝔇).scr hV 12 →
      ¬ OutV (𝔇) se.extra sp.extra gW x.val → x ≠ (𝔇).rsT e.ext2.ext1 hV 2 →
      ¬ ((𝔇).F + (𝔇).rt ≤ x.val ∧ x.val ≤ (𝔇).F + (𝔇).rt + 4 ∧ x.val ≠ (𝔇).F + (𝔇).rt + 3) →
      (∀ i, Dims.rfT e.ext2 hV i ≠ x) → x ≠ cnt → x ≠ c15 → x ≠ q284 →
      x ≠ Dims.hrT e hV 10 → x ≠ Dims.hrT e hV 11 → A3 x = Ai x ∧ H3 x = Hi x := by
    intro x a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12
    obtain ⟨b1, b2⟩ := cFr x a1 a4 a6 a7 a8
    obtain ⟨c1, c2⟩ := fKeep x a1 a2 a3 a5 a8 a9 a10 a11 a12
    exact ⟨b1.trans c1, b2.trans c2⟩
  have rs2C : ¬ (𝔇).InClear se.extra sp.extra gW ((𝔇).rsT e.ext2.ext1 hV 2).val := hiC _ (Or.inr (Or.inr (by rw [vrs]; omega)))
  have rs2O : ¬ OutV (𝔇) se.extra sp.extra gW ((𝔇).rsT e.ext2.ext1 hV 2).val := by unfold OutV; rw [vrs]; omega
  have rs2 := cFr ((𝔇).rsT e.ext2.ext1 hV 2) rs2C rs2O (by rw [vrs]; omega)
    (fun i h => by have := i.isLt; have := congrArg Fin.val h; rw [vrf, vrs] at this; omega)
    (ne_val (by rw [vrs, hcnt, vU, vprep]; omega))
  have scK : ∀ m : Fin 13, (m.val = 11 ∨ m.val = 12) → A3 ((𝔇).scr hV m) = Af ((𝔇).scr hV m) ∧
      H3 ((𝔇).scr hV m) = Hf ((𝔇).scr hV m) := by
    intro m hm
    exact cFr _ (by unfold SourceConstruction.Dims.InClear; rw [vscr]; omega) (by unfold OutV; rw [vscr]; omega)
      (by rw [vscr]; omega) (fun i h => by have := i.isLt; have := congrArg Fin.val h; rw [vrf, vscr] at this; omega)
      (ne_val (by rw [vscr, hcnt, vU, vprep]; omega))
  have hrK : ∀ i : Fin 12, A3 (Dims.hrT e hV i) = Af (Dims.hrT e hV i) ∧ H3 (Dims.hrT e hV i) = Hf (Dims.hrT e hV i) :=
    fun i => cFr _ (Dims.hrT_notClear e hV i) (Dims.hrT_notOut e hV i) (by rw [vhr]; omega)
      (fun m h => Dims.hrT_ne_rfT e hV i m h.symm) (ne_val (by rw [vhr, hcnt, vU, vprep]; omega))
  refine ⟨H3, A3, Av3, sAll, hM3, ⟨res3⟩, e4, e02, ecs1, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ⟨rs2.1.trans (fcT.trans (pad_tape0 Rc (by omega)).symm), rs2.2.trans fcTH⟩, ⟨kcA, kcH⟩,
    ⟨(scK 11 (Or.inl rfl)).1.trans fdrv, (scK 11 (Or.inl rfl)).2.trans fdrvH,
      (scK 12 (Or.inr rfl)).1.trans flg, (scK 12 (Or.inr rfl)).2.trans flgH⟩,
    ⟨(hrK 10).1.trans fz10, (hrK 10).2.trans fz10H, (hrK 11).1.trans fz11, (hrK 11).2.trans fz11H⟩,
    ?_, cKeep, dirt3, dirtZ3, ?_, mono, e02L⟩
  · rw [← Dims.rfT_cs2 e.ext2 hV, fv 0]; rfl
  · rw [← Dims.rfT_drv0 e.ext2 hV, fv 1]; rfl
  · rw [← Dims.rfT_drv1 e.ext2 hV, fv 2]; rfl
  · rw [← Dims.rfT_drv2 e.ext2 hV, fv 3]; rfl
  · rw [← Dims.rfT_drv4 e.ext2 hV, fv 4]; rfl
  · intro kk hk
    rw [(bl3 _ (Or.inr (by rw [csHigh kk hk]; have := kk.isLt; omega))).1]
    exact (Finish.blank_is_padded Rc).symm
  · intro kk h0 h3
    by_cases hh1 : kk.val = 1
    · have hk : kk = 1 := Fin.ext hh1
      rw [hk]; exact ecs1H
    by_cases hh2 : kk.val = 2
    · have hk : kk = 2 := Fin.ext hh2
      rw [hk, ← Dims.rfT_cs2 e.ext2 hV]; exact f0
    · have hk4 : 4 ≤ kk.val := by omega
      exact (bl3 _ (Or.inr (by rw [csHigh kk hk4]; have := kk.isLt; omega))).2
  · intro kk hk
    rcases hk with h | h | h | h <;> subst h
    · rw [← Dims.rfT_drv0 e.ext2 hV]; exact f14 1 (by decide)
    · rw [← Dims.rfT_drv1 e.ext2 hV]; exact f14 2 (by decide)
    · rw [← Dims.rfT_drv2 e.ext2 hV]; exact f14 3 (by decide)
    · rw [← Dims.rfT_drv4 e.ext2 hV]; exact f14 4 (by decide)
  · intro i
    exact bl3 _ (Or.inl (by simp only [Dims.natSlots]; have := i.isLt; omega))
  · intro x hx
    have hxc := hKcnt x hx
    rcases hKpos x hx with hl | ⟨hh, h10, h11⟩
    · obtain ⟨b1, b2⟩ := cFr x (hiC x (Or.inl hl)) (by unfold OutV; omega) (by omega)
        (fun i h => by have := i.isLt; have := congrArg Fin.val h; rw [vrf] at this; omega) hxc
      rw [b1, b2]; exact hKf x hx
    · obtain ⟨b1, b2⟩ := cFr x (hiC x (Or.inr (Or.inr (by omega)))) (by unfold OutV; omega) (by omega)
        (fun i h => by have := i.isLt; have := congrArg Fin.val h; rw [vrf] at this; omega) hxc
      rw [b1, b2]; exact hKf x hx
  · intro kk
    exact (encH3 kk).trans (encF kk).2

theorem first_seam5L {vE vP : Request → Nat}
    (se : PacketsGlue.RequestMeta.UnaryStage (decompositionOf sources) vE)
    (sp : PacketsGlue.RequestMeta.UnaryStage (decompositionOf sources) vP) {gW : Nat}
    (e : (𝔇).RestExt3 se.extra sp.extra gW) {V : Nat} (hV : (𝔇).U ≤ V)
    {si : Nat} (initM : Machine V si) {s7 : Nat} (g7M : Machine V s7) (g7cost : Nat → Nat)
    {q : Nat} {circuit : BooleanCircuit q} {pcpp : PointwisePCPP circuit}
    (coordinate : Fin (pcpp.systematicBits + pcpp.auxiliaryBits) →
      ComponentwisePolynomial.CircuitPolynomial (C10TotalDecode.Atom pcpp) 1)
    (ph : CloseoutRowsOriginalSchedule.Phase) (ci : Fin (2 ^ pcpp.clauseBits))
    (L target : Nat) (mode : Bool) (Rc Rk b : Nat)
    (layoutAt : ∀ m : Nat, Packets.Layout (decompositionOf sources)
      ((requestAt coordinate ph ci L target mode m).family (decompositionOf sources))
      (geometryOf selector (decompositionOf sources) (requestAt coordinate ph ci L target mode m)))
    (capsAt : Nat → RowCaps)
    (factsAt : ∀ m : Nat, ∀ row ∈ ((requestAt coordinate ph ci L target mode m).family (decompositionOf sources)).rows,
      Packets.PacketFacts (decompositionOf sources) ((requestAt coordinate ph ci L target mode m).family
        (decompositionOf sources)) (geometryOf selector (decompositionOf sources) (requestAt coordinate ph ci L target mode m))
        row)
    (goodAt : ∀ m : Nat, RowCaps.Good selector (decompositionOf sources) (printerOf sources)
      (requestAt coordinate ph ci L target mode m) (layoutAt m) (factsAt m) (capsAt m))
    (K : Fin V → Prop) (K0 : Fin V → List Bool) (KH0 : Fin V → Nat)
    (hG7 : ResidentRunH g7M g7cost mask (packets (decompositionOf sources)) (rows (decompositionOf sources) (printerOf sources))
      ((𝔇).maskSlots hV) ((𝔇).pslots hV) ((𝔇).slot hV) ((𝔇).ret hV) ((𝔇).scr hV 0) ((𝔇).scr hV 1)
      ((𝔇).familySlots hV) ((𝔇).poolSlots hV) (Dims.rewind2Slots e.ext2.ext1.ext hV)
      ((𝔇).scr hV 5) ((𝔇).scr hV 6) ((𝔇).scr hV 7) ((𝔇).scr hV 8) ((𝔇).scr hV 9) ((𝔇).scr hV 10)
      (Dims.lenTape e.ext2.ext1.ext hV) coordinate ph ci L target mode Rc b
      ((𝔇).pcT e.ext2.ext1 hV ⟨70, by unfold restPc; omega⟩)
      (fun i => (𝔇).pcT e.ext2.ext1 hV ⟨61 + i.val, by have := i.isLt; unfold restPc; omega⟩) layoutAt capsAt
      (Dims.Rpad (d := 𝔇) (eX := se.extra) (pX := sp.extra) (gW := gW) (V := V) Rc)
      (RestIn4 (𝔇) se.extra sp.extra gW Rc ((𝔇).pcT e.ext2.ext1 hV ⟨64, by unfold restPc; omega⟩) K K0 KH0)
      (fun x => OutV (𝔇) se.extra sp.extra gW x.val))
    (hminj : Function.Injective ((𝔇).maskSlots hV)) (hsinj : Function.Injective ((𝔇).pslots hV))
    (hfinj : Function.Injective ((𝔇).familySlots hV)) (hpinj : Function.Injective ((𝔇).poolSlots hV))
    (hrinj : Function.Injective (Dims.rewind2Slots e.ext2.ext1.ext hV))
    (hraw : (𝔇).pslots hV (packets (decompositionOf sources)).ordinary.program.outputTape = (𝔇).familySlots hV
      ((PCJ38fbfed565f64139_Ready.headerSlots (printerOf sources) (rowWork (rows (decompositionOf sources) (printerOf sources)).privateWork) 262).castAdd 1))
    (hpool : (𝔇).poolSlots hV 34 = (𝔇).familySlots hV
      ((PCJ38fbfed565f64139_Ready.headerSlots (printerOf sources) (rowWork (rows (decompositionOf sources) (printerOf sources)).privateWork) 0).castAdd 1))
    (hsrc : Dims.rewind2Slots e.ext2.ext1.ext hV 0 = (𝔇).familySlots hV
      ((PCJ38fbfed565f64139_Ready.descriptor (printerOf sources) (rowWork (rows (decompositionOf sources) (printerOf sources)).privateWork)).castAdd 1))
    (cnt c15 q284 c17 c18 : Fin V) (hcnt : cnt.val = (𝔇).U)
    (hlow : c15.val < (𝔇).F ∧ q284.val < (𝔇).F ∧ c17.val < (𝔇).F ∧ c18.val < (𝔇).F)
    (h1 : c15 ≠ q284) (h2 : c15 ≠ c17) (h3 : c15 ≠ c18) (h4 : q284 ≠ c17) (h5 : q284 ≠ c18) (h6 : c17 ≠ c18)
    (C : Nat) (wq : List Bool) (hwq : wq.length = C)
    (icost : Nat) (H0 Hi : Fin V → Nat) (A0 Ai : Fin V → List Bool) (hinit : Step initM icost H0 A0 Hi Ai)
    (Kc : Fin V → Prop) (w Mb Ms cW cQ cB cS S Rw B v U0 fuel0 : Nat)
    (hC : InvC e hV Rc Rk Kc K0 KH0 cnt w q Mb Ms cW cQ cB cS S Rw B v U0 Hi Ai)
    (hRk : Rc ≤ Rk) (hRc4 : 4 ≤ Rc)
    (hSl : S + 2 ≤ Rc) (hRl : Rw + 2 ≤ Rc) (hBl : B + 2 ≤ Rc) (hvl : v + 2 ≤ Rc) (hUl : U0 ≤ Rc)
    (hMb : Mb ≤ Rc) (hMs : Ms ≤ Rc)
    (hKpos : ∀ x, K x → x.val < (𝔇).F ∨
      ((𝔇).B + 29 + restPc se.extra sp.extra gW ≤ x.val ∧ x ≠ Dims.hrT e hV 10 ∧ x ≠ Dims.hrT e hV 11))
    (hKsub : ∀ x, K x → x ≠ c15 → x ≠ q284 → Kc x) (hKcnt : ∀ x, K x → x ≠ cnt)
    (hKfree : ∀ x, K x → Cycle.Free ((𝔇).slot hV) ((𝔇).maskSlots hV) ((𝔇).pslots hV) ((𝔇).poolSlots hV)
      ((𝔇).familySlots hV) (Dims.rewind2Slots e.ext2.ext1.ext hV) x ∨
      x = Dims.rewind2Slots e.ext2.ext1.ext hV 1 ∨ x = Dims.rewind2Slots e.ext2.ext1.ext hV 2)
    (hKr1 : K (Dims.rewind2Slots e.ext2.ext1.ext hV 1) →
      K0 (Dims.rewind2Slots e.ext2.ext1.ext hV 1) = List.replicate (capsAt 0).descriptorReserve true ∧
      KH0 (Dims.rewind2Slots e.ext2.ext1.ext hV 1) = 0)
    (hKr2 : K (Dims.rewind2Slots e.ext2.ext1.ext hV 2) →
      K0 (Dims.rewind2Slots e.ext2.ext1.ext hV 2) = List.replicate (capsAt 0).descriptorReserve false ∧
      KH0 (Dims.rewind2Slots e.ext2.ext1.ext hV 2) = 0)
    (hK15 : K c15 → K0 c15 = List.replicate C false ∧ KH0 c15 = 0)
    (hK284 : K q284 → K0 q284 = wq ∧ KH0 q284 = 0)
    (hq : Ai c15 = wq) (hq17 : Ai c17 = List.replicate C true) (hq18 : Ai c18 = List.replicate (C+1) false)
    (h284 : (Ai q284).length ≤ C)
    (hH15 : Hi c15 = 0) (hH284 : Hi q284 = 0) (hH17 : Hi c17 = 0) (hH18 : Hi c18 = 0)
    (hlong : ∀ x : Fin V, (𝔇).F ≤ x.val → x.val < (𝔇).U → Rc ≤ (Ai x).length)
    (hN : (RepairSource.VerifierDecoding.CompareMachine.word (monomials coordinate ph ci).length).length ≤ Rc)
    (hlog : 2 * ((requestAt coordinate ph ci L target mode 0).input (decompositionOf sources)).length + 1 ≤ Rc)
    (he1 : 1 ≤ vE (requestAt coordinate ph ci L target mode 0))
    (hpw : (CloseoutRowsCountBinary.bits (vP (requestAt coordinate ph ci L target mode 0))).length ≤ w)
    (hfirst : vP (requestAt coordinate ph ci L target mode 0) * 2^(natBitLength (vE (requestAt coordinate ph ci L target mode 0))) < 2^w)
    (hsecond : vP (requestAt coordinate ph ci L target mode 0) * vE (requestAt coordinate ph ci L target mode 0) * 2^(q+1) < 2^w)
    (hdescR : (capsAt 0).descriptorReserve ≤ Rc) (hL : (exactListWord (PCJ38fbfed565f64139_Cached.cacheArgs (decompositionOf sources) ((requestAt coordinate ph ci L target mode 0).family (decompositionOf sources))).gs).length + 3 ≤ Rc)
    (hfamH0 : ∀ i, r_inputH (printerOf sources) (dataList (decompositionOf sources) ((requestAt coordinate ph ci L target mode 0).family (decompositionOf sources)) (geometryOf selector (decompositionOf sources) (requestAt coordinate ph ci L target mode 0)) (layoutAt 0) (factsAt 0)) S Rw B (dataList (decompositionOf sources) ((requestAt coordinate ph ci L target mode 0).family (decompositionOf sources)) (geometryOf selector (decompositionOf sources) (requestAt coordinate ph ci L target mode 0)) (layoutAt 0) (factsAt 0)).length i + fuel0 + 1 ≤ Rc)
    (hwinI0 : g7cost 0 + 1 + (cycFuel mask (packets (decompositionOf sources)) (rows (decompositionOf sources) (printerOf sources)) (requestAt coordinate ph ci L target mode 0) (layoutAt 0) (factsAt 0) (capsAt 0) (if 3 < (exactListWord (PCJ38fbfed565f64139_Cached.cacheArgs (decompositionOf sources) ((requestAt coordinate ph ci L target mode 0).family (decompositionOf sources))).gs).length then Mb else Ms) U0 S Rw B v (0)) + 1 ≤ Rc)
    (hwinZ0 : (g7cost 0 + 1 + backCost se sp (requestAt coordinate ph ci L target mode 0) Rc w q (exactListWord (PCJ38fbfed565f64139_Cached.cacheArgs (decompositionOf sources) ((requestAt coordinate ph ci L target mode 0).family (decompositionOf sources))).gs).length Mb Ms) + 1 + (cycFuel mask (packets (decompositionOf sources)) (rows (decompositionOf sources) (printerOf sources)) (requestAt coordinate ph ci L target mode 0) (layoutAt 0) (factsAt 0) (capsAt 0) (if 3 < (exactListWord (PCJ38fbfed565f64139_Cached.cacheArgs (decompositionOf sources) ((requestAt coordinate ph ci L target mode 0).family (decompositionOf sources))).gs).length then Mb else Ms) U0 S Rw B v (0)) + 1 ≤ Rk)
    (firstCost : Nat)
    (hcost0 : (cycFuel mask (packets (decompositionOf sources)) (rows (decompositionOf sources) (printerOf sources)) (requestAt coordinate ph ci L target mode 0) (layoutAt 0) (factsAt 0) (capsAt 0) (if 3 < (exactListWord (PCJ38fbfed565f64139_Cached.cacheArgs (decompositionOf sources) ((requestAt coordinate ph ci L target mode 0).family (decompositionOf sources))).gs).length then Mb else Ms) U0 S Rw B v (icost + 1 + ((4*Rk+7) + 1 + (((4*Rc+7) + 1 + ((4*Rc+7) + 1 + ((2*C+4) + 1 + (2*C+4) + 1 + (2*C+4)))) + 1 + ((g7cost 0 + 1 + backCost se sp (requestAt coordinate ph ci L target mode 0) Rc w q (exactListWord (PCJ38fbfed565f64139_Cached.cacheArgs (decompositionOf sources) ((requestAt coordinate ph ci L target mode 0).family (decompositionOf sources))).gs).length Mb Ms) + 1 + (refreshCost Rc + 1 + ((2*Rc+4) + 1 + 1))))))) ≤ firstCost) :
    ∃ (H' : Fin V → Nat) (A' : Fin V → List Bool),
      (Cycle.cycleCode mask (packets (decompositionOf sources)) (rows (decompositionOf sources) (printerOf sources)) ((𝔇).maskSlots hV) hminj ((𝔇).pslots hV) hsinj ((𝔇).slot hV) ((𝔇).ret hV)
          ((𝔇).scr hV 0) ((𝔇).scr hV 1) ((𝔇).scr hV 2) ((𝔇).scr hV 3) ((𝔇).scr hV 4) ((𝔇).familySlots hV) hfinj
          ((𝔇).poolSlots hV) hpinj (Dims.rewind2Slots e.ext2.ext1.ext hV) hrinj hraw hpool hsrc
          ((𝔇).scr hV 5) ((𝔇).scr hV 6) ((𝔇).scr hV 7) ((𝔇).scr hV 8) ((𝔇).scr hV 9) ((𝔇).scr hV 10)
          (firstPro3 se sp e hV initM g7M cnt c15 q284 c17 c18) (Dims.csSlots e.ext2.ext1.ext hV) (Dims.natSlots hV) (Dims.drvSlots e.ext2.ext1.ext hV)).Prepared (dataList (decompositionOf sources) ((requestAt coordinate ph ci L target mode 0).family (decompositionOf sources)) (geometryOf selector (decompositionOf sources) (requestAt coordinate ph ci L target mode 0)) (layoutAt 0) (factsAt 0)) firstCost H0 H' A0 A' ∧
      (∀ i, H' (Dims.natSlots hV i) = r_inputH (printerOf sources) (dataList (decompositionOf sources) ((requestAt coordinate ph ci L target mode 0).family (decompositionOf sources)) (geometryOf selector (decompositionOf sources) (requestAt coordinate ph ci L target mode 0)) (layoutAt 0) (factsAt 0)) S Rw B (dataList (decompositionOf sources) ((requestAt coordinate ph ci L target mode 0).family (decompositionOf sources)) (geometryOf selector (decompositionOf sources) (requestAt coordinate ph ci L target mode 0)) (layoutAt 0) (factsAt 0)).length i) ∧
      (∀ i, A' (Dims.natSlots hV i) = ZeroPadding.pad Rc (r_inputT (printerOf sources) (dataList (decompositionOf sources) ((requestAt coordinate ph ci L target mode 0).family (decompositionOf sources)) (geometryOf selector (decompositionOf sources) (requestAt coordinate ph ci L target mode 0)) (layoutAt 0) (factsAt 0)) S Rw B
        (RowWidth.rw (if 3 < (exactListWord (PCJ38fbfed565f64139_Cached.cacheArgs (decompositionOf sources) ((requestAt coordinate ph ci L target mode 0).family (decompositionOf sources))).gs).length then Mb else Ms) U0 (exactListWord (PCJ38fbfed565f64139_Cached.cacheArgs (decompositionOf sources) ((requestAt coordinate ph ci L target mode 0).family (decompositionOf sources))).gs).length) v (dataList (decompositionOf sources) ((requestAt coordinate ph ci L target mode 0).family (decompositionOf sources)) (geometryOf selector (decompositionOf sources) (requestAt coordinate ph ci L target mode 0)) (layoutAt 0) (factsAt 0)).length i)) ∧
      (A' cnt = ZeroPadding.pad Rc (RepairSource.VerifierDecoding.CompareMachine.word (monomials coordinate ph ci).length) ∧
        H' cnt = 1) ∧
      InvR e hV Rc Rk K K0 KH0 0 w q Mb Ms cW cQ cB cS S Rw B v U0 fuel0 H' A' ∧
      (∀ kk : Fin 13, H' (Dims.encT (d := 𝔇) hV kk) = Hi (Dims.encT (d := 𝔇) hV kk)) ∧
      A' (Dims.encT (d := 𝔇) hV 4) = ZeroPadding.pad Rc (RepairOrdinary.frame (SignedSortKey.binary w
        (vP (requestAt coordinate ph ci L target mode 0) * vE (requestAt coordinate ph ci L target mode 0) * 2^q))) ∧
      (∀ hm : 0 < (monomials coordinate ph ci).length, ∀ i : Fin 3,
        A' (Dims.encT (d := 𝔇) hV ⟨i.val, by omega⟩) =
        ZeroPadding.pad Rc (RepairOrdinary.frame (CloseoutRowsEstimatorCoefficients.Stream.recordFields b
          (CloseoutFinalC10SupplierCalls.coefficientEstimate ((monomials coordinate ph ci)[0]).coefficient)
          0 0 ⟨i.val, by omega⟩))) ∧
      (∀ kk : Fin 13, (kk.val = 3 ∨ 5 ≤ kk.val) → A' (Dims.encT (d := 𝔇) hV kk) = Ai (Dims.encT (d := 𝔇) hV kk)) ∧
      (∀ x : Fin V, x.val < (𝔇).F → Cycle.Free ((𝔇).slot hV) ((𝔇).maskSlots hV) ((𝔇).pslots hV)
          ((𝔇).poolSlots hV) ((𝔇).familySlots hV) (Dims.rewind2Slots e.ext2.ext1.ext hV) x → x ≠ c15 → x ≠ q284 →
        H' x = Hi x ∧ A' x = Ai x) ∧
      (∀ x : Fin V, (𝔇).F ≤ x.val → x.val < (𝔇).U → Rc ≤ (A' x).length) ∧
      (∀ i : Fin 3, (A' (Dims.encT (d := 𝔇) hV ⟨i.val, by omega⟩)).length ≤ Rc) := by
  classical
  obtain ⟨H3, A3, Av3, realRun, hM3, ⟨res3⟩, e4, e02, ecs1, ecs2, edrv0, edrv1, edrv2, edrv4, hwork3, hcsH, hdrvH,
      hfam3, ⟨ecurT, ecurTH⟩, ⟨ecnt, ecntH⟩, ⟨a11, h11, a12, h12⟩, ⟨a10z, h10z, a11z, h11z⟩, eK, cKeep, dirt3, dirtZ3,
      encH3, mono, e02L⟩ :=
    first_pro5_runL mask packets rows sources res p k r se sp e hV initM g7M g7cost coordinate ph ci L target mode Rc Rk b
      layoutAt capsAt K K0 KH0 hG7 cnt c15 q284 c17 c18 hcnt hlow h1 h2 h3 h4 h5 h6 C wq hwq icost H0 Hi A0 Ai hinit
      Kc w Mb Ms cW cQ cB cS S Rw B v U0 hC hRk hRc4 hSl hRl hBl hvl hUl hMb hMs hKpos hKsub hKcnt hK15 hK284
      hq hq17 hq18 h284 hH15 hH284 hH17 hH18 hN hlog he1 hpw hfirst hsecond
  clear hlog he1 hpw hfirst hsecond hG7 hq hq17 hq18 h284 hH15 hH284 hH17 hH18 hinit
  obtain ⟨c0, hc0⟩ : ∃ c0 : Nat, c0 = (cycFuel mask (packets (decompositionOf sources)) (rows (decompositionOf sources) (printerOf sources)) (requestAt coordinate ph ci L target mode 0) (layoutAt 0) (factsAt 0) (capsAt 0) (if 3 < (exactListWord (PCJ38fbfed565f64139_Cached.cacheArgs (decompositionOf sources) ((requestAt coordinate ph ci L target mode 0).family (decompositionOf sources))).gs).length then Mb else Ms) U0 S Rw B v (0)) := ⟨_, rfl⟩
  obtain ⟨kc, hkc⟩ : ∃ kc : Nat, kc = (g7cost 0 + 1 + backCost se sp (requestAt coordinate ph ci L target mode 0) Rc w q (exactListWord (PCJ38fbfed565f64139_Cached.cacheArgs (decompositionOf sources) ((requestAt coordinate ph ci L target mode 0).family (decompositionOf sources))).gs).length Mb Ms) := ⟨_, rfl⟩
  have wI : g7cost 0 + 1 + c0 + 1 ≤ Rc := by rw [hc0]; exact hwinI0
  have wZ : kc + 1 + c0 + 1 ≤ Rk := by rw [hc0, hkc]; exact hwinZ0
  clear hwinI0 hwinZ0
  have vG : (𝔇).G = (𝔇).F + (𝔇).rt + 13 := rfl
  have vB : (𝔇).B = (𝔇).G + (𝔇).R1 + 410 + (𝔇).w + (𝔇).tc := rfl
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
  have vscr : ∀ m : Fin 13, ((𝔇).scr hV m).val = (𝔇).G + (𝔇).R1 + 397 + (𝔇).w + (𝔇).tc + m.val := fun _ => rfl
  have vhr : ∀ i : Fin 12, (Dims.hrT e hV i).val = (𝔇).B + 29 + restPc se.extra sp.extra gW + i.val := fun _ => rfl
  have venc : ∀ kk : Fin 13, (Dims.encT (d := 𝔇) hV kk).val = (𝔇).F + (𝔇).rt + kk.val := fun _ => rfl
  have vcs1 : (Dims.csSlots e.ext2.ext1.ext hV 1).val = (𝔇).B + 13 := rfl
  have vcs2 : (Dims.csSlots e.ext2.ext1.ext hV 2).val = (𝔇).B + 14 := rfl
  have vd0 : (Dims.drvSlots e.ext2.ext1.ext hV 0).val = (𝔇).B + 15 := rfl
  have vd1 : (Dims.drvSlots e.ext2.ext1.ext hV 1).val = (𝔇).B + 16 := rfl
  have vd2 : (Dims.drvSlots e.ext2.ext1.ext hV 2).val = (𝔇).B + 17 := rfl
  have vd4 : (Dims.drvSlots e.ext2.ext1.ext hV 4).val = (𝔇).B + 18 := rfl
  have hiZ : ∀ x : Fin V, (x.val < (𝔇).B + 19 ∨ (𝔇).B + 19 + restPc se.extra sp.extra gW ≤ x.val) →
      ¬ (𝔇).InZ se.extra sp.extra x.val := by
    intro x hx hz; unfold SourceConstruction.Dims.InZ at hz; rw [vPc] at hx; omega
  have encNZ : ∀ kk : Fin 13, ¬ (𝔇).InZ se.extra sp.extra (Dims.encT (d := 𝔇) hV kk).val := fun kk =>
    hiZ _ (Or.inl (by rw [venc]; omega))
  -- 1. the first cycle from the lifted prologue exit (as `refill_seam3`)
  have hres19 : 19 ≤ res := by
    have : (𝔇).res = res := rfl
    omega
  have wi := wiring mask packets rows sources res p k r hres19 hV
  have hA1low : ∀ x : Fin V, ¬ (𝔇).InZ se.extra sp.extra x.val →
      ZeroPadding.pad ((𝔇).capZ se.extra sp.extra Rk x) (A3 x) = A3 x := by
    intro x hz; simp only [SourceConstruction.Dims.capZ, if_neg hz, ZeroPadding.pad_zero]
  have A1eq : ∀ x : Fin V, x.val < (𝔇).B + 19 →
      (fun y => ZeroPadding.pad ((𝔇).capZ se.extra sp.extra Rk y) (A3 y)) x = A3 x :=
    fun x hx => hA1low x (hiZ x (Or.inl hx))
  have hMZ : ∀ x, (fun y => ZeroPadding.pad ((𝔇).capZ se.extra sp.extra Rk y) (A3 y)) x =
      ZeroPadding.pad ((𝔇).RZ se.extra sp.extra gW Rc Rk x) (Av3 x) := by
    intro x
    show ZeroPadding.pad ((𝔇).capZ se.extra sp.extra Rk x) (A3 x) = _
    rw [hM3 x, Uniform.pad_pad]
    simp only [SourceConstruction.Dims.capZ, SourceConstruction.Dims.RZ, Dims.Rpad]
    by_cases hz : (𝔇).InZ se.extra sp.extra x.val
    · rw [if_pos hz, if_pos hz, if_pos (Dims.InZ_clear (gW := gW) hz), max_eq_left hRk]
    · rw [if_neg hz, if_neg hz, Nat.zero_max]
  have hRZ1 : (𝔇).RZ se.extra sp.extra gW Rc Rk (Dims.rewind2Slots e.ext2.ext1.ext hV 1) = 0 := by
    have hv : (Dims.rewind2Slots e.ext2.ext1.ext hV 1).val = 278 := rfl
    have hz1 : ¬ (𝔇).InZ se.extra sp.extra (Dims.rewind2Slots e.ext2.ext1.ext hV 1).val := by
      unfold SourceConstruction.Dims.InZ; rw [hv]; omega
    have hc1 : ¬ (𝔇).InClear se.extra sp.extra gW (Dims.rewind2Slots e.ext2.ext1.ext hV 1).val := by
      unfold SourceConstruction.Dims.InClear; rw [hv]; omega
    simp only [SourceConstruction.Dims.RZ, Dims.Rpad, if_neg hz1, if_neg hc1]
  have hRZ2 : (𝔇).RZ se.extra sp.extra gW Rc Rk (Dims.rewind2Slots e.ext2.ext1.ext hV 2) = 0 := by
    have hv : (Dims.rewind2Slots e.ext2.ext1.ext hV 2).val = 279 := rfl
    have hz1 : ¬ (𝔇).InZ se.extra sp.extra (Dims.rewind2Slots e.ext2.ext1.ext hV 2).val := by
      unfold SourceConstruction.Dims.InZ; rw [hv]; omega
    have hc1 : ¬ (𝔇).InClear se.extra sp.extra gW (Dims.rewind2Slots e.ext2.ext1.ext hV 2).val := by
      unfold SourceConstruction.Dims.InClear; rw [hv]; omega
    simp only [SourceConstruction.Dims.RZ, Dims.Rpad, if_neg hz1, if_neg hc1]
  have csHigh : ∀ kk : Fin 16, 4 ≤ kk.val → (Dims.csSlots e.ext2.ext1.ext hV kk).val = (𝔇).B + (kk.val - 3) := by
    intro kk hk
    simp only [Dims.csSlots, Dims.csV]
    split_ifs <;> omega
  have famRes : ∀ i : Fin (𝔇).R1, i.val ≠ 0 → i.val ≠ 262 →
      SourceRequest.famReserve res3 ((𝔇).RZ se.extra sp.extra gW Rc Rk) i = Rc := by
    intro i h0 h262
    have hin := fam_in mask packets rows sources res p k r (eX := se.extra) (pX := sp.extra) (gW := gW) hV i
    have hnz : ¬ (𝔇).InZ se.extra sp.extra ((𝔇).familySlots hV i).val := by
      intro hz; unfold SourceConstruction.Dims.InZ at hz
      have := i.isLt; have := (𝔇).hsp
      simp only [SourceConstruction.Dims.familySlots, SourceConstruction.Dims.famV] at hz
      split_ifs at hz <;> omega
    have hb := res3.b_family i h0 h262
    have hlen := (dirt3 _ (Or.inl hin) hnz).1
    rw [hM3, hb] at hlen
    simp only [Dims.Rpad, if_pos hin, ZeroPadding.pad, List.length_append, List.length_replicate] at hlen
    simp only [SourceRequest.famReserve, if_neg h0, if_neg h262, SourceConstruction.Dims.RZ, if_neg hnz, Dims.Rpad,
      if_pos hin]
    exact max_eq_left (by omega)
  have hcnt' := famRes (Fin.last _) (Cycle.last_val (rows (decompositionOf sources) (printerOf sources))).1 (Cycle.last_val (rows (decompositionOf sources) (printerOf sources))).2
  have hdesc : max (SourceRequest.famReserve res3 ((𝔇).RZ se.extra sp.extra gW Rc Rk)
      (SLoad.Final.port (printerOf sources) (rows (decompositionOf sources) (printerOf sources)))) (capsAt 0).descriptorReserve = Rc := by
    rw [famRes _ (Cycle.port_val (rows (decompositionOf sources) (printerOf sources))).1 (Cycle.port_val (rows (decompositionOf sources) (printerOf sources))).2]
    exact max_eq_left hdescR
  obtain ⟨H', A', conj1, conj2, fH, fA, frC, rw1H, rw1A, rw2H, rw2A⟩ := Cycle.cycle_prepared_pad_rw mask (packets (decompositionOf sources)) (rows (decompositionOf sources) (printerOf sources))
    ((𝔇).maskSlots hV) hminj ((𝔇).pslots hV) hsinj ((𝔇).slot hV) ((𝔇).ret hV)
    ((𝔇).scr hV 0) ((𝔇).scr hV 1) ((𝔇).scr hV 2) ((𝔇).scr hV 3) ((𝔇).scr hV 4) ((𝔇).familySlots hV) hfinj
    ((𝔇).poolSlots hV) hpinj (Dims.rewind2Slots e.ext2.ext1.ext hV) hrinj hraw hpool hsrc
    ((𝔇).scr hV 5) ((𝔇).scr hV 6) ((𝔇).scr hV 7) ((𝔇).scr hV 8) ((𝔇).scr hV 9) ((𝔇).scr hV 10)
    (Dims.lenTape e.ext2.ext1.ext hV) (firstPro3 se sp e hV initM g7M cnt c15 q284 c17 c18) (Dims.csSlots e.ext2.ext1.ext hV)
    (Dims.natSlots hV) (Dims.drvSlots e.ext2.ext1.ext hV) wi H3 (fun y => ZeroPadding.pad ((𝔇).capZ se.extra sp.extra Rk y) (A3 y))
    Av3 ((𝔇).RZ se.extra sp.extra gW Rc Rk) hMZ (requestAt coordinate ph ci L target mode 0) (layoutAt 0) (factsAt 0) (capsAt 0)
    (goodAt 0) res3 hRZ1 hRZ2 (if 3 < (exactListWord (PCJ38fbfed565f64139_Cached.cacheArgs (decompositionOf sources) ((requestAt coordinate ph ci L target mode 0).family (decompositionOf sources))).gs).length then Mb else Ms) U0 Rc S Rw B v
    ((A1eq _ (by rw [vcs1]; omega)).trans ecs1)
    ((A1eq _ (by rw [vcs2]; omega)).trans ecs2)
    (fun kk hk => (A1eq _ (by rw [csHigh kk hk]; have := kk.isLt; omega)).trans (hwork3 kk hk))
    hcsH
    ((A1eq _ (by rw [vd0]; omega)).trans edrv0) ((A1eq _ (by rw [vd1]; omega)).trans edrv1)
    ((A1eq _ (by rw [vd2]; omega)).trans edrv2) ((A1eq _ (by rw [vd4]; omega)).trans edrv4) hdrvH
    (fun i _ => (A1eq _ (by
      have hrt : (𝔇).rt = r_tapes (printerOf sources) := rfl
      simp only [Dims.natSlots]; have := i.isLt; omega)).trans (hfam3 i).1)
    (fun i _ => (hfam3 i).2)
    hcnt' hdesc hL
  have sH : Step _ (cycFuel mask (packets (decompositionOf sources)) (rows (decompositionOf sources) (printerOf sources)) (requestAt coordinate ph ci L target mode 0) (layoutAt 0) (factsAt 0) (capsAt 0) (if 3 < (exactListWord (PCJ38fbfed565f64139_Cached.cacheArgs (decompositionOf sources) ((requestAt coordinate ph ci L target mode 0).family (decompositionOf sources))).gs).length then Mb else Ms) U0 S Rw B v (0)) H3 (fun y => ZeroPadding.pad ((𝔇).capZ se.extra sp.extra Rk y) (A3 y)) H' A' :=
    Cycle.prepared_step _ _ _ _ _ _ _ conj2
  have hP := Refill.prepared_mono _ _ hcost0 (conj1 _ _ _ realRun)
  clear hcost0 conj1 conj2 realRun hdescR hL famRes hcnt' hdesc hMZ hRZ1 hRZ2 wi
  -- 2. the exit facts
  have toA3 : ∀ x : Fin V, Cycle.Free ((𝔇).slot hV) ((𝔇).maskSlots hV) ((𝔇).pslots hV) ((𝔇).poolSlots hV)
        ((𝔇).familySlots hV) (Dims.rewind2Slots e.ext2.ext1.ext hV) x →
      (x.val < (𝔇).F ∨ ((𝔇).F + (𝔇).rt ≤ x.val ∧ x.val < (𝔇).G) ∨ (𝔇).B + 18 < x.val ∨
        ((𝔇).G + (𝔇).R1 ≤ x.val ∧ x.val < (𝔇).B)) →
      ¬ (𝔇).InZ se.extra sp.extra x.val → A' x = A3 x ∧ H' x = H3 x := by
    intro x hf hx hz
    obtain ⟨o1, o2, o3⟩ := off_cycle e.ext2.ext1.ext hV x hx
    obtain ⟨a, b'⟩ := frC x hf o1 o2 o3
    exact ⟨b'.trans (hA1low x hz), a⟩
  have keepAll : ∀ x : Fin V, Cycle.Free ((𝔇).slot hV) ((𝔇).maskSlots hV) ((𝔇).pslots hV) ((𝔇).poolSlots hV)
        ((𝔇).familySlots hV) (Dims.rewind2Slots e.ext2.ext1.ext hV) x →
      (x.val < (𝔇).F ∨ ((𝔇).F + (𝔇).rt ≤ x.val ∧ x.val < (𝔇).G) ∨
        (𝔇).B + 19 + restPc se.extra sp.extra gW ≤ x.val) →
      ¬ ((𝔇).F + (𝔇).rt ≤ x.val ∧ x.val ≤ (𝔇).F + (𝔇).rt + 4 ∧ x.val ≠ (𝔇).F + (𝔇).rt + 3) →
      x ≠ (𝔇).rsT e.ext2.ext1 hV 2 → x ≠ cnt → x ≠ c15 → x ≠ q284 → x ≠ Dims.hrT e hV 10 → x ≠ Dims.hrT e hV 11 →
      A' x = Ai x ∧ H' x = Hi x := by
    intro x hf hlo henc h2 hc hc15 hq284 h10 h11
    obtain ⟨c1, c2, c3, c4, c5, c6, c7⟩ := frame_region e hV x hlo
    obtain ⟨a1, a2⟩ := toA3 x hf c7 c5
    obtain ⟨b1, b2⟩ := cKeep x c1 c2 c3 c4 h2 henc c6 hc hc15 hq284 h10 h11
    exact ⟨a1.trans b1, a2.trans b2⟩
  have encA3 : ∀ kk : Fin 13, A' (Dims.encT (d := 𝔇) hV kk) = A3 (Dims.encT (d := 𝔇) hV kk) ∧
      H' (Dims.encT (d := 𝔇) hV kk) = H3 (Dims.encT (d := 𝔇) hV kk) := fun kk =>
    toA3 _ (free_mid e.ext2.ext1.ext hV _ (enc_region e hV kk).1 (enc_region e hV kk).2.1)
      (Or.inr (Or.inl ⟨(enc_region e hV kk).1, (enc_region e hV kk).2.1⟩)) (encNZ kk)
  have cntA := toA3 cnt (Dims.free_res e.ext2.ext1.ext hV cnt (by rw [hcnt, vU, vprep]; omega))
    (Or.inr (Or.inr (Or.inl (by rw [hcnt, vU, vprep]; omega)))) (hiZ cnt (Or.inr (by rw [hcnt, vU, vprep]; omega)))
  have rsH19 : ∀ i : Fin 5, (𝔇).B + 19 + restPc se.extra sp.extra gW ≤ ((𝔇).rsT e.ext2.ext1 hV i).val :=
    fun i => Nat.le_add_right _ _
  have mH19 : ∀ i : Fin 5, (𝔇).B + 19 + restPc se.extra sp.extra gW ≤ (Dims.mT e.ext2 hV i).val :=
    fun i => le_trans (Nat.le_add_right _ 5) (Nat.le_add_right _ _)
  have resid : ∀ x : Fin V, (𝔇).B + 19 + restPc se.extra sp.extra gW ≤ x.val → x ≠ (𝔇).rsT e.ext2.ext1 hV 2 → x ≠ cnt →
      x ≠ Dims.hrT e hV 10 → x ≠ Dims.hrT e hV 11 → A' x = Ai x ∧ H' x = Hi x := by
    intro x hx h2 hc h10 h11
    obtain ⟨_, _, _, g4, g5, _⟩ := high_region x hx
    exact keepAll x (Dims.free_res e.ext2.ext1.ext hV x g4) (Or.inr (Or.inr hx)) g5 h2 hc
      (ne_val (by have := hlow.1; omega)) (ne_val (by have := hlow.2.1; omega)) h10 h11
  have rsNe2 : ∀ i : Fin 5, i ≠ 2 → (𝔇).rsT e.ext2.ext1 hV i ≠ (𝔇).rsT e.ext2.ext1 hV 2 := fun i hi h =>
    hi (Dims.rsT_injective e.ext2.ext1 hV h)
  have rsNc : ∀ i : Fin 5, (𝔇).rsT e.ext2.ext1 hV i ≠ cnt := fun i => ne_val (by rw [vrs, hcnt, vU, vprep]; omega)
  have mNe2 : ∀ i : Fin 5, Dims.mT e.ext2 hV i ≠ (𝔇).rsT e.ext2.ext1 hV 2 := fun i h => by
    have := congrArg Fin.val h; rw [vmT, vrs] at this; omega
  have mNc : ∀ i : Fin 5, Dims.mT e.ext2 hV i ≠ cnt := fun i => ne_val (by rw [vmT, hcnt, vU, vprep]; omega)
  have sc : ∀ m : Fin 13, 5 ≤ m.val → A' ((𝔇).scr hV m) = A3 ((𝔇).scr hV m) ∧
      H' ((𝔇).scr hV m) = H3 ((𝔇).scr hV m) := fun m hm =>
    toA3 _ (free_scr mask packets rows sources res p k r e.ext2.ext1.ext hV m hm)
      (Or.inr (Or.inr (Or.inr (by rw [vscr]; omega)))) (hiZ _ (Or.inl (by rw [vscr]; omega)))
  have curA := toA3 ((𝔇).rsT e.ext2.ext1 hV 2) (Dims.free_res e.ext2.ext1.ext hV _ (high_region _ (rsH19 2)).2.2.2.1)
    (Or.inr (Or.inr (Or.inl (by rw [vrs]; omega)))) (hiZ _ (Or.inr (rsH19 2)))
  have hrA : ∀ i : Fin 12, A' (Dims.hrT e hV i) = A3 (Dims.hrT e hV i) ∧ H' (Dims.hrT e hV i) = H3 (Dims.hrT e hV i) :=
    fun i => toA3 _ (Dims.hrT_free e hV i) (Or.inr (Or.inr (Or.inl (by rw [vhr]; omega)))) (Dims.hrT_notZ e hV i)
  have lenOut : ∀ x : Fin V, (𝔇).F ≤ x.val → x.val < (𝔇).U → Rc ≤ (A' x).length := fun x h1 h2 =>
    ((hlong x h1 h2).trans (mono x)).trans (CloseoutFinalC10WorkerEmitShape.Step_length_le sH x)
  refine ⟨H', A', hP, fH, fA, ⟨cntA.1.trans ecnt, cntA.2.trans ecntH⟩, ?_, ?_, ?_, ?_, ?_, ?_, lenOut, ?_⟩
  · -- `InvR 0`
    refine ⟨?_, curA.1.trans ecurT, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
      (sc 11 (by decide)).1.trans a11, (sc 11 (by decide)).2.trans h11,
      (sc 12 (by decide)).1.trans a12, (sc 12 (by decide)).2.trans h12,
      (hrA 10).1.trans a10z, (hrA 10).2.trans h10z, (hrA 11).1.trans a11z, (hrA 11).2.trans h11z,
      ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro x hx
      rcases hKfree x hx with hfr | hr1 | hr2
      · rcases hKpos x hx with hl | ⟨hh, h10, h11⟩
        · have hfx : x.val < (𝔇).B + 19 := by omega
          obtain ⟨o1, o2, o3⟩ := off_cycle e.ext2.ext1.ext hV x (Or.inl hl)
          obtain ⟨a, b'⟩ := frC x hfr o1 o2 o3
          rw [a, b'.trans (A1eq x hfx)]
          exact eK x hx
        · obtain ⟨k1, _⟩ := kept_high e hV x hh
          obtain ⟨_, _, _, _, _, _⟩ := high_region x k1
          obtain ⟨a1, a2⟩ := toA3 x hfr (Or.inr (Or.inr (Or.inl (by omega)))) (hiZ x (Or.inr k1))
          rw [a1, a2]; exact eK x hx
      · subst hr1
        exact ⟨rw1A.trans (hKr1 hx).1.symm, rw1H.trans (hKr1 hx).2.symm⟩
      · subst hr2
        exact ⟨rw2A.trans (hKr2 hx).1.symm, rw2H.trans (hKr2 hx).2.symm⟩
    · rw [(resid _ (rsH19 0) (rsNe2 0 (by decide)) (rsNc 0) (Ne.symm (Dims.hrT_ne_rsT e hV 10 0))
        (Ne.symm (Dims.hrT_ne_rsT e hV 11 0))).1]; exact hC.big
    · rw [(resid _ (rsH19 1) (rsNe2 1 (by decide)) (rsNc 1) (Ne.symm (Dims.hrT_ne_rsT e hV 10 1))
        (Ne.symm (Dims.hrT_ne_rsT e hV 11 1))).1]; exact hC.small
    · rw [(resid _ (rsH19 3) (rsNe2 3 (by decide)) (rsNc 3) (Ne.symm (Dims.hrT_ne_rsT e hV 10 3))
        (Ne.symm (Dims.hrT_ne_rsT e hV 11 3))).1]; exact hC.wv
    · rw [(resid _ (rsH19 4) (rsNe2 4 (by decide)) (rsNc 4) (Ne.symm (Dims.hrT_ne_rsT e hV 10 4))
        (Ne.symm (Dims.hrT_ne_rsT e hV 11 4))).1]; exact hC.qv
    · intro i
      by_cases h2 : i = 2
      · subst h2; exact curA.2.trans ecurTH
      · rw [(resid _ (rsH19 i) (rsNe2 i h2) (rsNc i) (Ne.symm (Dims.hrT_ne_rsT e hV 10 i))
          (Ne.symm (Dims.hrT_ne_rsT e hV 11 i))).2]; exact hC.rsH i h2
    · rw [(resid _ (mH19 0) (mNe2 0) (mNc 0) (Ne.symm (Dims.hrT_ne_mT e hV 10 0))
        (Ne.symm (Dims.hrT_ne_mT e hV 11 0))).1]; exact hC.mU
    · rw [(resid _ (mH19 1) (mNe2 1) (mNc 1) (Ne.symm (Dims.hrT_ne_mT e hV 10 1))
        (Ne.symm (Dims.hrT_ne_mT e hV 11 1))).1]; exact hC.mS
    · rw [(resid _ (mH19 2) (mNe2 2) (mNc 2) (Ne.symm (Dims.hrT_ne_mT e hV 10 2))
        (Ne.symm (Dims.hrT_ne_mT e hV 11 2))).1]; exact hC.mR
    · rw [(resid _ (mH19 3) (mNe2 3) (mNc 3) (Ne.symm (Dims.hrT_ne_mT e hV 10 3))
        (Ne.symm (Dims.hrT_ne_mT e hV 11 3))).1]; exact hC.mB
    · rw [(resid _ (mH19 4) (mNe2 4) (mNc 4) (Ne.symm (Dims.hrT_ne_mT e hV 10 4))
        (Ne.symm (Dims.hrT_ne_mT e hV 11 4))).1]; exact hC.mv
    · intro i
      rw [(resid _ (mH19 i) (mNe2 i) (mNc i) (Ne.symm (Dims.hrT_ne_mT e hV 10 i))
        (Ne.symm (Dims.hrT_ne_mT e hV 11 i))).2]; exact hC.mH i
    · intro x hx hz
      obtain ⟨d1, d2⟩ := dirt3 x hx hz
      have b1 := (dirty_bound sH x).1
      have e1 := hA1low x hz
      simp only [e1] at b1
      rw [← hc0] at b1
      omega
    · intro x hx hz
      obtain ⟨_, d2⟩ := dirt3 x hx hz
      have b2 := (dirty_bound sH x).2
      rw [← hc0] at b2
      omega
    · intro x h1' h2'
      have hx : x = Dims.natSlots hV ⟨x.val - (𝔇).F, by omega⟩ := Fin.ext (by simp only [Dims.natSlots]; omega)
      rw [hx, fH]
      exact hfamH0 _
    · intro x hz
      obtain ⟨d1, d2⟩ := dirtZ3 x hz
      have b1 := (dirty_bound sH x).1
      have e1 : ZeroPadding.pad ((𝔇).capZ se.extra sp.extra Rk x) (A3 x) = ZeroPadding.pad Rk (A3 x) := by
        simp only [SourceConstruction.Dims.capZ, if_pos hz]
      simp only [e1, pad_len_max] at b1
      rw [← hc0] at b1
      rw [← hkc] at d1 d2
      omega
    · intro x hz
      obtain ⟨_, d2⟩ := dirtZ3 x hz
      have b2 := (dirty_bound sH x).2
      rw [← hc0] at b2
      rw [← hkc] at d2
      omega
    · intro kk hk
      rw [(encA3 kk).2, encH3 kk]
      exact hC.encH kk hk
  · -- (E1)
    intro kk
    exact (encA3 kk).2.trans (encH3 kk)
  · exact (encA3 4).1.trans e4
  · intro hm i
    exact (encA3 _).1.trans (e02 hm i)
  · -- (E3) the other `encT` tapes
    intro kk hk
    obtain ⟨n1, n2, n3, n4, n5⟩ := enc_region e hV kk
    have := kk.isLt
    exact (keepAll _ (free_mid e.ext2.ext1.ext hV _ n1 n2) (Or.inr (Or.inl ⟨n1, n2⟩)) (n5 hk) n3
      (ne_val (by rw [venc, hcnt, vU, vprep]; omega)) (ne_val (by rw [venc]; have := hlow.1; omega))
      (ne_val (by rw [venc]; have := hlow.2.1; omega)) (n4 10) (n4 11)).1
  · -- (E3) every `Free` tape below `F` off E6's tapes
    intro x hx hf hc15 hq284
    obtain ⟨l1, l2, l3, _, _⟩ := low_region e hV x hx
    obtain ⟨a1, a2⟩ := keepAll x hf (Or.inl hx) l3 l1 (ne_val (by rw [hcnt, vU, vprep]; omega)) hc15 hq284
      (l2 10) (l2 11)
    exact ⟨a2, a1⟩
  · intro i
    rw [(encA3 _).1]; exact e02L i

end concrete

end
end NearCubicWires.SourceConstruction.Rest
end

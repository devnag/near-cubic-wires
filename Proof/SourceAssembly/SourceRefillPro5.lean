import Proof.SourceAssembly.SourceRefillSeam3
import Proof.SourceAssembly.SourceProloguePro5
import Proof.SourceAssembly.SourceCyclePadRw

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
namespace NearCubicWires.SourceConstruction
noncomputable section

namespace Rest

section concrete
variable (mask : MaskProducer) {selector : CyclicChoice.Laws}
  (packets : PCJc4297ab269d8423a_Source.PacketLibrary selector)
  (rows : PCJc4297ab269d8423a_Source.RowLibrary selector) (sources : EightSources) (res : Nat)
  {gamma : Real} (p : Parameters sources gamma) (k r : Nat)

set_option hygiene false in
local notation "𝔇" => dimsOf mask packets rows sources res p k r

theorem refill_pro5_run {vE vP : Request → Nat}
    (se : PacketsGlue.RequestMeta.UnaryStage (decompositionOf sources) vE)
    (sp : PacketsGlue.RequestMeta.UnaryStage (decompositionOf sources) vP) {gW : Nat}
    (e : (𝔇).RestExt3 se.extra sp.extra gW) {V : Nat} (hV : (𝔇).U ≤ V)
    {s7 : Nat} (g7M : Machine V s7) (g7cost : Nat → Nat)
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
    {t2 t3 : Nat} (slots : Fin (𝔇).rt → Fin V) (hslots : ∀ i, (slots i).val = (𝔇).F + i.val)
    (enc : Fin t2 → Fin V) (app : Fin t3 → Fin V)
    (hencP : ∀ i, (𝔇).F ≤ (enc i).val ∧ (enc i).val < (𝔇).G)
    (happP : ∀ i, (app i).val < (𝔇).F ∨ ((𝔇).F ≤ (app i).val ∧ (app i).val < (𝔇).G))
    (reserve : Fin V → Nat) (hreserve : ∀ x : Fin V, reserve x = if (𝔇).F ≤ x.val then Rc else 0)
    {ι : Type} {sf : Nat} (fm : Machine V sf) (n : Nat) (Hj Hout : Fin V → Nat) (Aj : Fin V → List Bool)
    (Y : ι → Fin (𝔇).rt → List Bool) (E : Fin t2 → List Bool) (T : Fin t3 → List Bool)
    (hHout : ∀ x, (∀ i, slots i ≠ x) → Hout x = Hj x)
    (j : Nat) (hj : j + 1 ≤ (monomials coordinate ph ci).length) (hRc : j + 1 + 3 ≤ Rc) (hRk : Rc ≤ Rk)
    (w cW cQ Mb Ms cB cS S Rw B v U0 : Nat)
    (hInv : InvR e hV Rc Rk K K0 KH0 j w q Mb Ms cW cQ cB cS S Rw B v U0 n Hj Aj)
    (hcW : Rc ≤ cW) (hcQ : Rc ≤ cQ) (hcB : Rc ≤ cB) (hcS : Rc ≤ cS)
    (hSl : S + 2 ≤ Rc) (hRl : Rw + 2 ≤ Rc) (hBl : B + 2 ≤ Rc) (hvl : v + 2 ≤ Rc) (hUl : U0 ≤ Rc)
    (hMb : Mb ≤ Rc) (hMs : Ms ≤ Rc)
    (hKpos : ∀ x, K x → x.val < (𝔇).F ∨
      ((𝔇).B + 29 + restPc se.extra sp.extra gW ≤ x.val ∧ x ≠ Dims.hrT e hV 10 ∧ x ≠ Dims.hrT e hV 11))
    (hKpad : ∀ x, K x → (𝔇).F ≤ x.val → ZeroPadding.pad Rc (K0 x) = K0 x)
    (hKapp : ∀ x, K x → ∀ i, app i ≠ x)
    (henc0 : ∀ kk : Fin 13, (kk.val < 3 ∨ kk.val = 4) →
      (install app (install enc Aj E) T (Dims.encT (d := 𝔇) hV kk)).length ≤ Rc)
    (hlog : 2 * ((requestAt coordinate ph ci L target mode (j+1)).input (decompositionOf sources)).length + 1 ≤ Rc)
    (he1 : 1 ≤ vE (requestAt coordinate ph ci L target mode (j+1)))
    (hpw : (CloseoutRowsCountBinary.bits (vP (requestAt coordinate ph ci L target mode (j+1)))).length ≤ w)
    (hfirst : vP (requestAt coordinate ph ci L target mode (j+1)) * 2^(natBitLength (vE (requestAt coordinate ph ci L target mode (j+1)))) < 2^w)
    (hsecond : vP (requestAt coordinate ph ci L target mode (j+1)) * vE (requestAt coordinate ph ci L target mode (j+1)) * 2^(q+1) < 2^w) :
    ∃ (H3 : Fin V → Nat) (A3 : Fin V → List Bool) (Av3 : Fin V → List Bool),
      (∀ z, Step fm n Hj Aj Hout (install app (install enc (install slots Aj (Y z)) E) T) →
        Step (refillPro3 se sp e hV g7M) ((4*Rk+7) + 1 + ((4*Rc+7) + 1 + ((cursorCost j + 1 + (g7cost (j+1) + 1 + backCost se sp (requestAt coordinate ph ci L target mode (j+1)) Rc w q (exactListWord (PCJ38fbfed565f64139_Cached.cacheArgs (decompositionOf sources) ((requestAt coordinate ph ci L target mode (j+1)).family (decompositionOf sources))).gs).length Mb Ms)) + 1 + refreshCost Rc))) Hout (fun x => ZeroPadding.pad (reserve x) (install app (install enc (install slots Aj (Y z)) E) T x)) H3
          (fun y => ZeroPadding.pad ((𝔇).capZ se.extra sp.extra Rk y) (A3 y))) ∧
      (∀ x, A3 x = ZeroPadding.pad (Dims.Rpad (d := 𝔇) (eX := se.extra) (pX := sp.extra) (gW := gW) (V := V) Rc x)
        (Av3 x)) ∧
      Nonempty (Resident mask (packets (decompositionOf sources)) (rows (decompositionOf sources) (printerOf sources))
        ((𝔇).maskSlots hV) ((𝔇).pslots hV) ((𝔇).slot hV) ((𝔇).ret hV) ((𝔇).scr hV 0) ((𝔇).scr hV 1)
        ((𝔇).familySlots hV) ((𝔇).poolSlots hV) (Dims.rewind2Slots e.ext2.ext1.ext hV)
        ((𝔇).scr hV 5) ((𝔇).scr hV 6) ((𝔇).scr hV 7) ((𝔇).scr hV 8) ((𝔇).scr hV 9) ((𝔇).scr hV 10)
        (Dims.lenTape e.ext2.ext1.ext hV) (requestAt coordinate ph ci L target mode (j+1)) (layoutAt (j+1)) (capsAt (j+1)) H3 Av3) ∧
      A3 (Dims.encT (d := 𝔇) hV 4) = ZeroPadding.pad Rc (RepairOrdinary.frame (SignedSortKey.binary w
        (vP (requestAt coordinate ph ci L target mode (j+1)) * vE (requestAt coordinate ph ci L target mode (j+1)) * 2^q))) ∧
      (∀ hm : j + 1 < (monomials coordinate ph ci).length, ∀ i : Fin 3,
        A3 (Dims.encT (d := 𝔇) hV ⟨i.val, by omega⟩) =
        ZeroPadding.pad Rc (RepairOrdinary.frame (CloseoutRowsEstimatorCoefficients.Stream.recordFields b
          (CloseoutFinalC10SupplierCalls.coefficientEstimate ((monomials coordinate ph ci)[j+1]).coefficient)
          0 0 ⟨i.val, by omega⟩))) ∧
      A3 (Dims.csSlots e.ext2.ext1.ext hV 1) = ZeroPadding.pad Rc (List.replicate (if 3 < (exactListWord (PCJ38fbfed565f64139_Cached.cacheArgs (decompositionOf sources) ((requestAt coordinate ph ci L target mode (j+1)).family (decompositionOf sources))).gs).length then Mb else Ms) true) ∧
      A3 (Dims.csSlots e.ext2.ext1.ext hV 2) = ZeroPadding.pad Rc (List.replicate U0 true) ∧
      A3 (Dims.drvSlots e.ext2.ext1.ext hV 0) = ZeroPadding.pad Rc (UnaryTemplate.tape S) ∧
      A3 (Dims.drvSlots e.ext2.ext1.ext hV 1) = ZeroPadding.pad Rc (UnaryTemplate.tape Rw) ∧
      A3 (Dims.drvSlots e.ext2.ext1.ext hV 2) = ZeroPadding.pad Rc (UnaryTemplate.tape B) ∧
      A3 (Dims.drvSlots e.ext2.ext1.ext hV 4) = ZeroPadding.pad Rc (UnaryTemplate.tape v) ∧
      (∀ kk : Fin 16, 4 ≤ kk.val → A3 (Dims.csSlots e.ext2.ext1.ext hV kk) = ZeroPadding.pad Rc []) ∧
      (∀ kk : Fin 16, kk.val ≠ 0 → kk.val ≠ 3 → H3 (Dims.csSlots e.ext2.ext1.ext hV kk) = 0) ∧
      (∀ kk : Fin 7, (kk = 0 ∨ kk = 1 ∨ kk = 2 ∨ kk = 4) → H3 (Dims.drvSlots e.ext2.ext1.ext hV kk) = 1) ∧
      (∀ i : Fin (𝔇).rt, A3 (Dims.natSlots hV i) = List.replicate Rc false ∧ H3 (Dims.natSlots hV i) = 0) ∧
      (A3 ((𝔇).rsT e.ext2.ext1 hV 2) = ZeroPadding.pad Rc (UnaryTemplate.tape (j+1)) ∧ H3 ((𝔇).rsT e.ext2.ext1 hV 2) = 0) ∧
      (A3 ((𝔇).scr hV 11) = List.replicate Rc true ∧ H3 ((𝔇).scr hV 11) = 0 ∧
        A3 ((𝔇).scr hV 12) = List.replicate (Rc+2) false ∧ H3 ((𝔇).scr hV 12) = 0) ∧
      (A3 (Dims.hrT e hV 10) = List.replicate Rk true ∧ H3 (Dims.hrT e hV 10) = 0 ∧
        A3 (Dims.hrT e hV 11) = List.replicate (Rk+2) false ∧ H3 (Dims.hrT e hV 11) = 0) ∧
      (∀ x : Fin V, ¬ (𝔇).InClear se.extra sp.extra gW x.val → x ≠ (𝔇).scr hV 11 → x ≠ (𝔇).scr hV 12 →
        ¬ OutV (𝔇) se.extra sp.extra gW x.val → x ≠ (𝔇).rsT e.ext2.ext1 hV 2 →
        ¬ ((𝔇).F + (𝔇).rt ≤ x.val ∧ x.val ≤ (𝔇).F + (𝔇).rt + 4 ∧ x.val ≠ (𝔇).F + (𝔇).rt + 3) →
        (∀ i, Dims.rfT e.ext2 hV i ≠ x) → x ≠ Dims.hrT e hV 10 → x ≠ Dims.hrT e hV 11 →
        A3 x = ZeroPadding.pad (reserve x) (install app (install enc Aj E) T x) ∧ H3 x = Hout x) ∧
      (∀ x : Fin V, (𝔇).InDirt se.extra sp.extra gW x.val → ¬ (𝔇).InZ se.extra sp.extra x.val →
        (A3 x).length ≤ Rc ∧ H3 x ≤ cursorCost j + 1 + g7cost (j+1) + 1) ∧
      (∀ x : Fin V, (𝔇).InZ se.extra sp.extra x.val → (A3 x).length ≤ max Rc ((restCost se sp g7cost (requestAt coordinate ph ci L target mode (j+1)) Rc w q (exactListWord (PCJ38fbfed565f64139_Cached.cacheArgs (decompositionOf sources) ((requestAt coordinate ph ci L target mode (j+1)).family (decompositionOf sources))).gs).length Mb Ms j) + 1) ∧ H3 x ≤ (restCost se sp g7cost (requestAt coordinate ph ci L target mode (j+1)) Rc w q (exactListWord (PCJ38fbfed565f64139_Cached.cacheArgs (decompositionOf sources) ((requestAt coordinate ph ci L target mode (j+1)).family (decompositionOf sources))).gs).length Mb Ms j)) ∧
      (∀ kk : Fin 13, H3 (Dims.encT (d := 𝔇) hV kk) = Hout (Dims.encT (d := 𝔇) hV kk)) ∧
      (∀ i : Fin 3, (A3 (Dims.encT (d := 𝔇) hV ⟨i.val, by omega⟩)).length ≤ Rc) := by
  revert hlog he1 hpw hfirst hsecond
  classical
  have vG : (𝔇).G = (𝔇).F + (𝔇).rt + 13 := rfl
  have vB : (𝔇).B = (𝔇).G + (𝔇).R1 + 410 + (𝔇).w + (𝔇).tc := rfl
  have vp : (𝔇).pscr = (𝔇).R1 + 408 + (𝔇).w + (𝔇).tc := rfl
  have vPc : restPc se.extra sp.extra gW = 71 + se.extra + sp.extra + gW := rfl
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
  have vcs1 : (Dims.csSlots e.ext2.ext1.ext hV 1).val = (𝔇).B + 13 := rfl
  -- 0. the family exit: its `Z`-free ambient, heads, and the padded output off the slots
  let amb : Fin V → List Bool := fun x => ZeroPadding.pad (reserve x) (install app (install enc Aj E) T x)
  have ambHigh : ∀ x : Fin V, (𝔇).G ≤ x.val → amb x = ZeroPadding.pad Rc (Aj x) := by
    intro x hx
    have ha : ∀ i, app i ≠ x := fun i h => by
      have := happP i; have := congrArg Fin.val h; omega
    have he : ∀ i, enc i ≠ x := fun i h => by
      have := hencP i; have := congrArg Fin.val h; omega
    show ZeroPadding.pad (reserve x) (install app (install enc Aj E) T x) = _
    rw [hreserve x, if_pos (show (𝔇).F ≤ x.val by omega), install_other app _ _ x ha, install_other enc _ _ x he]
  have ambLow : ∀ x : Fin V, x.val < (𝔇).F → (∀ i, app i ≠ x) → amb x = Aj x := by
    intro x hx ha
    have he : ∀ i, enc i ≠ x := fun i h => by
      have := hencP i; have := congrArg Fin.val h; omega
    show ZeroPadding.pad (reserve x) (install app (install enc Aj E) T x) = _
    rw [hreserve x, if_neg (show ¬ (𝔇).F ≤ x.val by omega), ZeroPadding.pad_zero, install_other app _ _ x ha,
      install_other enc _ _ x he]
  have houtNS : ∀ x : Fin V, (x.val < (𝔇).F ∨ (𝔇).F + (𝔇).rt ≤ x.val) → Hout x = Hj x := by
    intro x hx
    apply hHout
    intro i h
    have := i.isLt; have := hslots i; have := congrArg Fin.val h
    omega
  have pzHigh : ∀ (z : ι) (x : Fin V), (𝔇).G ≤ x.val →
      ZeroPadding.pad (reserve x) (install app (install enc (install slots Aj (Y z)) E) T x) =
        ZeroPadding.pad Rc (Aj x) := by
    intro z x hx
    have hs : ∀ i, slots i ≠ x := fun i h => by
      have := i.isLt; have := hslots i; have := congrArg Fin.val h; omega
    rw [Refill.out_off_slots slots enc app Aj (Y z) E T x hs]
    exact ambHigh x hx
  have pzOff : ∀ (z : ι) (x : Fin V), (∀ i, slots i ≠ x) →
      ZeroPadding.pad (reserve x) (install app (install enc (install slots Aj (Y z)) E) T x) = amb x := by
    intro z x hs
    show _ = ZeroPadding.pad (reserve x) (install app (install enc Aj E) T x)
    rw [Refill.out_off_slots slots enc app Aj (Y z) E T x hs]
  have hiZ : ∀ x : Fin V, (x.val < (𝔇).B + 19 ∨ (𝔇).B + 19 + restPc se.extra sp.extra gW ≤ x.val) →
      ¬ (𝔇).InZ se.extra sp.extra x.val := by
    intro x hx hz; unfold SourceConstruction.Dims.InZ at hz; rw [vPc] at hx; omega
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
  -- 1. the family-exit dirt on the inner clear set (B1 (2): the family fuel only on the family bank)
  have hcH : ∀ z, Step fm n Hj Aj Hout (install app (install enc (install slots Aj (Y z)) E) T) →
      ∀ x : Fin V, (𝔇).InClear se.extra sp.extra gW x.val → ¬ (𝔇).InZ se.extra sp.extra x.val → Hout x ≤ Rc := by
    intro z hfam x hx hz
    by_cases hfb : (𝔇).F ≤ x.val ∧ x.val < (𝔇).F + (𝔇).rt
    · have h1 := (dirty_bound hfam x).2
      have h2 := hInv.famH x hfb.1 hfb.2
      omega
    · rw [houtNS x (by unfold SourceConstruction.Dims.InClear at hx; omega)]
      exact hInv.dirtH x (Or.inl hx) hz
  have hcA : ∀ z, Step fm n Hj Aj Hout (install app (install enc (install slots Aj (Y z)) E) T) →
      ∀ x : Fin V, (𝔇).InClear se.extra sp.extra gW x.val → ¬ (𝔇).InZ se.extra sp.extra x.val →
      (ZeroPadding.pad (reserve x) (install app (install enc (install slots Aj (Y z)) E) T x)).length ≤ Rc := by
    intro z hfam x hx hz
    have hdA := hInv.dirtA x (Or.inl hx) hz
    by_cases hfb : (𝔇).F ≤ x.val ∧ x.val < (𝔇).F + (𝔇).rt
    · have h1 := (dirty_bound hfam x).1
      have h2 := hInv.famH x hfb.1 hfb.2
      rw [hreserve x, if_pos hfb.1]
      exact Refill.pad_length_le _ _ _ le_rfl (by omega)
    · rw [pzHigh z x (by unfold SourceConstruction.Dims.InClear at hx; omega)]
      exact Refill.pad_length_le _ _ _ le_rfl hdA
  -- 2. the outer clear (real) of `Z`, driver `hrT 10 = 1^Rk`, log `hrT 11 = 0^(Rk+2)`
  have outerStep : ∀ z : ι, Step (RecoveryFocus.machine (Dims.clrZ e hV)
      (PCJ6e421fabe2aa4155_SourceClear.machine (71 + se.extra + sp.extra))) (4*Rk+7) Hout (fun x => ZeroPadding.pad (reserve x) (install app (install enc (install slots Aj (Y z)) E) T x))
      (dockH (Dims.clrZ e hV) Hout (fun _ => 0)) (install (Dims.clrZ e hV) (fun x => ZeroPadding.pad (reserve x) (install app (install enc (install slots Aj (Y z)) E) T x)) (PCJ6e421fabe2aa4155_SourceClear.join (fun _ => List.replicate Rk false) (List.replicate Rk true) (List.replicate (Rk+2) false))) := by
    intro z
    have hH : ∀ kk : Fin (71 + se.extra + sp.extra),
        Hout (Dims.clrZ e hV (Fin.castAdd 1 (Fin.castAdd 1 kk))) ≤ Rk := by
      intro kk
      have hin := Dims.clrZ_in e hV kk
      have hin' := hin
      unfold SourceConstruction.Dims.InZ at hin'
      rw [houtNS _ (Or.inr (by omega))]
      exact hInv.zH _ hin
    have hA : ∀ kk : Fin (71 + se.extra + sp.extra),
        (ZeroPadding.pad (reserve (Dims.clrZ e hV (Fin.castAdd 1 (Fin.castAdd 1 kk))))
          (install app (install enc (install slots Aj (Y z)) E) T
            (Dims.clrZ e hV (Fin.castAdd 1 (Fin.castAdd 1 kk))))).length ≤ Rk := by
      intro kk
      have hin := Dims.clrZ_in e hV kk
      have hin' := hin
      unfold SourceConstruction.Dims.InZ at hin'
      rw [pzHigh z _ (by omega)]
      exact Refill.pad_length_le _ _ _ hRk (hInv.zA _ hin)
    have hdH : Hout (Dims.clrZ e hV (Fin.castAdd 1 ((0 : Fin 1).natAdd (71 + se.extra + sp.extra)))) = 0 := by
      rw [Dims.clrZ_driver e hV, houtNS _ (Or.inr (by rw [vhr]; omega))]; exact hInv.zDH
    have hlH : Hout (Dims.clrZ e hV ((0 : Fin 1).natAdd (71 + se.extra + sp.extra + 1))) = 0 := by
      rw [Dims.clrZ_log e hV, houtNS _ (Or.inr (by rw [vhr]; omega))]; exact hInv.zLH
    have hd : ZeroPadding.pad (reserve (Dims.clrZ e hV (Fin.castAdd 1 ((0 : Fin 1).natAdd (71 + se.extra + sp.extra)))))
        (install app (install enc (install slots Aj (Y z)) E) T
          (Dims.clrZ e hV (Fin.castAdd 1 ((0 : Fin 1).natAdd (71 + se.extra + sp.extra))))) =
        List.replicate Rk true := by
      rw [Dims.clrZ_driver e hV, pzHigh z _ (by rw [vhr]; omega), hInv.zD]
      exact pad_long _ _ (by simp; omega)
    have hl : ZeroPadding.pad (reserve (Dims.clrZ e hV ((0 : Fin 1).natAdd (71 + se.extra + sp.extra + 1))))
        (install app (install enc (install slots Aj (Y z)) E) T
          (Dims.clrZ e hV ((0 : Fin 1).natAdd (71 + se.extra + sp.extra + 1)))) =
        List.replicate (Rk+2) false := by
      rw [Dims.clrZ_log e hV, pzHigh z _ (by rw [vhr]; omega), hInv.zL]
      exact pad_long _ _ (by simp; omega)
    exact Refill.clear_on (Dims.clrZ e hV) (Dims.clrZ_injective e hV) Rk Hout (fun x => ZeroPadding.pad (reserve x) (install app (install enc (install slots Aj (Y z)) E) T x)) hH hA hdH hlH hd hl
  -- 3. the virtual bank after the outer clear (`Z` blank at `Rc`) and its heads
  obtain ⟨Hc, hHc⟩ : ∃ Hc : Fin V → Nat, Hc = dockH (Dims.clrZ e hV) Hout (fun _ => 0) := ⟨_, rfl⟩
  obtain ⟨VV, hVV⟩ : ∃ VV : Fin V → List Bool,
      VV = (𝔇).virtZ se.extra sp.extra Rc (install (Dims.clrZ e hV) amb (PCJ6e421fabe2aa4155_SourceClear.join (fun _ => List.replicate Rk false) (List.replicate Rk true) (List.replicate (Rk+2) false))) := ⟨_, rfl⟩
  have HcOff : ∀ x : Fin V, ¬ (𝔇).InZ se.extra sp.extra x.val → x ≠ Dims.hrT e hV 10 → x ≠ Dims.hrT e hV 11 →
      Hc x = Hout x := by
    intro x h1 h2 h3; rw [hHc]; exact dockH_other _ Hout _ x (Dims.clrZ_off e hV x h1 h2 h3)
  have VVOff : ∀ x : Fin V, ¬ (𝔇).InZ se.extra sp.extra x.val → x ≠ Dims.hrT e hV 10 → x ≠ Dims.hrT e hV 11 →
      VV x = amb x := by
    intro x h1 h2 h3; rw [hVV]; simp only [SourceConstruction.Dims.virtZ, if_neg h1]
    exact install_other _ amb _ x (Dims.clrZ_off e hV x h1 h2 h3)
  have rsHc : ∀ i : Fin 5, Hc ((𝔇).rsT e.ext2.ext1 hV i) = 0 := fun i => by
    rw [HcOff _ (hiZ _ (Or.inr (by rw [vrs]; omega))) (Ne.symm (Dims.hrT_ne_rsT e hV 10 i))
      (Ne.symm (Dims.hrT_ne_rsT e hV 11 i)), houtNS _ (Or.inr (by rw [vrs]; omega))]
    exact hInv.rsH i
  have rsVV : ∀ i : Fin 5, VV ((𝔇).rsT e.ext2.ext1 hV i) = ZeroPadding.pad Rc (Aj ((𝔇).rsT e.ext2.ext1 hV i)) := fun i => by
    rw [VVOff _ (hiZ _ (Or.inr (by rw [vrs]; omega))) (Ne.symm (Dims.hrT_ne_rsT e hV 10 i))
      (Ne.symm (Dims.hrT_ne_rsT e hV 11 i)), ambHigh _ (by rw [vrs]; omega)]
  have mHc : ∀ i : Fin 5, Hc (Dims.mT e.ext2 hV i) = 0 := fun i => by
    rw [HcOff _ (hiZ _ (Or.inr (by rw [vmT]; omega))) (Ne.symm (Dims.hrT_ne_mT e hV 10 i))
      (Ne.symm (Dims.hrT_ne_mT e hV 11 i)), houtNS _ (Or.inr (by rw [vmT]; omega))]
    exact hInv.mH i
  have mVV : ∀ i : Fin 5, VV (Dims.mT e.ext2 hV i) = ZeroPadding.pad Rc (Aj (Dims.mT e.ext2 hV i)) := fun i => by
    rw [VVOff _ (hiZ _ (Or.inr (by rw [vmT]; omega))) (Ne.symm (Dims.hrT_ne_mT e hV 10 i))
      (Ne.symm (Dims.hrT_ne_mT e hV 11 i)), ambHigh _ (by rw [vmT]; omega)]
  have rfNZ : ∀ i : Fin 5, ¬ (𝔇).InZ se.extra sp.extra (Dims.rfT e.ext2 hV i).val := fun i =>
    hiZ _ (Or.inl (by rw [vrf]; omega))
  have rfIn : ∀ i : Fin 5, (𝔇).InDirt se.extra sp.extra gW (Dims.rfT e.ext2 hV i).val := fun i =>
    Or.inr (by rw [vrf]; omega)
  have rfHc : ∀ i : Fin 5, Hc (Dims.rfT e.ext2 hV i) = Hj (Dims.rfT e.ext2 hV i) := fun i => by
    rw [HcOff _ (rfNZ i) (Ne.symm (Dims.hrT_ne_rfT e hV 10 i)) (Ne.symm (Dims.hrT_ne_rfT e hV 11 i)),
      houtNS _ (Or.inr (by rw [vrf]; omega))]
  have rfVV : ∀ i : Fin 5, VV (Dims.rfT e.ext2 hV i) = ZeroPadding.pad Rc (Aj (Dims.rfT e.ext2 hV i)) := fun i => by
    rw [VVOff _ (rfNZ i) (Ne.symm (Dims.hrT_ne_rfT e hV 10 i)) (Ne.symm (Dims.hrT_ne_rfT e hV 11 i)),
      ambHigh _ (by rw [vrf]; omega)]
  have encNZ : ∀ kk : Fin 13, ¬ (𝔇).InZ se.extra sp.extra (Dims.encT (d := 𝔇) hV kk).val := fun kk =>
    hiZ _ (Or.inl (by rw [venc]; omega))
  have encN10 : ∀ kk : Fin 13, Dims.encT (d := 𝔇) hV kk ≠ Dims.hrT e hV 10 := fun kk =>
    ne_val (by rw [venc, vhr]; omega)
  have encN11 : ∀ kk : Fin 13, Dims.encT (d := 𝔇) hV kk ≠ Dims.hrT e hV 11 := fun kk =>
    ne_val (by rw [venc, vhr]; omega)
  have hMv : ∀ i, VV (Dims.mT e.ext2 hV i) = M i := by
    intro i
    rw [mVV i]
    fin_cases i
    · show ZeroPadding.pad Rc (Aj (Dims.mT e.ext2 hV 0)) = ZeroPadding.pad Rc (List.replicate U0 true)
      rw [hInv.mU]; exact pad_same _ _
    · show ZeroPadding.pad Rc (Aj (Dims.mT e.ext2 hV 1)) = ZeroPadding.pad Rc (UnaryTemplate.tape S)
      rw [hInv.mS]; exact pad_same _ _
    · show ZeroPadding.pad Rc (Aj (Dims.mT e.ext2 hV 2)) = ZeroPadding.pad Rc (UnaryTemplate.tape Rw)
      rw [hInv.mR]; exact pad_same _ _
    · show ZeroPadding.pad Rc (Aj (Dims.mT e.ext2 hV 3)) = ZeroPadding.pad Rc (UnaryTemplate.tape B)
      rw [hInv.mB]; exact pad_same _ _
    · show ZeroPadding.pad Rc (Aj (Dims.mT e.ext2 hV 4)) = ZeroPadding.pad Rc (UnaryTemplate.tape v)
      rw [hInv.mv]; exact pad_same _ _
  have hKc : ∀ x, K x → VV x = K0 x ∧ Hc x = KH0 x := by
    intro x hx
    rcases hKpos x hx with hl | ⟨hh, h10, h11⟩
    · have hz : ¬ (𝔇).InZ se.extra sp.extra x.val := hiZ x (Or.inl (by omega))
      have n10 : x ≠ Dims.hrT e hV 10 := ne_val (by rw [vhr]; omega)
      have n11 : x ≠ Dims.hrT e hV 11 := ne_val (by rw [vhr]; omega)
      rw [VVOff x hz n10 n11, HcOff x hz n10 n11, ambLow x hl (hKapp x hx), houtNS x (Or.inl hl)]
      exact hInv.kept x hx
    · have hz : ¬ (𝔇).InZ se.extra sp.extra x.val := hiZ x (Or.inr (by omega))
      rw [VVOff x hz h10 h11, HcOff x hz h10 h11, ambHigh x (by omega), houtNS x (Or.inr (by omega)),
        (hInv.kept x hx).1, (hInv.kept x hx).2, hKpad x hx (by omega)]
      exact ⟨rfl, rfl⟩
  intro hlog he1 hpw hfirst hsecond
  -- 4. `rest ; refresh` after the inner clear, on the virtual bank (`prologue_run3`, no window)
  obtain ⟨H3, A3, Av3, sP, hM3, ⟨res3⟩, e4, e02, ecs1, ecs1H, ecurT, ecurTH, fv, f0, f14, bl3, a11, h11, a12, h12,
      fr3, dirt3, dirtZ3, encH3, e02L⟩ := prologue_run5 mask packets rows sources res p k r se sp e.ext2 hV g7M g7cost
    coordinate ph ci L target mode Rc b layoutAt capsAt K K0 KH0 hG7 j hj hRc w cW cQ Mb Ms cB cS M hMl Hc VV
    hKc (fun x hx => (hKpos x hx).imp id (fun h => by have := h.1; omega)) hMb hMs
    (by rw [rsVV 2, hInv.curT]; exact pad_same _ _) (rsHc 2)
    (fun kk hk => by
      rw [VVOff _ (encNZ kk) (encN10 kk) (encN11 kk)]
      show (ZeroPadding.pad (reserve _) _).length ≤ Rc
      rw [hreserve, if_pos (show (𝔇).F ≤ (Dims.encT (d := 𝔇) hV kk).val by rw [venc]; omega)]
      exact le_of_eq (pad_len_exact _ _ (henc0 kk hk)))
    (fun kk hk => by
      rw [HcOff _ (encNZ kk) (encN10 kk) (encN11 kk), houtNS _ (Or.inr (by rw [venc]; omega))]
      exact hInv.encH kk hk)
    (by rw [rsVV 3, hInv.wv]; exact pad_over _ _ hcW _) (rsHc 3)
    (by rw [rsVV 4, hInv.qv]; exact pad_over _ _ hcQ _) (rsHc 4)
    (by rw [rsVV 0, hInv.big]; exact pad_over _ _ hcB _) (rsHc 0)
    (by rw [rsVV 1, hInv.small]; exact pad_over _ _ hcS _) (rsHc 1)
    hMv mHc
    (fun i => by rw [rfVV i]; exact le_of_eq (pad_len_exact _ _ (hInv.dirtA _ (rfIn i) (rfNZ i))))
    (fun i => by rw [rfHc i]; exact hInv.dirtH _ (rfIn i) (rfNZ i))
    hlog he1 hpw hfirst hsecond
  -- 5. the inner clear on the virtual bank absorbs the family output
  have innerStep : ∀ z, Step fm n Hj Aj Hout (install app (install enc (install slots Aj (Y z)) E) T) →
      Step (RecoveryFocus.machine (Dims.clr2 e.ext2.ext1 hV)
        (PCJ6e421fabe2aa4155_SourceClear.machine ((𝔇).tcl2 se.extra sp.extra gW))) (4*Rc+7)
        Hc ((𝔇).virtZ se.extra sp.extra Rc (install (Dims.clrZ e hV) (fun x => ZeroPadding.pad (reserve x) (install app (install enc (install slots Aj (Y z)) E) T x)) (PCJ6e421fabe2aa4155_SourceClear.join (fun _ => List.replicate Rk false) (List.replicate Rk true) (List.replicate (Rk+2) false))))
        (dockH (Dims.clr2 e.ext2.ext1 hV) Hc (fun _ => 0))
        (install (Dims.clr2 e.ext2.ext1 hV) VV (PCJ6e421fabe2aa4155_SourceClear.join (fun _ => List.replicate Rc false) (List.replicate Rc true) (List.replicate (Rc+2) false))) := by
    intro z hfam
    have hH : ∀ kk : Fin ((𝔇).tcl2 se.extra sp.extra gW),
        Hc (Dims.clr2 e.ext2.ext1 hV (Fin.castAdd 1 (Fin.castAdd 1 kk))) ≤ Rc := by
      intro kk
      have hin := Dims.clr2_in e.ext2.ext1 hV kk
      by_cases hz : (𝔇).InZ se.extra sp.extra (Dims.clr2 e.ext2.ext1 hV (Fin.castAdd 1 (Fin.castAdd 1 kk))).val
      · obtain ⟨k0, hk0⟩ := Dims.clrZ_cover e hV _ hz
        rw [hHc, ← hk0, dockH_slot _ (Dims.clrZ_injective e hV)]
        exact Nat.zero_le _
      · rw [HcOff _ hz (clear_ne_hrT e hV hin 10) (clear_ne_hrT e hV hin 11)]
        exact hcH z hfam _ hin hz
    have hA : ∀ kk : Fin ((𝔇).tcl2 se.extra sp.extra gW),
        ((𝔇).virtZ se.extra sp.extra Rc (install (Dims.clrZ e hV) (fun x => ZeroPadding.pad (reserve x) (install app (install enc (install slots Aj (Y z)) E) T x)) (PCJ6e421fabe2aa4155_SourceClear.join (fun _ => List.replicate Rk false) (List.replicate Rk true) (List.replicate (Rk+2) false)))
          (Dims.clr2 e.ext2.ext1 hV (Fin.castAdd 1 (Fin.castAdd 1 kk)))).length ≤ Rc := by
      intro kk
      have hin := Dims.clr2_in e.ext2.ext1 hV kk
      simp only [SourceConstruction.Dims.virtZ]
      split_ifs with hz
      · simp
      · rw [install_other _ _ _ _ (Dims.clrZ_off e hV _ hz (clear_ne_hrT e hV hin 10) (clear_ne_hrT e hV hin 11))]
        exact hcA z hfam _ hin hz
    have s11Z : ¬ (𝔇).InZ se.extra sp.extra ((𝔇).scr hV 11).val := hiZ _ (Or.inl (by rw [vscr]; omega))
    have s12Z : ¬ (𝔇).InZ se.extra sp.extra ((𝔇).scr hV 12).val := hiZ _ (Or.inl (by rw [vscr]; omega))
    have hdH : Hc (Dims.clr2 e.ext2.ext1 hV (Fin.castAdd 1 ((0 : Fin 1).natAdd ((𝔇).tcl2 se.extra sp.extra gW)))) = 0 := by
      rw [Dims.clr2_driver e.ext2.ext1 hV, HcOff _ s11Z (Ne.symm (Dims.hrT_ne_scr e hV 10 11))
        (Ne.symm (Dims.hrT_ne_scr e hV 11 11)), houtNS _ (Or.inr (by rw [vscr]; omega))]
      exact hInv.drvH
    have hlH : Hc (Dims.clr2 e.ext2.ext1 hV ((0 : Fin 1).natAdd ((𝔇).tcl2 se.extra sp.extra gW + 1))) = 0 := by
      rw [Dims.clr2_log e.ext2.ext1 hV, HcOff _ s12Z (Ne.symm (Dims.hrT_ne_scr e hV 10 12))
        (Ne.symm (Dims.hrT_ne_scr e hV 11 12)), houtNS _ (Or.inr (by rw [vscr]; omega))]
      exact hInv.lgH
    have hd : (𝔇).virtZ se.extra sp.extra Rc (install (Dims.clrZ e hV) (fun x => ZeroPadding.pad (reserve x) (install app (install enc (install slots Aj (Y z)) E) T x)) (PCJ6e421fabe2aa4155_SourceClear.join (fun _ => List.replicate Rk false) (List.replicate Rk true) (List.replicate (Rk+2) false)))
        (Dims.clr2 e.ext2.ext1 hV (Fin.castAdd 1 ((0 : Fin 1).natAdd ((𝔇).tcl2 se.extra sp.extra gW)))) =
        List.replicate Rc true := by
      rw [Dims.clr2_driver e.ext2.ext1 hV]
      simp only [SourceConstruction.Dims.virtZ, if_neg s11Z]
      rw [install_other _ _ _ _ (Dims.clrZ_off e hV _ s11Z (Ne.symm (Dims.hrT_ne_scr e hV 10 11))
        (Ne.symm (Dims.hrT_ne_scr e hV 11 11)))]
      show ZeroPadding.pad (reserve _) _ = _
      rw [pzHigh z _ (by rw [vscr]; omega), hInv.drv]; exact pad_long _ _ (by simp)
    have hl : (𝔇).virtZ se.extra sp.extra Rc (install (Dims.clrZ e hV) (fun x => ZeroPadding.pad (reserve x) (install app (install enc (install slots Aj (Y z)) E) T x)) (PCJ6e421fabe2aa4155_SourceClear.join (fun _ => List.replicate Rk false) (List.replicate Rk true) (List.replicate (Rk+2) false)))
        (Dims.clr2 e.ext2.ext1 hV ((0 : Fin 1).natAdd ((𝔇).tcl2 se.extra sp.extra gW + 1))) =
        List.replicate (Rc+2) false := by
      rw [Dims.clr2_log e.ext2.ext1 hV]
      simp only [SourceConstruction.Dims.virtZ, if_neg s12Z]
      rw [install_other _ _ _ _ (Dims.clrZ_off e hV _ s12Z (Ne.symm (Dims.hrT_ne_scr e hV 10 12))
        (Ne.symm (Dims.hrT_ne_scr e hV 11 12)))]
      show ZeroPadding.pad (reserve _) _ = _
      rw [pzHigh z _ (by rw [vscr]; omega), hInv.lg]; exact pad_long _ _ (by simp)
    have habs := virt_absorb e hV Rc Rk (fun x => ZeroPadding.pad (reserve x) (install app (install enc (install slots Aj (Y z)) E) T x)) amb (Dims.clr2 e.ext2.ext1 hV) (Dims.clr2_injective e.ext2.ext1 hV) (PCJ6e421fabe2aa4155_SourceClear.join (fun _ => List.replicate Rc false) (List.replicate Rc true) (List.replicate (Rc+2) false))
      (fun x hx => pzOff z x (fun i h => (Dims.slots_in_clr2 e.ext2.ext1 hV slots hslots i).elim
        fun kk hk => hx _ (hk.trans h)))
    rw [← hVV] at habs
    exact (Refill.clear_on (Dims.clr2 e.ext2.ext1 hV) (Dims.clr2_injective e.ext2.ext1 hV) Rc Hc
      ((𝔇).virtZ se.extra sp.extra Rc (install (Dims.clrZ e hV) (fun x => ZeroPadding.pad (reserve x) (install app (install enc (install slots Aj (Y z)) E) T x)) (PCJ6e421fabe2aa4155_SourceClear.join (fun _ => List.replicate Rk false) (List.replicate Rk true) (List.replicate (Rk+2) false)))) hH hA hdH hlH hd hl).congr rfl habs
  -- 6. the virtual prologue, lifted by `Step.pad`, after the real outer clear: ONE run of `refillPro3`
  have realRun : ∀ z, Step fm n Hj Aj Hout (install app (install enc (install slots Aj (Y z)) E) T) →
      Step (refillPro3 se sp e hV g7M) ((4*Rk+7) + 1 + ((4*Rc+7) + 1 + ((cursorCost j + 1 + (g7cost (j+1) + 1 + backCost se sp (requestAt coordinate ph ci L target mode (j+1)) Rc w q (exactListWord (PCJ38fbfed565f64139_Cached.cacheArgs (decompositionOf sources) ((requestAt coordinate ph ci L target mode (j+1)).family (decompositionOf sources))).gs).length Mb Ms)) + 1 + refreshCost Rc))) Hout (fun x => ZeroPadding.pad (reserve x) (install app (install enc (install slots Aj (Y z)) E) T x)) H3
        (fun y => ZeroPadding.pad ((𝔇).capZ se.extra sp.extra Rk y) (A3 y)) := by
    intro z hfam
    have hv : Step (refillPro se sp e.ext2 hV g7M) ((4*Rc+7) + 1 + ((cursorCost j + 1 + (g7cost (j+1) + 1 + backCost se sp (requestAt coordinate ph ci L target mode (j+1)) Rc w q (exactListWord (PCJ38fbfed565f64139_Cached.cacheArgs (decompositionOf sources) ((requestAt coordinate ph ci L target mode (j+1)).family (decompositionOf sources))).gs).length Mb Ms)) + 1 + refreshCost Rc))
        Hc ((𝔇).virtZ se.extra sp.extra Rc (install (Dims.clrZ e hV) (fun x => ZeroPadding.pad (reserve x) (install app (install enc (install slots Aj (Y z)) E) T x)) (PCJ6e421fabe2aa4155_SourceClear.join (fun _ => List.replicate Rk false) (List.replicate Rk true) (List.replicate (Rk+2) false))) ) H3 A3 :=
      (innerStep z hfam).seq sP
    have h1 := (hv.pad ((𝔇).capZ se.extra sp.extra Rk)).congr_in rfl (outer_exit_pad e hV Rc Rk hRk (fun x => ZeroPadding.pad (reserve x) (install app (install enc (install slots Aj (Y z)) E) T x)))
    have h0 := (outerStep z).congr hHc.symm rfl
    exact h0.seq h1
  -- 7. the exports
  have csHigh : ∀ kk : Fin 16, 4 ≤ kk.val → (Dims.csSlots e.ext2.ext1.ext hV kk).val = (𝔇).B + (kk.val - 3) := by
    intro kk hk
    simp only [Dims.csSlots, Dims.csV]
    split_ifs <;> omega
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
  have hrF : ∀ i : Fin 12, A3 (Dims.hrT e hV i) = VV (Dims.hrT e hV i) ∧ H3 (Dims.hrT e hV i) = Hc (Dims.hrT e hV i) :=
    fun i => fr3 _ (Dims.hrT_notClear e hV i) (Dims.hrT_ne_scr e hV i 11) (Dims.hrT_ne_scr e hV i 12)
      (Dims.hrT_notOut e hV i) (Dims.hrT_ne_rsT e hV i 2) (by rw [vhr]; omega)
      (fun m h => Dims.hrT_ne_rfT e hV i m h.symm)
  refine ⟨H3, A3, Av3, realRun, hM3, ⟨res3⟩, e4, e02, ecs1, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ⟨ecurT, ecurTH⟩,
    ⟨a11, h11, a12, h12⟩, ⟨(hrF 10).1.trans VV10, (hrF 10).2.trans Hc10, (hrF 11).1.trans VV11, (hrF 11).2.trans Hc11⟩,
    ?_, dirt3, dirtZ3, ?_, e02L⟩
  · rw [← Dims.rfT_cs2 e.ext2 hV, fv 0]; rfl
  · rw [← Dims.rfT_drv0 e.ext2 hV, fv 1]; rfl
  · rw [← Dims.rfT_drv1 e.ext2 hV, fv 2]; rfl
  · rw [← Dims.rfT_drv2 e.ext2 hV, fv 3]; rfl
  · rw [← Dims.rfT_drv4 e.ext2 hV, fv 4]; rfl
  · intro kk hk
    rw [(bl3 _ (Or.inr (by rw [csHigh kk hk]; have := kk.isLt; omega))).1]
    exact (Finish.blank_is_padded Rc).symm
  · intro kk h0 h3
    by_cases h1 : kk.val = 1
    · have hk : kk = 1 := Fin.ext h1
      rw [hk]; exact ecs1H
    by_cases h2 : kk.val = 2
    · have hk : kk = 2 := Fin.ext h2
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
  · intro x h1 h2 h3 h4 h5 h6 h7 h10 h11
    have hz : ¬ (𝔇).InZ se.extra sp.extra x.val := fun hz => h1 (Dims.InZ_clear hz)
    obtain ⟨b1, b2⟩ := fr3 x h1 h2 h3 h4 h5 h6 h7
    exact ⟨b1.trans (VVOff x hz h10 h11), b2.trans (HcOff x hz h10 h11)⟩
  · intro kk
    exact (encH3 kk).trans (HcOff _ (encNZ kk) (encN10 kk) (encN11 kk))

end concrete

end Rest
end
end NearCubicWires.SourceConstruction
end

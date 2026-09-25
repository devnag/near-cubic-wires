import Proof.SourceAssembly.SourceSkelFirstStart
import Proof.SourceAssembly.SourceSkelView

section
set_option autoImplicit false
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unusedVariables false

open NearCubicWires NearCubicWires.ComponentwisePolynomial NearCubicWires.RepairOrdinary.CompetitorRawFieldEmit NearCubicWires.RepairOrdinary.CloseoutRowsOriginalSchedule LocalBitMultitape ExtDecompositionBatch RepairOrdinary RepairRepresentation SourceInterfaces RepairSource RepairSource.CloseoutFinal P1TopDown RepairSource.VerifierDecoding RecoveryRootRound RecoveryExecution CloseoutRowsEstimator CloseoutRowsEstimatorCoefficients CompetitorSelectedCount MatrixScoreBatch CompetitorCountMask SupplierPipeline SupplierEstimator SupplierPrime CanonicalFourfoldRowProgram CloseoutRawRows C10ExternalRowLoop C10ThresholdNaturalRowPrint C10ThresholdParityRow C10ThresholdEstimateRowJoin CloseoutFinalC10RowAnswerWord P1Closure P1TopDownPaidReusable P1TopDownPaidReusableReserves P1TopDownPaidBinaryReserves
open PCJ1fef9807c6954e94_Native PCJ515eaa990d75455b_FamilyInit
open PCJ9eff70d512234a4c_Fixed PCJd4d1d9d7d1fa4313_Production
open PCJc4297ab269d8423a_Source
open NearCubicWires.SourceRequest NearCubicWires.SourceRequest.FactorLoop
open NearCubicWires.SourceConstruction NearCubicWires.SourceConstruction.Rest
namespace NearCubicWires.SourceSkeleton
open NearCubicWires.SourceParent NearCubicWires.SourcePhase
noncomputable section
attribute [local irreducible] P1TopDownPaidPayload.tapes WorkspaceSelectedAdmission.originalTapes
  WorkspaceSelectedEntry.size SelectedRecoveryIntegration.outer

section start
variable (mask : MaskProducer) {selector : CyclicChoice.Laws}
  (packets : PCJc4297ab269d8423a_Source.PacketLibrary selector)
  (rows : PCJc4297ab269d8423a_Source.RowLibrary selector) (sources : EightSources)
  (res : Nat) (hres : 19 ≤ res) {gamma : Real} (p : Parameters sources gamma) (k r : Nat)

set_option hygiene false in
local notation "𝔇" => dimsOf mask packets rows sources res p k r
set_option hygiene false in
local notation "𝒽" => UOf_le mask packets rows sources res p k r
set_option hygiene false in
local notation "𝒽1" => UOf_le_succ mask packets rows sources res p k r
set_option hygiene false in
local notation "𝒞" => skelCodeR mask packets rows sources res hres p k r ph refill preF

theorem invR_viewOf (ph : Phase) (refill : Σ s, Machine (UOf mask packets rows sources res p k r) s)
    (preF : Σ s, Machine (UOf mask packets rows sources res p k r + 1) s)
    {eX pX gW : Nat} {e : (𝔇).RestExt3 eX pX gW} {Rc Rk : Nat}
    {K : Fin (UOf mask packets rows sources res p k r) → Prop}
    {K0 : Fin (UOf mask packets rows sources res p k r) → List Bool}
    {KH0 : Fin (UOf mask packets rows sources res p k r) → Nat}
    {jj w q Mb Ms cW cQ cB cS S Rw B v U0 fuel : Nat} {H : Fin (UOf mask packets rows sources res p k r) → Nat}
    {X : Fin (UOf mask packets rows sources res p k r) → List Bool} {Atom : Type}
    {vd : RCFive.Source.CallValues Atom (𝒞).sourceTapes} {b : Nat}
    (h : InvR e 𝒽 Rc Rk K K0 KH0 jj w q Mb Ms cW cQ cB cS S Rw B v U0 fuel H X)
    (hKpos : ∀ y, K y → y.val < (𝔇).F ∨ (𝔇).G ≤ y.val)
    (hKapp : ∀ y, K y → ∀ i, (𝒞).app i ≠ y)
    (hencP : ∀ i, (𝔇).F ≤ ((𝒞).enc i).val ∧ ((𝒞).enc i).val < (𝔇).G)
    (happP : ∀ i, ((𝒞).app i).val < (𝔇).F ∨ ((𝔇).F ≤ ((𝒞).app i).val ∧ ((𝒞).app i).val < (𝔇).G))
    (j : Nat) (hS : ∀ i, (inTOf 𝒞 b vd j i).length ≤ Rc) :
    InvR e 𝒽 Rc Rk K K0 KH0 jj w q Mb Ms cW cQ cB cS S Rw B v U0 fuel H (viewOf 𝒞 b vd j X) := by
  have hB : (𝔇).B = (𝔇).G + (𝔇).R1 + 410 + (𝔇).w + (𝔇).tc := rfl
  have hG : (𝔇).G = (𝔇).F + (𝔇).rt + 13 := rfl
  have hrt : (𝔇).rt = r_tapes (𝒞).a := rfl
  have slotv : ∀ i, ((𝒞).slots i).val = (𝔇).F + i.val := fun i => (𝒞)._hs i
  -- a tape in `[F, F + rt)` is a slot
  have isSlot : ∀ x : Fin (UOf mask packets rows sources res p k r), (𝔇).F ≤ x.val → x.val < (𝔇).F + (𝔇).rt →
      ∃ i, (𝒞).slots i = x := fun x h1 h2 =>
    ⟨⟨x.val - (𝔇).F, by omega⟩, Fin.ext (by rw [slotv]; simp only; omega)⟩
  have high : ∀ x : Fin (UOf mask packets rows sources res p k r), (𝔇).G ≤ x.val → viewOf 𝒞 b vd j X x = X x := by
    intro x hx
    refine viewOf_other 𝒞 b vd j X x (fun i hi => ?_) (fun i hi => ?_) (fun i hi => ?_)
    · have := slotv i; have := i.isLt; have := congrArg Fin.val hi; omega
    · have := (hencP i).2; have := congrArg Fin.val hi; omega
    · have := congrArg Fin.val hi; rcases happP i with h1 | h1 <;> omega
  -- off the slots, `enc`/`app` tapes are never dirt
  have nodirt : ∀ x : Fin (UOf mask packets rows sources res p k r), (∀ i, (𝒞).slots i ≠ x) →
      (x.val < (𝔇).F ∨ ((𝔇).F ≤ x.val ∧ x.val < (𝔇).G)) → ¬ (𝔇).InDirt eX pX gW x.val := by
    intro x hs hx hd
    have hp : (𝔇).pscr = (𝔇).R1 + 408 + (𝔇).w + (𝔇).tc := rfl
    by_cases hin : (𝔇).F ≤ x.val ∧ x.val < (𝔇).F + (𝔇).rt
    · obtain ⟨i, hi⟩ := isSlot x hin.1 hin.2
      exact hs i hi
    · unfold SourceConstruction.Dims.InDirt SourceConstruction.Dims.InClear at hd
      omega
  refine ⟨fun x hx => ?_, ?_, ?_, ?_, ?_, ?_, h.rsH, ?_, ?_, ?_, ?_, ?_, h.mH, ?_, h.drvH, ?_, h.lgH,
    ?_, h.zDH, ?_, h.zLH, fun x hx hz => ?_, h.dirtH, h.famH, fun x hz => ?_, h.zH, h.encH⟩
  · rcases hKpos x hx with hl | hh
    · rw [viewOf_other 𝒞 b vd j X x (fun i hi => by have := slotv i; have := congrArg Fin.val hi; omega)
        (fun i hi => by have := (hencP i).1; have := congrArg Fin.val hi; omega) (hKapp x hx)]
      exact h.kept x hx
    · rw [high x hh]; exact h.kept x hx
  · rw [high _ (by show _ ≤ (𝔇).B + 19 + restPc eX pX gW + 2; omega)]; exact h.curT
  · rw [high _ (by show _ ≤ (𝔇).B + 19 + restPc eX pX gW + 0; omega)]; exact h.big
  · rw [high _ (by show _ ≤ (𝔇).B + 19 + restPc eX pX gW + 1; omega)]; exact h.small
  · rw [high _ (by show _ ≤ (𝔇).B + 19 + restPc eX pX gW + 3; omega)]; exact h.wv
  · rw [high _ (by show _ ≤ (𝔇).B + 19 + restPc eX pX gW + 4; omega)]; exact h.qv
  · rw [high _ (by show _ ≤ (𝔇).B + 19 + restPc eX pX gW + 5 + 0; omega)]; exact h.mU
  · rw [high _ (by show _ ≤ (𝔇).B + 19 + restPc eX pX gW + 5 + 1; omega)]; exact h.mS
  · rw [high _ (by show _ ≤ (𝔇).B + 19 + restPc eX pX gW + 5 + 2; omega)]; exact h.mR
  · rw [high _ (by show _ ≤ (𝔇).B + 19 + restPc eX pX gW + 5 + 3; omega)]; exact h.mB
  · rw [high _ (by show _ ≤ (𝔇).B + 19 + restPc eX pX gW + 5 + 4; omega)]; exact h.mv
  · rw [high _ (by show _ ≤ (𝔇).G + (𝔇).R1 + 397 + (𝔇).w + (𝔇).tc + 11; omega)]; exact h.drv
  · rw [high _ (by show _ ≤ (𝔇).G + (𝔇).R1 + 397 + (𝔇).w + (𝔇).tc + 12; omega)]; exact h.lg
  · rw [high _ (by rw [Dims.hrT_val]; omega)]; exact h.zD
  · rw [high _ (by rw [Dims.hrT_val]; omega)]; exact h.zL
  · by_cases hs : ∃ i, (𝒞).slots i = x
    · obtain ⟨i, rfl⟩ := hs
      rw [viewOf_slot]; exact hS i
    · have hs' : ∀ i, (𝒞).slots i ≠ x := fun i hh => hs ⟨i, hh⟩
      by_cases he : ∃ i, (𝒞).enc i = x
      · obtain ⟨i, rfl⟩ := he
        exact absurd hx (nodirt _ hs' (Or.inr (hencP i)))
      · have he' : ∀ i, (𝒞).enc i ≠ x := fun i hh => he ⟨i, hh⟩
        by_cases ha : ∃ i, (𝒞).app i = x
        · obtain ⟨i, rfl⟩ := ha
          exact absurd hx (nodirt _ hs' (happP i))
        · have ha' : ∀ i, (𝒞).app i ≠ x := fun i hh => ha ⟨i, hh⟩
          rw [viewOf_other 𝒞 b vd j X x hs' he' ha']
          exact h.dirtA x hx hz
  · rw [high x (by unfold SourceConstruction.Dims.InZ at hz; omega)]; exact h.zA x hz

theorem first_startV (ph : Phase) (refill : Σ s, Machine (UOf mask packets rows sources res p k r) s)
    (preF : Σ s, Machine (UOf mask packets rows sources res p k r + 1) s)
    {eX pX gW : Nat} (e : (𝔇).RestExt3 eX pX gW)
    {q : Nat} {circuit : BooleanCircuit q} {pcpp : PointwisePCPP circuit}
    (coordinate : Fin (pcpp.systematicBits + pcpp.auxiliaryBits) →
      ComponentwisePolynomial.CircuitPolynomial (C10TotalDecode.Atom pcpp) 1)
    (ci : Fin (2 ^ pcpp.clauseBits)) (L target : Nat) (mode : Bool) (Rc Rk b : Nat)
    (layoutAt : ∀ m : Nat, Packets.Layout (decompositionOf sources)
      ((requestAt coordinate ph ci L target mode m).family (decompositionOf sources))
      (geometryOf selector (decompositionOf sources) (requestAt coordinate ph ci L target mode m)))
    (factsAt : ∀ m : Nat, ∀ row ∈ ((requestAt coordinate ph ci L target mode m).family (decompositionOf sources)).rows,
      Packets.PacketFacts (decompositionOf sources) ((requestAt coordinate ph ci L target mode m).family
        (decompositionOf sources)) (geometryOf selector (decompositionOf sources) (requestAt coordinate ph ci L target mode m))
        row)
    (K : Fin (UOf mask packets rows sources res p k r) → Prop)
    (K0 : Fin (UOf mask packets rows sources res p k r) → List Bool)
    (KH0 : Fin (UOf mask packets rows sources res p k r) → Nat)
    (K1 : Fin (UOf mask packets rows sources res p k r + 1) → Prop)
    (K01 : Fin (UOf mask packets rows sources res p k r + 1) → List Bool)
    (KH01 : Fin (UOf mask packets rows sources res p k r + 1) → Nat)
    (w Mb Ms cW cQ cB cS S Rw B U0 : Nat)
    {Atom : Type} (vd : RCFive.Source.CallValues Atom (𝒞).sourceTapes)
    -- the clause's data at call `0` (as `seam3_spec`'s at `j+1`)
    (hds0 : vd.ds 0 = dataList (decompositionOf sources) ((requestAt coordinate ph ci L target mode 0).family (decompositionOf sources)) (geometryOf selector (decompositionOf sources) (requestAt coordinate ph ci L target mode 0)) (layoutAt 0) (factsAt 0))
    (hxs0 : (vd.xs 0).length = (vd.ds 0).length)
    (hS0 : vd.S 0 = S) (hR0 : vd.R 0 = Rw) (hB0 : vd.B 0 = B)
    (hrw0 : vd.rowWidth 0 = RowWidth.rw (if 3 < (exactListWord (PCJ38fbfed565f64139_Cached.cacheArgs (decompositionOf sources) ((requestAt coordinate ph ci L target mode 0).family (decompositionOf sources))).gs).length then Mb else Ms) U0 (exactListWord (PCJ38fbfed565f64139_Cached.cacheArgs (decompositionOf sources) ((requestAt coordinate ph ci L target mode 0).family (decompositionOf sources))).gs).length)
    (hRes : vd.reserveSize = Rc) (hcR : vd.counterReserve = Rc)
    (hNm : vd.entries.length = (monomials coordinate ph ci).length)
    -- the kept sets (`seam3_spec`'s `hKpos`; the first prologue's `K1` restricts to `K`)
    (hKpos : ∀ y, K y → y.val < (𝔇).F ∨
      ((𝔇).B + 29 + restPc eX pX gW ≤ y.val ∧ y ≠ Dims.hrT e 𝒽 10 ∧ y ≠ Dims.hrT e 𝒽 11))
    (hK : ∀ y, K y → K1 y.castSucc) (hK0 : ∀ y, K y → K01 y.castSucc = K0 y ∧ KH01 y.castSucc = KH0 y)
    -- `first_seam3L`'s exit and the conclusions used
    (H' : Fin (UOf mask packets rows sources res p k r + 1) → Nat)
    (A' : Fin (UOf mask packets rows sources res p k r + 1) → List Bool)
    (cnt : Fin (UOf mask packets rows sources res p k r + 1)) (hcnt : cnt.val = (𝔇).U)
    (hnatH : ∀ i, H' (Dims.natSlots 𝒽1 i) = r_inputH (printerOf sources) (dataList (decompositionOf sources) ((requestAt coordinate ph ci L target mode 0).family (decompositionOf sources)) (geometryOf selector (decompositionOf sources) (requestAt coordinate ph ci L target mode 0)) (layoutAt 0) (factsAt 0)) S Rw B (dataList (decompositionOf sources) ((requestAt coordinate ph ci L target mode 0).family (decompositionOf sources)) (geometryOf selector (decompositionOf sources) (requestAt coordinate ph ci L target mode 0)) (layoutAt 0) (factsAt 0)).length i)
    (hnatA : ∀ i, A' (Dims.natSlots 𝒽1 i) = ZeroPadding.pad Rc (r_inputT (printerOf sources) (dataList (decompositionOf sources) ((requestAt coordinate ph ci L target mode 0).family (decompositionOf sources)) (geometryOf selector (decompositionOf sources) (requestAt coordinate ph ci L target mode 0)) (layoutAt 0) (factsAt 0)) S Rw B
      (RowWidth.rw (if 3 < (exactListWord (PCJ38fbfed565f64139_Cached.cacheArgs (decompositionOf sources) ((requestAt coordinate ph ci L target mode 0).family (decompositionOf sources))).gs).length then Mb else Ms) U0 (exactListWord (PCJ38fbfed565f64139_Cached.cacheArgs (decompositionOf sources) ((requestAt coordinate ph ci L target mode 0).family (decompositionOf sources))).gs).length) b (dataList (decompositionOf sources) ((requestAt coordinate ph ci L target mode 0).family (decompositionOf sources)) (geometryOf selector (decompositionOf sources) (requestAt coordinate ph ci L target mode 0)) (layoutAt 0) (factsAt 0)).length i))
    (hcA : A' cnt = ZeroPadding.pad Rc (CompareMachine.word (monomials coordinate ph ci).length)) (hcH : H' cnt = 1)
    (hInv : InvR e 𝒽1 Rc Rk K1 K01 KH01 0 w q Mb Ms cW cQ cB cS S Rw B b U0 (fuelOf 𝒞 b vd 0) H' A')
    (hlong : ∀ y : Fin (UOf mask packets rows sources res p k r + 1), (𝔇).F ≤ y.val → y.val < (𝔇).U → Rc ≤ (A' y).length)
    
    (N : Nat)
    (hencP : ∀ i, (𝔇).F ≤ ((𝒞).enc i).val ∧ ((𝒞).enc i).val < (𝔇).G)
    (happP : ∀ i, ((𝒞).app i).val < (𝔇).F ∨ ((𝔇).F ≤ ((𝒞).app i).val ∧ ((𝒞).app i).val < (𝔇).G))
    (hencInj : Function.Injective (𝒞).enc) (happInj : Function.Injective (𝒞).app)
    (hKapp : ∀ y, K y → ∀ i, (𝒞).app i ≠ y)
    (hE0 : 0 < N → ∀ i, (∀ i', (𝒞).slots i' ≠ (𝒞).enc i) →
      ZeroPadding.pad (reserveOf 𝒞 vd ((𝒞).enc i)) (encInOf 𝒞 b vd 0 i) = A' ((𝒞).enc i).castSucc)
    (hA0' : 0 < N → ∀ i, (∀ i', (𝒞).slots i' ≠ (𝒞).app i) → (∀ i', (𝒞).enc i' ≠ (𝒞).app i) →
      ZeroPadding.pad (reserveOf 𝒞 vd ((𝒞).app i)) (appInOf 𝒞 b vd 0 i) = A' ((𝒞).app i).castSucc) :
    (∀ i, (fun y => H' y.castSucc) ((𝒞).slots i) = r_inputH (𝒞).a (vd.ds 0) (vd.S 0) (vd.R 0) (vd.B 0) (vd.xs 0).length i) ∧
    (∀ i, chainView 𝒞 b vd N 0 (fun y => A' y.castSucc) ((𝒞).slots i) =
      r_inputT (𝒞).a (vd.ds 0) (vd.S 0) (vd.R 0) (vd.B 0) (vd.rowWidth 0) b (vd.xs 0).length i) ∧
    InvR e 𝒽 Rc Rk K K0 KH0 0 w q Mb Ms cW cQ cB cS S Rw B b U0 (fuelOf 𝒞 b vd 0) (fun y => H' y.castSucc)
      (chainView 𝒞 b vd N 0 (fun y => A' y.castSucc)) ∧
    (Fin.addCases (fun y : Fin (𝒞).sourceTapes => H' y.castSucc) (fun _ : Fin 1 => (1 : Nat)) : Fin ((𝒞).sourceTapes + 1) → Nat) = H' ∧
    (fun i : Fin ((𝒞).sourceTapes + 1) => ZeroPadding.pad (if i.val = (𝒞).sourceTapes then vd.counterReserve else 0)
      ((Fin.addCases (fun y : Fin (𝒞).sourceTapes =>
          ZeroPadding.pad (if (PCJda54a286946142d3_BranchPhases.offset sources p k r + 1155) ≤ y.val then vd.reserveSize else 0)
            (chainView 𝒞 b vd N 0 (fun z => A' z.castSucc) y))
        (fun _ : Fin 1 => CompareMachine.word vd.entries.length) : Fin ((𝒞).sourceTapes + 1) → List Bool) i)) = A' := by
  obtain ⟨hH0, -, -, hHs, -⟩ := first_start mask packets rows sources res hres p k r ph refill preF e coordinate ci L target mode Rc Rk b
    layoutAt factsAt K K0 KH0 K1 K01 KH01 w Mb Ms cW cQ cB cS S Rw B U0 vd hds0 hxs0 hS0 hR0 hB0 hrw0 hRes hcR hNm hKpos hK hK0
    H' A' cnt hcnt hnatH hnatA hcA hcH hInv hlong
  have hsl : ∀ i, ((𝒞).slots i).castSucc = Dims.natSlots 𝒽1 i := fun _ => Fin.ext rfl
  have hin : ∀ i, inTOf 𝒞 b vd 0 i = r_inputT (printerOf sources) (dataList (decompositionOf sources) ((requestAt coordinate ph ci L target mode 0).family (decompositionOf sources)) (geometryOf selector (decompositionOf sources) (requestAt coordinate ph ci L target mode 0)) (layoutAt 0) (factsAt 0)) S Rw B (RowWidth.rw (if 3 < (exactListWord (PCJ38fbfed565f64139_Cached.cacheArgs (decompositionOf sources) ((requestAt coordinate ph ci L target mode 0).family (decompositionOf sources))).gs).length then Mb else Ms) U0 (exactListWord (PCJ38fbfed565f64139_Cached.cacheArgs (decompositionOf sources) ((requestAt coordinate ph ci L target mode 0).family (decompositionOf sources))).gs).length) b (dataList (decompositionOf sources) ((requestAt coordinate ph ci L target mode 0).family (decompositionOf sources)) (geometryOf selector (decompositionOf sources) (requestAt coordinate ph ci L target mode 0)) (layoutAt 0) (factsAt 0)).length i := by
    intro i
    show r_inputT (printerOf sources) (vd.ds 0) (vd.S 0) (vd.R 0) (vd.B 0) (vd.rowWidth 0) b (vd.xs 0).length i = _
    rw [hxs0, hds0, hS0, hR0, hB0, hrw0]
  have hfA : ∀ i, A' ((𝒞).slots i).castSucc = ZeroPadding.pad Rc (inTOf 𝒞 b vd 0 i) := by
    intro i; rw [hsl i, hnatA i, hin i]
  have hlast : Fin.last (UOf mask packets rows sources res p k r) = cnt := Fin.ext (by rw [hcnt]; rfl)
  have hBG : (𝔇).B = (𝔇).G + (𝔇).R1 + 410 + (𝔇).w + (𝔇).tc := rfl
  have hGF : (𝔇).G = (𝔇).F + (𝔇).rt + 13 := rfl
  have slotv : ∀ i, ((𝒞).slots i).val = (𝔇).F + i.val := fun i => (𝒞)._hs i
  have hrt : (𝔇).rt = r_tapes (𝒞).a := rfl
  -- the slot tapes are dirt, their family words `≤ Rc` (the slot holds `pad Rc inT`, of length `≤ Rc`)
  have hR := InvR.restrict (hV := 𝒽) hInv K K0 KH0 hK hK0
  have hSlen : ∀ i, (inTOf 𝒞 b vd 0 i).length ≤ Rc := by
    intro i
    have hd := hR.dirtA ((𝒞).slots i) (Or.inl (Or.inl (by rw [slotv i]; have := i.isLt; omega)))
      (by unfold SourceConstruction.Dims.InZ; rw [slotv i]; have := i.isLt; omega)
    have hd2 : (A' ((𝒞).slots i).castSucc).length ≤ Rc := hd
    rw [hfA i, ZeroPadding.pad_length] at hd2
    exact (le_max_right _ _).trans hd2
  -- the reserve is `Rc` from `F` on
  have hresF : ∀ y : Fin (UOf mask packets rows sources res p k r), (𝔇).F ≤ y.val → reserveOf 𝒞 vd y = Rc := by
    intro y hy
    show (if _ ≤ y.val then vd.reserveSize else 0) = Rc
    rw [if_pos (by show _ ≤ y.val; exact hy), hRes]
  have hresL : ∀ y : Fin (UOf mask packets rows sources res p k r), reserveOf 𝒞 vd y ≤ (A' y.castSucc).length := by
    intro y
    show (if _ ≤ y.val then vd.reserveSize else 0) ≤ _
    split_ifs with hy
    · rw [hRes]; exact hlong y.castSucc hy y.isLt
    · exact Nat.zero_le _
  -- the re-padding of the chain start
  have hpad : (fun y => ZeroPadding.pad (reserveOf 𝒞 vd y) (chainView 𝒞 b vd N 0 (fun z => A' z.castSucc) y)) =
      (fun y => A' y.castSucc) := by
    by_cases hN : 0 < N
    · rw [chainView_lt 𝒞 b vd N 0 hN]
      exact pad_viewOf 𝒞 b vd hencInj happInj (reserveOf 𝒞 vd) 0 (fun y => A' y.castSucc)
        (fun i => by rw [hresF _ (by rw [slotv i]; omega)]; exact (hfA i).symm) (hE0 hN) (hA0' hN)
        (fun y _ _ _ => hresL y)
    · rw [chainView_ge 𝒞 b vd N 0 (by omega)]
      exact pad_install_slots 𝒞 b vd (reserveOf 𝒞 vd) 0 (fun y => A' y.castSucc)
        (fun i => by rw [hresF _ (by rw [slotv i]; omega)]; exact (hfA i).symm) (fun y _ => hresL y)
  refine ⟨hH0, fun i => ?_, ?_, hHs, ?_⟩
  · by_cases hN : 0 < N
    · rw [chainView_lt 𝒞 b vd N 0 hN, viewOf_slot]
    · rw [chainView_ge 𝒞 b vd N 0 (by omega)]
      exact install_slot _ (slots_injective 𝒞) _ _ i
  · by_cases hN : 0 < N
    · rw [chainView_lt 𝒞 b vd N 0 hN]
      refine invR_viewOf mask packets rows sources res hres p k r ph refill preF hR (fun y hy => ?_) hKapp hencP happP 0 hSlen
      rcases hKpos y hy with h | h
      · exact Or.inl h
      · exact Or.inr (by omega)
    · rw [chainView_ge 𝒞 b vd N 0 (by omega)]
      refine InvR.view hR (fun y hy => ?_) (𝒞).slots (fun _ => rfl) (slots_injective 𝒞) (inTOf 𝒞 b vd 0) (fun i => ?_)
      · rcases hKpos y hy with h | h
        · exact Or.inl h
        · exact Or.inr (by omega)
      · show (inTOf 𝒞 b vd 0 i).length ≤ (A' ((𝒞).slots i).castSucc).length
        rw [hfA i, ZeroPadding.pad_length]
        exact Nat.le_max_right _ _
  · funext i
    refine Fin.addCases (fun y => ?_) (fun jj => ?_) i
    · have hy : (Fin.castAdd 1 y).val ≠ (𝒞).sourceTapes := by simp only [Fin.val_castAdd]; exact Nat.ne_of_lt y.isLt
      beta_reduce
      rw [if_neg hy, ZeroPadding.pad_zero, Fin.addCases_left]
      exact congrFun hpad y
    · have hj : (Fin.natAdd (𝒞).sourceTapes jj).val = (𝒞).sourceTapes := by simp only [Fin.val_natAdd]; have := jj.isLt; omega
      have hl : Fin.natAdd (𝒞).sourceTapes jj = cnt := by rw [← hlast]; exact Fin.ext (by rw [hj]; rfl)
      beta_reduce
      rw [if_pos hj, Fin.addCases_right, hl, hcA, hcR, hNm]

end start

end
end NearCubicWires.SourceSkeleton
end

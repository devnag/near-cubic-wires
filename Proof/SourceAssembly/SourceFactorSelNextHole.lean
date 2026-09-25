import Proof.SourceAssembly.SourceFactorSelNextFinal

section
set_option autoImplicit false
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unusedVariables false

open NearCubicWires NearCubicWires.ComponentwisePolynomial NearCubicWires.RepairOrdinary.CompetitorRawFieldEmit NearCubicWires.RepairOrdinary.CloseoutRowsOriginalSchedule LocalBitMultitape ExtDecompositionBatch RepairOrdinary RepairRepresentation SourceInterfaces RepairSource RepairSource.CloseoutFinal P1TopDown RepairSource.VerifierDecoding RecoveryRootRound RecoveryExecution CloseoutRowsEstimator CloseoutRowsEstimatorCoefficients CompetitorSelectedCount MatrixScoreBatch CompetitorCountMask SupplierPipeline SupplierEstimator SupplierPrime CanonicalFourfoldRowProgram CloseoutRawRows C10ExternalRowLoop C10ThresholdNaturalRowPrint C10ThresholdParityRow C10ThresholdEstimateRowJoin CloseoutFinalC10RowAnswerWord P1Closure P1TopDownPaidReusable P1TopDownPaidReusableReserves P1TopDownPaidBinaryReserves
open PCJ1fef9807c6954e94_Native
open PCJ9eff70d512234a4c_Fixed PCJd4d1d9d7d1fa4313_Production
open PCJc4297ab269d8423a_Source
namespace NearCubicWires.SourceFactorSel.Next
open NearCubicWires.SourceSkeleton NearCubicWires.SourceParent NearCubicWires.SourcePhase NearCubicWires.SourceConstruction
open NearCubicWires.SourceSteps
noncomputable section
attribute [local irreducible] P1TopDownPaidPayload.tapes WorkspaceSelectedAdmission.originalTapes
  WorkspaceSelectedEntry.size SelectedRecoveryIntegration.outer

section slots
variable (sources : EightSources) {gamma : Real} (p : Parameters sources gamma) (k r scratch : Nat)

/-- The phase word slots `81`/`90`: at their own index in the penalty phase, in the phase's tail block otherwise. -/
theorem wd_8190 (ph : Phase) (i : Fin 278) (hi : i.val = 81 ∨ i.val = 90) :
    ((C10TailUniformSlots.phaseIndex ph).val = 0 ∧ (Wd sources p k r scratch ph i).val = i.val) ∨
    ((C10TailUniformSlots.phaseIndex ph).val ≠ 0 ∧ (Wd sources p k r scratch ph i).val =
      PCJda54a286946142d3_BranchPhases.offset sources p k r + 599 + ((C10TailUniformSlots.phaseIndex ph).val - 1) * 278 + i.val) := by
  rcases wd_cases sources p k r scratch ph i with h | h | h | h
  · exfalso; omega
  · exfalso; omega
  · left
    have h4 := h.2.2.2
    refine ⟨?_, h.1⟩
    omega
  · right
    exact ⟨h.2.2.2.2.2.2.2, h.1⟩

/-- A phase word slot lies in the region, below `offset + 1155`, off the cache. -/
theorem wd_facts (mode : Bool) (ph : Phase) (i : Fin 278) (hi : i.val = 81 ∨ i.val = 90) :
    Region (PCJda54a286946142d3_BranchPhases.offset sources p k r) (Wd sources p k r scratch ph i).val ∧
    (Wd sources p k r scratch ph i).val < PCJda54a286946142d3_BranchPhases.offset sources p k r + 1155 ∧
    ∀ j, Wd sources p k r scratch ph i ≠ PCJda54a286946142d3_BranchPhases.cache sources p k r scratch mode j := by
  have hoff := offset_ge_300 sources p k r
  have hidx := (C10TailUniformSlots.phaseIndex ph).isLt
  have hc : ∀ j, (PCJda54a286946142d3_BranchPhases.cache sources p k r scratch mode j).val < 2 ∨
      302 ≤ (PCJda54a286946142d3_BranchPhases.cache sources p k r scratch mode j).val ∧
      (PCJda54a286946142d3_BranchPhases.cache sources p k r scratch mode j).val < PCJda54a286946142d3_BranchPhases.offset sources p k r :=
    fun j => cache_range sources p k r scratch mode j
  rcases wd_8190 sources p k r scratch ph i hi with ⟨h0, hv⟩ | ⟨h0, hv⟩
  · refine ⟨?_, ?_, fun j e => ?_⟩
    · unfold Region
      omega
    · omega
    · have e' := congrArg Fin.val e
      have := hc j
      omega
  · have hle : ((C10TailUniformSlots.phaseIndex ph).val - 1) * 278 ≤ 278 := by
      have : (C10TailUniformSlots.phaseIndex ph).val - 1 ≤ 1 := by omega
      exact (Nat.mul_le_mul_right 278 this).trans (by omega)
    refine ⟨?_, ?_, fun j e => ?_⟩
    · unfold Region
      omega
    · omega
    · have e' := congrArg Fin.val e
      have := hc j
      omega

/-- A later phase's word slots differ from the current phase's. -/
theorem wd_later (ph ph' : Phase) (hL : LaterPhase ph ph') (i i' : Fin 278) (hi : i.val = 81 ∨ i.val = 90)
    (hi' : i'.val = 81 ∨ i'.val = 90) : Wd sources p k r scratch ph' i' ≠ Wd sources p k r scratch ph i := by
  have hpi : (C10TailUniformSlots.phaseIndex ph).val = 0 ∧ (C10TailUniformSlots.phaseIndex ph').val ≠ 0 ∨
      (C10TailUniformSlots.phaseIndex ph).val = 1 ∧ (C10TailUniformSlots.phaseIndex ph').val = 2 := by
    rcases hL with ⟨rfl, rfl | rfl⟩ | ⟨rfl, rfl⟩
    · left; exact ⟨rfl, by decide⟩
    · left; exact ⟨rfl, by decide⟩
    · right; exact ⟨rfl, rfl⟩
  have hoff := offset_ge_300 sources p k r
  intro e
  have e' := congrArg Fin.val e
  rcases wd_8190 sources p k r scratch ph i hi with ⟨h0, hv⟩ | ⟨h0, hv⟩ <;>
    rcases wd_8190 sources p k r scratch ph' i' hi' with ⟨h0', hv'⟩ | ⟨h0', hv'⟩
  · exact absurd hpi (by omega)
  · omega
  · exact absurd hpi (by omega)
  · have hp1 : (C10TailUniformSlots.phaseIndex ph).val = 1 ∧ (C10TailUniformSlots.phaseIndex ph').val = 2 := by omega
    rw [hp1.1] at hv
    rw [hp1.2] at hv'
    omega

end slots

section main
variable (mask : MaskProducer) (selector : CyclicChoice.Laws)
    (packets : PCJc4297ab269d8423a_Source.PacketLibrary selector)
    (rows : PCJc4297ab269d8423a_Source.RowLibrary selector) (compiler : Packets.CompilerLaws)
    (sources : EightSources) {gamma : Real} (p : Parameters sources gamma)
    (den : Nat) (hden : 0 < den) (k r scratch n : Nat) (x : BitInput n) (bits : List Bool)
    (hp : P1Independent.CappedLegalAdmission.passed sources p
      (ControllerCappedSelected.reference den hden k (PolynomialClock.ordinaryClock k))
      (WorkspaceSelectedAdmission.coldCutoff sources) n x bits = true)
    (site : Bool → Phase → Σ states, Machine (ControllerSelectedContinuation.bodyTapes sources p k r scratch) states)
    (code : (ph : Phase) → RCFive.Source.SourceCode mask selector packets rows sources p k r scratch ph)
    (ph : Phase) (ci : Fin (NC sources k (PolynomialClock.ordinaryClock k) x (C10TotalDecode.oracleOf sources k (PolynomialClock.ordinaryClock k) p.degree n bits)))
    (H0 : Fin (ControllerSelectedContinuation.bodyTapes sources p k r scratch) → Nat) (A0 : Fin (ControllerSelectedContinuation.bodyTapes sources p k r scratch) → List Bool)
    (values : RCFive.Source.CallValues (C10TotalDecode.Atom (pcppAt sources k (PolynomialClock.ordinaryClock k) x (C10TotalDecode.oracleOf sources k (PolynomialClock.ordinaryClock k) p.degree n bits))) (code ph).sourceTapes)

set_option hygiene false in
local notation "𝒞" => PCJda54a286946142d3_BranchPhases.cache sources p k r scratch (PCJ374c44bb8b7f47d9_.S.mode sources p den hden k r scratch n x bits hp)
set_option hygiene false in
local notation "𝒜" => install (PCJda54a286946142d3_BranchPhases.cache sources p k r scratch (PCJ374c44bb8b7f47d9_.S.mode sources p den hden k r scratch n x bits hp))
  (finalA mask selector packets rows compiler sources p den hden k r scratch n x bits hp site code ph ci A0 values)
  (CD sources k (PolynomialClock.ordinaryClock k) x (C10TotalDecode.oracleOf sources k (PolynomialClock.ordinaryClock k) p.degree n bits) (ci.val + 1))
set_option hygiene false in
local notation "𝒮" => queriedAt sources p den hden k r scratch n x bits hp (ci.val + 1) 𝒜
set_option hygiene false in
local notation "ℋ" => finalH mask selector packets rows compiler sources p den hden k r scratch n x bits hp site code ph H0 values
set_option hygiene false in
local notation "𝒪" => PCJda54a286946142d3_BranchPhases.offset sources p k r

/-- The exit bank at a low source tape off the cache is the chain end's word. -/
theorem finA_low (hw : ∀ y, ((code ph).whole y).val = y.val) (z : Fin (code ph).sourceTapes) (hlow : z.val < 𝒪 + 1155)
    (hc : ∀ j, (code ph).whole z.castSucc ≠ 𝒞 j) : 𝒜 ((code ph).whole z.castSucc) = values.A values.entries.length z := by
  rw [install_other _ _ _ _ (fun j hj => hc j hj.symm),
    finalA_cs mask selector packets rows compiler sources p den hden k r scratch n x bits hp site code ph ci A0 values hw z,
    if_neg (by omega), ZeroPadding.pad_zero]

/-- A low body tape is the image of a source tape. -/
theorem exists_z (hw : ∀ y, ((code ph).whole y).val = y.val) (t : Fin (ControllerSelectedContinuation.bodyTapes sources p k r scratch))
    (ht : t.val < (code ph).sourceTapes) : ∃ z : Fin (code ph).sourceTapes, (code ph).whole z.castSucc = t :=
  ⟨⟨t.val, ht⟩, Fin.ext (by rw [hw]; rfl)⟩

theorem nextHole_holds (d : SourceConstruction.Dims) {eX pX gW eR eV X : Nat}
    (pl : Phase → SourceConstruction.InitRun.Place d eX pX gW eR eV X ((code ph).sourceTapes + 1))
    (e : d.RestExt3 eX pX gW) (hV : d.U ≤ (code ph).sourceTapes) (Rc Rk Ce : Nat)
    (Kc : Fin ((code ph).sourceTapes + 1) → Prop) (K0 : Phase → Nat → Fin ((code ph).sourceTapes + 1) → List Bool)
    (KH0 : Fin ((code ph).sourceTapes + 1) → Nat)
    (cnt c15 q284 c17 c18 : Fin ((code ph).sourceTapes + 1)) (b q Mb Ms S Rw B U0 : Nat)
    (EF : Phase → Fin (NC sources k (PolynomialClock.ordinaryClock k) x (C10TotalDecode.oracleOf sources k (PolynomialClock.ordinaryClock k) p.degree n bits)) → List Stream.Entry)
    (KU : Fin (code ph).sourceTapes → Prop) (K0U : Fin (code ph).sourceTapes → List Bool) (KH0U : Fin (code ph).sourceTapes → Nat) (fuel : Nat)
    
    (hcK : ∀ (y : Fin (code ph).sourceTapes) (i : Fin 19), (code ph).whole y.castSucc = 𝒞 i → KU y ∧ KH0U y = 0)
    -- (b) the kept words above `F` are padded
    (hKpad : ∀ y : Fin (code ph).sourceTapes, KU y → d.F ≤ y.val → ZeroPadding.pad Rc (K0U y) = K0U y)
    -- (c) the `encT 0..2, 4` lengths at the chain's end
    (henc : ∀ kk : Fin 13, (kk.val < 3 ∨ kk.val = 4) →
      (values.A values.entries.length (Dims.encT (d := d) hV kk)).length ≤ Rc)
    -- (d)
    (hRk : Rc ≤ Rk)
    -- (e) the record width is the site's schedule width
    (hb : b = C10PartsSchedule.entryWidthSchedule sources k r n) :
    NextHole mask selector packets rows compiler sources p den hden k r scratch n x bits hp site code ph ci H0 A0 values
      d pl e hV Rc Rk Ce Kc K0 KH0 cnt c15 q284 c17 c18 b q Mb Ms S Rw B U0 EF KU K0U KH0U fuel := by
  intro hw hF hU hcnt hres hcres hN hwN hInv hEnc hKc1 hKc2 hnlast h15 h17 h18 hq284F hq284c hq284 hPW hent hpre hkeepA hkeepH happ
  have hoff := offset_ge_300 sources p k r
  have hFU : d.F ≤ d.U := by
    unfold Dims.U Dims.G
    omega
  have hcl : ∀ j, (𝒞 j).val < 𝒪 := by
    intro j
    rcases cache_range sources p k r scratch (PCJ374c44bb8b7f47d9_.S.mode sources p den hden k r scratch n x bits hp) j with h | h
    · omega
    · exact h.2
  -- a source tape at or above `F` is off the cache
  have ncF : ∀ z : Fin (code ph).sourceTapes, d.F ≤ z.val → ∀ j, (code ph).whole z.castSucc ≠ 𝒞 j := by
    intro z hz j e'
    have h1 := congrArg Fin.val e'
    rw [hw, Fin.val_castSucc] at h1
    have := hcl j
    omega
  -- the next entry's site bank: above `F`, on the counter, on the cache
  have sA_high : ∀ z : Fin (code ph).sourceTapes, d.F ≤ z.val →
      𝒮 ((code ph).whole z.castSucc) = ZeroPadding.pad Rc (values.A values.entries.length z) := by
    intro z hz
    rw [site_off mask selector packets rows compiler sources p den hden k r scratch n x bits hp site code ph ci A0 values _ (ncF z hz),
      finalA_cs mask selector packets rows compiler sources p den hden k r scratch n x bits hp site code ph ci A0 values hw z,
      if_pos (by omega), hres]
  have nclast : ∀ j, (code ph).whole (Fin.last (code ph).sourceTapes) ≠ 𝒞 j := by
    intro j e'
    have h1 := congrArg Fin.val e'
    rw [hw, Fin.val_last] at h1
    have := hcl j
    omega
  have sA_last : 𝒮 ((code ph).whole (Fin.last (code ph).sourceTapes)) =
      ZeroPadding.pad Rc (CompareMachine.word values.entries.length) := by
    rw [site_off mask selector packets rows compiler sources p den hden k r scratch n x bits hp site code ph ci A0 values _ nclast,
      finalA_last mask selector packets rows compiler sources p den hden k r scratch n x bits hp site code ph ci A0 values hw, hcres]
  have sA_low : ∀ z : Fin (code ph).sourceTapes, z.val < 𝒪 + 1155 → (∀ j, (code ph).whole z.castSucc ≠ 𝒞 j) →
      𝒮 ((code ph).whole z.castSucc) = values.A values.entries.length z := by
    intro z hz hc
    rw [site_off mask selector packets rows compiler sources p den hden k r scratch n x bits hp site code ph ci A0 values _ hc,
      finalA_cs mask selector packets rows compiler sources p den hden k r scratch n x bits hp site code ph ci A0 values hw z,
      if_neg (by omega), ZeroPadding.pad_zero]
  have sA_cache : ∀ (y : Fin ((code ph).sourceTapes + 1)) (j : Fin 19), (code ph).whole y = 𝒞 j →
      𝒮 ((code ph).whole y) = cdAt sources p k n x bits (ci.val + 1) j := fun y j h =>
    site_cache mask selector packets rows compiler sources p den hden k r scratch n x bits hp site code ph ci A0 values _ j h
  have sH : ∀ z : Fin (code ph).sourceTapes, ℋ ((code ph).whole z.castSucc) = values.H values.entries.length z := fun z =>
    finalH_cs mask selector packets rows compiler sources p den hden k r scratch n x bits hp site code ph H0 values hw z
  have sH_last : ℋ ((code ph).whole (Fin.last (code ph).sourceTapes)) = 1 :=
    finalH_last mask selector packets rows compiler sources p den hden k r scratch n x bits hp site code ph H0 values hw
  -- a site tape below `U` is a source tape
  have down : ∀ y : Fin ((code ph).sourceTapes + 1), y.val < (code ph).sourceTapes →
      ∃ z : Fin (code ph).sourceTapes, y = z.castSucc := fun y hy => ⟨⟨y.val, hy⟩, Fin.ext rfl⟩
  -- a cache site tape: below `U`, its head is `0`
  have cacheH : ∀ (y : Fin ((code ph).sourceTapes + 1)) (j : Fin 19), (code ph).whole y = 𝒞 j →
      ℋ ((code ph).whole y) = 0 := by
    intro y j hy
    have hyv : y.val < (code ph).sourceTapes := by
      have h1 := congrArg Fin.val hy
      rw [hw] at h1
      have := hcl j
      omega
    obtain ⟨z, rfl⟩ := down y hyv
    obtain ⟨hk, h0⟩ := hcK z j hy
    rw [sH z, (hInv.kept z hk).2, h0]
  unfold entryInvAt3
  refine ⟨?_, ?_, fun _ => ?_⟩
  · -- the later entry pair
    unfold entryInvAt2
    rw [if_neg (fun h => Nat.succ_ne_zero _ h.2)]
    refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ⟨?_, ?_, ?_, ?_⟩⟩
    · show 𝒮 ((code ph).whole c15) = _
      rw [sA_cache c15 15 h15, cdAt_15]
    · show 𝒮 ((code ph).whole c17) = _
      rw [sA_cache c17 17 h17, cdAt_17]
    · show 𝒮 ((code ph).whole c18) = _
      rw [sA_cache c18 18 h18, cdAt_18]
    · show (𝒮 ((code ph).whole q284)).length ≤ _
      obtain ⟨y, hy, hk, hlen, _⟩ := hq284
      have hyF : y.val < 𝒪 + 1155 := by
        have : y.castSucc.val < d.F := hy ▸ hq284F
        rw [Fin.val_castSucc] at this
        omega
      rw [← hy, sA_low y hyF (hy ▸ hq284c), (hInv.kept y hk).1]
      exact hlen
    · exact cacheH c15 15 h15
    · show ℋ ((code ph).whole q284) = 0
      obtain ⟨y, hy, hk, _, h0⟩ := hq284
      rw [← hy, sH y, (hInv.kept y hk).2, h0]
    · exact cacheH c17 17 h17
    · exact cacheH c18 18 h18
    · -- the driver `scr 11`
      show 𝒮 ((code ph).whole (d.scr (pl ph).hT 11)) = _
      have e1 : d.scr (pl ph).hT 11 = (d.scr hV 11).castSucc := Fin.ext rfl
      have hs : d.F ≤ (d.scr hV 11).val := by
        have vs : (d.scr hV 11).val = d.G + d.R1 + 397 + d.w + d.tc + 11 := rfl
        have hG : d.G = d.F + d.rt + 13 := rfl
        omega
      rw [e1, sA_high _ hs, hInv.drv]
      exact pad_exact _ _ List.length_replicate
    · show ℋ ((code ph).whole (d.scr (pl ph).hT 11)) = 0
      have e1 : d.scr (pl ph).hT 11 = (d.scr hV 11).castSucc := Fin.ext rfl
      rw [e1, sH, hInv.drvH]
    · -- S's clause invariant at the site view
      rw [hcnt]
      refine Rest.InvC_of_InvR (hV1 := (pl ph).hT) hInv hRk hN (le_refl _) (le_refl _) (le_refl _) (le_refl _) Kc (K0 ph (ci.val + 1)) KH0
        (fun i => ℋ ((code ph).whole i)) (fun i => 𝒮 ((code ph).whole i))
        (fun z hz => sA_high z hz) (fun z _ => sH z) ?_ ?_ henc ?_
      · show (𝒮 ((code ph).whole (Fin.last (code ph).sourceTapes))).length ≤ Rc
        rw [sA_last, pad_len]
        omega
      · show ℋ ((code ph).whole (Fin.last (code ph).sourceTapes)) ≤ Rc
        rw [sH_last]
        omega
      · intro y hy
        by_cases hyl : y = Fin.last (code ph).sourceTapes
        · exact absurd (hyl ▸ hy) hnlast
        · have hyv : y.val < (code ph).sourceTapes := by
            have h1 : y.val ≠ (code ph).sourceTapes := fun h => hyl (Fin.ext h)
            have := y.isLt
            omega
          obtain ⟨z, rfl⟩ := down y hyv
          obtain ⟨hkU, hKH, hK0⟩ := hKc1 z hy
          refine ⟨?_, ?_⟩
          · show 𝒮 ((code ph).whole z.castSucc) = _
            by_cases hc : ∃ j, (code ph).whole z.castSucc = 𝒞 j
            · obtain ⟨j, hj⟩ := hc
              rw [sA_cache _ j hj, (hKc2 _ j hy hj).1]
            · have hc' : ∀ j, (code ph).whole z.castSucc ≠ 𝒞 j := fun j h => hc ⟨j, h⟩
              rw [hK0 hc']
              by_cases hzF : d.F ≤ z.val
              · rw [sA_high z hzF, (hInv.kept z hkU).1, hKpad z hkU hzF]
              · rw [sA_low z (by omega) hc', (hInv.kept z hkU).1]
          · show ℋ ((code ph).whole z.castSucc) = _
            rw [sH z, (hInv.kept z hkU).2, hKH]
    · -- every region tape above `F` is padded to `Rc`
      intro y hyF hyU
      have hyU' : y.val < d.U := hyU
      have hyF' : d.F ≤ y.val := hyF
      obtain ⟨z, rfl⟩ := down y (by omega)
      show Rc ≤ (𝒮 ((code ph).whole z.castSucc)).length
      rw [sA_high z (by rw [Fin.val_castSucc] at hyF'; exact hyF'), pad_len]
      omega
  · -- the phase words at `ci + 1`
    show PhaseWords sources p k r scratch n x bits b EF ph (ci.val + 1) 𝒜 ℋ
    have hVF : 𝒪 + 1155 ≤ (code ph).sourceTapes := by omega
    -- the current phase's two word slots
    have f81 := wd_facts sources p k r scratch (PCJ374c44bb8b7f47d9_.S.mode sources p den hden k r scratch n x bits hp) ph 81 (Or.inl rfl)
    have f90 := wd_facts sources p k r scratch (PCJ374c44bb8b7f47d9_.S.mode sources p den hden k r scratch n x bits hp) ph 90 (Or.inr rfl)
    obtain ⟨z81, hz81⟩ := exists_z mask selector packets rows sources p k r scratch code ph hw _ (by omega : (Wd sources p k r scratch ph 81).val < (code ph).sourceTapes)
    obtain ⟨z90, hz90⟩ := exists_z mask selector packets rows sources p k r scratch code ph hw _ (by omega : (Wd sources p k r scratch ph 90).val < (code ph).sourceTapes)
    have v81 : z81.val = (Wd sources p k r scratch ph 81).val := by
      rw [← hz81, hw, Fin.val_castSucc]
    have v90 : z90.val = (Wd sources p k r scratch ph 90).val := by
      rw [← hz90, hw, Fin.val_castSucc]
    have c81 : ∀ j, (code ph).whole z81.castSucc ≠ 𝒞 j := by rw [hz81]; exact f81.2.2
    have c90 : ∀ j, (code ph).whole z90.castSucc ≠ 𝒞 j := by rw [hz90]; exact f90.2.2
    have a81 : 𝒜 (Wd sources p k r scratch ph 81) = values.A values.entries.length z81 := by
      rw [← hz81]
      exact finA_low mask selector packets rows compiler sources p den hden k r scratch n x bits hp site code ph ci A0 values hw z81 (by omega) c81
    have a90 : 𝒜 (Wd sources p k r scratch ph 90) = values.A values.entries.length z90 := by
      rw [← hz90]
      exact finA_low mask selector packets rows compiler sources p den hden k r scratch n x bits hp site code ph ci A0 values hw z90 (by omega) c90
    have hpre1 : values.phasePrefix ++ values.entries = prefixEntries (EF ph) (ci.val + 1) := by
      rw [hpre, hent, prefixEntries_succ (EF ph) ci.val ci.isLt]
    obtain ⟨p81, p90, q81, q90, pl'⟩ := hPW
    have hap := happ (by rw [hpre, ← hb]; exact p81) (by rw [hpre]; exact p90) z81 z90 hz81 hz90
    refine ⟨?_, ?_, ?_, ?_, fun ph' hL => ?_⟩
    · rw [a81, hap.1, hpre1, hb]
    · rw [a90, hap.2, hpre1]
    · show ℋ (Wd sources p k r scratch ph 81) = 0
      rw [← hz81, sH z81, hkeepH z81 (v81 ▸ f81.1) c81, hz81]
      exact q81
    · show ℋ (Wd sources p k r scratch ph 90) = 0
      rw [← hz90, sH z90, hkeepH z90 (v90 ▸ f90.1) c90, hz90]
      exact q90
    · -- a later phase's slots: kept from the entry
      obtain ⟨l81, l90, m81, m90⟩ := pl' ph' hL
      have g81 := wd_facts sources p k r scratch (PCJ374c44bb8b7f47d9_.S.mode sources p den hden k r scratch n x bits hp) ph' 81 (Or.inl rfl)
      have g90 := wd_facts sources p k r scratch (PCJ374c44bb8b7f47d9_.S.mode sources p den hden k r scratch n x bits hp) ph' 90 (Or.inr rfl)
      obtain ⟨y81, hy81⟩ := exists_z mask selector packets rows sources p k r scratch code ph hw _ (by omega : (Wd sources p k r scratch ph' 81).val < (code ph).sourceTapes)
      obtain ⟨y90, hy90⟩ := exists_z mask selector packets rows sources p k r scratch code ph hw _ (by omega : (Wd sources p k r scratch ph' 90).val < (code ph).sourceTapes)
      have w81 : y81.val = (Wd sources p k r scratch ph' 81).val := by
        rw [← hy81, hw, Fin.val_castSucc]
      have w90 : y90.val = (Wd sources p k r scratch ph' 90).val := by
        rw [← hy90, hw, Fin.val_castSucc]
      have d81 : ∀ j, (code ph).whole y81.castSucc ≠ 𝒞 j := by rw [hy81]; exact g81.2.2
      have d90 : ∀ j, (code ph).whole y90.castSucc ≠ 𝒞 j := by rw [hy90]; exact g90.2.2
      have n81a : (code ph).whole y81.castSucc ≠ Wd sources p k r scratch ph 81 := by
        rw [hy81]; exact wd_later sources p k r scratch ph ph' hL 81 81 (Or.inl rfl) (Or.inl rfl)
      have n81b : (code ph).whole y81.castSucc ≠ Wd sources p k r scratch ph 90 := by
        rw [hy81]; exact wd_later sources p k r scratch ph ph' hL 90 81 (Or.inr rfl) (Or.inl rfl)
      have n90a : (code ph).whole y90.castSucc ≠ Wd sources p k r scratch ph 81 := by
        rw [hy90]; exact wd_later sources p k r scratch ph ph' hL 81 90 (Or.inl rfl) (Or.inr rfl)
      have n90b : (code ph).whole y90.castSucc ≠ Wd sources p k r scratch ph 90 := by
        rw [hy90]; exact wd_later sources p k r scratch ph ph' hL 90 90 (Or.inr rfl) (Or.inr rfl)
      refine ⟨?_, ?_, ?_, ?_⟩
      · rw [← hy81, finA_low mask selector packets rows compiler sources p den hden k r scratch n x bits hp site code ph ci A0 values hw y81 (by omega) d81,
          hkeepA y81 (w81 ▸ g81.1) d81 n81a n81b, hy81]
        exact l81
      · rw [← hy90, finA_low mask selector packets rows compiler sources p den hden k r scratch n x bits hp site code ph ci A0 values hw y90 (by omega) d90,
          hkeepA y90 (w90 ▸ g90.1) d90 n90a n90b, hy90]
        exact l90
      · show ℋ (Wd sources p k r scratch ph' 81) = 0
        rw [← hy81, sH y81, hkeepH y81 (w81 ▸ g81.1) d81, hy81]
        exact m81
      · show ℋ (Wd sources p k r scratch ph' 90) = 0
        rw [← hy90, sH y90, hkeepH y90 (w90 ▸ g90.1) d90, hy90]
        exact m90
  · -- the emitter/appender words (the chain end's, padded once more)
    show EncWords (pl ph).hT Rc b (fun i => ℋ ((code ph).whole i)) (fun i => 𝒮 ((code ph).whole i))
    have encF : ∀ kk : Fin 13, d.F ≤ (Dims.encT (d := d) hV kk).val := fun kk => by
      have : (Dims.encT (d := d) hV kk).val = d.F + d.rt + kk.val := rfl
      omega
    have encE : ∀ kk : Fin 13, Dims.encT (d := d) (pl ph).hT kk = (Dims.encT (d := d) hV kk).castSucc := fun _ => Fin.ext rfl
    have encA : ∀ kk : Fin 13, 𝒮 ((code ph).whole (Dims.encT (d := d) (pl ph).hT kk)) =
        ZeroPadding.pad Rc (values.A values.entries.length (Dims.encT (d := d) hV kk)) := fun kk => by
      rw [encE, sA_high _ (encF kk)]
    obtain ⟨eH, eW, eA, eP⟩ := hEnc
    refine ⟨fun kk => ?_, fun en old => ⟨?_, ?_, ?_, ?_, ?_⟩, fun en xs => ⟨?_, ?_, ?_⟩, ?_⟩
    · show ℋ ((code ph).whole (Dims.encT (d := d) (pl ph).hT kk)) = 0
      rw [encE, sH, eH kk]
    · show 𝒮 ((code ph).whole (Dims.encT (d := d) (pl ph).hT 3)) = _
      rw [encA, (eW en old).1, pad_pad]
    · show 𝒮 ((code ph).whole (Dims.encT (d := d) (pl ph).hT 6)) = _
      rw [encA, (eW en old).2.1, pad_pad]
    · show 𝒮 ((code ph).whole (Dims.encT (d := d) (pl ph).hT 7)) = _
      rw [encA, (eW en old).2.2.1, pad_pad]
    · show 𝒮 ((code ph).whole (Dims.encT (d := d) (pl ph).hT 8)) = _
      rw [encA, (eW en old).2.2.2.1, pad_pad]
    · show 𝒮 ((code ph).whole (Dims.encT (d := d) (pl ph).hT 9)) = _
      rw [encA, (eW en old).2.2.2.2, pad_pad]
    · show 𝒮 ((code ph).whole (Dims.encT (d := d) (pl ph).hT 10)) = _
      rw [encA, (eA en xs).1, pad_pad]
    · show 𝒮 ((code ph).whole (Dims.encT (d := d) (pl ph).hT 11)) = _
      rw [encA, (eA en xs).2.1, pad_pad]
    · show 𝒮 ((code ph).whole (Dims.encT (d := d) (pl ph).hT 12)) = _
      rw [encA, (eA en xs).2.2, pad_pad]
    · obtain ⟨w, hwl, hw5⟩ := eP
      refine ⟨w, hwl, ?_⟩
      show 𝒮 ((code ph).whole (Dims.encT (d := d) (pl ph).hT 5)) = _
      rw [encA, hw5, pad_pad]

end main

end
end NearCubicWires.SourceFactorSel.Next
end


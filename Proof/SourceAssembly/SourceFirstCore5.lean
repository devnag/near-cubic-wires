import Proof.SourceAssembly.SourceFirstCore4

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

section concrete
variable (mask : MaskProducer) {selector : CyclicChoice.Laws}
  (packets : PCJc4297ab269d8423a_Source.PacketLibrary selector)
  (rows : PCJc4297ab269d8423a_Source.RowLibrary selector) (sources : EightSources) (res : Nat)
  {gamma : Real} (p : Parameters sources gamma) (k r : Nat)

set_option hygiene false in
local notation "𝔇" => dimsOf mask packets rows sources res p k r

theorem first_rest_run_d5 {vE vP : Request → Nat}
    (se : PacketsGlue.RequestMeta.UnaryStage (decompositionOf sources) vE)
    (sp : PacketsGlue.RequestMeta.UnaryStage (decompositionOf sources) vP) {gW : Nat}
    (e : (𝔇).RestExt se.extra sp.extra gW) {V : Nat} (hV : (𝔇).U ≤ V)
    {s7 : Nat} (g7M : Machine V s7) (g7cost : Nat → Nat)
    {q : Nat} {circuit : BooleanCircuit q} {pcpp : PointwisePCPP circuit}
    (coordinate : Fin (pcpp.systematicBits + pcpp.auxiliaryBits) →
      ComponentwisePolynomial.CircuitPolynomial (C10TotalDecode.Atom pcpp) 1)
    (ph : CloseoutRowsOriginalSchedule.Phase) (ci : Fin (2 ^ pcpp.clauseBits))
    (L target : Nat) (mode : Bool) (Rc b : Nat)
    (layoutAt : ∀ m : Nat, Packets.Layout (decompositionOf sources)
      ((requestAt coordinate ph ci L target mode m).family (decompositionOf sources))
      (geometryOf selector (decompositionOf sources) (requestAt coordinate ph ci L target mode m)))
    (capsAt : Nat → RowCaps)
    (K : Fin V → Prop) (K0 : Fin V → List Bool) (KH0 : Fin V → Nat)
    (hG7 : ResidentRunH g7M g7cost mask (packets (decompositionOf sources))
      (rows (decompositionOf sources) (printerOf sources))
      ((𝔇).maskSlots hV) ((𝔇).pslots hV) ((𝔇).slot hV) ((𝔇).ret hV) ((𝔇).scr hV 0) ((𝔇).scr hV 1)
      ((𝔇).familySlots hV) ((𝔇).poolSlots hV) (Dims.rewind2Slots e.ext hV)
      ((𝔇).scr hV 5) ((𝔇).scr hV 6) ((𝔇).scr hV 7) ((𝔇).scr hV 8) ((𝔇).scr hV 9) ((𝔇).scr hV 10)
      (Dims.lenTape e.ext hV) coordinate ph ci L target mode Rc b
      ((𝔇).pcT e hV ⟨70, by unfold restPc; omega⟩)
      (fun i => (𝔇).pcT e hV ⟨61 + i.val, by have := i.isLt; unfold restPc; omega⟩) layoutAt capsAt
      (Dims.Rpad (d := 𝔇) (eX := se.extra) (pX := sp.extra) (gW := gW) (V := V) Rc)
      (RestIn4 (𝔇) se.extra sp.extra gW Rc ((𝔇).pcT e hV ⟨64, by unfold restPc; omega⟩) K K0 KH0)
      (fun x => OutV (𝔇) se.extra sp.extra gW x.val))
    (w cW cQ Mb Ms cB cS : Nat)
    (H : Fin V → Nat) (A : Fin V → List Bool)
    (hclr : ∀ x : Fin V, (𝔇).InClear se.extra sp.extra gW x.val → Rc ≤ (A x).length)
    (hpc : ∀ i : Fin (restPc se.extra sp.extra gW), A ((𝔇).pcT e hV i) = List.replicate Rc false ∧
      H ((𝔇).pcT e hV i) = 0)
    (hOut : ∀ x : Fin V, OutV (𝔇) se.extra sp.extra gW x.val → A x = List.replicate Rc false ∧ H x = 0)
    (hK : ∀ x, K x → A x = K0 x ∧ H x = KH0 x)
    (hclrB : ∀ x : Fin V, (𝔇).InClear se.extra sp.extra gW x.val → x ≠ (𝔇).pcT e hV ⟨64, by unfold restPc; omega⟩ →
      A x = List.replicate Rc false ∧ H x = 0)
    (henc : ∀ kk : Fin 13, (kk.val < 3 ∨ kk.val = 4) → (A (Dims.encT (d := 𝔇) hV kk)).length ≤ Rc)
    (hencH : ∀ kk : Fin 13, (kk.val < 3 ∨ kk.val = 4) → H (Dims.encT (d := 𝔇) hV kk) = 0)
    (hW : A ((𝔇).rsT e hV 3) = ZeroPadding.pad cW (List.replicate w true)) (hWH : H ((𝔇).rsT e hV 3) = 0)
    (hQ : A ((𝔇).rsT e hV 4) = ZeroPadding.pad cQ (List.replicate q true)) (hQH : H ((𝔇).rsT e hV 4) = 0)
    (hdrv : A ((𝔇).scr hV 11) = List.replicate Rc true) (hdrvH : H ((𝔇).scr hV 11) = 0)
    (hlg : A ((𝔇).scr hV 12) = List.replicate (Rc+2) false) (hlgH : H ((𝔇).scr hV 12) = 0)
    (hbig : A ((𝔇).rsT e hV 0) = ZeroPadding.pad cB (List.replicate Mb true)) (hbigH : H ((𝔇).rsT e hV 0) = 0)
    (hsmall : A ((𝔇).rsT e hV 1) = ZeroPadding.pad cS (List.replicate Ms true))
    (hsmallH : H ((𝔇).rsT e hV 1) = 0)
    (hcs1 : A (Dims.csSlots e.ext hV 1) = List.replicate Rc false) (hcs1H : H (Dims.csSlots e.ext hV 1) = 0)
    (hlog : 2 * ((requestAt coordinate ph ci L target mode 0).input (decompositionOf sources)).length + 1 ≤ Rc)
    (he1 : 1 ≤ vE (requestAt coordinate ph ci L target mode 0))
    (hpw : (CloseoutRowsCountBinary.bits (vP (requestAt coordinate ph ci L target mode 0))).length ≤ w)
    (hfirst : vP (requestAt coordinate ph ci L target mode 0) *
      2^(natBitLength (vE (requestAt coordinate ph ci L target mode 0))) < 2^w)
    (hsecond : vP (requestAt coordinate ph ci L target mode 0) *
      vE (requestAt coordinate ph ci L target mode 0) * 2^(q+1) < 2^w) :
    ∃ (H' : Fin V → Nat) (A' : Fin V → List Bool) (Av' : Fin V → List Bool),
      Step (Composition.machine g7M (backMachine se sp e hV))
        (g7cost 0 + 1 + backCost se sp (requestAt coordinate ph ci L target mode 0)
          Rc w q (exactListWord (PCJ38fbfed565f64139_Cached.cacheArgs (decompositionOf sources)
            ((requestAt coordinate ph ci L target mode 0).family (decompositionOf sources))).gs).length
          Mb Ms) H A H' A' ∧
      (∀ x, A' x = ZeroPadding.pad (Dims.Rpad (d := 𝔇) (eX := se.extra) (pX := sp.extra) (gW := gW) (V := V) Rc x)
        (Av' x)) ∧
      Nonempty (Resident mask (packets (decompositionOf sources)) (rows (decompositionOf sources) (printerOf sources))
        ((𝔇).maskSlots hV) ((𝔇).pslots hV) ((𝔇).slot hV) ((𝔇).ret hV) ((𝔇).scr hV 0) ((𝔇).scr hV 1)
        ((𝔇).familySlots hV) ((𝔇).poolSlots hV) (Dims.rewind2Slots e.ext hV)
        ((𝔇).scr hV 5) ((𝔇).scr hV 6) ((𝔇).scr hV 7) ((𝔇).scr hV 8) ((𝔇).scr hV 9) ((𝔇).scr hV 10)
        (Dims.lenTape e.ext hV) (requestAt coordinate ph ci L target mode 0) (layoutAt 0) (capsAt 0)
        H' Av') ∧
      A' (Dims.encT (d := 𝔇) hV 4) = ZeroPadding.pad Rc (RepairOrdinary.frame (SignedSortKey.binary w
        (vP (requestAt coordinate ph ci L target mode 0) * vE (requestAt coordinate ph ci L target mode 0) *
          2^q))) ∧
      (∀ hm : 0 < (monomials coordinate ph ci).length, ∀ i : Fin 3, A' (Dims.encT (d := 𝔇) hV ⟨i.val, by omega⟩) =
        ZeroPadding.pad Rc (RepairOrdinary.frame (CloseoutRowsEstimatorCoefficients.Stream.recordFields b
          (CloseoutFinalC10SupplierCalls.coefficientEstimate ((monomials coordinate ph ci)[0]).coefficient)
          0 0 ⟨i.val, by omega⟩))) ∧
      A' (Dims.csSlots e.ext hV 1) = ZeroPadding.pad Rc (List.replicate
        (if 3 < (exactListWord (PCJ38fbfed565f64139_Cached.cacheArgs (decompositionOf sources)
            ((requestAt coordinate ph ci L target mode 0).family (decompositionOf sources))).gs).length
          then Mb else Ms) true) ∧
      (∀ x : Fin V, ¬ OutV (𝔇) se.extra sp.extra gW x.val →
        ¬ ((𝔇).B + 19 ≤ x.val ∧ x.val < (𝔇).B + 19 + restPc se.extra sp.extra gW) →
        x ≠ Dims.csSlots e.ext hV 1 →
        ¬ ((𝔇).F + (𝔇).rt ≤ x.val ∧ x.val ≤ (𝔇).F + (𝔇).rt + 4 ∧ x.val ≠ (𝔇).F + (𝔇).rt + 3) →
        A' x = A x ∧ H' x = H x) ∧
      (∀ x : Fin V, ¬ OutV (𝔇) se.extra sp.extra gW x.val →
        ¬ ((𝔇).B + 19 + 71 ≤ x.val ∧ x.val < (𝔇).B + 19 + 71 + se.extra + sp.extra) →
        H' x = H x) ∧
      A' ((𝔇).pcT e hV ⟨70, by unfold restPc; omega⟩) =
        ZeroPadding.pad Rc (RepairSource.VerifierDecoding.CompareMachine.word (monomials coordinate ph ci).length) ∧
      H' ((𝔇).pcT e hV ⟨70, by unfold restPc; omega⟩) = 0 ∧
      (∀ x : Fin V, OutV (𝔇) se.extra sp.extra gW x.val → ¬ (𝔇).InZ se.extra sp.extra x.val →
        H' x ≤ H x + g7cost 0 ∧ (A' x).length ≤ Rc) ∧
      (∀ i : Fin 3, (A' (Dims.encT (d := 𝔇) hV ⟨i.val, by omega⟩)).length ≤ Rc) := by
  classical

  have hres := e.hres
  have vPc : restPc se.extra sp.extra gW = 71 + se.extra + sp.extra + gW := rfl
  have vG : (𝔇).G = (𝔇).F + (𝔇).rt + 13 := rfl
  have vB : (𝔇).B = (𝔇).G + (𝔇).R1 + 410 + (𝔇).w + (𝔇).tc := rfl
  have vp : (𝔇).pscr = (𝔇).R1 + 408 + (𝔇).w + (𝔇).tc := rfl
  have Ac_cur : A ((𝔇).pcT e hV ⟨64, by unfold restPc; omega⟩) = ZeroPadding.pad Rc (List.replicate 0 true) := by
    rw [(hpc _).1]; exact (Finish.blank_is_padded Rc).symm
  
  have hin : RestIn (𝔇) se.extra sp.extra gW Rc ((𝔇).pcT e hV ⟨64, by unfold restPc; omega⟩) K K0 KH0 0 H A :=
    ⟨fun x hx => hOut x hx, Ac_cur, (hpc _).2, fun x hx => hK x hx⟩
  obtain ⟨H1, A1, Av, sG, hpad, ⟨res1⟩, hnTH, hnTW, hcoefH, hcoefW, hfr, hOL⟩ := hG7 0 (Nat.zero_le _) H A ⟨hin, hclrB⟩
  have fr1 : ∀ x : Fin V, ¬ OutV (𝔇) se.extra sp.extra gW x.val → A1 x = A x ∧ H1 x = H x := fun x h1 => hfr x h1
  have Rpad_clear : ∀ x : Fin V, (𝔇).InClear se.extra sp.extra gW x.val →
      Dims.Rpad (d := 𝔇) (eX := se.extra) (pX := sp.extra) (gW := gW) (V := V) Rc x = Rc := by
    intro x hx; simp only [Dims.Rpad, if_pos hx]
  have scr_clear : ∀ m : Fin 13, m.val ≤ 10 → (𝔇).InClear se.extra sp.extra gW ((𝔇).scr hV m).val := by
    intro m hm
    unfold SourceConstruction.Dims.InClear
    right; left
    show (𝔇).G ≤ (𝔇).G + (𝔇).R1 + 397 + (𝔇).w + (𝔇).tc + m.val ∧ (𝔇).G + (𝔇).R1 + 397 + (𝔇).w + (𝔇).tc + m.val < (𝔇).G + (𝔇).pscr
    omega
  
  have fr1_rs : ∀ i : Fin 5, i.val ≠ 2 → A1 ((𝔇).rsT e hV i) = A ((𝔇).rsT e hV i) ∧ H1 ((𝔇).rsT e hV i) = H ((𝔇).rsT e hV i) := by
    intro i hi
    have := i.isLt
    exact fr1 _ (notOut_rs (𝔇) se.extra sp.extra gW i.val)
  have fr1_enc : ∀ kk : Fin 13, A1 ((𝔇).encT hV kk) = A ((𝔇).encT hV kk) ∧ H1 ((𝔇).encT hV kk) = H ((𝔇).encT hV kk) := by
    intro kk
    have := kk.isLt
    exact fr1 _ (notOut_enc (𝔇) se.extra sp.extra gW kk.val kk.isLt)
  have fr1_scr : ∀ m : Fin 13, 11 ≤ m.val → A1 ((𝔇).scr hV m) = A ((𝔇).scr hV m) ∧ H1 ((𝔇).scr hV m) = H ((𝔇).scr hV m) := by
    intro m hm
    have := m.isLt
    exact fr1 _ (notOut_scr (𝔇) se.extra sp.extra gW m.val hm (by omega))
  have fr1_cs1 : A1 (Dims.csSlots e.ext hV 1) = A (Dims.csSlots e.ext hV 1) ∧
      H1 (Dims.csSlots e.ext hV 1) = H (Dims.csSlots e.ext hV 1) :=
    fr1 _ (notOut_cs1 (𝔇) se.extra sp.extra gW)
  
  obtain ⟨H', A', sB, bEnc4, bEnc, bCs1, bFr, bH, b70⟩ := back_run70 se sp e hV
    (requestAt coordinate ph ci L target mode 0) Rc (max Rc res1.capS1) (max Rc res1.capD1) w q cW cQ
    (exactListWord (PCJ38fbfed565f64139_Cached.cacheArgs (decompositionOf sources)
      ((requestAt coordinate ph ci L target mode 0).family (decompositionOf sources))).gs).length
    (max Rc res1.capLen) Mb Ms cB cS H1 A1
    (by rw [hpad, Rpad_clear _ (scr_clear 5 (by decide)), res1.w_input, Uniform.pad_pad])
    (by rw [hpad, Rpad_clear _ (scr_clear 6 (by decide)), res1.w_inputLen, Uniform.pad_pad])
    res1.hH_s1 res1.hH_d1 hlog
    (by
      intro i hi
      rw [(fr1 _ (notOut_pcv (𝔇) se.extra sp.extra gW i.val (by omega))).1]
      exact (hpc i).1)
    (by
      intro i hi
      by_cases hc : 61 ≤ i.val ∧ i.val < 64
      · have e1 : i = ⟨61 + (i.val - 61), by unfold restPc; omega⟩ := Fin.ext (by simp; omega)
        rw [e1]; exact hcoefH ⟨i.val - 61, by omega⟩
      by_cases h70 : i.val = 70
      · rw [show i = ⟨70, by unfold restPc; omega⟩ from Fin.ext h70]; exact hnTH
      by_cases h64 : i.val = 64 ∨ i.val = 65
      · rw [(hfr _ (notOut_pcv (𝔇) se.extra sp.extra gW i.val (by omega))).2]; exact (hpc i).2
      · rw [(fr1 _ (notOut_pcv (𝔇) se.extra sp.extra gW i.val (by omega))).2]
        exact (hpc i).2)
    (by
      intro kk
      have hle := hOL ((𝔇).pcT e hV ⟨61 + kk.val, by unfold restPc; omega⟩)
        (isOut_coef (𝔇) se.extra sp.extra gW (61 + kk.val) (by omega))
      have h0 := CloseoutFinalC10WorkerEmitShape.Step_length_le sG ((𝔇).pcT e hV ⟨61 + kk.val, by unfold restPc; omega⟩)
      rw [(hpc _).1, List.length_replicate] at h0
      omega)
    (fun kk hk => by rw [(fr1_enc kk).1]; exact henc kk hk)
    (fun kk hk => by rw [(fr1_enc kk).2]; exact hencH kk hk)
    (by rw [(fr1_rs 3 (by decide)).1]; exact hW) (by rw [(fr1_rs 3 (by decide)).2]; exact hWH)
    (by rw [(fr1_rs 4 (by decide)).1]; exact hQ) (by rw [(fr1_rs 4 (by decide)).2]; exact hQH)
    (by rw [(fr1_scr 11 (by decide)).1]; exact hdrv) (by rw [(fr1_scr 11 (by decide)).2]; exact hdrvH)
    (by rw [(fr1_scr 12 (by decide)).1]; exact hlg) (by rw [(fr1_scr 12 (by decide)).2]; exact hlgH)
    (by rw [(fr1_rs 0 (by decide)).1]; exact hbig) (by rw [(fr1_rs 0 (by decide)).2]; exact hbigH)
    (by rw [(fr1_rs 1 (by decide)).1]; exact hsmall) (by rw [(fr1_rs 1 (by decide)).2]; exact hsmallH)
    (by
      have hlc : (𝔇).InClear se.extra sp.extra gW (Dims.lenTape e.ext hV).val := by
        unfold SourceConstruction.Dims.InClear; right; right; left
        show (𝔇).B ≤ (𝔇).B ∧ (𝔇).B < (𝔇).B + 14
        omega
      rw [hpad, Rpad_clear _ hlc, res1.w_len, Uniform.pad_pad])
    res1.hH_len
    (by rw [fr1_cs1.1, hcs1]; exact (Finish.blank_is_padded Rc).symm)
    (by rw [fr1_cs1.2]; exact hcs1H)
    he1 hpw hfirst hsecond
  -- 4. the padded exit
  let Av' : Fin V → List Bool := fun x => if A' x = A1 x then Av x else A' x
  have hM' : ∀ x, A' x = ZeroPadding.pad (Dims.Rpad (d := 𝔇) (eX := se.extra) (pX := sp.extra) (gW := gW)
      (V := V) Rc x) (Av' x) := by
    intro x
    by_cases hx : A' x = A1 x
    · simp only [Av', if_pos hx]; rw [hx]; exact hpad x
    · simp only [Av', if_neg hx]
      by_cases hc : (𝔇).InClear se.extra sp.extra gW x.val
      · rw [Rpad_clear x hc]
        have hl : Rc ≤ (A' x).length := by
          have h0 := CloseoutFinalC10WorkerEmitShape.Step_length_le (sG.seq sB) x
          exact (hclr x hc).trans h0
        simp only [ZeroPadding.pad, Nat.sub_eq_zero_of_le hl, List.replicate_zero, List.append_nil]
      · simp only [Dims.Rpad, if_neg hc, ZeroPadding.pad_zero]
  have keepT : ∀ x : Fin V, LowT (𝔇) x.val → A' x = A1 x ∧ H' x = H1 x := by
    intro x hx
    obtain ⟨b1, b2, b3, b4⟩ := low_back hx se.extra sp.extra
    exact ⟨bFr x (ne_val (by show x.val ≠ (𝔇).B + 13; exact b1)) (by omega) b3, bH x b4⟩
  have avT : ∀ x : Fin V, LowT (𝔇) x.val → Av' x = Av x := by
    intro x hx
    simp only [Av', if_pos (keepT x hx).1]
  have res' := resident_transport res1 H' Av'
    (fun jj => avT _ (low_slot hV jj)) (fun ii => avT _ (low_mask hV ii)) (fun jj => avT _ (low_pslots hV jj))
    (fun ii => avT _ (low_pool hV ii)) (fun ii => avT _ (low_family hV ii)) (fun ii => avT _ (low_rewind e.ext hV ii))
    (fun ii => avT _ (low_ret hV ii)) (avT _ (low_scr hV 0 (by decide))) (avT _ (low_scr hV 1 (by decide)))
    (avT _ (low_scr hV 5 (by decide))) (avT _ (low_scr hV 6 (by decide))) (avT _ (low_scr hV 7 (by decide)))
    (avT _ (low_scr hV 8 (by decide))) (avT _ (low_scr hV 9 (by decide))) (avT _ (low_scr hV 10 (by decide)))
    (avT _ (low_len e.ext hV))
    (fun jj => (keepT _ (low_slot hV jj)).2) (fun ii => (keepT _ (low_mask hV ii)).2)
    (fun jj => (keepT _ (low_pslots hV jj)).2) (fun ii => (keepT _ (low_pool hV ii)).2)
    (fun ii => (keepT _ (low_family hV ii)).2) (fun ii => (keepT _ (low_rewind e.ext hV ii)).2)
    (fun ii => (keepT _ (low_ret hV ii)).2) (keepT _ (low_scr hV 0 (by decide))).2
    (keepT _ (low_scr hV 1 (by decide))).2 (keepT _ (low_scr hV 5 (by decide))).2
    (keepT _ (low_scr hV 6 (by decide))).2 (keepT _ (low_scr hV 7 (by decide))).2
    (keepT _ (low_scr hV 8 (by decide))).2 (keepT _ (low_scr hV 9 (by decide))).2
    (keepT _ (low_scr hV 10 (by decide))).2 (keepT _ (low_len e.ext hV)).2
  refine ⟨H', A', Av', sG.seq sB, hM', ⟨res'⟩, bEnc4, ?_, bCs1, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro hm i
    rw [bEnc i]
    exact (hcoefW hm) i
  · intro x h1 h2 h4 h5
    exact ⟨(bFr x h4 (by omega) h5).trans (fr1 x h1).1, (bH x (by omega)).trans (fr1 x h1).2⟩
  · intro x h1 h2
    exact (bH x h2).trans (fr1 x h1).2
  · rw [b70]; exact hnTW
  · rw [bH _ (by simp only [SourceConstruction.Dims.pcT]; omega)]; exact hnTH
  · intro x hO hZ
    have hZ' : ¬ ((𝔇).B + 19 ≤ x.val ∧ x.val < (𝔇).B + 19 + 71 + se.extra + sp.extra) := by
      unfold SourceConstruction.Dims.InZ at hZ; omega
    have hc1 : x ≠ Dims.csSlots e.ext hV 1 := by
      intro h; apply notOut_cs1 (𝔇) se.extra sp.extra gW
      have hv : (Dims.csSlots e.ext hV 1).val = (𝔇).B + 13 := rfl
      rw [← hv, ← h]; exact hO
    have hen : ¬ ((𝔇).F + (𝔇).rt ≤ x.val ∧ x.val ≤ (𝔇).F + (𝔇).rt + 4 ∧ x.val ≠ (𝔇).F + (𝔇).rt + 3) := by
      intro h
      apply notOut_enc (𝔇) se.extra sp.extra gW (x.val - ((𝔇).F + (𝔇).rt)) (by omega)
      rw [show (𝔇).F + (𝔇).rt + (x.val - ((𝔇).F + (𝔇).rt)) = x.val by omega]; exact hO
    have hdb := (dirty_bound sG x).2
    have hH' : H' x = H1 x := bH x (by omega)
    have hA' : A' x = A1 x := bFr x hc1 hZ' hen
    exact ⟨by rw [hH']; exact hdb, by rw [hA']; exact hOL x hO⟩
  · intro i
    rw [bEnc i]
    exact hOL _ (isOut_coef (𝔇) se.extra sp.extra gW (61 + i.val) (by omega))

theorem first_core_run5 {vE vP : Request → Nat}
    (se : PacketsGlue.RequestMeta.UnaryStage (decompositionOf sources) vE)
    (sp : PacketsGlue.RequestMeta.UnaryStage (decompositionOf sources) vP) {gW : Nat}
    (e : (𝔇).RestExt2 se.extra sp.extra gW) {V : Nat} (hV : (𝔇).U ≤ V)
    {s7 : Nat} (g7M : Machine V s7) (g7cost : Nat → Nat)
    {q : Nat} {circuit : BooleanCircuit q} {pcpp : PointwisePCPP circuit}
    (coordinate : Fin (pcpp.systematicBits + pcpp.auxiliaryBits) →
      ComponentwisePolynomial.CircuitPolynomial (C10TotalDecode.Atom pcpp) 1)
    (ph : CloseoutRowsOriginalSchedule.Phase) (ci : Fin (2 ^ pcpp.clauseBits))
    (L target : Nat) (mode : Bool) (Rc b : Nat)
    (layoutAt : ∀ m : Nat, Packets.Layout (decompositionOf sources)
      ((requestAt coordinate ph ci L target mode m).family (decompositionOf sources))
      (geometryOf selector (decompositionOf sources) (requestAt coordinate ph ci L target mode m)))
    (capsAt : Nat → RowCaps)
    (K : Fin V → Prop) (K0 : Fin V → List Bool) (KH0 : Fin V → Nat)
    (hG7 : ResidentRunH g7M g7cost mask (packets (decompositionOf sources))
      (rows (decompositionOf sources) (printerOf sources))
      ((𝔇).maskSlots hV) ((𝔇).pslots hV) ((𝔇).slot hV) ((𝔇).ret hV) ((𝔇).scr hV 0) ((𝔇).scr hV 1)
      ((𝔇).familySlots hV) ((𝔇).poolSlots hV) (Dims.rewind2Slots e.ext1.ext hV)
      ((𝔇).scr hV 5) ((𝔇).scr hV 6) ((𝔇).scr hV 7) ((𝔇).scr hV 8) ((𝔇).scr hV 9) ((𝔇).scr hV 10)
      (Dims.lenTape e.ext1.ext hV) coordinate ph ci L target mode Rc b
      ((𝔇).pcT e.ext1 hV ⟨70, by unfold restPc; omega⟩)
      (fun i => (𝔇).pcT e.ext1 hV ⟨61 + i.val, by have := i.isLt; unfold restPc; omega⟩) layoutAt capsAt
      (Dims.Rpad (d := 𝔇) (eX := se.extra) (pX := sp.extra) (gW := gW) (V := V) Rc)
      (RestIn4 (𝔇) se.extra sp.extra gW Rc ((𝔇).pcT e.ext1 hV ⟨64, by unfold restPc; omega⟩) K K0 KH0)
      (fun x => OutV (𝔇) se.extra sp.extra gW x.val))
    (w cW cQ Mb Ms cB cS : Nat) (M : Fin 5 → List Bool) (hMl : ∀ i, (M i).length = Rc)
    (cnt : Fin V) (hcnt : cnt.val = (𝔇).U)
    (H : Fin V → Nat) (A : Fin V → List Bool)
    (hclr0 : ∀ x : Fin V, (𝔇).InClear se.extra sp.extra gW x.val → A x = List.replicate Rc false ∧ H x = 0)
    (hK : ∀ x, K x → A x = K0 x ∧ H x = KH0 x)
    (henc : ∀ kk : Fin 13, (kk.val < 3 ∨ kk.val = 4) → (A (Dims.encT (d := 𝔇) hV kk)).length ≤ Rc)
    (hencH : ∀ kk : Fin 13, (kk.val < 3 ∨ kk.val = 4) → H (Dims.encT (d := 𝔇) hV kk) = 0)
    (hW : A ((𝔇).rsT e.ext1 hV 3) = ZeroPadding.pad cW (List.replicate w true)) (hWH : H ((𝔇).rsT e.ext1 hV 3) = 0)
    (hQ : A ((𝔇).rsT e.ext1 hV 4) = ZeroPadding.pad cQ (List.replicate q true)) (hQH : H ((𝔇).rsT e.ext1 hV 4) = 0)
    (hdrv : A ((𝔇).scr hV 11) = List.replicate Rc true) (hdrvH : H ((𝔇).scr hV 11) = 0)
    (hlg : A ((𝔇).scr hV 12) = List.replicate (Rc+2) false) (hlgH : H ((𝔇).scr hV 12) = 0)
    (hbig : A ((𝔇).rsT e.ext1 hV 0) = ZeroPadding.pad cB (List.replicate Mb true))
    (hbigH : H ((𝔇).rsT e.ext1 hV 0) = 0)
    (hsmall : A ((𝔇).rsT e.ext1 hV 1) = ZeroPadding.pad cS (List.replicate Ms true))
    (hsmallH : H ((𝔇).rsT e.ext1 hV 1) = 0)
    (hm : ∀ i, A (Dims.mT e hV i) = M i) (hmH : ∀ i, H (Dims.mT e hV i) = 0)
    (hrfA : ∀ i, (A (Dims.rfT e hV i)).length ≤ Rc) (hrfH : ∀ i, H (Dims.rfT e hV i) ≤ Rc)
    (hcnt0 : A cnt = List.replicate Rc false) (hcntH : H cnt = 0)
    (hN : (RepairSource.VerifierDecoding.CompareMachine.word (monomials coordinate ph ci).length).length ≤ Rc)
    (hlog : 2 * ((requestAt coordinate ph ci L target mode 0).input (decompositionOf sources)).length + 1 ≤ Rc)
    (he1 : 1 ≤ vE (requestAt coordinate ph ci L target mode 0))
    (hpw : (CloseoutRowsCountBinary.bits (vP (requestAt coordinate ph ci L target mode 0))).length ≤ w)
    (hfirst : vP (requestAt coordinate ph ci L target mode 0) * 2^(natBitLength (vE (requestAt coordinate ph ci L target mode 0))) < 2^w)
    (hsecond : vP (requestAt coordinate ph ci L target mode 0) * vE (requestAt coordinate ph ci L target mode 0) * 2^(q+1) < 2^w)
    (hMb : Mb ≤ Rc) (hMs : Ms ≤ Rc) :
    ∃ (H3 : Fin V → Nat) (A3 : Fin V → List Bool) (Av3 : Fin V → List Bool),
      Step (firstCore se sp e hV g7M cnt) ((g7cost 0 + 1 + backCost se sp (requestAt coordinate ph ci L target mode 0) Rc w q (exactListWord (PCJ38fbfed565f64139_Cached.cacheArgs (decompositionOf sources) ((requestAt coordinate ph ci L target mode 0).family (decompositionOf sources))).gs).length Mb Ms) + 1 + (refreshCost Rc + 1 + ((2*Rc+4) + 1 + 1))) H A H3 A3 ∧
      (∀ x, A3 x = ZeroPadding.pad (Dims.Rpad (d := 𝔇) (eX := se.extra) (pX := sp.extra) (gW := gW) (V := V) Rc x)
        (Av3 x)) ∧
      Nonempty (Resident mask (packets (decompositionOf sources)) (rows (decompositionOf sources) (printerOf sources))
        ((𝔇).maskSlots hV) ((𝔇).pslots hV) ((𝔇).slot hV) ((𝔇).ret hV) ((𝔇).scr hV 0) ((𝔇).scr hV 1)
        ((𝔇).familySlots hV) ((𝔇).poolSlots hV) (Dims.rewind2Slots e.ext1.ext hV)
        ((𝔇).scr hV 5) ((𝔇).scr hV 6) ((𝔇).scr hV 7) ((𝔇).scr hV 8) ((𝔇).scr hV 9) ((𝔇).scr hV 10)
        (Dims.lenTape e.ext1.ext hV) (requestAt coordinate ph ci L target mode 0) (layoutAt 0) (capsAt 0)
        H3 Av3) ∧
      A3 (Dims.encT (d := 𝔇) hV 4) = ZeroPadding.pad Rc (RepairOrdinary.frame (SignedSortKey.binary w
        (vP (requestAt coordinate ph ci L target mode 0) * vE (requestAt coordinate ph ci L target mode 0) * 2^q))) ∧
      (∀ hm : 0 < (monomials coordinate ph ci).length, ∀ i : Fin 3, A3 (Dims.encT (d := 𝔇) hV ⟨i.val, by omega⟩) =
        ZeroPadding.pad Rc (RepairOrdinary.frame (CloseoutRowsEstimatorCoefficients.Stream.recordFields b
          (CloseoutFinalC10SupplierCalls.coefficientEstimate ((monomials coordinate ph ci)[0]).coefficient)
          0 0 ⟨i.val, by omega⟩))) ∧
      A3 (Dims.csSlots e.ext1.ext hV 1) = ZeroPadding.pad Rc (List.replicate (if 3 < (exactListWord (PCJ38fbfed565f64139_Cached.cacheArgs (decompositionOf sources) ((requestAt coordinate ph ci L target mode 0).family (decompositionOf sources))).gs).length then Mb else Ms) true) ∧
      H3 (Dims.csSlots e.ext1.ext hV 1) = 0 ∧
      (∀ i, A3 (Dims.rfT e hV i) = M i) ∧ H3 (Dims.rfT e hV 0) = 0 ∧
      (∀ i : Fin 5, i.val ≠ 0 → H3 (Dims.rfT e hV i) = 1) ∧
      (∀ x : Fin V, (((𝔇).F ≤ x.val ∧ x.val < (𝔇).F + (𝔇).rt) ∨ ((𝔇).B + 1 ≤ x.val ∧ x.val ≤ (𝔇).B + 12)) →
        A3 x = List.replicate Rc false ∧ H3 x = 0) ∧
      A3 cnt = ZeroPadding.pad Rc (RepairSource.VerifierDecoding.CompareMachine.word (monomials coordinate ph ci).length) ∧ H3 cnt = 1 ∧
      (∀ x : Fin V, ¬ (𝔇).InClear se.extra sp.extra gW x.val →
        ¬ OutV (𝔇) se.extra sp.extra gW x.val →
        ¬ ((𝔇).F + (𝔇).rt ≤ x.val ∧ x.val ≤ (𝔇).F + (𝔇).rt + 4 ∧ x.val ≠ (𝔇).F + (𝔇).rt + 3) →
        (∀ i, Dims.rfT e hV i ≠ x) → x ≠ cnt → A3 x = A x ∧ H3 x = H x) ∧
      (∀ x : Fin V, (𝔇).InDirt se.extra sp.extra gW x.val → ¬ (𝔇).InZ se.extra sp.extra x.val →
        (A3 x).length ≤ Rc ∧ H3 x ≤ g7cost 0 + 1) ∧
      (∀ x : Fin V, (𝔇).InZ se.extra sp.extra x.val →
        (A3 x).length ≤ max Rc ((g7cost 0 + 1 + backCost se sp (requestAt coordinate ph ci L target mode 0) Rc w q (exactListWord (PCJ38fbfed565f64139_Cached.cacheArgs (decompositionOf sources) ((requestAt coordinate ph ci L target mode 0).family (decompositionOf sources))).gs).length Mb Ms) + 1) ∧
        H3 x ≤ (g7cost 0 + 1 + backCost se sp (requestAt coordinate ph ci L target mode 0) Rc w q (exactListWord (PCJ38fbfed565f64139_Cached.cacheArgs (decompositionOf sources) ((requestAt coordinate ph ci L target mode 0).family (decompositionOf sources))).gs).length Mb Ms)) ∧
      (∀ kk : Fin 13, H3 (Dims.encT (d := 𝔇) hV kk) = H (Dims.encT (d := 𝔇) hV kk)) ∧
      (∀ i : Fin 3, (A3 (Dims.encT (d := 𝔇) hV ⟨i.val, by omega⟩)).length ≤ Rc) := by
  classical
  have vG : (𝔇).G = (𝔇).F + (𝔇).rt + 13 := rfl
  have vB : (𝔇).B = (𝔇).G + (𝔇).R1 + 410 + (𝔇).w + (𝔇).tc := rfl
  have vp : (𝔇).pscr = (𝔇).R1 + 408 + (𝔇).w + (𝔇).tc := rfl
  have vPc : restPc se.extra sp.extra gW = 71 + se.extra + sp.extra + gW := rfl
  have vU : (𝔇).U = (𝔇).G + (𝔇).prepT := rfl
  have vprep : (𝔇).prepT = (𝔇).R1 + 410 + (𝔇).w + (𝔇).tc + (𝔇).res := rfl
  have hres2 := e.hres2
  have hF := e.ext1.ext.hF
  have vscr : ∀ m : Fin 13, ((𝔇).scr hV m).val = (𝔇).G + (𝔇).R1 + 397 + (𝔇).w + (𝔇).tc + m.val := fun _ => rfl
  have vrs : ∀ i : Fin 5, ((𝔇).rsT e.ext1 hV i).val = (𝔇).B + 19 + restPc se.extra sp.extra gW + i.val :=
    fun _ => rfl
  have vcs1 : (Dims.csSlots e.ext1.ext hV 1).val = (𝔇).B + 13 := rfl
  have vrf : ∀ i : Fin 5, (Dims.rfT e hV i).val = (𝔇).B + 14 + i.val := fun _ => rfl
  have vmT : ∀ i : Fin 5, (Dims.mT e hV i).val = (𝔇).B + 19 + restPc se.extra sp.extra gW + 5 + i.val :=
    fun _ => rfl
  have v70 : ((𝔇).pcT e.ext1 hV ⟨70, by unfold restPc; omega⟩).val = (𝔇).B + 19 + 70 := rfl
  have cs1_in : (𝔇).InClear se.extra sp.extra gW (Dims.csSlots e.ext1.ext hV 1).val := by
    unfold SourceConstruction.Dims.InClear; rw [vcs1]; omega
  
  obtain ⟨H2, A2, Av2, sR, hM2, ⟨res2⟩, e4, e02, ecs1, frR, frRH, n70, n70H, dG, e02L⟩ :=
    first_rest_run_d5 mask packets rows sources res p k r se sp e.ext1 hV g7M g7cost coordinate ph ci L target mode Rc b
      layoutAt capsAt K K0 KH0 hG7 w cW cQ Mb Ms cB cS H A
      (fun x hx => by rw [(hclr0 x hx).1, List.length_replicate])
      (fun i => hclr0 _ (pcT_in e.ext1 hV i))
      (fun x hx => hclr0 x (out_in hx))
      hK (fun x hx _ => hclr0 x hx) henc hencH hW hWH hQ hQH hdrv hdrvH hlg hlgH hbig hbigH hsmall hsmallH
      (hclr0 _ cs1_in).1 (hclr0 _ cs1_in).2
      hlog he1 hpw hfirst hsecond
  have keepC : ∀ x : Fin V, ¬ (𝔇).InClear se.extra sp.extra gW x.val → ¬ OutV (𝔇) se.extra sp.extra gW x.val →
      ¬ ((𝔇).F + (𝔇).rt ≤ x.val ∧ x.val ≤ (𝔇).F + (𝔇).rt + 4 ∧ x.val ≠ (𝔇).F + (𝔇).rt + 3) →
      A2 x = A x ∧ H2 x = H x := by
    intro x h1 h4 h6
    have hpc : ¬ ((𝔇).B + 19 ≤ x.val ∧ x.val < (𝔇).B + 19 + restPc se.extra sp.extra gW) := by
      intro h; apply h1; unfold SourceConstruction.Dims.InClear; omega
    have hcs : x ≠ Dims.csSlots e.ext1.ext hV 1 := by
      intro h; apply h1; rw [h]; exact cs1_in
    exact frR x h4 hpc hcs h6
  have scrK : ∀ m : Fin 13, (m.val = 11 ∨ m.val = 12) → A2 ((𝔇).scr hV m) = A ((𝔇).scr hV m) ∧
      H2 ((𝔇).scr hV m) = H ((𝔇).scr hV m) := by
    intro m hm
    apply frR
    · unfold OutV; rw [vscr]; omega
    · rw [vscr]; omega
    · exact ne_val (by rw [vscr, vcs1]; omega)
    · rw [vscr]; omega
  have rfNotClear : ∀ i : Fin 5, ¬ (𝔇).InClear se.extra sp.extra gW (Dims.rfT e hV i).val := by
    intro i; have := i.isLt; unfold SourceConstruction.Dims.InClear; rw [vrf]; omega
  have rfK : ∀ i : Fin 5, A2 (Dims.rfT e hV i) = A (Dims.rfT e hV i) ∧ H2 (Dims.rfT e hV i) = H (Dims.rfT e hV i) := by
    intro i
    have := i.isLt
    apply keepC
    · exact rfNotClear i
    · unfold OutV; rw [vrf]; omega
    · rw [vrf]; omega
  have mK : ∀ i : Fin 5, A2 (Dims.mT e hV i) = A (Dims.mT e hV i) ∧ H2 (Dims.mT e hV i) = H (Dims.mT e hV i) := by
    intro i
    have := i.isLt
    apply keepC
    · exact mT_notClear e hV i
    · exact mT_notOut e hV i
    · rw [vmT]; omega
  have cntNotClear : ¬ (𝔇).InClear se.extra sp.extra gW cnt.val := by
    unfold SourceConstruction.Dims.InClear; rw [hcnt, vU]; omega
  have cntK : A2 cnt = A cnt ∧ H2 cnt = H cnt := by
    apply keepC _ cntNotClear
    · unfold OutV; rw [hcnt, vU]; omega
    · rw [hcnt, vU]; omega
  -- 2. the refresh
  obtain ⟨H3, A3, sF, fv, f0, f14, frF⟩ := refresh_run e hV Rc M hMl H2 A2
    (fun i => by rw [(rfK i).1]; exact hrfA i) (fun i => by rw [(rfK i).2]; exact hrfH i)
    (by rw [(scrK 11 (Or.inl rfl)).1]; exact hdrv) (by rw [(scrK 11 (Or.inl rfl)).2]; exact hdrvH)
    (by rw [(scrK 12 (Or.inr rfl)).1]; exact hlg) (by rw [(scrK 12 (Or.inr rfl)).2]; exact hlgH)
    (fun i => by rw [(mK i).1]; exact hm i) (fun i => by rw [(mK i).2]; exact hmH i)
  have rfNe : ∀ x : Fin V, (x.val < (𝔇).B + 14 ∨ (𝔇).B + 18 < x.val) → ∀ i, Dims.rfT e hV i ≠ x := by
    intro x hx i h
    have := i.isLt
    have hv := congrArg Fin.val h
    rw [vrf] at hv
    omega
  -- 3. the counter: copy `nT`, then move its head to `1`
  have n11 : ((𝔇).pcT e.ext1 hV ⟨70, by unfold restPc; omega⟩) ≠ (𝔇).scr hV 11 := ne_val (by rw [v70, vscr]; omega)
  have n12 : ((𝔇).pcT e.ext1 hV ⟨70, by unfold restPc; omega⟩) ≠ (𝔇).scr hV 12 := ne_val (by rw [v70, vscr]; omega)
  have nc : ((𝔇).pcT e.ext1 hV ⟨70, by unfold restPc; omega⟩) ≠ cnt := ne_val (by rw [v70, hcnt, vU]; omega)
  have c11 : cnt ≠ (𝔇).scr hV 11 := ne_val (by rw [hcnt, vU, vscr]; omega)
  have c12 : cnt ≠ (𝔇).scr hV 12 := ne_val (by rw [hcnt, vU, vscr]; omega)
  have s1112 : (𝔇).scr hV 11 ≠ (𝔇).scr hV 12 := ne_val (by rw [vscr, vscr]; simp)
  have f70 := frF ((𝔇).pcT e.ext1 hV ⟨70, by unfold restPc; omega⟩) (rfNe _ (Or.inr (by rw [v70]; omega)))
  have fc := frF cnt (rfNe _ (Or.inr (by rw [hcnt, vU]; omega)))
  have f11 := frF ((𝔇).scr hV 11) (rfNe _ (Or.inl (by rw [vscr]; omega)))
  have f12 := frF ((𝔇).scr hV 12) (rfNe _ (Or.inl (by rw [vscr]; omega)))
  obtain ⟨A4, sK, k1, k2⟩ := copy_one ((𝔇).pcT e.ext1 hV ⟨70, by unfold restPc; omega⟩) cnt ((𝔇).scr hV 11) ((𝔇).scr hV 12) nc n11 n12 c11 c12 s1112 Rc
    (ZeroPadding.pad Rc (RepairSource.VerifierDecoding.CompareMachine.word (monomials coordinate ph ci).length)) (pad_len_exact' Rc _ hN) H3 A3
    (by rw [f70.1]; exact n70) (by rw [fc.1, cntK.1]; exact hcnt0)
    (by rw [f11.1, (scrK 11 (Or.inl rfl)).1]; exact hdrv) (by rw [f12.1, (scrK 12 (Or.inr rfl)).1]; exact hlg)
    (by rw [f70.2]; exact n70H) (by rw [fc.2, cntK.2]; exact hcntH)
    (by rw [f11.2, (scrK 11 (Or.inl rfl)).2]; exact hdrvH) (by rw [f12.2, (scrK 12 (Or.inr rfl)).2]; exact hlgH)
  let dirs : Fin V → HeadMove := fun x => if x = cnt then HeadMove.right else HeadMove.stay
  obtain ⟨rr, hr, hf, _⟩ := DecompositionCountPosition.move_run dirs H3 A4
  have sM : Step (DecompositionCountPosition.move dirs) 1 H3 A4 (fun x => (dirs x).apply (H3 x)) A4 :=
    Step.of_run hr (by rw [hf]) (congrArg Configuration.tapes hf)
  have H4o : ∀ x, x ≠ cnt → (dirs x).apply (H3 x) = H3 x := by
    intro x hx; simp only [dirs, if_neg hx]; rfl
  have H4c : (dirs cnt).apply (H3 cnt) = 1 := by
    simp only [dirs, if_pos rfl]
    show H3 cnt + 1 = 1
    rw [fc.2, cntK.2, hcntH]
  -- 4. the padded exit and `Resident`
  let Av4 : Fin V → List Bool := fun x => if (∃ i, Dims.rfT e hV i = x) ∨ x = cnt then A4 x else Av2 x
  have hM4 : ∀ x, A4 x = ZeroPadding.pad (Dims.Rpad (d := 𝔇) (eX := se.extra) (pX := sp.extra) (gW := gW)
      (V := V) Rc x) (Av4 x) := by
    intro x
    by_cases hx : (∃ i, Dims.rfT e hV i = x) ∨ x = cnt
    · simp only [Av4, if_pos hx]
      have hnc : ¬ (𝔇).InClear se.extra sp.extra gW x.val := by
        rcases hx with ⟨i, rfl⟩ | rfl
        · exact rfNotClear i
        · exact cntNotClear
      simp only [Dims.Rpad, if_neg hnc, ZeroPadding.pad_zero]
    · simp only [Av4, if_neg hx]
      have h1 : ∀ i, Dims.rfT e hV i ≠ x := fun i h => hx (Or.inl ⟨i, h⟩)
      have h2 : x ≠ cnt := fun h => hx (Or.inr h)
      rw [k2 x (Ne.symm (Ne.symm h2)), (frF x h1).1]
      exact hM2 x
  have lowOff : ∀ x : Fin V, LowT (𝔇) x.val → (∀ i, Dims.rfT e hV i ≠ x) ∧ x ≠ cnt := by
    intro x hx
    unfold LowT at hx
    refine ⟨rfNe x (Or.inl (by omega)), fun h => ?_⟩
    have := congrArg Fin.val h
    rw [hcnt, vU] at this
    omega
  have avT : ∀ x : Fin V, LowT (𝔇) x.val → Av4 x = Av2 x := by
    intro x hx
    have hn : ¬ ((∃ i, Dims.rfT e hV i = x) ∨ x = cnt) := by
      rintro (⟨i, h⟩ | h)
      · exact (lowOff x hx).1 i h
      · exact (lowOff x hx).2 h
    simp only [Av4, if_neg hn]
  have hT : ∀ x : Fin V, LowT (𝔇) x.val → (dirs x).apply (H3 x) = H2 x := by
    intro x hx
    rw [H4o x (lowOff x hx).2, (frF x (lowOff x hx).1).2]
  obtain ⟨res4⟩ := resident_keep_low mask packets rows sources res p k r e.ext1.ext hV res2 avT hT
  -- 5. exports
  have k2o : ∀ x, x ≠ cnt → A4 x = A3 x := fun x hx => k2 x hx
  refine ⟨_, A4, Av4, sR.seq (sF.seq (sK.seq sM)), hM4, ⟨res4⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [k2o _ (ne_val (by simp only [Dims.encT]; rw [hcnt, vU]; omega)),
      (frF _ (rfNe _ (Or.inl (by simp only [Dims.encT]; omega)))).1]; exact e4
  · intro hm i
    have := i.isLt
    rw [k2o _ (ne_val (by simp only [Dims.encT]; rw [hcnt, vU]; omega)),
      (frF _ (rfNe _ (Or.inl (by simp only [Dims.encT]; omega)))).1]; exact e02 hm i
  · rw [k2o _ (ne_val (by rw [vcs1, hcnt, vU]; omega)), (frF _ (rfNe _ (Or.inl (by rw [vcs1]; omega)))).1]
    exact ecs1
  · show (dirs _).apply (H3 _) = 0
    rw [H4o _ (ne_val (by rw [vcs1, hcnt, vU]; omega)), (frF _ (rfNe _ (Or.inl (by rw [vcs1]; omega)))).2,
      frRH _ (by unfold OutV; rw [vcs1]; omega) (by rw [vcs1]; omega)]
    exact (hclr0 _ cs1_in).2
  · intro i
    rw [k2o _ (ne_val (by rw [vrf, hcnt, vU]; have := i.isLt; omega))]; exact fv i
  · show (dirs _).apply (H3 _) = 0
    rw [H4o _ (ne_val (by rw [vrf, hcnt, vU]; omega))]; exact f0
  · intro i hi
    show (dirs _).apply (H3 _) = 1
    rw [H4o _ (ne_val (by rw [vrf, hcnt, vU]; have := i.isLt; omega))]; exact f14 i hi
  · intro x hx
    have hin : (𝔇).InClear se.extra sp.extra gW x.val := by
      unfold SourceConstruction.Dims.InClear; omega
    have hoff : ∀ i, Dims.rfT e hV i ≠ x := rfNe x (by omega)
    have hxc : x ≠ cnt := ne_val (by rw [hcnt, vU]; omega)
    obtain ⟨a1, a2⟩ := frR x (by unfold OutV; omega) (by omega) (ne_val (by rw [vcs1]; omega)) (by omega)
    show A4 x = _ ∧ (dirs x).apply (H3 x) = _
    rw [k2o x hxc, H4o x hxc, (frF x hoff).1, (frF x hoff).2, a1, a2]
    exact hclr0 x hin
  · exact k1
  · exact H4c
  · intro x h1 h4 h6 h7 h8
    show A4 x = _ ∧ (dirs x).apply (H3 x) = _
    obtain ⟨a1, a2⟩ := keepC x h1 h4 h6
    rw [k2o x h8, H4o x h8, (frF x h7).1, (frF x h7).2]
    exact ⟨a1, a2⟩
  · -- dirt off `Z`: `Rc`-free heads
    intro x hx hz
    unfold SourceConstruction.Dims.InDirt at hx
    by_cases hr' : (𝔇).B + 14 ≤ x.val ∧ x.val ≤ (𝔇).B + 18
    · have hi : Dims.rfT e hV ⟨x.val - ((𝔇).B + 14), by omega⟩ = x := Fin.ext (by rw [vrf]; simp; omega)
      have hxc : x ≠ cnt := ne_val (by rw [hcnt, vU]; omega)
      show (A4 x).length ≤ Rc ∧ (dirs x).apply (H3 x) ≤ _
      rw [k2o x hxc, H4o x hxc, ← hi]
      refine ⟨by rw [fv, hMl], ?_⟩
      by_cases h0 : x.val - ((𝔇).B + 14) = 0
      · have e0 : (⟨x.val - ((𝔇).B + 14), by omega⟩ : Fin 5) = 0 := Fin.ext h0
        rw [e0, f0]; omega
      · rw [f14 _ h0]; omega
    · have hin : (𝔇).InClear se.extra sp.extra gW x.val := by
        rcases hx with h | h
        · exact h
        · exact absurd h hr'
      have hoff : ∀ i, Dims.rfT e hV i ≠ x := rfNe x (by
        unfold SourceConstruction.Dims.InClear at hin; omega)
      have hxc : x ≠ cnt := fun h => cntNotClear (h ▸ hin)
      show (A4 x).length ≤ Rc ∧ (dirs x).apply (H3 x) ≤ _
      rw [k2o x hxc, H4o x hxc, (frF x hoff).1, (frF x hoff).2]
      by_cases hO : OutV (𝔇) se.extra sp.extra gW x.val
      · obtain ⟨d1, d2⟩ := dG x hO hz
        rw [(hclr0 x hin).2] at d1
        exact ⟨d2, by omega⟩
      by_cases hc : x = Dims.csSlots e.ext1.ext hV 1
      · subst hc
        refine ⟨by rw [ecs1]; exact le_of_eq (pad_len_exact' _ _ (by simp; split_ifs <;> omega)), ?_⟩
        rw [frRH _ (by unfold OutV; rw [vcs1]; omega) (by rw [vcs1]; omega), (hclr0 _ cs1_in).2]; omega
      · have hz' : ¬ ((𝔇).B + 19 ≤ x.val ∧ x.val < (𝔇).B + 19 + restPc se.extra sp.extra gW) := by
          intro h; apply hO; unfold OutV; unfold SourceConstruction.Dims.InZ at hz; omega
        have hen : ¬ ((𝔇).F + (𝔇).rt ≤ x.val ∧ x.val ≤ (𝔇).F + (𝔇).rt + 4 ∧ x.val ≠ (𝔇).F + (𝔇).rt + 3) := by
          intro h; unfold SourceConstruction.Dims.InClear at hin; omega
        obtain ⟨a1, a2⟩ := frR x hO hz' hc hen
        rw [a1, a2, (hclr0 x hin).1, (hclr0 x hin).2]
        exact ⟨by simp, by omega⟩
  · -- dirt on `Z`: at the core's cost
    intro x hz
    have hin : (𝔇).InClear se.extra sp.extra gW x.val := Dims.InZ_clear hz
    have hoff : ∀ i, Dims.rfT e hV i ≠ x := rfNe x (by unfold SourceConstruction.Dims.InZ at hz; omega)
    have hxc : x ≠ cnt := fun h => cntNotClear (h ▸ hin)
    obtain ⟨b1, b2⟩ := dirty_bound sR x
    rw [(hclr0 x hin).1, List.length_replicate, (hclr0 x hin).2] at b1
    rw [(hclr0 x hin).2] at b2
    show (A4 x).length ≤ _ ∧ (dirs x).apply (H3 x) ≤ _
    rw [k2o x hxc, H4o x hxc, (frF x hoff).1, (frF x hoff).2]
    constructor
    · omega
    · omega
  · -- the `encT` heads
    intro kk
    have := kk.isLt
    have hxc : Dims.encT (d := 𝔇) hV kk ≠ cnt := ne_val (by simp only [Dims.encT]; rw [hcnt, vU]; omega)
    have hoff : ∀ i, Dims.rfT e hV i ≠ Dims.encT (d := 𝔇) hV kk := rfNe _ (Or.inl (by simp only [Dims.encT]; omega))
    show (dirs _).apply (H3 _) = _
    rw [H4o _ hxc, (frF _ hoff).2]
    exact frRH _ (notOut_enc (𝔇) se.extra sp.extra gW kk.val kk.isLt)
      (by simp only [Dims.encT]; omega)
  · intro i
    have := i.isLt
    rw [k2o _ (ne_val (by simp only [Dims.encT]; rw [hcnt, vU]; omega)),
      (frF _ (rfNe _ (Or.inl (by simp only [Dims.encT]; omega)))).1]; exact e02L i

end concrete

end
end NearCubicWires.SourceConstruction.Rest
end

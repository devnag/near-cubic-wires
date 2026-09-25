import Proof.SourceAssembly.SourceRequestInput

set_option autoImplicit false
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unusedVariables false

namespace NearCubicWires.SourceRequest.InputPass
open NearCubicWires LocalBitMultitape ExtDecompositionBatch
open RepairOrdinary RepairOrdinary.RecoveryRootRound
open RepairRepresentation SupplierEstimator SupplierPipeline SourceInterfaces
open RepairSource.VerifierDecoding
open PCJ9eff70d512234a4c_Fixed PCJd4d1d9d7d1fa4313_Production PCJc4297ab269d8423a_Source
noncomputable section

theorem input_step_mask (mask : MaskProducer) (a : DecompositionAlgorithm) (r : Request) (cap : Nat)
    (uK um : List Bool) (blank : Fin (5 + mask.work) → Nat)
    (hk : uK.length = normalizedLiveCount r.q r.liveScale)
    (hmm : um.length = (r.family a).occurrences.length)
    (cs : (r.supportWord a).length ≤ cap) (cq : 4 * r.q + 3 ≤ cap)
    (ck : 4 * uK.length + 3 ≤ cap) (cm : 4 * um.length + 3 ≤ cap)
    (cq2 : 2 * r.q + 1 ≤ cap) (cn : 2 * r.nativeWord.length + 1 ≤ cap)
    (cs2 : 2 * (r.supportWord a).length + 1 ≤ cap) (ci : 2 * (r.indexWord a).length + 1 ≤ cap)
    (ct : 2 * (r.topWord a).length + 1 ≤ cap) :
    ∃ A' : Fin (22 + mask.work) → List Bool,
      Step (machine mask) (cost mask a r) (fun _ => 0) (entry mask.work a r cap uK um blank)
        (fun _ => 0) A' ∧
      A' ⟨7, by omega⟩ = r.input a ∧
      A' ⟨9, by omega⟩ = List.replicate (r.input a).length true ∧
      (∀ x : Fin (22 + mask.work), 3 ≤ x.val → x.val ≤ 6 → A' x = entry mask.work a r cap uK um blank x) ∧
      (∀ x : Fin (22 + mask.work), 11 ≤ x.val → x.val ≤ 16 → A' x = entry mask.work a r cap uK um blank x) ∧
      A' ⟨0, by omega⟩ = ZeroPadding.pad (SLoad.MaskInput.reserve blank ⟨4, by omega⟩) (maskData a r).word := by
  classical
  have hinj := maskSlots_injective mask.work
  have mv : ∀ j : Fin (5 + mask.work), (maskSlots mask.work j).val = if j.val = 4 then 0 else 17 + j.val := by
    intro j; unfold maskSlots; split_ifs <;> rfl
  -- stage 1: the lead
  have hlenq : (List.replicate r.q true).length = r.q := List.length_replicate
  have e1 := SLoad.LeadDriver.lead_driver_step mask (maskSlots mask.work) hinj (ret mask.work) (retDrv mask.work) (drv mask.work)
    (leadLog mask.work)
    (by intro i j h; have := congrArg Fin.val h; rw [mv] at this; simp only [ret] at this
        split_ifs at this <;> omega)
    (by intro i h; have := congrArg Fin.val h; simp only [ret, leadLog] at this; omega)
    (by intro j h; have := congrArg Fin.val h; rw [mv] at this; simp only [leadLog] at this
        split_ifs at this; omega)
    (by intro j h; have := congrArg Fin.val h; rw [mv] at this; simp only [drv] at this
        split_ifs at this; omega)
    (by intro i h; have := congrArg Fin.val h; simp only [drv, ret] at this; omega)
    (by intro h; have := congrArg Fin.val h; simp only [drv, leadLog] at this; omega)
    (by intro h; have := congrArg Fin.val h; simp only [drv, retDrv] at this; omega)
    (by intro h; have := congrArg Fin.val h; simp only [retDrv, leadLog] at this; omega)
    a r cap (List.replicate r.q true) uK um hlenq hk hmm cs (by rw [hlenq]; exact cq) ck cm blank
    (fun _ => 0) (entry mask.work a r cap uK um blank) (fun _ => rfl) (fun _ => rfl) rfl rfl rfl
    (entry_15 _ rfl) (entry_1 _ rfl) (entry_11 _ rfl) (entry_12 _ rfl) (entry_13 _ rfl)
    (entry_14 _ rfl)
    (by
      intro j hj
      apply entry_live
      · rw [mv, if_neg (by omega)]; omega
      · rw [mv, if_neg (by omega)]; omega)
    (by
      intro j hj
      by_cases h4 : j.val = 4
      · rw [entry_0 _ (by rw [mv, if_pos h4])]
        exact congrArg (fun k => List.replicate (blank k) false) (Fin.ext h4.symm)
      · rw [entry_high _ (by rw [mv, if_neg h4]; omega)]
        exact congrArg (fun k => List.replicate (blank k) false)
          (Fin.ext (by simp only; rw [mv, if_neg h4]; omega)))
    (entry_16 _ rfl)
  have hz : ∀ {t : Nat} (sl : Fin t → Fin (22 + mask.work)), dockH sl (fun _ => 0) (fun _ => 0) = fun _ => 0 :=
    fun sl => SLoad.dockH_existing sl _ _ (fun _ => rfl)
  rw [hz] at e1
  set A1 := Function.update (entry mask.work a r cap uK um blank) (drv mask.work) (List.replicate r.q true) with hA1
  -- stage 2: the mask worker, once
  obtain ⟨B, hrunB, hword⟩ := mask.correct (maskData a r)
  have e2 := (hrunB.pad (SLoad.MaskInput.reserve blank)).focus (maskSlots mask.work) hinj (fun _ => 0) A1
  rw [hz] at e2
  set A2 := install (maskSlots mask.work) A1 (fun i => ZeroPadding.pad (SLoad.MaskInput.reserve blank i) (B i))
    with hA2
  have hql : (B ⟨4, by omega⟩).length = r.q := by
    rw [hword]; exact SLoad.LeadDriver.word_length a r
  -- stage 3: the framing pass, measured
  have hraw := SLoad.RequestFrames.request_frames_step (0 : Fin 9) 1 2 3 4 5 6 7 8
    SLoad.SuffixFrame.ports_injective a r B hword (SLoad.MaskInput.reserve blank ⟨4, by omega⟩) 0 cap
    (by rw [hql]; exact cq2) cn cs2 ci ct (fun _ => 0)
    (SLoad.SuffixFrame.rawEntry (SLoad.MaskInput.reserve blank ⟨4, by omega⟩) 0 cap (B ⟨4, by omega⟩)
      r.nativeWord (r.supportWord a) (r.indexWord a) (r.topWord a))
    (fun j => rfl) rfl rfl rfl rfl rfl rfl rfl rfl rfl
  obtain ⟨rec0, hrun0, hh0, ht0, hs0⟩ := hraw
  have hrun : run SLoad.SuffixFrame.raw
      (SLoad.RequestFrames.cost (B ⟨4, by omega⟩).length r.nativeWord.length (r.supportWord a).length
        (r.indexWord a).length (r.topWord a).length)
      (SLoad.SuffixFrame.rawEntry (SLoad.MaskInput.reserve blank ⟨4, by omega⟩) 0 cap (B ⟨4, by omega⟩)
        r.nativeWord (r.supportWord a) (r.indexWord a) (r.topWord a)) = some rec0 := hrun0
  have htape : rec0.final.tapes 7 = r.input a := by rw [ht0, Function.update_self]
  have hhead : rec0.final.heads 7 = (r.input a).length := by rw [hh0, Function.update_self]
  obtain ⟨r2, hr2, hkeep, hcnt, hheads, hsteps⟩ := AppendOutputLength.length_run SLoad.SuffixFrame.raw 7
    SLoad.SuffixFrame.raw_forward _ _ rec0 hrun
  rw [hql] at hs0
  have l3 : Step (AppendOutputLength.machine SLoad.SuffixFrame.raw 7)
      (2 * SLoad.RequestFrames.cost r.q r.nativeWord.length (r.supportWord a).length
        (r.indexWord a).length (r.topWord a).length + 2) (fun _ => 0)
      (AppendOutputLength.input (AppendOutputLength.input
        (SLoad.SuffixFrame.rawEntry (SLoad.MaskInput.reserve blank ⟨4, by omega⟩) 0 cap (B ⟨4, by omega⟩)
          r.nativeWord (r.supportWord a) (r.indexWord a) (r.topWord a)))) (fun _ => 0) r2.final.tapes :=
    (Step.of_run hr2 (funext hheads) rfl).enlarge (by omega)
  -- the bank before stage 3, at the low tapes
  have hlow : ∀ x : Fin (22 + mask.work), x.val ≠ 0 → x.val < 17 → A2 x = A1 x := by
    intro x h0 h17
    rw [hA2, install_other _ _ _ _ (fun j e => by
      have := congrArg Fin.val e; rw [mv] at this; split_ifs at this <;> omega)]
  have hdrv : A1 (drv mask.work) = List.replicate r.q true := by rw [hA1, Function.update_self]
  have hoff : ∀ x : Fin (22 + mask.work), x.val ≠ 1 → A1 x = (entry mask.work a r cap uK um blank) x := by
    intro x hx
    rw [hA1, Function.update_of_ne (fun e => hx (by rw [e]; rfl))]
  have hm0 : (⟨0, by omega⟩ : Fin (22 + mask.work)) = maskSlots mask.work ⟨4, by omega⟩ := by
    apply Fin.ext; rw [mv]; simp
  have e3 := l3.dock (lenSlots mask.work) (lenSlots_injective mask.work) (fun _ => 0) A2 (fun _ => rfl) (by
    intro j
    have hj := j.isLt
    rw [lenIn]
    by_cases h0 : j.val = 0
    · rw [dif_pos (by omega), show lenSlots mask.work j = maskSlots mask.work ⟨4, by omega⟩ from Fin.ext (by
        rw [mv]; simp [lenSlots, h0]), hA2, install_slot _ hinj]
      simp only [show (⟨j.val, by omega⟩ : Fin 9) = 0 from Fin.ext h0]
      rfl
    have hl : A2 (lenSlots mask.work j) = A1 (lenSlots mask.work j) :=
      hlow _ (by simp only [lenSlots]; omega) (by simp only [lenSlots]; omega)
    rw [hl]
    by_cases h1 : j.val = 1
    · rw [dif_pos (by omega), show lenSlots mask.work j = drv mask.work from Fin.ext (by simp [lenSlots, drv, h1]), hdrv,
        show (⟨j.val, by omega⟩ : Fin 9) = 1 from Fin.ext h1]
      show _ = ZeroPadding.pad 0 (List.replicate (B ⟨4, by omega⟩).length true)
      rw [ZeroPadding.pad_zero, hql]
    rw [hoff _ (by simp only [lenSlots]; omega)]
    have hv : (lenSlots mask.work j).val = j.val := rfl
    by_cases h9 : j.val < 9
    · rw [dif_pos h9]
      have : j.val = 2 ∨ j.val = 3 ∨ j.val = 4 ∨ j.val = 5 ∨ j.val = 6 ∨ j.val = 7 ∨ j.val = 8 := by omega
      rcases this with h | h | h | h | h | h | h
      · rw [entry_2 _ (by rw [hv, h]), show (⟨j.val, h9⟩ : Fin 9) = 2 from Fin.ext h]; rfl
      · rw [entry_3 _ (by rw [hv, h]), show (⟨j.val, h9⟩ : Fin 9) = 3 from Fin.ext h]; rfl
      · rw [entry_4 _ (by rw [hv, h]), show (⟨j.val, h9⟩ : Fin 9) = 4 from Fin.ext h]; rfl
      · rw [entry_5 _ (by rw [hv, h]), show (⟨j.val, h9⟩ : Fin 9) = 5 from Fin.ext h]; rfl
      · rw [entry_6 _ (by rw [hv, h]), show (⟨j.val, h9⟩ : Fin 9) = 6 from Fin.ext h]; rfl
      · rw [entry_7 _ (by rw [hv, h]), show (⟨j.val, h9⟩ : Fin 9) = 7 from Fin.ext h]; rfl
      · rw [entry_8 _ (by rw [hv, h]), show (⟨j.val, h9⟩ : Fin 9) = 8 from Fin.ext h]; rfl
    · rw [dif_neg h9]
      by_cases h9' : j.val = 9
      · exact entry_9 _ (by rw [hv, h9'])
      · exact entry_10 _ (by rw [hv]; omega))
  rw [hz] at e3
  refine ⟨install (lenSlots mask.work) A2 r2.final.tapes, (e1.seq (e2.seq e3)).enlarge (le_of_eq rfl),
    ?_, ?_, ?_, ?_, ?_⟩
  · rw [show (⟨7, by omega⟩ : Fin (22 + mask.work)) = lenSlots mask.work 7 from rfl, install_slot _ (lenSlots_injective mask.work),
      show (7 : Fin 11) = ((7 : Fin 9).castAdd 1).castAdd 1 from rfl, hkeep, htape]
  · rw [show (⟨9, by omega⟩ : Fin (22 + mask.work)) = lenSlots mask.work 9 from rfl, install_slot _ (lenSlots_injective mask.work),
      show (9 : Fin 11) = ((0 : Fin 1).natAdd 9).castAdd 1 from rfl, hcnt, hhead]
  · intro x h3 h6
    have ex : x = lenSlots mask.work ((⟨x.val, by omega⟩ : Fin 9).castAdd 1 |>.castAdd 1) := Fin.ext rfl
    rw [ex, install_slot _ (lenSlots_injective mask.work), hkeep, ht0,
      Function.update_of_ne (fun e => by have := congrArg Fin.val e; simp at this; omega),
      Function.update_of_ne (fun e => by have := congrArg Fin.val e; simp at this; omega),
      ← ex]
    have : x.val = 3 ∨ x.val = 4 ∨ x.val = 5 ∨ x.val = 6 := by omega
    rcases this with h | h | h | h
    · rw [entry_3 _ h, show (⟨x.val, by omega⟩ : Fin 9) = 3 from Fin.ext h]; rfl
    · rw [entry_4 _ h, show (⟨x.val, by omega⟩ : Fin 9) = 4 from Fin.ext h]; rfl
    · rw [entry_5 _ h, show (⟨x.val, by omega⟩ : Fin 9) = 5 from Fin.ext h]; rfl
    · rw [entry_6 _ h, show (⟨x.val, by omega⟩ : Fin 9) = 6 from Fin.ext h]; rfl
  · intro x h11 h16
    rw [install_other _ _ _ _ (fun j e => by
      have := congrArg Fin.val e; simp only [lenSlots] at this; omega),
      hlow x (by omega) (by omega), hoff x (by omega)]
  · rw [show (⟨0, by omega⟩ : Fin (22 + mask.work)) = lenSlots mask.work 0 from rfl,
      install_slot _ (lenSlots_injective mask.work),
      show (0 : Fin 11) = ((0 : Fin 9).castAdd 1).castAdd 1 from rfl, hkeep, ht0,
      Function.update_of_ne (fun e => by have := congrArg Fin.val e; simp at this),
      Function.update_of_ne (fun e => by have := congrArg Fin.val e; simp at this), ← hword]
    rfl

/-- `pad R` of a `pad R` word. -/
theorem pad_pad_same (R : Nat) (x : List Bool) : ZeroPadding.pad R (ZeroPadding.pad R x) = ZeroPadding.pad R x := by
  simp only [ZeroPadding.pad, List.length_append, List.length_replicate, List.append_assoc, ← List.replicate_add]
  congr 2
  omega

/-- `pad R` of a blank of length `≤ R`. -/
theorem pad_blank (R k : Nat) (h : k ≤ R) : ZeroPadding.pad R (List.replicate k false) = List.replicate R false := by
  simp only [ZeroPadding.pad, List.length_replicate, ← List.replicate_add]
  congr 1
  omega

/-- The entry bank padded by `R` (backing `R` everywhere): the eight word tapes, blank elsewhere. -/
theorem entry_padded (mask : MaskProducer) (a : DecompositionAlgorithm) (r : Request) (R : Nat) (uK um : List Bool)
    (j : Fin (22 + mask.work)) :
    ZeroPadding.pad R (entry mask.work a r R uK um (fun _ => R) j) =
      if j.val = 3 then ZeroPadding.pad R (frame r.nativeWord)
      else if j.val = 4 then ZeroPadding.pad R (frame (r.supportWord a))
      else if j.val = 5 then ZeroPadding.pad R (frame (r.indexWord a))
      else if j.val = 6 then ZeroPadding.pad R (frame (r.topWord a))
      else if j.val = 11 then ZeroPadding.pad R (frame (r.supportWord a))
      else if j.val = 12 then ZeroPadding.pad R (frame (List.replicate r.q true))
      else if j.val = 13 then ZeroPadding.pad R (frame uK)
      else if j.val = 14 then ZeroPadding.pad R (frame um)
      else if j.val = 15 then ZeroPadding.pad R (frame (List.replicate r.q true))
      else List.replicate R false := by
  have hnil : ZeroPadding.pad R ([] : List Bool) = List.replicate R false := by simp [ZeroPadding.pad]
  have hj := j.isLt
  by_cases h22 : 22 ≤ j.val
  · rw [entry_high j h22, pad_blank R R le_rfl]
    simp only [show j.val ≠ 3 by omega, show j.val ≠ 4 by omega, show j.val ≠ 5 by omega, show j.val ≠ 6 by omega,
      show j.val ≠ 11 by omega, show j.val ≠ 12 by omega, show j.val ≠ 13 by omega, show j.val ≠ 14 by omega,
      show j.val ≠ 15 by omega, if_false]
  by_cases h17 : 17 ≤ j.val
  · rw [entry_live j h17 (by omega), hnil]
    simp only [show j.val ≠ 3 by omega, show j.val ≠ 4 by omega, show j.val ≠ 5 by omega, show j.val ≠ 6 by omega,
      show j.val ≠ 11 by omega, show j.val ≠ 12 by omega, show j.val ≠ 13 by omega, show j.val ≠ 14 by omega,
      show j.val ≠ 15 by omega, if_false]
  have hc : j.val = 0 ∨ j.val = 1 ∨ j.val = 2 ∨ j.val = 3 ∨ j.val = 4 ∨ j.val = 5 ∨ j.val = 6 ∨ j.val = 7 ∨
      j.val = 8 ∨ j.val = 9 ∨ j.val = 10 ∨ j.val = 11 ∨ j.val = 12 ∨ j.val = 13 ∨ j.val = 14 ∨ j.val = 15 ∨
      j.val = 16 := by omega
  rcases hc with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · rw [entry_0 j h, pad_blank R R le_rfl]; simp [h]
  · rw [entry_1 j h, hnil]; simp [h]
  · rw [entry_2 j h, pad_blank R R le_rfl]; simp [h]
  · rw [entry_3 j h, pad_pad_same]; simp [h]
  · rw [entry_4 j h, pad_pad_same]; simp [h]
  · rw [entry_5 j h, pad_pad_same]; simp [h]
  · rw [entry_6 j h, pad_pad_same]; simp [h]
  · rw [entry_7 j h, hnil]; simp [h]
  · rw [entry_8 j h, pad_blank R R le_rfl]; simp [h]
  · rw [entry_9 j h, hnil]; simp [h]
  · rw [entry_10 j h, hnil]; simp [h]
  · rw [entry_11 j h, pad_pad_same]; simp [h]
  · rw [entry_12 j h, pad_pad_same]; simp [h]
  · rw [entry_13 j h, pad_pad_same]; simp [h]
  · rw [entry_14 j h, pad_pad_same]; simp [h]
  · rw [entry_15 j h, pad_pad_same]; simp [h]
  · rw [entry_16 j h, pad_blank R R le_rfl]; simp [h]

/-- **InputPass docked, backing `R` everywhere** (any universe; host heads `0` on the dock). Writes the bare request input on
`sl 7`, its unary length on `sl 9`, the mask word on `sl 0`; every host tape off the dock's writable part (local `3..6`, `11..16`
are returned) is unchanged; heads unchanged. -/
theorem input_dock {U : Nat} (mask : MaskProducer) (a : DecompositionAlgorithm) (r : Request) (R : Nat)
    (uK um : List Bool)
    (hk : uK.length = normalizedLiveCount r.q r.liveScale)
    (hmm : um.length = (r.family a).occurrences.length)
    (cs : (r.supportWord a).length ≤ R) (cq : 4 * r.q + 3 ≤ R)
    (ck : 4 * uK.length + 3 ≤ R) (cm : 4 * um.length + 3 ≤ R)
    (cq2 : 2 * r.q + 1 ≤ R) (cn : 2 * r.nativeWord.length + 1 ≤ R)
    (cs2 : 2 * (r.supportWord a).length + 1 ≤ R) (ci : 2 * (r.indexWord a).length + 1 ≤ R)
    (ct : 2 * (r.topWord a).length + 1 ≤ R)
    (sl : Fin (22 + mask.work) → Fin U) (hsl : Function.Injective sl)
    (H : Fin U → Nat) (A : Fin U → List Bool) (hH : ∀ j, H (sl j) = 0)
    (hA : ∀ j, A (sl j) =
      if j.val = 3 then ZeroPadding.pad R (frame r.nativeWord)
      else if j.val = 4 then ZeroPadding.pad R (frame (r.supportWord a))
      else if j.val = 5 then ZeroPadding.pad R (frame (r.indexWord a))
      else if j.val = 6 then ZeroPadding.pad R (frame (r.topWord a))
      else if j.val = 11 then ZeroPadding.pad R (frame (r.supportWord a))
      else if j.val = 12 then ZeroPadding.pad R (frame (List.replicate r.q true))
      else if j.val = 13 then ZeroPadding.pad R (frame uK)
      else if j.val = 14 then ZeroPadding.pad R (frame um)
      else if j.val = 15 then ZeroPadding.pad R (frame (List.replicate r.q true))
      else List.replicate R false) :
    ∃ A' : Fin U → List Bool, Step (RecoveryFocus.machine sl (machine mask)) (cost mask a r) H A H A' ∧
      A' (sl ⟨7, by omega⟩) = ZeroPadding.pad R (r.input a) ∧
      A' (sl ⟨9, by omega⟩) = ZeroPadding.pad R (List.replicate (r.input a).length true) ∧
      A' (sl ⟨0, by omega⟩) = ZeroPadding.pad R (maskData a r).word ∧
      (∀ x, (∀ j, sl j = x → (3 ≤ j.val ∧ j.val ≤ 6) ∨ (11 ≤ j.val ∧ j.val ≤ 16)) → A' x = A x) := by
  obtain ⟨E', st, o7, o9, k36, k1116, o0⟩ := input_step_mask mask a r R uK um (fun _ => R) hk hmm cs cq ck cm
    cq2 cn cs2 ci ct
  have d := (st.pad (fun _ => R)).dock sl hsl H A (fun j => hH j) (fun j => by rw [hA j, entry_padded])
  rw [SLoad.dockH_existing sl H (fun _ => 0) hH] at d
  refine ⟨_, d, ?_, ?_, ?_, ?_⟩
  · rw [install_slot sl hsl, o7]
  · rw [install_slot sl hsl, o9]
  · rw [install_slot sl hsl, o0]
    have h4 : SLoad.MaskInput.reserve (work := mask.work) (fun _ => R) ⟨4, by omega⟩ = R := by
      simp [SLoad.MaskInput.reserve]
    rw [h4, pad_pad_same]
  · intro x hx
    by_cases hp : ∃ j, sl j = x
    · obtain ⟨j, rfl⟩ := hp
      rw [install_slot sl hsl]
      rcases hx j rfl with h | h
      · rw [k36 j h.1 h.2, entry_padded, ← hA j]
      · rw [k1116 j h.1 h.2, entry_padded, ← hA j]
    · exact install_other sl A _ x (fun j e => hp ⟨j, e⟩)

end
end NearCubicWires.SourceRequest.InputPass


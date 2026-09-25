import Proof.SourceAssembly.SourceProloguePro3

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
attribute [local irreducible] P1TopDownPaidPayload.tapes

namespace Dims

/-- The outer padding: `Rk` on the lower per-call block `Z`, `0` elsewhere. -/
def capZ (d : Dims) (eX pX : Nat) {V : Nat} (Rk : Nat) (x : Fin V) : Nat :=
  if d.InZ eX pX x.val then Rk else 0

/-- The virtual bank: `Z` blank at the inner capacity `Rc`, the given bank elsewhere. -/
def virtZ (d : Dims) (eX pX : Nat) {V : Nat} (Rc : Nat) (W : Fin V → List Bool) : Fin V → List Bool := fun x =>
  if d.InZ eX pX x.val then List.replicate Rc false else W x

/-- The cycle's padding after the outer clear: `Rk` on `Z`, `Rpad Rc` elsewhere. -/
def RZ (d : Dims) (eX pX gW : Nat) {V : Nat} (Rc Rk : Nat) (x : Fin V) : Nat :=
  if d.InZ eX pX x.val then Rk else Rpad (d := d) (eX := eX) (pX := pX) (gW := gW) (V := V) Rc x

end Dims

/-! ### Layout facts (small contexts) -/

/-- A tape between the family bank and `G` is `Free`. -/
theorem free_mid {d : Dims} (e : d.Ext) {V : Nat} (hV : d.U ≤ V) (x : Fin V)
    (h1 : d.F + d.rt ≤ x.val) (h2 : x.val < d.G) :
    Cycle.Free (d.slot hV) (d.maskSlots hV) (d.pslots hV) (d.poolSlots hV) (d.familySlots hV)
      (Dims.rewind2Slots e hV) x := by
  have := d.hdesc; have := d.hdesc440; have := d.hout; have := d.hsp; have := e.hF
  refine ⟨⟨fun jj => ne_of_val ?_, fun jj => ne_of_val ?_, fun jj => ne_of_val ?_, fun jj => ne_of_val ?_⟩,
    fun jj => ne_of_val ?_, fun jj => ne_of_val ?_⟩ <;> have := jj.isLt <;> wgeo

/-- The cycle's working tapes (`cs`, the native family bank, `drv`) avoid four value ranges. -/
theorem off_cycle {d : Dims} (e : d.Ext) {V : Nat} (hV : d.U ≤ V) (x : Fin V)
    (hx : x.val < d.F ∨ (d.F + d.rt ≤ x.val ∧ x.val < d.G) ∨ d.B + 18 < x.val ∨
      (d.G + d.R1 ≤ x.val ∧ x.val < d.B)) :
    (∀ kk, Dims.csSlots e hV kk ≠ x) ∧ (∀ i, Dims.natSlots hV i ≠ x) ∧ (∀ kk, Dims.drvSlots e hV kk ≠ x) := by
  have hR1pos : 1 ≤ d.R1 := by have := d.hdesc; omega
  have hG : d.G = d.F + d.rt + 13 := rfl
  have hB : d.B = d.G + d.R1 + 410 + d.w + d.tc := rfl
  refine ⟨fun kk h => ?_, fun i h => ?_, fun kk h => ?_⟩
  · have hv := congrArg Fin.val h
    simp only [Dims.csSlots, Dims.csV] at hv
    split_ifs at hv <;> omega
  · have hv := congrArg Fin.val h
    have := i.isLt
    simp only [Dims.natSlots] at hv
    omega
  · have hv := congrArg Fin.val h
    simp only [Dims.drvSlots, Dims.drvV] at hv
    split_ifs at hv <;> omega

namespace Rest

theorem pad_blank (a b : Nat) (h : a ≤ b) :
    ZeroPadding.pad b (List.replicate a false) = List.replicate b false := by
  simp only [ZeroPadding.pad, List.length_replicate, List.replicate_append_replicate]
  congr 1; omega

theorem pad_len_max (c : Nat) (w : List Bool) : (ZeroPadding.pad c w).length = max c w.length := by
  simp only [ZeroPadding.pad, List.length_append, List.length_replicate]; omega

section layout
variable {d : SourceConstruction.Dims} {eX pX gW : Nat} (e : d.RestExt3 eX pX gW) {V : Nat} (hV : d.U ≤ V)

/-- **The outer clear's exit, read at the inner capacity**: re-padding the virtual bank by `capZ` gives the real
exit back. -/
theorem outer_exit_pad (Rc Rk : Nat) (hRk : Rc ≤ Rk) (W : Fin V → List Bool) :
    (fun x => ZeroPadding.pad (d.capZ eX pX Rk x) (d.virtZ eX pX Rc (install (Dims.clrZ e hV) W
      (PCJ6e421fabe2aa4155_SourceClear.join (fun _ => List.replicate Rk false) (List.replicate Rk true)
        (List.replicate (Rk+2) false))) x)) =
    install (Dims.clrZ e hV) W (PCJ6e421fabe2aa4155_SourceClear.join (fun _ => List.replicate Rk false)
      (List.replicate Rk true) (List.replicate (Rk+2) false)) := by
  funext x
  simp only [Dims.capZ, Dims.virtZ]
  by_cases hz : d.InZ eX pX x.val
  · rw [if_pos hz, if_pos hz, pad_blank Rc Rk hRk]
    obtain ⟨kk, hk⟩ := Dims.clrZ_cover e hV x hz
    rw [← hk, install_slot _ (Dims.clrZ_injective e hV)]
    simp [PCJ6e421fabe2aa4155_SourceClear.join]
  · rw [if_neg hz, if_neg hz, ZeroPadding.pad_zero]

/-- **The inner clear absorbs the family output on the virtual bank.** -/
theorem virt_absorb (Rc Rk : Nat) (W W' : Fin V → List Bool) {m : Nat} (clr : Fin m → Fin V)
    (hclr : Function.Injective clr) (J : Fin m → List Bool)
    (hW : ∀ x, (∀ k, clr k ≠ x) → W x = W' x) :
    install clr (d.virtZ eX pX Rc (install (Dims.clrZ e hV) W
      (PCJ6e421fabe2aa4155_SourceClear.join (fun _ => List.replicate Rk false) (List.replicate Rk true)
        (List.replicate (Rk+2) false)))) J =
    install clr (d.virtZ eX pX Rc (install (Dims.clrZ e hV) W'
      (PCJ6e421fabe2aa4155_SourceClear.join (fun _ => List.replicate Rk false) (List.replicate Rk true)
        (List.replicate (Rk+2) false)))) J := by
  funext x
  by_cases hx : ∃ k, clr k = x
  · obtain ⟨k, rfl⟩ := hx
    rw [install_slot clr hclr, install_slot clr hclr]
  · have hx' : ∀ k, clr k ≠ x := fun k h => hx ⟨k, h⟩
    rw [install_other clr _ _ x hx', install_other clr _ _ x hx']
    simp only [Dims.virtZ]
    split_ifs
    · rfl
    · exact Refill.install_at _ _ _ _ x (hW x hx')

/-- A tape of the refill's clear set is no high resident. -/
theorem clear_ne_hrT {x : Fin V} (hx : d.InClear eX pX gW x.val) (i : Fin 12) : x ≠ Dims.hrT e hV i := by
  intro h; rw [h] at hx; exact Dims.hrT_notClear e hV i hx

/-- **The exit frame's value facts** for a tape below `F`, between the family bank and `G`, or above the per-call
block (small context, so the disjunctive `omega` calls stay cheap). -/
theorem frame_region (x : Fin V)
    (hv : x.val < d.F ∨ (d.F + d.rt ≤ x.val ∧ x.val < d.G) ∨ d.B + 19 + restPc eX pX gW ≤ x.val) :
    ¬ d.InClear eX pX gW x.val ∧ x ≠ d.scr hV 11 ∧ x ≠ d.scr hV 12 ∧ ¬ OutV d eX pX gW x.val ∧
      ¬ d.InZ eX pX x.val ∧ (∀ i, Dims.rfT e.ext2 hV i ≠ x) ∧
      (x.val < d.F ∨ (d.F + d.rt ≤ x.val ∧ x.val < d.G) ∨ d.B + 18 < x.val ∨
        (d.G + d.R1 ≤ x.val ∧ x.val < d.B)) := by
  have hB : d.B = d.G + d.R1 + 410 + d.w + d.tc := rfl
  have hG : d.G = d.F + d.rt + 13 := rfl
  have hp : d.pscr = d.R1 + 408 + d.w + d.tc := rfl
  have vPc : restPc eX pX gW = 71 + eX + pX + gW := rfl
  refine ⟨?_, ne_val ?_, ne_val ?_, ?_, ?_, fun i h => ?_, by omega⟩
  · unfold SourceConstruction.Dims.InClear; omega
  · simp only [Dims.scr, Dims.scrV]; omega
  · simp only [Dims.scr, Dims.scrV]; omega
  · unfold OutV; omega
  · unfold SourceConstruction.Dims.InZ; omega
  · have := i.isLt; have hv2 := congrArg Fin.val h; simp only [Dims.rfT] at hv2; omega

/-- A tape below `F`: off the prologue residents, the high residents and the `enc` window. -/
theorem low_region (x : Fin V) (hx : x.val < d.F) :
    x ≠ d.rsT e.ext2.ext1 hV 2 ∧ (∀ i : Fin 12, x ≠ Dims.hrT e hV i) ∧
      ¬ (d.F + d.rt ≤ x.val ∧ x.val ≤ d.F + d.rt + 4 ∧ x.val ≠ d.F + d.rt + 3) ∧
      x.val < d.B + 19 ∧ (x.val < d.F ∨ d.F + d.rt ≤ x.val) := by
  have hB : d.B = d.G + d.R1 + 410 + d.w + d.tc := rfl
  have hG : d.G = d.F + d.rt + 13 := rfl
  refine ⟨ne_val ?_, fun i => ne_val ?_, by omega, by omega, Or.inl hx⟩
  · simp only [Dims.rsT]; omega
  · simp only [Dims.hrT_val]; omega

/-- A tape above the per-call block. -/
theorem high_region (x : Fin V) (hx : d.B + 19 + restPc eX pX gW ≤ x.val) :
    d.G ≤ x.val ∧ d.F ≤ x.val ∧ d.F + d.rt ≤ x.val ∧ d.B ≤ x.val ∧
      ¬ (d.F + d.rt ≤ x.val ∧ x.val ≤ d.F + d.rt + 4 ∧ x.val ≠ d.F + d.rt + 3) ∧
      (x.val < d.B + 19 ∨ d.B + 19 + restPc eX pX gW ≤ x.val) := by
  have hB : d.B = d.G + d.R1 + 410 + d.w + d.tc := rfl
  have hG : d.G = d.F + d.rt + 13 := rfl
  refine ⟨by omega, by omega, by omega, by omega, by omega, Or.inr hx⟩

/-- A kept high resident is above the per-call block and off `rsT 2`. -/
theorem kept_high (x : Fin V) (hx : d.B + 29 + restPc eX pX gW ≤ x.val) :
    d.B + 19 + restPc eX pX gW ≤ x.val ∧ x ≠ d.rsT e.ext2.ext1 hV 2 := by
  refine ⟨by omega, ne_val ?_⟩
  simp only [Dims.rsT]; omega

/-- The thirteen `encT` tapes lie between the family bank and `G`; `encT 3, 5..12` are off `rest`'s writes. -/
theorem enc_region (kk : Fin 13) :
    d.F + d.rt ≤ (Dims.encT (d := d) hV kk).val ∧ (Dims.encT (d := d) hV kk).val < d.G ∧
      Dims.encT (d := d) hV kk ≠ d.rsT e.ext2.ext1 hV 2 ∧ (∀ i : Fin 12, Dims.encT (d := d) hV kk ≠ Dims.hrT e hV i) ∧
      (kk.val = 3 ∨ 5 ≤ kk.val →
        ¬ (d.F + d.rt ≤ (Dims.encT (d := d) hV kk).val ∧ (Dims.encT (d := d) hV kk).val ≤ d.F + d.rt + 4 ∧
          (Dims.encT (d := d) hV kk).val ≠ d.F + d.rt + 3)) := by
  have hB : d.B = d.G + d.R1 + 410 + d.w + d.tc := rfl
  have hG : d.G = d.F + d.rt + 13 := rfl
  have := kk.isLt
  refine ⟨?_, ?_, ne_val ?_, fun i => ne_val ?_, fun hk => ?_⟩ <;>
    simp only [Dims.encT, Dims.rsT, Dims.hrT_val] <;> omega

end layout

/-- **The loop invariant of the repaired seam** at loop point `j`, on the unpadded view `(H, A)`: `Inv3`'s residents,
masters and outer driver/log; the dirt split — off `Z`: length and head `≤ Rc`; on the family bank `[F, F+rt)`:
head `+ fuel + 1 ≤ Rc` (B1 (2): the ONLY place the family fuel enters); on `Z`: length and head `≤ Rk`; and the four
`enc` heads `rest` reads are `0`. `K` may hold tapes below `F` and high residents. -/
structure InvR {d : SourceConstruction.Dims} {eX pX gW : Nat} (e : d.RestExt3 eX pX gW) {V : Nat} (hV : d.U ≤ V)
    (Rc Rk : Nat) (K : Fin V → Prop) (K0 : Fin V → List Bool) (KH0 : Fin V → Nat)
    (j w q Mb Ms cW cQ cB cS S Rw B v U0 fuel : Nat) (H : Fin V → Nat) (A : Fin V → List Bool) : Prop where
  kept : ∀ x, K x → A x = K0 x ∧ H x = KH0 x
  curT : A (d.rsT e.ext2.ext1 hV 2) = ZeroPadding.pad Rc (UnaryTemplate.tape j)
  big : A (d.rsT e.ext2.ext1 hV 0) = ZeroPadding.pad cB (List.replicate Mb true)
  small : A (d.rsT e.ext2.ext1 hV 1) = ZeroPadding.pad cS (List.replicate Ms true)
  wv : A (d.rsT e.ext2.ext1 hV 3) = ZeroPadding.pad cW (List.replicate w true)
  qv : A (d.rsT e.ext2.ext1 hV 4) = ZeroPadding.pad cQ (List.replicate q true)
  rsH : ∀ i, H (d.rsT e.ext2.ext1 hV i) = 0
  mU : A (Dims.mT e.ext2 hV 0) = ZeroPadding.pad Rc (List.replicate U0 true)
  mS : A (Dims.mT e.ext2 hV 1) = ZeroPadding.pad Rc (UnaryTemplate.tape S)
  mR : A (Dims.mT e.ext2 hV 2) = ZeroPadding.pad Rc (UnaryTemplate.tape Rw)
  mB : A (Dims.mT e.ext2 hV 3) = ZeroPadding.pad Rc (UnaryTemplate.tape B)
  mv : A (Dims.mT e.ext2 hV 4) = ZeroPadding.pad Rc (UnaryTemplate.tape v)
  mH : ∀ i, H (Dims.mT e.ext2 hV i) = 0
  drv : A (d.scr hV 11) = List.replicate Rc true
  drvH : H (d.scr hV 11) = 0
  lg : A (d.scr hV 12) = List.replicate (Rc+2) false
  lgH : H (d.scr hV 12) = 0
  zD : A (Dims.hrT e hV 10) = List.replicate Rk true
  zDH : H (Dims.hrT e hV 10) = 0
  zL : A (Dims.hrT e hV 11) = List.replicate (Rk+2) false
  zLH : H (Dims.hrT e hV 11) = 0
  dirtA : ∀ x : Fin V, d.InDirt eX pX gW x.val → ¬ d.InZ eX pX x.val → (A x).length ≤ Rc
  dirtH : ∀ x : Fin V, d.InDirt eX pX gW x.val → ¬ d.InZ eX pX x.val → H x ≤ Rc
  famH : ∀ x : Fin V, d.F ≤ x.val → x.val < d.F + d.rt → H x + fuel + 1 ≤ Rc
  zA : ∀ x : Fin V, d.InZ eX pX x.val → (A x).length ≤ Rk
  zH : ∀ x : Fin V, d.InZ eX pX x.val → H x ≤ Rk
  encH : ∀ kk : Fin 13, (kk.val < 3 ∨ kk.val = 4) → H (Dims.encT (d := d) hV kk) = 0

theorem InvR.view {d : SourceConstruction.Dims} {eX pX gW : Nat} {e : d.RestExt3 eX pX gW} {V : Nat} {hV : d.U ≤ V}
    {Rc Rk : Nat} {K : Fin V → Prop} {K0 : Fin V → List Bool} {KH0 : Fin V → Nat}
    {j w q Mb Ms cW cQ cB cS S Rw B v U0 fuel : Nat} {H : Fin V → Nat} {A : Fin V → List Bool}
    (h : InvR e hV Rc Rk K K0 KH0 j w q Mb Ms cW cQ cB cS S Rw B v U0 fuel H A)
    (hKpos : ∀ x, K x → x.val < d.F ∨ d.G ≤ x.val)
    (slots : Fin d.rt → Fin V) (hslots : ∀ i, (slots i).val = d.F + i.val) (hinj : Function.Injective slots)
    (inT : Fin d.rt → List Bool) (hlen : ∀ i, (inT i).length ≤ (A (slots i)).length) :
    InvR e hV Rc Rk K K0 KH0 j w q Mb Ms cW cQ cB cS S Rw B v U0 fuel H (install slots A inT) := by
  have hB : d.B = d.G + d.R1 + 410 + d.w + d.tc := rfl
  have hG : d.G = d.F + d.rt + 13 := rfl
  have hi : ∀ x : Fin V, d.G ≤ x.val → install slots A inT x = A x := fun x hx =>
    install_other slots A inT x (fun i h => by
      have := i.isLt; have := hslots i; have := congrArg Fin.val h; omega)
  have vrs : ∀ i : Fin 5, (d.rsT e.ext2.ext1 hV i).val = d.B + 19 + restPc eX pX gW + i.val := fun _ => rfl
  have vmT : ∀ i : Fin 5, (Dims.mT e.ext2 hV i).val = d.B + 19 + restPc eX pX gW + 5 + i.val := fun _ => rfl
  have vscr : ∀ m : Fin 13, (d.scr hV m).val = d.G + d.R1 + 397 + d.w + d.tc + m.val := fun _ => rfl
  have vhr : ∀ i : Fin 12, (Dims.hrT e hV i).val = d.B + 29 + restPc eX pX gW + i.val := fun _ => rfl
  refine ⟨fun x hx => ?_, ?_, ?_, ?_, ?_, ?_, h.rsH, ?_, ?_, ?_, ?_, ?_, h.mH, ?_, h.drvH, ?_, h.lgH,
    ?_, h.zDH, ?_, h.zLH, fun x hx hz => ?_, h.dirtH, h.famH, fun x hz => ?_, h.zH, h.encH⟩
  · rcases hKpos x hx with hl | hh
    · rw [install_other slots A inT x (fun i hh => by
        have := hslots i; have := congrArg Fin.val hh; omega)]
      exact h.kept x hx
    · rw [hi x hh]; exact h.kept x hx
  · rw [hi _ (by rw [vrs]; omega)]; exact h.curT
  · rw [hi _ (by rw [vrs]; omega)]; exact h.big
  · rw [hi _ (by rw [vrs]; omega)]; exact h.small
  · rw [hi _ (by rw [vrs]; omega)]; exact h.wv
  · rw [hi _ (by rw [vrs]; omega)]; exact h.qv
  · rw [hi _ (by rw [vmT]; omega)]; exact h.mU
  · rw [hi _ (by rw [vmT]; omega)]; exact h.mS
  · rw [hi _ (by rw [vmT]; omega)]; exact h.mR
  · rw [hi _ (by rw [vmT]; omega)]; exact h.mB
  · rw [hi _ (by rw [vmT]; omega)]; exact h.mv
  · rw [hi _ (by rw [vscr]; omega)]; exact h.drv
  · rw [hi _ (by rw [vscr]; omega)]; exact h.lg
  · rw [hi _ (by rw [vhr]; omega)]; exact h.zD
  · rw [hi _ (by rw [vhr]; omega)]; exact h.zL
  · by_cases hs : ∃ i, slots i = x
    · obtain ⟨i, rfl⟩ := hs
      rw [install_slot slots hinj A inT i]
      exact (hlen i).trans (h.dirtA _ hx hz)
    · rw [install_other slots A inT x (fun i hh => hs ⟨i, hh⟩)]
      exact h.dirtA x hx hz
  · have hzv := hz
    unfold SourceConstruction.Dims.InZ at hzv
    rw [hi x (by omega)]; exact h.zA x hz

/-- `rest`'s cost is `14·Rc` plus its value at `Rc = 0` (F6's seven `2Rc+4` sweeps are its only `Rc` terms). -/
theorem restCost_eq {a : DecompositionAlgorithm} {vE vP : Request → Nat}
    (se : PacketsGlue.RequestMeta.UnaryStage a vE) (sp : PacketsGlue.RequestMeta.UnaryStage a vP)
    (g7cost : Nat → Nat) (rq : Request) (Rc w q L Mb Ms j : Nat) :
    restCost se sp g7cost rq Rc w q L Mb Ms j = 14 * Rc + restCost se sp g7cost rq 0 w q L Mb Ms j := by
  simp only [restCost, backCost, Prologue.f6FullCost, Prologue.f6Cost]
  omega

theorem windows_of_free {a : DecompositionAlgorithm} {vE vP : Request → Nat}
    (se : PacketsGlue.RequestMeta.UnaryStage a vE) (sp : PacketsGlue.RequestMeta.UnaryStage a vP)
    (g7cost : Nat → Nat) (rq : Request) (Rc w q L Mb Ms j c0 : Nat)
    (h : restCost se sp g7cost rq 0 w q L Mb Ms j + c0 + 2 ≤ Rc) :
    cursorCost j + 1 + g7cost (j+1) + 1 + c0 + 1 ≤ Rc ∧
    restCost se sp g7cost rq Rc w q L Mb Ms j + 1 + c0 + 1 ≤ 16 * (Rc + 1) := by
  rw [restCost_eq]
  simp only [restCost] at h ⊢
  constructor <;> omega

section concrete
variable (mask : MaskProducer) {selector : CyclicChoice.Laws}
  (packets : PCJc4297ab269d8423a_Source.PacketLibrary selector)
  (rows : PCJc4297ab269d8423a_Source.RowLibrary selector) (sources : EightSources) (res : Nat)
  {gamma : Real} (p : Parameters sources gamma) (k r : Nat)

set_option hygiene false in
local notation "𝔇" => dimsOf mask packets rows sources res p k r

end concrete

end Rest
end
end NearCubicWires.SourceConstruction
end

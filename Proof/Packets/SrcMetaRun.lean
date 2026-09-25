import Proof.Packets.SrcMetaProg
import Proof.Packets.SrcMetaIface2

set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unusedSimpArgs false

open NearCubicWires LocalBitMultitape ExtDecompositionBatch
open RepairOrdinary RepairOrdinary.RecoveryRootRound
open RepairRepresentation SupplierEstimator SupplierPipeline SourceInterfaces
open NearCubicWires.P1Closure
open PCJ9eff70d512234a4c_Fixed PCJd4d1d9d7d1fa4313_Production PCJc4297ab269d8423a_Source
open NearCubicWires.RepairSource NearCubicWires.RepairSource.CloseoutFinal
namespace NearCubicWires.SourceStart.MetaRun
open NearCubicWires.SourceBudget NearCubicWires.SourceBudget.Params NearCubicWires.SourceBudget.Pow2
open NearCubicWires.Admission NearCubicWires.SourceConstruction
open NearCubicWires.SourceStart.MetaTM NearCubicWires.SourceStart.MetaWords NearCubicWires.SourceStart.Regs
open NearCubicWires.SourceStart.MetaAsm NearCubicWires.SourceStart.MetaProg
noncomputable section

/-! ## 1. Word facts -/

theorem bitlen_clog (m : ℕ) (hm : 1 ≤ m) : natBitLength m = Nat.clog 2 (m + 1) := by
  unfold natBitLength
  apply le_antisymm
  · have h := Nat.pow_log_le_self 2 (show m ≠ 0 by omega)
    have := (Nat.lt_clog_iff_pow_lt (b := 2) (by norm_num) (x := m + 1) (y := Nat.log 2 m)).mpr (by omega)
    omega
  · apply Nat.clog_le_of_le_pow
    have := Nat.lt_pow_succ_log_self (b := 2) (by norm_num) m
    exact this

theorem natWord_zero : natWord 0 = [true, false, false] := by
  rw [natWord_eq]
  simp [natBitLength, SignedSortKey.binary]

theorem bits_zero : CloseoutRowsCountBinary.bits 0 = [] := by
  simp [CloseoutRowsCountBinary.bits]

theorem wA_le (q L : ℕ) : wA q L ≤ q := by
  unfold wA wU
  exact (Nat.div_le_self _ _).trans ((Nat.sub_le _ _).trans ((Nat.div_le_self _ _).trans (Nat.sub_le _ _)))

theorem deg_le (q L : ℕ) : uniformDeg q L ≤ q := by
  unfold uniformDeg
  exact Nat.div_le_self _ _

theorem finRange_flatMap_getD (l : List (List Bool)) (g : List Bool → List Bool) :
    (List.finRange l.length).flatMap (fun i => g (l.getD i.val [])) = l.flatMap g := by
  have hm : (List.finRange l.length).map (fun i => l.getD i.val []) = l := by
    apply List.ext_getElem (by simp)
    intro i h1 h2
    simp [List.getD_eq_getElem?_getD]
  have h := congrArg (fun l' => l'.flatMap g) hm
  simp only [List.flatMap_map] at h
  exact h

/-! ## 2. The pieces -/

/-- The meta word (decision 80b's caps). -/
def MBof (selector : CyclicChoice.Laws) (s : EightSources) {gamma : Real} (p : Parameters s gamma)
    (packets : PCJc4297ab269d8423a_Source.PacketLibrary selector) (L q : ℕ) : List Bool :=
  SLoad.Setup.metaBits (wA q L) (uniformDeg q L) (COf selector s p q)
    (⟨hFOf2 selector s p L q, cCOf2 selector s p L q, VvOf selector s p L q, rROf2 selector s p packets q⟩ :
      PCJd4d1d9d7d1fa4313_Production.RowCaps)

/-- `C`'s leading ones (`1` in the degenerate case `mC = 0`). -/
def BC (selector : CyclicChoice.Laws) (s : EightSources) {gamma : Real} (p : Parameters s gamma) (cz : Bool) (q : ℕ) : ℕ :=
  if cz then 1 else Nat.clog 2 (Meta.mC selector s p q + 1) + q/4
/-- `C`'s shift zeros. -/
def XC (cz : Bool) (q : ℕ) : ℕ := if cz then 1 else q/4
/-- `Vv`'s leading ones. -/
def BV (selector : CyclicChoice.Laws) (s : EightSources) {gamma : Real} (p : Parameters s gamma) (L : ℕ) (vz : Bool) (q : ℕ) : ℕ :=
  if vz then 1 else Nat.clog 2 (Meta.mV selector s p q + 1) + (q - normalizedLiveCount q L)
/-- `Vv`'s shift zeros. -/
def XV (L : ℕ) (vz : Bool) (q : ℕ) : ℕ := if vz then 1 else q - normalizedLiveCount q L
/-- `cCOf2`'s exponent. -/
def yCC (selector : CyclicChoice.Laws) (s : EightSources) {gamma : Real} (p : Parameters s gamma) (L q : ℕ) : ℕ :=
  max (yA selector s p L q) (yB selector s p q) + 1

/-- **The 25 pieces of `MB`**, in order. -/
def pw (selector : CyclicChoice.Laws) (s : EightSources) {gamma : Real} (p : Parameters s gamma)
    (packets : PCJc4297ab269d8423a_Source.PacketLibrary selector) (L : ℕ) (cz vz : Bool) (q : ℕ) : List (List Bool) :=
  [natWord 3, natWord (wA q L), natWord (uniformDeg q L),
   List.replicate (BC selector s p cz q) true, [false], List.replicate (XC cz q) false, CloseoutRowsCountBinary.bits (Meta.mC selector s p q),
   natWord 4 ++ [true],
   List.replicate (yH selector s p L q) true, [false], List.replicate (yH selector s p L q) false, [true, true],
   List.replicate (yCC selector s p L q) true, [false], List.replicate (yCC selector s p L q) false, [true],
   List.replicate (BV selector s p L vz q) true, [false], List.replicate (XV L vz q) false, CloseoutRowsCountBinary.bits (Meta.mV selector s p q),
   [true], List.replicate (yR selector s p packets q) true, [false], List.replicate (yR selector s p packets q) false, [true]]

def pwF (selector : CyclicChoice.Laws) (s : EightSources) {gamma : Real} (p : Parameters s gamma)
    (packets : PCJc4297ab269d8423a_Source.PacketLibrary selector) (L : ℕ) (cz vz : Bool) (q : ℕ) (k : Fin 25) : List Bool :=
  (pw selector s p packets L cz vz q).getD k.val []

theorem bdC (selector : CyclicChoice.Laws) (s : EightSources) {gamma : Real} (p : Parameters s gamma) (cz : Bool) (q : ℕ)
    (hcz : cz = true ↔ Meta.mC selector s p q = 0) :
    bd (natWord (COf selector s p q)) = bd (List.replicate (BC selector s p cz q) true) ++ bd [false] ++
      bd (List.replicate (XC cz q) false) ++ bd (CloseoutRowsCountBinary.bits (Meta.mC selector s p q)) := by
  rw [Meta.COf_eq]
  cases cz with
  | true =>
    have h0 := hcz.mp rfl
    rw [h0, zero_mul, natWord_zero, bits_zero]
    simp [BC, XC, bd, body, dat]
  | false =>
    have h1 : 1 ≤ Meta.mC selector s p q := Nat.one_le_iff_ne_zero.mpr (fun h => absurd (hcz.mpr h) (by simp))
    rw [bd_shift _ _ h1, bitlen_clog _ h1]
    simp [BC, XC]

theorem bdV (selector : CyclicChoice.Laws) (s : EightSources) {gamma : Real} (p : Parameters s gamma) (L : ℕ) (vz : Bool) (q : ℕ)
    (hvz : vz = true ↔ Meta.mV selector s p q = 0) :
    bd (natWord (VvOf selector s p L q)) = bd (List.replicate (BV selector s p L vz q) true) ++ bd [false] ++
      bd (List.replicate (XV L vz q) false) ++ bd (CloseoutRowsCountBinary.bits (Meta.mV selector s p q)) := by
  rw [Meta.VvOf_eq]
  cases vz with
  | true =>
    have h0 := hvz.mp rfl
    rw [h0, zero_mul, natWord_zero, bits_zero]
    simp [BV, XV, bd, body, dat]
  | false =>
    have h1 : 1 ≤ Meta.mV selector s p q := Nat.one_le_iff_ne_zero.mpr (fun h => absurd (hvz.mpr h) (by simp))
    rw [bd_shift _ _ h1, bitlen_clog _ h1]
    simp [BV, XV]

theorem bdP (y : ℕ) : bd (natWord (2^y)) =
    bd [true] ++ bd (List.replicate y true) ++ bd [false] ++ bd (List.replicate y false) ++ bd [true] := by
  rw [bd_pow2, List.replicate_succ]
  simp only [bd, ← body_append, List.cons_append, List.nil_append, List.append_assoc]

/-- **`frame MB` from the pieces.** -/
theorem pieces_frame (selector : CyclicChoice.Laws) (s : EightSources) {gamma : Real} (p : Parameters s gamma)
    (packets : PCJc4297ab269d8423a_Source.PacketLibrary selector) (L : ℕ) (cz vz : Bool) (q : ℕ)
    (hcz : cz = true ↔ Meta.mC selector s p q = 0) (hvz : vz = true ↔ Meta.mV selector s p q = 0) :
    (List.finRange 25).flatMap (fun i => body false (pwF selector s p packets L cz vz q i)) ++ [false] =
      RepairOrdinary.frame (MBof selector s p packets L q) := by
  have e := finRange_flatMap_getD (pw selector s p packets L cz vz q) (body false)
  rw [show (pw selector s p packets L cz vz q).length = 25 from rfl] at e
  unfold pwF
  rw [e, MBof, meta_frame, bdC selector s p cz q hcz, bdV selector s p L vz q hvz]
  unfold hFOf2 cCOf2 rROf2
  rw [bdP, bdP, bdP]
  simp only [pw, yCC, List.flatMap_cons, List.flatMap_nil, List.append_nil, bd, body_append, List.append_assoc]
  rfl

/-! ## 3. The pipeline stage -/

variable {selector : CyclicChoice.Laws} {s : EightSources} {gamma : Real} {p : Parameters s gamma}
  {packets : PCJc4297ab269d8423a_Source.PacketLibrary selector} {L : ℕ}

/-- The pipeline's thirteen ports, in the order of registers `0..12`. -/
def vports (V : Meta.MetaVals2 selector s p packets L) : List (Fin V.NP) :=
  [V.iq, V.iK, V.oW, V.oD, V.oX, V.oXK, V.oM, V.oB, V.oH, V.oC, V.oMV, V.oBV, V.oR]

theorem idx_lt (V : Meta.MetaVals2 selector s p packets L) (j : Fin V.NP) (h : j ∈ vports V) : (vports V).idxOf j < 13 :=
  List.idxOf_lt_length_iff.mpr h

/-- Port `j` is register `idxOf j`; the pipeline's other tapes are scratch. -/
def nmV (V : Meta.MetaVals2 selector s p packets L) {NL : ℕ} (hNL : 13 ≤ NL) (j : Fin V.NP) : Option (Fin NL) :=
  if h : j ∈ vports V then some ⟨(vports V).idxOf j, by have := idx_lt V j h; omega⟩ else none

/-- The pipeline's entry. -/
def tinV (V : Meta.MetaVals2 selector s p packets L) (q R : ℕ) (j : Fin V.NP) : List Bool :=
  if j = V.iq then ZeroPadding.pad R (List.replicate q true)
  else if j = V.iK then ZeroPadding.pad R (List.replicate (2*normalizedLiveCount q L) true) else List.replicate R false

/-- The pipeline's thirteen words (registers `0..12`). -/
def outsV (selector : CyclicChoice.Laws) (s : EightSources) {gamma : Real} (p : Parameters s gamma)
    (packets : PCJc4297ab269d8423a_Source.PacketLibrary selector) (L q : ℕ) : List (List Bool) :=
  [List.replicate q true, List.replicate (2*normalizedLiveCount q L) true, List.replicate (wA q L) true,
   List.replicate (uniformDeg q L) true, List.replicate (q/4) true, List.replicate (q - normalizedLiveCount q L) true,
   List.replicate (Meta.mC selector s p q) true, List.replicate (Nat.clog 2 (Meta.mC selector s p q + 1) + q/4) true,
   List.replicate (yH selector s p L q) true, List.replicate (max (yA selector s p L q) (yB selector s p q) + 1) true,
   List.replicate (Meta.mV selector s p q) true,
   List.replicate (Nat.clog 2 (Meta.mV selector s p q + 1) + (q - normalizedLiveCount q L)) true,
   List.replicate (yR selector s p packets q) true]

/-- The tracking after the pipeline. -/
def valV (outs : List (List Bool)) (val : ℕ → Option (List Bool)) : ℕ → Option (List Bool) := fun i =>
  if i < 13 then some (outs.getD i []) else val i

theorem v_trk (V : Meta.MetaVals2 selector s p packets L) (q R G : ℕ) {NL : ℕ} (hNL : 13 ≤ NL) (hG : 13 ≤ G)
    (f : ℕ) (hs : f + V.NP ≤ NL) {E : Fin NL → List Bool} {val : ℕ → Option (List Bool)} (hT : Trk R G E val f)
    (h0 : val 0 = some (List.replicate q true)) (h1 : val 1 = some (List.replicate (2*normalizedLiveCount q L) true))
    (hz : ∀ i, 2 ≤ i → i < 13 → val i = some []) :
    ∃ E', Step (RecoveryFocus.machine (nslot (nmV V hNL) f hs) V.machine) (V.cost q) (fun _ => 0) E (fun _ => 0) E' ∧
      Trk R G E' (valV (outsV selector s p packets L q) val) (f + V.NP) := by
  have nd := V.nodup
  have hqK : V.iK ≠ V.iq := by
    intro e
    exact (List.nodup_cons.mp nd).1 (by rw [← e]; exact List.mem_cons_self)
  obtain ⟨E', hst, eq, eK, eW, eD, eX, eXK, eM, eB, eH, eC, eMV, eBV, eR⟩ :=
    V.run q R (tinV V q R) (by simp [tinV]) (by simp [tinV, hqK]) (by intro x h1 h2; simp [tinV, h1, h2])
  have i0 : (vports V).idxOf V.iq = 0 := List.idxOf_cons_self
  have i1 : (vports V).idxOf V.iK = 1 := by
    rw [vports, List.idxOf_cons_ne _ hqK.symm, List.idxOf_cons_self]
  have pp : ∀ w : List Bool, ZeroPadding.pad R (ZeroPadding.pad R w) = ZeroPadding.pad R w := fun w => padpad R R w le_rfl
  have outs_eq : ∀ k (hk : k < 13), ZeroPadding.pad R ((outsV selector s p packets L q).getD k []) =
      ZeroPadding.pad R (E' ((vports V)[k]'hk)) := by
    intro k hk
    match k, hk with
    | 0, _ => show _ = ZeroPadding.pad R (E' V.iq); rw [eq]; simp only [tinV, if_true]; rw [pp]; rfl
    | 1, _ => show _ = ZeroPadding.pad R (E' V.iK); rw [eK]; simp only [tinV, if_neg hqK, if_true]; rw [pp]; rfl
    | 2, _ => show _ = ZeroPadding.pad R (E' V.oW); rw [eW, pp]; rfl
    | 3, _ => show _ = ZeroPadding.pad R (E' V.oD); rw [eD, pp]; rfl
    | 4, _ => show _ = ZeroPadding.pad R (E' V.oX); rw [eX, pp]; rfl
    | 5, _ => show _ = ZeroPadding.pad R (E' V.oXK); rw [eXK, pp]; rfl
    | 6, _ => show _ = ZeroPadding.pad R (E' V.oM); rw [eM, pp]; rfl
    | 7, _ => show _ = ZeroPadding.pad R (E' V.oB); rw [eB, pp]; rfl
    | 8, _ => show _ = ZeroPadding.pad R (E' V.oH); rw [eH, pp]; rfl
    | 9, _ => show _ = ZeroPadding.pad R (E' V.oC); rw [eC, pp]; rfl
    | 10, _ => show _ = ZeroPadding.pad R (E' V.oMV); rw [eMV, pp]; rfl
    | 11, _ => show _ = ZeroPadding.pad R (E' V.oBV); rw [eBV, pp]; rfl
    | 12, _ => show _ = ZeroPadding.pad R (E' V.oR); rw [eR, pp]; rfl
  refine trk_stage hst (nmV V hNL) f hs ?_ ?_ hT ?_ ?_ _ ?_
  · intro i j r hi hj
    unfold nmV at hi hj
    by_cases ci : i ∈ vports V
    · by_cases cj : j ∈ vports V
      · rw [dif_pos ci] at hi; rw [dif_pos cj] at hj
        have e := congrArg Fin.val ((Option.some.inj hi).trans (Option.some.inj hj).symm)
        exact (List.idxOf_inj ci).mp e
      · rw [dif_neg cj] at hj; exact absurd hj (by simp)
    · rw [dif_neg ci] at hi; exact absurd hi (by simp)
  · intro j r e
    unfold nmV at e
    by_cases cj : j ∈ vports V
    · rw [dif_pos cj] at e; rw [← Option.some.inj e]
      show (vports V).idxOf j < G
      have := idx_lt V j cj
      omega
    · rw [dif_neg cj] at e; exact absurd e (by simp)
  · intro j r e
    unfold nmV at e
    by_cases cj : j ∈ vports V
    · rw [dif_pos cj] at e; rw [← Option.some.inj e]
      show ∃ w, val ((vports V).idxOf j) = some w ∧ _
      by_cases hq : j = V.iq
      · subst hq
        rw [i0]
        refine ⟨_, h0, ?_⟩
        simp only [tinV, if_true]; rw [pp]
      · by_cases hK : j = V.iK
        · subst hK
          rw [i1]
          refine ⟨_, h1, ?_⟩
          simp only [tinV, if_neg hqK, if_true]; rw [pp]
        · have hk := idx_lt V j cj
          have k0 : (vports V).idxOf j ≠ 0 := fun e0 => hq ((List.idxOf_inj cj).mp (e0.trans i0.symm))
          have k1 : (vports V).idxOf j ≠ 1 := fun e1 => hK ((List.idxOf_inj cj).mp (e1.trans i1.symm))
          refine ⟨[], hz _ (by omega) hk, ?_⟩
          simp only [tinV, if_neg hq, if_neg hK]
          rw [Stages.pad_nil, pad_blank]
    · rw [dif_neg cj] at e; exact absurd e (by simp)
  · intro j e
    unfold nmV at e
    by_cases cj : j ∈ vports V
    · rw [dif_pos cj] at e; exact absurd e (by simp)
    · have hq : j ≠ V.iq := fun h => cj (by rw [h]; simp [vports])
      have hK : j ≠ V.iK := fun h => cj (by rw [h]; simp [vports])
      simp only [tinV, if_neg hq, if_neg hK]
      exact pad_blank R
  · intro x hx w e
    unfold valV at e
    by_cases c : x.val < 13
    · rw [if_pos c] at e
      left
      have hxl : x.val < (vports V).length := c
      refine ⟨(vports V)[x.val], ?_, ?_⟩
      · unfold nmV
        rw [dif_pos (List.getElem_mem hxl)]
        congr 1
        exact Fin.ext (nd.idxOf_getElem x.val hxl)
      · rw [← Option.some.inj e]; exact outs_eq x.val c
    · rw [if_neg c] at e
      right
      refine ⟨fun j hj => ?_, e⟩
      unfold nmV at hj
      by_cases cj : j ∈ vports V
      · rw [dif_pos cj] at hj
        have e2 := congrArg Fin.val (Option.some.inj hj)
        have := idx_lt V j cj
        simp only at e2
        omega
      · rw [dif_neg cj] at hj; exact absurd hj (by simp)

/-! ## 4. The program -/

/-- A register of the program's universe. -/
def rg (V : Meta.MetaVals2 selector s p packets L) (i : ℕ) (h : i < 41 := by decide) : Fin (191 + V.NP) := ⟨i, by omega⟩

theorem rg_lt (V : Meta.MetaVals2 selector s p packets L) (i : ℕ) (h : i < 41) : (rg V i h).val < 41 := h

theorem rg_ne (V : Meta.MetaVals2 selector s p packets L) (i j : ℕ) (hi : i < 41) (hj : j < 41) (h : i ≠ j) :
    rg V i hi ≠ rg V j hj := fun e => h (congrArg Fin.val e)

theorem trk_eq {R G NL : ℕ} {E : Fin NL → List Bool} {val : ℕ → Option (List Bool)} {f f' : ℕ}
    (h : Trk R G E val f) (e : f = f') : Trk R G E val f' := e ▸ h

/-- The tracking at entry. -/
def val0 (q K : ℕ) : ℕ → Option (List Bool) := fun i =>
  if i = 0 then some (List.replicate q true) else if i = 1 then some (List.replicate (2*K) true) else some []

/-- **The meta program** (ONE fixed machine; `cz`/`vz` select the degenerate `mC = 0` / `mV = 0` sources, fixed before any input). -/
def progM (V : Meta.MetaVals2 selector s p packets L) (cz vz : Bool) :=
  Composition.machine (Composition.machine (Composition.machine (Composition.machine (Composition.machine (Composition.machine (Composition.machine (Composition.machine (Composition.machine (Composition.machine (Composition.machine (Composition.machine (Composition.machine (Composition.machine (Composition.machine (Composition.machine (Composition.machine (Composition.machine (Composition.machine (Composition.machine (Composition.machine (Composition.machine (Composition.machine (Composition.machine (Composition.machine (Composition.machine (Composition.machine (Composition.machine (RecoveryFocus.machine (nslot (nmV V (by omega : 13 ≤ 191 + V.NP)) 41 (by omega)) V.machine)
    (fixM ([true]) (rg V 15) (41 + V.NP + 0) (by omega)))
    (fixM (RepairOrdinary.frame (natWord 3)) (rg V 16) (41 + V.NP + 2) (by omega)))
    (natM (rg V 2) (rg V 17) (41 + V.NP + 4) (by omega)))
    (natM (rg V 3) (rg V 18) (41 + V.NP + 26) (by omega)))
    (fruM (if cz then rg V 15 else rg V 7) (rg V 19) (41 + V.NP + 48) (by omega)))
    (fixM (RepairOrdinary.frame [false]) (rg V 20) (41 + V.NP + 51) (by omega)))
    (zerM (if cz then rg V 15 else rg V 4) (rg V 21) (41 + V.NP + 53) (by omega)))
    (cntM (rg V 6) (rg V 22) (41 + V.NP + 56) (by omega)))
    (fixM (RepairOrdinary.frame (natWord 4 ++ [true])) (rg V 23) (41 + V.NP + 66) (by omega)))
    (fruM (rg V 8) (rg V 24) (41 + V.NP + 68) (by omega)))
    (fixM (RepairOrdinary.frame [false]) (rg V 25) (41 + V.NP + 71) (by omega)))
    (zerM (rg V 8) (rg V 26) (41 + V.NP + 73) (by omega)))
    (fixM (RepairOrdinary.frame [true, true]) (rg V 27) (41 + V.NP + 76) (by omega)))
    (fruM (rg V 9) (rg V 28) (41 + V.NP + 78) (by omega)))
    (fixM (RepairOrdinary.frame [false]) (rg V 29) (41 + V.NP + 81) (by omega)))
    (zerM (rg V 9) (rg V 30) (41 + V.NP + 83) (by omega)))
    (fixM (RepairOrdinary.frame [true]) (rg V 31) (41 + V.NP + 86) (by omega)))
    (fruM (if vz then rg V 15 else rg V 11) (rg V 32) (41 + V.NP + 88) (by omega)))
    (fixM (RepairOrdinary.frame [false]) (rg V 33) (41 + V.NP + 91) (by omega)))
    (zerM (if vz then rg V 15 else rg V 5) (rg V 34) (41 + V.NP + 93) (by omega)))
    (cntM (rg V 10) (rg V 35) (41 + V.NP + 96) (by omega)))
    (fixM (RepairOrdinary.frame [true]) (rg V 36) (41 + V.NP + 106) (by omega)))
    (fruM (rg V 12) (rg V 37) (41 + V.NP + 108) (by omega)))
    (fixM (RepairOrdinary.frame [false]) (rg V 38) (41 + V.NP + 111) (by omega)))
    (zerM (rg V 12) (rg V 39) (41 + V.NP + 113) (by omega)))
    (fixM (RepairOrdinary.frame [true]) (rg V 40) (41 + V.NP + 116) (by omega)))
    (phAM 25 16 (by omega) (rg V 13) (41 + V.NP + 118) (by omega)))
    (phBM (rg V 13) (rg V 14) (41 + V.NP + 146) (by omega))

/-- Its cost. -/
def progCost (V : Meta.MetaVals2 selector s p packets L) (cz vz : Bool) (q : ℕ) : ℕ :=
  (((((((((((((((((((((((((((V.cost q + 1 + (2*([true]).length+2)) + 1 + (2*(RepairOrdinary.frame (natWord 3)).length+2)) + 1 + CloseoutRowsEstimatorParity.Natural.budget (wA q L)) + 1 + CloseoutRowsEstimatorParity.Natural.budget (uniformDeg q L)) + 1 + (2*(2*(BC selector s p cz q)+1)+2)) + 1 + (2*(RepairOrdinary.frame [false]).length+2)) + 1 + (2*(2*(XC cz q)+1)+2)) + 1 + CloseoutRowsCountBinary.budget (Meta.mC selector s p q)) + 1 + (2*(RepairOrdinary.frame (natWord 4 ++ [true])).length+2)) + 1 + (2*(2*(yH selector s p L q)+1)+2)) + 1 + (2*(RepairOrdinary.frame [false]).length+2)) + 1 + (2*(2*(yH selector s p L q)+1)+2)) + 1 + (2*(RepairOrdinary.frame [true, true]).length+2)) + 1 + (2*(2*(yCC selector s p L q)+1)+2)) + 1 + (2*(RepairOrdinary.frame [false]).length+2)) + 1 + (2*(2*(yCC selector s p L q)+1)+2)) + 1 + (2*(RepairOrdinary.frame [true]).length+2)) + 1 + (2*(2*(BV selector s p L vz q)+1)+2)) + 1 + (2*(RepairOrdinary.frame [false]).length+2)) + 1 + (2*(2*(XV L vz q)+1)+2)) + 1 + CloseoutRowsCountBinary.budget (Meta.mV selector s p q)) + 1 + (2*(RepairOrdinary.frame [true]).length+2)) + 1 + (2*(2*(yR selector s p packets q)+1)+2)) + 1 + (2*(RepairOrdinary.frame [false]).length+2)) + 1 + (2*(2*(yR selector s p packets q)+1)+2)) + 1 + (2*(RepairOrdinary.frame [true]).length+2)) + 1 + costA 25 (pwF selector s p packets L cz vz q)) + 1 + (2*((2*(MBof selector s p packets L q).length+1) + 1 + (2*0+1)) + 2)

/-- **The meta program's local run.** -/
theorem prog_run (V : Meta.MetaVals2 selector s p packets L) (cz vz : Bool) (q R : ℕ) (hR : 1 ≤ R)
    (hcap : CloseoutRowsEstimatorParity.Capacity.value q ≤ R)
    (hcz : cz = true ↔ Meta.mC selector s p q = 0) (hvz : vz = true ↔ Meta.mV selector s p q = 0)
    (E : Fin (191 + V.NP) → List Bool) (h0 : E (rg V 0) = ZeroPadding.pad R (List.replicate q true))
    (h1 : E (rg V 1) = ZeroPadding.pad R (List.replicate (2*normalizedLiveCount q L) true))
    (hz : ∀ x : Fin (191 + V.NP), 2 ≤ x.val → E x = List.replicate R false) :
    ∃ E' : Fin (191 + V.NP) → List Bool, Step (progM V cz vz) (progCost V cz vz q) (fun _ => 0) E (fun _ => 0) E' ∧
      E' (rg V 0) = E (rg V 0) ∧ E' (rg V 1) = E (rg V 1) ∧
      E' (rg V 13) = ZeroPadding.pad R (RepairOrdinary.frame (MBof selector s p packets L q)) ∧
      E' (rg V 14) = ZeroPadding.pad R (RepairOrdinary.frame (List.replicate (MBof selector s p packets L q).length true)) := by
  have hid := pieces_frame selector s p packets L cz vz q hcz hvz
  have T0 : Trk R 41 E (val0 q (normalizedLiveCount q L)) 41 := by
    refine ⟨le_rfl, ?_, fun x hx => hz x (by omega)⟩
    intro x hx w e
    unfold val0 at e
    by_cases c0 : x.val = 0
    · rw [if_pos c0] at e
      have ex : x = rg V 0 := Fin.ext c0
      rw [ex, h0, ← Option.some.inj e]
    · rw [if_neg c0] at e
      by_cases c1 : x.val = 1
      · rw [if_pos c1] at e
        have ex : x = rg V 1 := Fin.ext c1
        rw [ex, h1, ← Option.some.inj e]
      · rw [if_neg c1] at e
        rw [← Option.some.inj e, Stages.pad_nil]
        exact hz x (by omega)
  obtain ⟨E1, s1, T1⟩ := v_trk V q R 41 (by omega) (by decide) 41 (by omega) T0 (by simp [val0]) (by simp [val0])
    (by intro i h2 _; unfold val0; rw [if_neg (by omega), if_neg (by omega)])
  obtain ⟨E2, s2, T2⟩ := fix_trk ([true]) (rg V 15) (rg_lt V _ _) (41 + V.NP + 0) (by omega) (trk_eq T1 (by omega)) (by simp [Function.update_apply, valV, outsV, val0, rg, valA, yCC])
  obtain ⟨E3, s3, T3⟩ := fix_trk (RepairOrdinary.frame (natWord 3)) (rg V 16) (rg_lt V _ _) (41 + V.NP + 2) (by omega) (trk_eq T2 (by omega)) (by simp [Function.update_apply, valV, outsV, val0, rg, valA, yCC])
  obtain ⟨E4, s4, T4⟩ := nat_trk q (wA q L) (wA_le q L) hcap (rg V 2) (rg V 17) (rg_ne V _ _ _ _ (by decide)) (rg_lt V _ _) (rg_lt V _ _) (41 + V.NP + 4) (by omega) (trk_eq T3 (by omega)) (by simp [Function.update_apply, valV, outsV, val0, rg, valA, yCC]) (by simp [Function.update_apply, valV, outsV, val0, rg, valA, yCC])
  obtain ⟨E5, s5, T5⟩ := nat_trk q (uniformDeg q L) (deg_le q L) hcap (rg V 3) (rg V 18) (rg_ne V _ _ _ _ (by decide)) (rg_lt V _ _) (rg_lt V _ _) (41 + V.NP + 26) (by omega) (trk_eq T4 (by omega)) (by simp [Function.update_apply, valV, outsV, val0, rg, valA, yCC]) (by simp [Function.update_apply, valV, outsV, val0, rg, valA, yCC])
  obtain ⟨E6, s6, T6⟩ := fru_trk (BC selector s p cz q) (if cz then rg V 15 else rg V 7) (rg V 19) (by cases cz <;> exact rg_ne V _ _ (by decide) (by decide) (by decide)) (by cases cz <;> exact rg_lt V _ (by decide)) (rg_lt V _ _) (41 + V.NP + 48) (by omega) (trk_eq T5 (by omega)) (by cases cz <;> simp [Function.update_apply, valV, outsV, val0, rg, valA, yCC, BC, XC, BV, XV]) (by simp [Function.update_apply, valV, outsV, val0, rg, valA, yCC])
  obtain ⟨E7, s7, T7⟩ := fix_trk (RepairOrdinary.frame [false]) (rg V 20) (rg_lt V _ _) (41 + V.NP + 51) (by omega) (trk_eq T6 (by omega)) (by simp [Function.update_apply, valV, outsV, val0, rg, valA, yCC])
  obtain ⟨E8, s8, T8⟩ := zer_trk (XC cz q) (if cz then rg V 15 else rg V 4) (rg V 21) (by cases cz <;> exact rg_ne V _ _ (by decide) (by decide) (by decide)) (by cases cz <;> exact rg_lt V _ (by decide)) (rg_lt V _ _) (41 + V.NP + 53) (by omega) (trk_eq T7 (by omega)) (by cases cz <;> simp [Function.update_apply, valV, outsV, val0, rg, valA, yCC, BC, XC, BV, XV]) (by simp [Function.update_apply, valV, outsV, val0, rg, valA, yCC])
  obtain ⟨E9, s9, T9⟩ := cnt_trk (Meta.mC selector s p q) (rg V 6) (rg V 22) (rg_ne V _ _ _ _ (by decide)) (rg_lt V _ _) (rg_lt V _ _) (41 + V.NP + 56) (by omega) (trk_eq T8 (by omega)) (by simp [Function.update_apply, valV, outsV, val0, rg, valA, yCC]) (by simp [Function.update_apply, valV, outsV, val0, rg, valA, yCC])
  obtain ⟨E10, s10, T10⟩ := fix_trk (RepairOrdinary.frame (natWord 4 ++ [true])) (rg V 23) (rg_lt V _ _) (41 + V.NP + 66) (by omega) (trk_eq T9 (by omega)) (by simp [Function.update_apply, valV, outsV, val0, rg, valA, yCC])
  obtain ⟨E11, s11, T11⟩ := fru_trk (yH selector s p L q) (rg V 8) (rg V 24) (rg_ne V _ _ _ _ (by decide)) (rg_lt V _ _) (rg_lt V _ _) (41 + V.NP + 68) (by omega) (trk_eq T10 (by omega)) (by simp [Function.update_apply, valV, outsV, val0, rg, valA, yCC]) (by simp [Function.update_apply, valV, outsV, val0, rg, valA, yCC])
  obtain ⟨E12, s12, T12⟩ := fix_trk (RepairOrdinary.frame [false]) (rg V 25) (rg_lt V _ _) (41 + V.NP + 71) (by omega) (trk_eq T11 (by omega)) (by simp [Function.update_apply, valV, outsV, val0, rg, valA, yCC])
  obtain ⟨E13, s13, T13⟩ := zer_trk (yH selector s p L q) (rg V 8) (rg V 26) (rg_ne V _ _ _ _ (by decide)) (rg_lt V _ _) (rg_lt V _ _) (41 + V.NP + 73) (by omega) (trk_eq T12 (by omega)) (by simp [Function.update_apply, valV, outsV, val0, rg, valA, yCC]) (by simp [Function.update_apply, valV, outsV, val0, rg, valA, yCC])
  obtain ⟨E14, s14, T14⟩ := fix_trk (RepairOrdinary.frame [true, true]) (rg V 27) (rg_lt V _ _) (41 + V.NP + 76) (by omega) (trk_eq T13 (by omega)) (by simp [Function.update_apply, valV, outsV, val0, rg, valA, yCC])
  obtain ⟨E15, s15, T15⟩ := fru_trk (yCC selector s p L q) (rg V 9) (rg V 28) (rg_ne V _ _ _ _ (by decide)) (rg_lt V _ _) (rg_lt V _ _) (41 + V.NP + 78) (by omega) (trk_eq T14 (by omega)) (by simp [Function.update_apply, valV, outsV, val0, rg, valA, yCC]) (by simp [Function.update_apply, valV, outsV, val0, rg, valA, yCC])
  obtain ⟨E16, s16, T16⟩ := fix_trk (RepairOrdinary.frame [false]) (rg V 29) (rg_lt V _ _) (41 + V.NP + 81) (by omega) (trk_eq T15 (by omega)) (by simp [Function.update_apply, valV, outsV, val0, rg, valA, yCC])
  obtain ⟨E17, s17, T17⟩ := zer_trk (yCC selector s p L q) (rg V 9) (rg V 30) (rg_ne V _ _ _ _ (by decide)) (rg_lt V _ _) (rg_lt V _ _) (41 + V.NP + 83) (by omega) (trk_eq T16 (by omega)) (by simp [Function.update_apply, valV, outsV, val0, rg, valA, yCC]) (by simp [Function.update_apply, valV, outsV, val0, rg, valA, yCC])
  obtain ⟨E18, s18, T18⟩ := fix_trk (RepairOrdinary.frame [true]) (rg V 31) (rg_lt V _ _) (41 + V.NP + 86) (by omega) (trk_eq T17 (by omega)) (by simp [Function.update_apply, valV, outsV, val0, rg, valA, yCC])
  obtain ⟨E19, s19, T19⟩ := fru_trk (BV selector s p L vz q) (if vz then rg V 15 else rg V 11) (rg V 32) (by cases vz <;> exact rg_ne V _ _ (by decide) (by decide) (by decide)) (by cases vz <;> exact rg_lt V _ (by decide)) (rg_lt V _ _) (41 + V.NP + 88) (by omega) (trk_eq T18 (by omega)) (by cases vz <;> simp [Function.update_apply, valV, outsV, val0, rg, valA, yCC, BC, XC, BV, XV]) (by simp [Function.update_apply, valV, outsV, val0, rg, valA, yCC])
  obtain ⟨E20, s20, T20⟩ := fix_trk (RepairOrdinary.frame [false]) (rg V 33) (rg_lt V _ _) (41 + V.NP + 91) (by omega) (trk_eq T19 (by omega)) (by simp [Function.update_apply, valV, outsV, val0, rg, valA, yCC])
  obtain ⟨E21, s21, T21⟩ := zer_trk (XV L vz q) (if vz then rg V 15 else rg V 5) (rg V 34) (by cases vz <;> exact rg_ne V _ _ (by decide) (by decide) (by decide)) (by cases vz <;> exact rg_lt V _ (by decide)) (rg_lt V _ _) (41 + V.NP + 93) (by omega) (trk_eq T20 (by omega)) (by cases vz <;> simp [Function.update_apply, valV, outsV, val0, rg, valA, yCC, BC, XC, BV, XV]) (by simp [Function.update_apply, valV, outsV, val0, rg, valA, yCC])
  obtain ⟨E22, s22, T22⟩ := cnt_trk (Meta.mV selector s p q) (rg V 10) (rg V 35) (rg_ne V _ _ _ _ (by decide)) (rg_lt V _ _) (rg_lt V _ _) (41 + V.NP + 96) (by omega) (trk_eq T21 (by omega)) (by simp [Function.update_apply, valV, outsV, val0, rg, valA, yCC]) (by simp [Function.update_apply, valV, outsV, val0, rg, valA, yCC])
  obtain ⟨E23, s23, T23⟩ := fix_trk (RepairOrdinary.frame [true]) (rg V 36) (rg_lt V _ _) (41 + V.NP + 106) (by omega) (trk_eq T22 (by omega)) (by simp [Function.update_apply, valV, outsV, val0, rg, valA, yCC])
  obtain ⟨E24, s24, T24⟩ := fru_trk (yR selector s p packets q) (rg V 12) (rg V 37) (rg_ne V _ _ _ _ (by decide)) (rg_lt V _ _) (rg_lt V _ _) (41 + V.NP + 108) (by omega) (trk_eq T23 (by omega)) (by simp [Function.update_apply, valV, outsV, val0, rg, valA, yCC]) (by simp [Function.update_apply, valV, outsV, val0, rg, valA, yCC])
  obtain ⟨E25, s25, T25⟩ := fix_trk (RepairOrdinary.frame [false]) (rg V 38) (rg_lt V _ _) (41 + V.NP + 111) (by omega) (trk_eq T24 (by omega)) (by simp [Function.update_apply, valV, outsV, val0, rg, valA, yCC])
  obtain ⟨E26, s26, T26⟩ := zer_trk (yR selector s p packets q) (rg V 12) (rg V 39) (rg_ne V _ _ _ _ (by decide)) (rg_lt V _ _) (rg_lt V _ _) (41 + V.NP + 113) (by omega) (trk_eq T25 (by omega)) (by simp [Function.update_apply, valV, outsV, val0, rg, valA, yCC]) (by simp [Function.update_apply, valV, outsV, val0, rg, valA, yCC])
  obtain ⟨E27, s27, T27⟩ := fix_trk (RepairOrdinary.frame [true]) (rg V 40) (rg_lt V _ _) (41 + V.NP + 116) (by omega) (trk_eq T26 (by omega)) (by simp [Function.update_apply, valV, outsV, val0, rg, valA, yCC])
  obtain ⟨E28, s28, T28⟩ := phA_trk hR 25 16 (by decide) (by omega) (rg V 13) (Or.inl (by show 13 < 16; decide)) (rg_lt V _ _) (pwF selector s p packets L cz vz q) (41 + V.NP + 118) (by omega) (trk_eq T27 (by omega)) (by intro k; fin_cases k <;> simp [Function.update_apply, valV, outsV, val0, rg, valA, yCC, pwF, pw]) (by simp [Function.update_apply, valV, outsV, val0, rg, valA, yCC])
  obtain ⟨E29, s29, T29⟩ := phB_trk hR (MBof selector s p packets L q) (rg V 13) (rg V 14) (rg_ne V _ _ _ _ (by decide)) (rg_lt V _ _) (rg_lt V _ _) (41 + V.NP + 146) (by omega) (trk_eq T28 (by omega)) (by simp only [Function.update_apply, rg, Fin.val_mk]; unfold valA; rw [if_pos rfl, hid]) (by simp [Function.update_apply, valV, outsV, val0, rg, valA, yCC])
  refine ⟨E29, ((((((((((((((((((((((((((((s1.seq s2).seq s3).seq s4).seq s5).seq s6).seq s7).seq s8).seq s9).seq s10).seq s11).seq s12).seq s13).seq s14).seq s15).seq s16).seq s17).seq s18).seq s19).seq s20).seq s21).seq s22).seq s23).seq s24).seq s25).seq s26).seq s27).seq s28).seq s29), ?_, ?_, ?_, ?_⟩
  · rw [T29.2.1 (rg V 0) (rg_lt V _ _) (List.replicate q true) (by simp [Function.update_apply, valV, outsV, val0, rg, valA, yCC])]; exact h0.symm
  · rw [T29.2.1 (rg V 1) (rg_lt V _ _) (List.replicate (2*normalizedLiveCount q L) true) (by simp [Function.update_apply, valV, outsV, val0, rg, valA, yCC])]; exact h1.symm
  · rw [T29.2.1 (rg V 13) (rg_lt V _ _) (RepairOrdinary.frame (MBof selector s p packets L q))
      (by simp only [Function.update_apply, rg, Fin.val_mk]; unfold valA; rw [if_pos rfl, hid]; exact if_neg (by decide))]
  · rw [T29.2.1 (rg V 14) (rg_lt V _ _) _ (Function.update_self _ _ _)]

end
end NearCubicWires.SourceStart.MetaRun


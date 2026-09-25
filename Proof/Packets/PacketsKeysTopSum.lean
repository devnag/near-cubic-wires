import Proof.Packets.PacketsKeysNativeStages

set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unusedSimpArgs false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false

namespace NearCubicWires.PacketsKeys.Native
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.RepairOrdinary.RecoveryExecution NearCubicWires.ExtDecompositionBatch
open NearCubicWires.RepairRepresentation NearCubicWires.PacketsMeta NearCubicWires.PacketsKeys
open NearCubicWires.SupplierPipeline PCJd4d1d9d7d1fa4313_Production NearCubicWires.PacketsGlue.RequestMeta
noncomputable section

section Block2
variable {W : ℕ} (w : List Bool) (s : NS)

/-- Read circuit `c`'s stream at an arbitrary cursor `p`. -/
theorem readBCp (c : Fin 4) (pay : List Bool) (x p : ℕ)
    (hS : ∀ i, i < (natWord x).length → sf pay (p + i) = (natWord x).getD i false) (hW : natBitLength x ≤ W)
    (hcs : s.ct (cS c) = .cells (sf pay) p) (hcm : s.ct (cM c) = .cells (Setup.mk pay) p) :
    LRuns W (ReadNat.at5 (4 : Fin 26) (sS c) (sM c) 5 13) (3 * W + 5) (nv w s)
      (nv w { s with
        b := x,
        ct := Function.update (Function.update s.ct (cS c) (.cells (sf pay) (p + (natWord x).length))) (cM c)
          (.cells (Setup.mk pay) (p + (natWord x).length)) }) := by
  have hi : Function.Injective ![(4 : Fin 26), sS c, sM c, 5, 13] := by fin_cases c <;> decide
  have h := ReadNat.at_run (W := W) (nv w s) (4 : Fin 26) (sS c) (sM c) 5 13 hi p x s.b (sf pay) (Setup.mk pay)
    hW hS rfl ((nv_S w s c).trans hcs) ((nv_M w s c).trans hcm) rfl rfl
  refine h.congr_out ?_
  funext i; fin_cases c <;> fin_cases i <;> rfl

/-- The THR block body: unframe the payload, read its two leading numbers, `sum := sum + second`. -/
def body2 (c : Fin 4) :=
  Composition.machine (RecoveryFocus.machine ![(2 : Fin 26), sS c, sM c] Unframe.machine)
    (Composition.machine (ReadNat.at5 (4 : Fin 26) (sS c) (sM c) 5 13)
      (Composition.machine (ReadNat.at5 (4 : Fin 26) (sS c) (sM c) 5 13)
        (swAt addF false true (4 : Fin 26) 11 13 6)))

def block2 (c : Fin 4) := Ite (RecoveryFocus.machine ![(2 : Fin 26), 6] peek) (body2 c) (nop 26) (6 : Fin 26)

def body2Cost (W m : ℕ) : ℕ := (5 * m + 10) + 1 + ((3 * W + 5) + 1 + ((3 * W + 5) + 1 + (2 * W + 3)))

def block2Cost (W m : ℕ) : ℕ := 1 + body2Cost W m + 0 + 2

theorem block2_present (c : Fin 4) (pay rest : List Bool) (x1 x2 : ℕ)
    (hpay : pay = natWord x1 ++ natWord x2 ++ rest)
    (hX : ∀ i, i < (RepairOrdinary.frame pay).length → sf w (s.sp + i) = (RepairOrdinary.frame pay).getD i false)
    (hct : s.ct = ctAfter c.val) (hW1 : natBitLength x1 ≤ W) (hW2 : natBitLength x2 ≤ W)
    (hx2 : x2 < 2 ^ W) (hsum : s.sum + x2 < 2 ^ W) :
    LRuns W (block2 c) (block2Cost W pay.length) (nv w s)
      (nv w { s with
        sp := s.sp + (RepairOrdinary.frame pay).length, fl := false, b := x2, sum := s.sum + x2,
        ct := ctAfter (c.val + 1) }) := by
  have hne : 0 < (RepairOrdinary.frame pay).length := by rw [RepairOrdinary.frame_length]; omega
  have hbit : sf w s.sp = true := by
    have := hX 0 hne
    rw [Nat.add_zero] at this
    rw [this, hpay]
    have hl := ReadNat.natWord_length x1
    cases hn : natWord x1 with
    | nil => rw [hn] at hl; simp at hl
    | cons y ys => simp [RepairOrdinary.frame]
  unfold block2Cost block2
  refine Ite.runs (W := W) (np := body2Cost W pay.length) (nq := 0) _ _ _ (6 : Fin 26) (true) (peekS w s)
    (by simp [nv, hbit]) ?_ (fun h => by simp at h)
  intro _
  set s1 : NS := { s with fl := sf w s.sp } with hs1
  have e1 := unframeC (W := W) w s1 c pay hX (by show s.ct (cS c) = _; rw [hct]; exact ctAfter_S c)
    (by show s.ct (cM c) = _; rw [hct]; exact ctAfter_M c)
  have e2 := readBCp (W := W) w (uf s1 c pay) c pay x1 1 (by
      intro i hi
      have := read_mid [] (natWord x2 ++ rest) x1 i hi
      simp only [List.nil_append, List.length_nil, Nat.zero_add] at this
      rw [hpay, List.append_assoc]
      exact this) hW1 (by fin_cases c <;> rfl) (by fin_cases c <;> rfl)
  have e3 := readBCp (W := W) w
    { uf s1 c pay with
      b := x1,
      ct := Function.update (Function.update (uf s1 c pay).ct (cS c) (.cells (sf pay) (1 + (natWord x1).length)))
        (cM c) (.cells (Setup.mk pay) (1 + (natWord x1).length)) }
    c pay x2 (1 + (natWord x1).length) (by
      intro i hi
      have := read_mid (natWord x1) rest x2 i hi
      rw [hpay, show 1 + (natWord x1).length + i = (natWord x1).length + 1 + i by omega]
      exact this) hW2 (by fin_cases c <;> rfl) (by fin_cases c <;> rfl)
  have e4 := addSum (W := W) w
    { { uf s1 c pay with
        b := x1,
        ct := Function.update (Function.update (uf s1 c pay).ct (cS c) (.cells (sf pay) (1 + (natWord x1).length)))
          (cM c) (.cells (Setup.mk pay) (1 + (natWord x1).length)) } with
      b := x2,
      ct := Function.update (Function.update (Function.update (Function.update (uf s1 c pay).ct (cS c)
          (.cells (sf pay) (1 + (natWord x1).length))) (cM c) (.cells (Setup.mk pay) (1 + (natWord x1).length)))
          (cS c) (.cells (sf pay) (1 + (natWord x1).length + (natWord x2).length))) (cM c)
          (.cells (Setup.mk pay) (1 + (natWord x1).length + (natWord x2).length)) }
    (by show s.sum < _; omega) hx2 hsum
  have hall := e1.seq (e2.seq (e3.seq e4))
  refine (hall.weaken (weaken_ct w _ _ ?_)).enlarge (by unfold body2Cost; omega)
  intro j H A h
  simp only [uf] at h
  rw [hct] at h
  fin_cases c <;> fin_cases j <;> first | trivial | exact h

theorem block2_absent (c : Fin 4) (m : ℕ) (hbit : sf w s.sp = false) (hct : s.ct = ctAfter c.val) :
    LRuns W (block2 c) (block2Cost W m) (nv w s) (nv w { s with fl := false, ct := ctAfter (c.val + 1) }) := by
  unfold block2Cost block2
  refine Ite.runs (W := W) (np := body2Cost W m) (nq := 0) _ _ _ (6 : Fin 26) false (peekS w s) (by simp [nv, hbit])
    (fun h => by simp at h) ?_
  intro _
  have e : ({ s with fl := sf w s.sp } : NS) = { s with fl := false } := by rw [hbit]
  rw [e]
  refine (nop_lruns _).weaken (weaken_ct w { s with fl := false } _ ?_)
  intro j H A h
  have h' : TR W (ctAfter c.val j) H A := by rw [← hct]; exact h
  exact ctAfter_mono c.val j H A h'

end Block2

/-- The chain state after `c` THR blocks. -/
def chain2 {α : Type} (S0 : NS) (L : List α) (F : α → List Bool) (g : α → ℕ) (c bb : ℕ) : NS :=
  { S0 with
    sp := 1 + ((L.take c).flatMap F).length,
    sum := ((L.take c).map g).sum,
    ct := ctAfter c, fl := false, b := bb }

theorem block2_step {α : Type} {W : ℕ} (w : List Bool) (L : List α) (pay : α → List Bool) (n1 n2 : α → ℕ)
    (hw : w = L.flatMap (fun a => RepairOrdinary.frame (pay a)))
    (hpay : ∀ a, ∃ rest, pay a = natWord (n1 a) ++ natWord (n2 a) ++ rest)
    (hnb : ∀ a ∈ L, natBitLength (n1 a) ≤ W ∧ natBitLength (n2 a) ≤ W)
    (hsumB : (L.map n2).sum < 2 ^ W)
    (S0 : NS) (c : Fin 4) (bb m : ℕ) (hm : w.length ≤ m) :
    ∃ bb', LRuns W (block2 c) (block2Cost W m)
      (nv w (chain2 S0 L (fun a => RepairOrdinary.frame (pay a)) n2 c.val bb))
      (nv w (chain2 S0 L (fun a => RepairOrdinary.frame (pay a)) n2 (c.val + 1) bb')) := by
  set F : α → List Bool := fun a => RepairOrdinary.frame (pay a) with hF
  by_cases hc : c.val < L.length
  · obtain ⟨rest, hr⟩ := hpay L[c.val]
    have hsplit := flatMap_split L F c.val hc
    have hpl : (pay L[c.val]).length ≤ m := by
      have h1 : (F L[c.val]).length ≤ w.length := by
        rw [hw, hsplit]; simp only [List.length_append]; omega
      have h2 : (F L[c.val]).length = 2 * (pay L[c.val]).length + 1 := RepairOrdinary.frame_length _
      omega
    have hX : ∀ i, i < (RepairOrdinary.frame (pay L[c.val])).length →
        sf w ((chain2 S0 L F n2 c.val bb).sp + i) = (RepairOrdinary.frame (pay L[c.val])).getD i false := by
      intro i hi
      have e : w = ((L.take c.val).flatMap F) ++ F L[c.val] ++ (L.drop (c.val + 1)).flatMap F := by
        rw [hw, hsplit]
      have := sf_mid ((L.take c.val).flatMap F) (F L[c.val]) ((L.drop (c.val + 1)).flatMap F) i hi
      rw [e]
      convert this using 2
      simp only [chain2]
      omega
    have hsum1 := sum_take_le L n2 (c.val + 1)
    rw [take_succ_of_lt L c.val hc, List.map_append, List.sum_append] at hsum1
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.add_zero] at hsum1
    refine ⟨n2 L[c.val], ?_⟩
    have h := block2_present (W := W) w (chain2 S0 L F n2 c.val bb) c (pay L[c.val]) rest (n1 L[c.val])
      (n2 L[c.val]) hr hX rfl (hnb _ (List.getElem_mem hc)).1 (hnb _ (List.getElem_mem hc)).2
      (by omega) (by show ((L.take c.val).map n2).sum + n2 L[c.val] < 2 ^ W; omega)
    refine (h.enlarge (by unfold block2Cost body2Cost; omega)).congr_out ?_
    congr 1
    simp only [chain2, take_succ_of_lt L c.val hc, List.flatMap_append, List.map_append,
      List.sum_append, List.length_append, List.flatMap_cons, List.flatMap_nil,
      List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, List.append_nil]
    simp only [hF]
    congr 1 <;> omega
  · have hle : L.length ≤ c.val := by omega
    have htake : L.take c.val = L := List.take_of_length_le hle
    have htake1 : L.take (c.val + 1) = L := List.take_of_length_le (by omega)
    have hbit : sf w (chain2 S0 L F n2 c.val bb).sp = false := by
      simp only [chain2, htake]
      rw [show 1 + (L.flatMap F).length = (L.flatMap F).length + 1 by omega, sf_succ]
      apply List.getD_eq_default
      rw [hw]
    refine ⟨bb, ?_⟩
    have h := block2_absent (W := W) w (chain2 S0 L F n2 c.val bb) c m hbit rfl
    refine h.congr_out ?_
    simp only [chain2, htake, htake1]

end
end NearCubicWires.PacketsKeys.Native


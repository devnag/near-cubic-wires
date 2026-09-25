import Proof.Packets.PacketsKeysNativeRun

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
noncomputable section

def symPart :=
  Composition.machine (swAt addF true true (4 : Fin 26) 12 7 6)
    (Composition.machine (block 0) (Composition.machine (block 1) (Composition.machine (block 2) (block 3))))

def symPartCost (W m : ℕ) : ℕ :=
  (2 * W + 3) + 1 + (blockCost W m + 1 + (blockCost W m + 1 + (blockCost W m + 1 + blockCost W m)))

def headerPart := Ite header symPart (nop 26) (6 : Fin 26)

def headerPartCost (W m : ℕ) : ℕ := headerCost W + symPartCost W m + 0 + 2

def main := Ite front headerPart (nop 26) (6 : Fin 26)

def mainCost (W m : ℕ) : ℕ := frontCost W m + headerPartCost W m + 0 + 2

/-- **The four blocks.** -/
theorem symPart_run {α : Type} {W : ℕ} (w pre : List Bool) (L : List α) (pay : α → List Bool) (num : α → ℕ)
    (hw : w = pre ++ L.flatMap (fun a => RepairOrdinary.frame (pay a)))
    (hpay : ∀ a, ∃ rest, pay a = natWord (num a) ++ rest)
    (hnb : ∀ a ∈ L, natBitLength (num a) ≤ W) (hW1 : 1 ≤ W)
    (hsumB : (L.map (fun a => num a + 1)).sum < 2 ^ W) (hprodB : (L.map (fun a => num a + 1)).prod < 2 ^ W)
    (S : NS) (hsp : S.sp = 1 + pre.length) (hsum : S.sum = 0) (hprod : S.prod = 0)
    (hct : S.ct = ctAfter 0) :
    ∃ bb pp, LRuns W symPart (symPartCost W w.length) (nv w S)
      (nv w (chainSt S pre L (fun a => RepairOrdinary.frame (pay a)) (fun a => num a + 1) 4 bb pp)) := by
  have e0 := incProd (W := W) w S (by
    rw [hprod]
    have : 2 ^ 0 < 2 ^ W := Nat.pow_lt_pow_right (by norm_num) (by omega)
    simpa using this)
  have hs0 : ({ S with prod := S.prod + 1, fl := false } : NS) =
      chainSt S pre L (fun a => RepairOrdinary.frame (pay a)) (fun a => num a + 1) 0 S.b S.p2 := by
    cases S
    simp only [chainSt] at hsp hsum hprod hct ⊢
    subst hsp hsum hprod hct
    simp
  rw [hs0] at e0
  obtain ⟨b1, p1, e1⟩ := block_step (W := W) w pre L pay num hw hpay hnb hW1 hsumB hprodB S 0 S.b S.p2 _ le_rfl
  obtain ⟨b2, p2, e2⟩ := block_step (W := W) w pre L pay num hw hpay hnb hW1 hsumB hprodB S 1 b1 p1 _ le_rfl
  obtain ⟨b3, p3, e3⟩ := block_step (W := W) w pre L pay num hw hpay hnb hW1 hsumB hprodB S 2 b2 p2 _ le_rfl
  obtain ⟨b4, p4, e4⟩ := block_step (W := W) w pre L pay num hw hpay hnb hW1 hsumB hprodB S 3 b3 p3 _ le_rfl
  exact ⟨b4, p4, e0.seq (e1.seq (e2.seq (e3.seq e4)))⟩

/-! ## The three kinds -/

/-- The result of `main`: the output still empty, the three registers holding `nc`, `sum`, `prod`. -/
def MainResult (w : List Bool) (nc sm pr : ℕ) : Prop :=
  ∃ s : NS, LRuns (8 * w.length) main (mainCost (8 * w.length) w.length) (initRoles 26 w) (nv w s) ∧
    s.out = 0 ∧ s.nc = nc ∧ s.sum = sm ∧ s.prod = pr

/-- The terminal sentinel (`tag = 2`): nothing after the kind test. -/
theorem main_term : MainResult (natWord 2) 0 0 0 := by
  refine ⟨sF (natWord 2) 2, ?_, rfl, rfl, rfl, rfl⟩
  unfold main mainCost
  refine Ite.runs (W := 8 * (natWord 2).length) (np := headerPartCost (8 * (natWord 2).length) (natWord 2).length)
    (nq := 0) _ _ _ (6 : Fin 26) false (front_run (natWord 2) [] 2 (by simp) le_rfl (by simp [ReadNat.natWord_length]))
    (by rfl) (fun h => by simp at h) (fun _ => nop_lruns _)

/-- A kind-`t` request with `t < 2`, the header, then (SYM only) the four circuit blocks. -/
theorem main_thr (rest : List Bool) (q L tg n : ℕ) :
    MainResult (hdr 1 q L tg n ++ rest) n 0 0 := by
  set w := hdr 1 q L tg n ++ rest with hw
  refine ⟨sH w 1 q L tg n, ?_, rfl, rfl, rfl, rfl⟩
  have hW1 : 1 ≤ w.length := by rw [hw]; simp [hdr, ReadNat.natWord_length]; omega
  unfold main mainCost
  refine Ite.runs (W := 8 * w.length) (np := headerPartCost (8 * w.length) w.length) (nq := 0) _ _ _ (6 : Fin 26) true
    (front_run w (natWord q ++ natWord L ++ natWord tg ++ natWord n ++ rest) 1 (by simp [hw, hdr]) (by omega) hW1)
    (by rfl) (fun _ => ?_) (fun h => by simp at h)
  unfold headerPart headerPartCost
  exact Ite.runs (W := 8 * w.length) (np := symPartCost (8 * w.length) w.length) (nq := 0) _ _ _ (6 : Fin 26) false
    (header_run w rest 1 q L tg n rfl (by omega)) (by rfl) (fun h => by simp at h) (fun _ => nop_lruns _)

theorem main_sym {α : Type} (q Lv tg : ℕ) (L : List α) (pay : α → List Bool) (num : α → ℕ)
    (hpay : ∀ a, ∃ rest, pay a = natWord (num a) ++ rest)
    (hnb : ∀ a ∈ L, natBitLength (num a) ≤ 8 * (hdr 0 q Lv tg L.length ++
      L.flatMap (fun a => RepairOrdinary.frame (pay a))).length)
    (hsumB : (L.map (fun a => num a + 1)).sum < 2 ^ (8 * (hdr 0 q Lv tg L.length ++
      L.flatMap (fun a => RepairOrdinary.frame (pay a))).length))
    (hprodB : (L.map (fun a => num a + 1)).prod < 2 ^ (8 * (hdr 0 q Lv tg L.length ++
      L.flatMap (fun a => RepairOrdinary.frame (pay a))).length))
    (hL : L.length ≤ 4) :
    MainResult (hdr 0 q Lv tg L.length ++ L.flatMap (fun a => RepairOrdinary.frame (pay a))) L.length
      (L.map (fun a => num a + 1)).sum (L.map (fun a => num a + 1)).prod := by
  set w := hdr 0 q Lv tg L.length ++ L.flatMap (fun a => RepairOrdinary.frame (pay a)) with hw
  have hW1 : 1 ≤ w.length := by rw [hw]; simp [hdr, ReadNat.natWord_length]; omega
  obtain ⟨bb, pp, hsp⟩ := symPart_run (W := 8 * w.length) w (hdr 0 q Lv tg L.length) L pay num hw hpay hnb
    (by omega) hsumB hprodB (sH w 0 q Lv tg L.length) rfl rfl rfl rfl
  have htake : L.take 4 = L := List.take_of_length_le hL
  refine ⟨chainSt (sH w 0 q Lv tg L.length) (hdr 0 q Lv tg L.length) L (fun a => RepairOrdinary.frame (pay a))
    (fun a => num a + 1) 4 bb pp, ?_, rfl, rfl, by simp only [chainSt, htake], by simp only [chainSt, htake]⟩
  unfold main mainCost
  refine Ite.runs (W := 8 * w.length) (np := headerPartCost (8 * w.length) w.length) (nq := 0) _ _ _ (6 : Fin 26) true
    (front_run w (natWord q ++ natWord Lv ++ natWord tg ++ natWord L.length ++
      L.flatMap (fun a => RepairOrdinary.frame (pay a))) 0 (by simp [hw, hdr]) (by omega) hW1)
    (by rfl) (fun _ => ?_) (fun h => by simp at h)
  unfold headerPart headerPartCost
  exact Ite.runs (W := 8 * w.length) (np := symPartCost (8 * w.length) w.length) (nq := 0) _ _ _ (6 : Fin 26) true
    (header_run w _ 0 q Lv tg L.length rfl (by omega)) (by rfl) (fun _ => hsp) (fun h => by simp at h)

/-! ## Emission -/

def prog (v : Fin 26) := Composition.machine main (RecoveryFocus.machine ![(4 : Fin 26), 7, v, 6, 1] Emit.machine)

def progCost (W m V : ℕ) : ℕ := mainCost W m + 1 + (V + 1) * ((2 * W + 3) + (2 * W + 3 + 1 + 1) + 2)

theorem prog_run (w : List Bool) (nc sm pr : ℕ) (h : MainResult w nc sm pr) (v : Fin 26)
    (hinj : Function.Injective ![(4 : Fin 26), 7, v, 6, 1]) (V : ℕ)
    (hV : ∀ s : NS, s.nc = nc → s.sum = sm → s.prod = pr → nv w s v = .reg V) (hVW : V < 2 ^ (8 * w.length)) :
    ∃ σ' : Fin 26 → TS, LRuns (8 * w.length) (prog v) (progCost (8 * w.length) w.length V) (initRoles 26 w) σ' ∧
      σ' 1 = .out V := by
  obtain ⟨s, hm, ho, hn, hs, hp⟩ := h
  have he := emitAt (W := 8 * w.length) w s v hinj V (hV s hn hs hp) hVW
  refine ⟨_, hm.seq he, ?_⟩
  simp [ho]

end
end NearCubicWires.PacketsKeys.Native


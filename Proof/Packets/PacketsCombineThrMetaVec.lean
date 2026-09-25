import Proof.Packets.PacketsCombineThrWord
import Proof.Packets.PacketsCombineTabReads

set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false

namespace NearCubicWires.PacketsCombine.Asm
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairSource.VerifierDecoding
open NearCubicWires.RepairRepresentation NearCubicWires.SupplierPipeline NearCubicWires.SupplierEstimator
open NearCubicWires.SupplierPrime NearCubicWires.SupplierWalkBridge NearCubicWires.SourceInterfaces
open NearCubicWires.RepairSource NearCubicWires.RepairSource.CloseoutFinal
open PCJ9eff70d512234a4c_Fixed PCJd4d1d9d7d1fa4313_Production
open NearCubicWires.PacketFamilyParent NearCubicWires.PacketsConstruction
open NearCubicWires.PacketsGlue.RequestMeta
noncomputable section

/-! ## The slot maps -/

/-- The vector's tapes `0..19` keep their indices; its private tapes move past the writer's five (`20..24`). -/
def fA (e : ℕ) (i : Fin (9 + 11 + e)) : Fin (16 + (e + 9)) :=
  ⟨if i.val < 20 then i.val else i.val + 5, by have := i.isLt; split_ifs <;> omega⟩

/-- The writer's slots: inputs `0..5 ↦ 16, 17, 12, 18, 19, 14`, output `10 ↦ 15`, private `6..9, 11 ↦ 20..24`. -/
def fWv (i : ℕ) : ℕ :=
  if i = 0 then 16 else if i = 1 then 17 else if i = 2 then 12 else if i = 3 then 18 else if i = 4 then 19
  else if i = 5 then 14 else if i = 10 then 15 else if i = 11 then 24 else i + 14

theorem fWv_lt : ∀ i : Fin 12, fWv i.val < 25 := by decide

theorem fWv_inj : ∀ x y : Fin 12, fWv x.val = fWv y.val → x = y := by decide

def fW (e : ℕ) (i : Fin 12) : Fin (16 + (e + 9)) := ⟨fWv i.val, by have := fWv_lt i; omega⟩

theorem fA_val (e : ℕ) (i : Fin (9 + 11 + e)) : (fA e i).val = if i.val < 20 then i.val else i.val + 5 := rfl

theorem fA_inj (e : ℕ) : Function.Injective (fA e) := by
  intro x y h
  have hv := congrArg Fin.val h
  rw [fA_val, fA_val] at hv
  apply Fin.ext
  split_ifs at hv <;> omega

theorem fW_inj (e : ℕ) : Function.Injective (fW e) := by
  intro x y h
  exact fWv_inj x y (congrArg Fin.val h)

variable {a : DecompositionAlgorithm}

/-- **`ThrMeta` from eleven THR words and the table writer.** -/
def ThrMeta.ofVec {K : KitShape a} {outs : ℕ → TVal a} (V : ThrVec a 11 outs)
    (hout : ∀ (r : TReq) (four : r.circuits.length ≤ 4) (L target : ℕ) (k : RCFive.RowKeys.ThrKey a r L target),
      k ∈ RCFive.RowKeys.thrKeys a r L target →
      outs 0 r four L target k = UnaryTemplate.tape (K.C (.thr r four L target)) ∧
      outs 1 r four L target k = UnaryTemplate.tape (K.C (.thr r four L target)) ∧
      outs 2 r four L target k = UnaryTemplate.tape (K.w (.thr r four L target)) ∧
      outs 3 r four L target k = UnaryTemplate.tape (thrD k * ((thresholdFourfoldOccurrences r).length + 1)) ∧
      outs 4 r four L target k = UnaryTemplate.tape (thrD k * ((thresholdFourfoldOccurrences r).length + 1)) ∧
      outs 5 r four L target k = UnaryTemplate.tape (((thresholdFourfoldOccurrences r).length + 1) ^ thrD k) ∧
      outs 6 r four L target k = [] ∧
      outs 7 r four L target k = UnaryTemplate.tape (thresholdFourfoldOccurrences r).length ∧
      outs 8 r four L target k = UnaryTemplate.tape (thrD k) ∧
      outs 9 r four L target k = UnaryTemplate.tape k.prime.val ∧
      outs 10 r four L target k = UnaryTemplate.tape k.residue.val)
    (wB : Request → ℕ)
    (hwB : ∀ (r : TReq) (four : r.circuits.length ≤ 4) (L target : ℕ) (k : RCFive.RowKeys.ThrKey a r L target),
      k ∈ RCFive.RowKeys.thrKeys a r L target →
      Tab.writerCost (thresholdFourfoldOccurrences r).length (thrD k) k.prime.val k.residue.val
        (((thresholdFourfoldOccurrences r).length + 1) ^ thrD k) ≤ wB (.thr r four L target))
    (cw dw : ℕ) (hcw : ∀ R, wB R ≤ cw * (R.smallSize a) ^ dw) : ThrMeta a K where
  extra := V.extra + 9
  states := _
  machine := Composition.machine (RecoveryFocus.machine (fA V.extra) V.machine)
    (RecoveryFocus.machine (fW V.extra) Tab.writerM)
  cost := fun R => V.cost R + 1 + wB R
  coefficient := V.costC + 1 + cw
  degree := V.costD + dw
  cost_le := fun R => sum_le _ _ _ _ _ _ _ (one_le_small a R) (V.cost_le R) (hcw R)
  run := by
    intro r four L target k hk
    obtain ⟨H1, A1, st1, keep1, out1⟩ := V.run r four L target k hk
    obtain ⟨H2, A2, st2, hs2, ho2⟩ := Dock.lift st1 (fA V.extra) (fA_inj _) (fun _ => 0) (fun _ => 0)
      (metaEntry a (.thr r four L target) (some k) (16 + (V.extra + 9))) (by
        intro j
        refine ⟨rfl, ?_⟩
        rw [ZeroPadding.pad_zero]
        apply metaEntry_match
        rw [fA_val]
        split_ifs <;> omega)
    have lo : ∀ t (ht : t < 20),
        A2 ⟨t, by omega⟩ = A1 ⟨t, by omega⟩ ∧ H2 ⟨t, by omega⟩ = H1 ⟨t, by omega⟩ := by
      intro t ht
      have e : (⟨t, by omega⟩ : Fin (16 + (V.extra + 9))) = fA V.extra ⟨t, by omega⟩ :=
        Fin.ext (by rw [fA_val]; simp only; split_ifs <;> omega)
      rw [e]
      exact ⟨(hs2 _).2.trans (ZeroPadding.pad_zero _), (hs2 _).1⟩
    have hi : ∀ t (ht1 : 20 ≤ t) (ht3 : t < 25) (ht2 : t < 16 + (V.extra + 9)),
        A2 ⟨t, ht2⟩ = [] ∧ H2 ⟨t, ht2⟩ = 0 := by
      intro t ht1 ht3 ht2
      have hn : ∀ j, fA V.extra j ≠ ⟨t, ht2⟩ := by
        intro j hj
        have hv := congrArg Fin.val hj
        rw [fA_val] at hv
        simp only at hv
        split_ifs at hv <;> omega
      exact ⟨(ho2 _ hn).2.trans (metaEntry_high _ _ _ _ (by simp only; omega)), (ho2 _ hn).1⟩
    have tw : ∀ j (hj : j < 11), A2 ⟨9 + j, by omega⟩ = outs j r four L target k ∧ H2 ⟨9 + j, by omega⟩ = 0 := by
      intro j hj
      obtain ⟨l1, l2⟩ := lo (9 + j) (by omega)
      obtain ⟨o1, o2⟩ := out1 j hj
      exact ⟨l1.trans o1, l2.trans o2⟩
    obtain ⟨e0, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10⟩ := hout r four L target k hk
    obtain ⟨H3, A3, st3, hin3, hout3, hhead3⟩ := writer_thr r L target k
      (UnaryTemplate.tape (thresholdFourfoldOccurrences r).length) (UnaryTemplate.tape (thrD k))
      (UnaryTemplate.tape (thrD k * ((thresholdFourfoldOccurrences r).length + 1)))
      (UnaryTemplate.tape k.prime.val) (UnaryTemplate.tape k.residue.val)
      (UnaryTemplate.tape (((thresholdFourfoldOccurrences r).length + 1) ^ thrD k))
      (Tab.readsWord_template _) (Tab.readsWord_template _) (Tab.readsWord_template _)
      (Tab.readsWord_template _) (Tab.readsWord_template _) (Tab.readsWord_template _)
    obtain ⟨H4, A4, st4, hs4, ho4⟩ := Dock.lift st3 (fW V.extra) (fW_inj _) (fun _ => 0) H2 A2 (by
      intro j
      rw [ZeroPadding.pad_zero]
      fin_cases j
      · have e : fW V.extra ⟨0, by omega⟩ = ⟨9 + 7, by omega⟩ := Fin.ext rfl
        rw [e, (tw 7 (by omega)).1, (tw 7 (by omega)).2, e7]
        exact ⟨rfl, rfl⟩
      · have e : fW V.extra ⟨1, by omega⟩ = ⟨9 + 8, by omega⟩ := Fin.ext rfl
        rw [e, (tw 8 (by omega)).1, (tw 8 (by omega)).2, e8]
        exact ⟨rfl, rfl⟩
      · have e : fW V.extra ⟨2, by omega⟩ = ⟨9 + 3, by omega⟩ := Fin.ext rfl
        rw [e, (tw 3 (by omega)).1, (tw 3 (by omega)).2, e3]
        exact ⟨rfl, rfl⟩
      · have e : fW V.extra ⟨3, by omega⟩ = ⟨9 + 9, by omega⟩ := Fin.ext rfl
        rw [e, (tw 9 (by omega)).1, (tw 9 (by omega)).2, e9]
        exact ⟨rfl, rfl⟩
      · have e : fW V.extra ⟨4, by omega⟩ = ⟨9 + 10, by omega⟩ := Fin.ext rfl
        rw [e, (tw 10 (by omega)).1, (tw 10 (by omega)).2, e10]
        exact ⟨rfl, rfl⟩
      · have e : fW V.extra ⟨5, by omega⟩ = ⟨9 + 5, by omega⟩ := Fin.ext rfl
        rw [e, (tw 5 (by omega)).1, (tw 5 (by omega)).2, e5]
        exact ⟨rfl, rfl⟩
      · have e : fW V.extra ⟨6, by omega⟩ = ⟨20, by omega⟩ := Fin.ext rfl
        rw [e, (hi 20 (by omega) (by omega) (by omega)).1, (hi 20 (by omega) (by omega) (by omega)).2]
        exact ⟨rfl, rfl⟩
      · have e : fW V.extra ⟨7, by omega⟩ = ⟨21, by omega⟩ := Fin.ext rfl
        rw [e, (hi 21 (by omega) (by omega) (by omega)).1, (hi 21 (by omega) (by omega) (by omega)).2]
        exact ⟨rfl, rfl⟩
      · have e : fW V.extra ⟨8, by omega⟩ = ⟨22, by omega⟩ := Fin.ext rfl
        rw [e, (hi 22 (by omega) (by omega) (by omega)).1, (hi 22 (by omega) (by omega) (by omega)).2]
        exact ⟨rfl, rfl⟩
      · have e : fW V.extra ⟨9, by omega⟩ = ⟨23, by omega⟩ := Fin.ext rfl
        rw [e, (hi 23 (by omega) (by omega) (by omega)).1, (hi 23 (by omega) (by omega) (by omega)).2]
        exact ⟨rfl, rfl⟩
      · have e : fW V.extra ⟨10, by omega⟩ = ⟨9 + 6, by omega⟩ := Fin.ext rfl
        rw [e, (tw 6 (by omega)).1, (tw 6 (by omega)).2, e6]
        exact ⟨rfl, rfl⟩
      · have e : fW V.extra ⟨11, by omega⟩ = ⟨24, by omega⟩ := Fin.ext rfl
        rw [e, (hi 24 (by omega) (by omega) (by omega)).1, (hi 24 (by omega) (by omega) (by omega)).2]
        exact ⟨rfl, rfl⟩)
    have nw : ∀ t (ht : t < 16 + (V.extra + 9)), t ≠ 12 → t ≠ 14 → t ≠ 15 → t < 16 →
        A4 ⟨t, ht⟩ = A2 ⟨t, ht⟩ ∧ H4 ⟨t, ht⟩ = H2 ⟨t, ht⟩ := by
      intro t ht h12 h14 h15 h16
      have hn : ∀ j, fW V.extra j ≠ ⟨t, ht⟩ := by
        intro j hj
        have hv : fWv j.val = t := congrArg Fin.val hj
        have hj12 := j.isLt
        unfold fWv at hv
        split_ifs at hv <;> omega
      exact ⟨(ho4 _ hn).2, (ho4 _ hn).1⟩
    have kw : ∀ (i : Fin 12) (t : ℕ) (ht : t < 16 + (V.extra + 9)), fW V.extra i = ⟨t, ht⟩ →
        A4 ⟨t, ht⟩ = A3 i ∧ H4 ⟨t, ht⟩ = H3 i := by
      intro i t ht he
      rw [← he]
      exact ⟨(hs4 i).2.trans (ZeroPadding.pad_zero _), (hs4 i).1⟩
    have hcost := hwB r four L target k hk
    refine ⟨H4, A4, (st2.seq st4).enlarge (by omega), ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro i hi8
      obtain ⟨n1, n2⟩ := nw i.val i.isLt (by omega) (by omega) (by omega) (by omega)
      obtain ⟨l1, l2⟩ := lo i.val (by omega)
      obtain ⟨k1, k2⟩ := keep1 ⟨i.val, by omega⟩ (by simp only; omega)
      refine ⟨n1.trans (l1.trans (k1.trans (metaEntry_val _ _ _ _ _ rfl))), n2.trans (l2.trans k2)⟩
    · exact (nw 9 (by omega) (by omega) (by omega) (by omega) (by omega)).1.trans ((tw 0 (by omega)).1.trans e0)
    · exact (nw 9 (by omega) (by omega) (by omega) (by omega) (by omega)).2.trans (tw 0 (by omega)).2
    · exact (nw 10 (by omega) (by omega) (by omega) (by omega) (by omega)).1.trans ((tw 1 (by omega)).1.trans e1)
    · exact (nw 10 (by omega) (by omega) (by omega) (by omega) (by omega)).2.trans (tw 1 (by omega)).2
    · exact (nw 11 (by omega) (by omega) (by omega) (by omega) (by omega)).1.trans ((tw 2 (by omega)).1.trans e2)
    · exact (nw 11 (by omega) (by omega) (by omega) (by omega) (by omega)).2.trans (tw 2 (by omega)).2
    · exact (kw 2 12 (by omega) (Fin.ext rfl)).1.trans (hin3 2 (by decide)).1
    · exact (kw 2 12 (by omega) (Fin.ext rfl)).2.trans (hin3 2 (by decide)).2
    · exact (nw 13 (by omega) (by omega) (by omega) (by omega) (by omega)).1.trans ((tw 4 (by omega)).1.trans e4)
    · exact (nw 13 (by omega) (by omega) (by omega) (by omega) (by omega)).2.trans (tw 4 (by omega)).2
    · exact (kw 5 14 (by omega) (Fin.ext rfl)).1.trans (hin3 5 (by decide)).1
    · exact (kw 5 14 (by omega) (Fin.ext rfl)).2.trans (hin3 5 (by decide)).2
    · exact (kw 10 15 (by omega) (Fin.ext rfl)).1.trans hout3
    · exact (kw 10 15 (by omega) (Fin.ext rfl)).2.trans hhead3

end
end NearCubicWires.PacketsCombine.Asm


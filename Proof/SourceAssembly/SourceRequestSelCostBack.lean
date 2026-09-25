import Proof.SourceAssembly.SourceRequestSelCostCoef

set_option autoImplicit false
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unusedVariables false

namespace NearCubicWires.SourceRequest.SelLocal
open NearCubicWires LocalBitMultitape ExtDecompositionBatch RepairOrdinary
noncomputable section

/-! ## Powers of `W` up to 24 -/

theorem pw_le (W a b : Nat) (hW : 1 ≤ W) (h : a ≤ b) : W ^ a ≤ W ^ b := Nat.pow_le_pow_right hW h

theorem succ_pow_le (n W k : Nat) (h : n + 1 ≤ W) : (n + 1) ^ k ≤ W ^ k := Nat.pow_le_pow_left h k

/-! ## The term reader -/

theorem segA_le (n W : Nat) (h : n + 1 ≤ W) : SourceRequest.TermSeg.cost n ≤ 2200000 * W ^ 3 := by
  unfold SourceRequest.TermSeg.cost
  have h3 := succ_pow_le n W 3 h
  have h2 := succ_pow_le n W 2 h
  have hW : 1 ≤ W := by omega
  have q1 : W ^ 1 ≤ W ^ 3 := pw_le W 1 3 hW (by decide)
  have q2 : W ^ 2 ≤ W ^ 3 := pw_le W 2 3 hW (by decide)
  have e1 : W = W ^ 1 := (pow_one W).symm
  omega

theorem segB_le (n W : Nat) (h : n + 1 ≤ W) : SourceRequest.TermSegB.cost n ≤ 2200000 * W ^ 3 := by
  unfold SourceRequest.TermSegB.cost
  have h3 := succ_pow_le n W 3 h
  have h2 := succ_pow_le n W 2 h
  have hW : 1 ≤ W := by omega
  have q1 : W ^ 1 ≤ W ^ 3 := pw_le W 1 3 hW (by decide)
  have q2 : W ^ 2 ≤ W ^ 3 := pw_le W 2 3 hW (by decide)
  have e1 : W = W ^ 1 := (pow_one W).symm
  omega

theorem seek_le (w j b W : Nat) (hw : w ≤ W) (hj : j ≤ W) (hb : b ≤ W) :
    SourceRequest.TermSeg.seekCost w j b ≤ 8 * (W * W) + 20 := by
  unfold SourceRequest.TermSeg.seekCost CloseoutRowsTouching.FrameSeek.budget
  have h1 : j * (2 * w + 4) ≤ W * (2 * W + 4) := Nat.mul_le_mul hj (by omega)
  have e : W * (2 * W + 4) = 2 * (W * W) + 4 * W := by ring
  have hWW : W ≤ W * W ∨ W = 0 := by
    rcases Nat.eq_zero_or_pos W with h0 | h0
    · right; exact h0
    · left; exact Nat.le_mul_of_pos_left W h0
  omega

theorem cWord_len (bits : List Bool) (j : Nat) : (SourceRequest.TermCompose.cWord bits j).length = bits.length := by
  unfold SourceRequest.TermCompose.cWord; rw [SignedSortKey.binary_length]

theorem tWord_len (bits : List Bool) (j i : Nat) :
    (SourceRequest.TermCompose.tWord bits j i).length = bits.length := by
  unfold SourceRequest.TermCompose.tWord; rw [SignedSortKey.binary_length, cWord_len]

theorem termCoef_le (a : List Bool) (cw W : Nat) (ha : a.length + 1 ≤ W) (hcw : cw ≤ W) :
    SourceRequest.TermCoef.cost a cw ≤ 36000000000000100000 * W ^ 24 := by
  unfold SourceRequest.TermCoef.cost CloseoutWitness.PairHeader.budget CloseoutRowsIntegerFields.budget
    CloseoutWitness.NatCold.budget CloseoutWitness.CoefficientRecord.budget
  have l0 : (SourceRequest.TermCoef.intW a).length = a.length := CloseoutWitness.RationalCold.code_length a 0
  have l1 : (SourceRequest.TermCoef.natW a).length = a.length := CloseoutWitness.RationalCold.code_length a 1
  have l2 : (SourceRequest.TermCoef.nb a cw).length = cw := by
    unfold SourceRequest.TermCoef.nb; rw [ClockNormalize.resize_length]
  have l3 : (SourceRequest.TermCoef.db a cw).length = cw := by
    unfold SourceRequest.TermCoef.db; rw [ClockNormalize.resize_length]
  rw [l0, l1, l2, l3]
  have hW : 1 ≤ W := by omega
  have p24 := succ_pow_le a.length W 24 ha
  have p2 := succ_pow_le a.length W 2 ha
  have q2 : W ^ 2 ≤ W ^ 24 := pw_le W 2 24 hW (by decide)
  have q1 : W ^ 1 ≤ W ^ 24 := pw_le W 1 24 hW (by decide)
  have e1 : W = W ^ 1 := (pow_one W).symm
  omega

theorem readerCost_le (bits : List Bool) (j i cwid cw W : Nat) (hbj : bits.length + j + 2 ≤ W) (hi : i + 1 ≤ W)
    (hcwid : cwid ≤ W) (hcw : cw ≤ W) :
    SourceRequest.TermCompose.readerCost bits j i cwid cw ≤ 50000000000000000000 * W ^ 24 := by
  unfold SourceRequest.TermCompose.readerCost SourceRequest.TermSeg.costA SourceRequest.TermSegB.costB
    SourceRequest.TermSegC.cost
  rw [cWord_len, tWord_len]
  have hW : 1 ≤ W := by omega
  have a1 := segA_le bits.length W (by omega)
  have a2 := seek_le bits.length j bits.length W (by omega) (by omega) (by omega)
  have b1 := segB_le bits.length W (by omega)
  have b2 := seek_le bits.length i bits.length W (by omega) (by omega) (by omega)
  have c1 := termCoef_le (CloseoutWitness.PairHeader.codeWord (SourceRequest.TermCompose.tWord bits j i) 0) cw W
    (by rw [CloseoutWitness.RationalCold.code_length, tWord_len]; omega) hcw
  have c2 := succ_pow_le bits.length W 2 (by omega)
  have e2 : W * W = W ^ 2 := (sq W).symm
  have q2 : W ^ 2 ≤ W ^ 24 := pw_le W 2 24 hW (by decide)
  have q3 : W ^ 3 ≤ W ^ 24 := pw_le W 3 24 hW (by decide)
  have q1 : W ^ 1 ≤ W ^ 24 := pw_le W 1 24 hW (by decide)
  have e1 : W = W ^ 1 := (pow_one W).symm
  omega

/-- **One slot pipeline's cost** (THR and SYM share `Slot.slotCost`). -/
theorem slotCost_le (bits : List Bool) (jj idx cwid cw D W : Nat) (hbj : bits.length + jj + 2 ≤ W) (hi : idx + 1 ≤ W)
    (hcwid : cwid ≤ W) (hcw : cw ≤ W) (hD : D ≤ W) :
    SourceFactorSel.Slot.slotCost bits jj idx cwid cw D ≤ 60000000000000000000 * W ^ 24 := by
  have r := readerCost_le bits jj idx cwid cw W hbj hi hcwid hcw
  unfold SourceFactorSel.Slot.slotCost
  simp only [SourceFactorSel.DescF.costF, SourceFactorSel.DescF.origCostF, SourceFactorSel.Desc.sysCost]
  have hW : 1 ≤ W := by omega
  have q1 : W ^ 1 ≤ W ^ 24 := pw_le W 1 24 hW (by decide)
  have e1 : W = W ^ 1 := (pow_one W).symm
  omega

/-! ## The header block -/

theorem natWord_le (n : Nat) : (RepairRepresentation.natWord n).length ≤ 2 * n + 3 := by
  rw [DecompositionSource.natWord_length]
  have := bitlen_le n
  omega

theorem sum_map_len (l : List (List Bool)) :
    (l.map (fun x => 4 * x.length + 4)).sum = 4 * l.flatten.length + 4 * l.length := by
  induction l with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.map_cons, List.sum_cons, List.flatten_cons, List.length_append, List.length_cons, ih]
    ring

theorem header_len (mode : Bool) (q L target k W : Nat) (hq : q ≤ W) (hL : L ≤ W) (ht : target ≤ W) (hk : k ≤ W) :
    (SourceRequest.header mode q L target k).length ≤ 10 * W + 20 := by
  unfold SourceRequest.header
  simp only [List.length_append]
  have h0 := natWord_le (if mode then 0 else 1)
  have h00 : (if mode then 0 else 1) ≤ 1 := by split <;> omega
  have h1 := natWord_le q
  have h2 := natWord_le L
  have h3 := natWord_le target
  have h4 := natWord_le k
  omega

/-- **The header block's cost.** -/
theorem hdrCost_le (mode : Bool) (q L target k D W : Nat) (hq : q ≤ W) (hL : L ≤ W) (ht : target ≤ W) (hk : k ≤ W)
    (hD : D ≤ W) : SourceFactorSel.HdrBlock.hdrCost mode q L target k D ≤ 4000 * (W + 1) ^ 2 := by
  unfold SourceFactorSel.HdrBlock.hdrCost SourceFactorSel.Nat.natCost CloseoutRowsEstimatorParity.Natural.budget
    EquationHeaderAppend.budget SourceRequest.FieldPass.cost SourceRequest.FieldPass.chainCost
  have hlen : (List.ofFn (SourceFactorSel.Header.fields mode q L target k)).length = 5 := List.length_ofFn
  rw [List.take_of_length_le (by rw [hlen]), sum_map_len, hlen,
    SourceFactorSel.Header.fields_flatten]
  have hh := header_len mode q L target k W hq hL ht hk
  have hb := bitlen_le k
  have hn := natWord_le k
  have hk2 : k ^ 2 ≤ (W + 1) ^ 2 := Nat.pow_le_pow_left (by omega) 2
  have hW : W + 1 ≤ (W + 1) ^ 2 := by
    calc W + 1 = (W + 1) ^ 1 := (pow_one _).symm
      _ ≤ (W + 1) ^ 2 := Nat.pow_le_pow_right (by omega) (by decide)
  omega

end
end NearCubicWires.SourceRequest.SelLocal


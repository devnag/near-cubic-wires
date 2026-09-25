import Proof.Rows.RowsInitLive

set_option autoImplicit false
set_option maxRecDepth 120000
set_option warningAsError true

namespace RowsInit
open NearCubicWires NearCubicWires.LocalBitMultitape
open NearCubicWires.RepairRepresentation NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch
open NearCubicWires.RepairOrdinary.RecoveryRootRound NearCubicWires.RepairOrdinary.RecoveryExecution
open NearCubicWires.PacketsGlue.RequestMeta
open PCJ9eff70d512234a4c_Fixed PCJd4d1d9d7d1fa4313_Production NearCubicWires.P1Closure
noncomputable section

/-! ## 1. The chain's cost: a fixed polynomial of `smallSize` -/

theorem complCount_le_small (a : DecompositionAlgorithm) (r : Request) : complCount a r ≤ r.smallSize a := by
  have h1 : complCount a r ≤ r.q := by
    unfold complCount
    exact le_trans (Finset.card_le_univ _) (by rw [Fintype.card_fin])
  have key : ∀ q n x1 x2 x3 x4 x5 x6 : ℕ, q ≤ q + n + x1 + x2 + x3 + x4 + x5 + x6 + 1 := by
    intros; omega
  have h2 : r.q ≤ r.smallSize a := by
    unfold Request.smallSize
    exact key _ _ _ _ _ _ _ _
  omega

theorem liveCount_le_small (a : DecompositionAlgorithm) (r : Request) : liveCount a r ≤ r.smallSize a := by
  have h1 : liveCount a r < twoK a r := by
    unfold twoK
    exact Nat.lt_two_pow_self
  have h2 := twoK_le_small a r
  omega

theorem small_pos (a : DecompositionAlgorithm) (r : Request) : 1 ≤ r.smallSize a := by
  have key : ∀ q n x1 x2 x3 x4 x5 x6 : ℕ, 1 ≤ q + n + x1 + x2 + x3 + x4 + x5 + x6 + 1 := by
    intros; omega
  unfold Request.smallSize
  exact key _ _ _ _ _ _ _ _

/-- **The cost of `liveChain a`**: `c · smallSize^d` with `c`, `d` fixed by `a` (the three reused stages' own
coefficients and degrees), for every request. -/
theorem liveCost_le (a : DecompositionAlgorithm) :
    ∃ c d : Nat, ∀ r : Request, liveCost a r ≤ c * (r.smallSize a)^d := by
  refine ⟨2*(complStage a).coefficient + 2*(liveStage a).coefficient + 2*(twoKStage a).coefficient + 100,
    max (complStage a).degree (max (liveStage a).degree (max (twoKStage a).degree 1)), fun r => ?_⟩
  have hS := small_pos a r
  have p1 : (r.smallSize a)^(complStage a).degree ≤
      (r.smallSize a)^(max (complStage a).degree (max (liveStage a).degree (max (twoKStage a).degree 1))) :=
    Nat.pow_le_pow_right hS (by omega)
  have p2 : (r.smallSize a)^(liveStage a).degree ≤
      (r.smallSize a)^(max (complStage a).degree (max (liveStage a).degree (max (twoKStage a).degree 1))) :=
    Nat.pow_le_pow_right hS (by omega)
  have p3 : (r.smallSize a)^(twoKStage a).degree ≤
      (r.smallSize a)^(max (complStage a).degree (max (liveStage a).degree (max (twoKStage a).degree 1))) :=
    Nat.pow_le_pow_right hS (by omega)
  have pS : r.smallSize a ≤
      (r.smallSize a)^(max (complStage a).degree (max (liveStage a).degree (max (twoKStage a).degree 1))) := by
    calc r.smallSize a = (r.smallSize a)^1 := (pow_one _).symm
      _ ≤ _ := Nat.pow_le_pow_right hS (by omega)
  set X := (r.smallSize a)^(max (complStage a).degree (max (liveStage a).degree (max (twoKStage a).degree 1)))
    with hX
  have q1 := le_trans ((complStage a).cost_le r) (Nat.mul_le_mul_left (complStage a).coefficient p1)
  have q2 := le_trans ((liveStage a).cost_le r) (Nat.mul_le_mul_left (liveStage a).coefficient p2)
  have q3 := le_trans ((twoKStage a).cost_le r) (Nat.mul_le_mul_left (twoKStage a).coefficient p3)
  have hc := complCount_le_small a r
  have hl := liveCount_le_small a r
  have ht := twoK_le_small a r
  unfold liveCost
  simp only [RepairSource.ProjectionNormalization.Counter.budget]
  rw [Nat.add_mul, Nat.add_mul, Nat.add_mul, Nat.mul_assoc 2, Nat.mul_assoc 2, Nat.mul_assoc 2]
  omega

/-! ## 2. The `rowp 2` template -/

/-- The template length of `RowsBaseLayout.rowpWords n … 2` is `n+2`. -/
theorem tpl_arith (n : Nat) : 2*((n+1)/2)-(decide (n%2=1)).toNat+2 = n+2 := by
  rcases Nat.mod_two_eq_zero_or_one n with h | h
  · rw [show decide (n%2=1) = false by simp [h]]
    simp only [Bool.toNat_false]
    omega
  · rw [show decide (n%2=1) = true by simp [h]]
    simp only [Bool.toNat_true]
    omega

/-! ## 3. The three Header words -/

theorem common_live {q L : Nat} (a : DecompositionAlgorithm) (F : Packets.Family q L) (g : Packets.Geometry F)
    (layout : Packets.Layout a F g) :
    PCJ45bee56da9f34d5a_RowState.commonHeader a F g layout 3 =
      UnaryTemplate.tape ((Packets.residual F+1)/2+Packets.residual F/2) ∧
    PCJ45bee56da9f34d5a_RowState.commonHeader a F g layout 283 = UnaryTemplate.tape ((Packets.live F).card+1) ∧
    PCJ45bee56da9f34d5a_RowState.commonHeader a F g layout 277 =
      NearCubicWires.RepairSource.VerifierDecoding.CompareMachine.word (2^(Packets.live F).card) := by
  unfold PCJ45bee56da9f34d5a_RowState.commonHeader CompactNativeInitialize.input
  refine ⟨?_, ?_, ?_⟩
  · rw [show (3 : Fin 440) = CompactNativeInitialize.metadataSlots 1 from rfl,
      install_slot _ CompactNativeInitialize.meta_injective]
    rfl
  · rw [show (283 : Fin 440) = CompactNativeInitialize.metadataSlots 5 from rfl,
      install_slot _ CompactNativeInitialize.meta_injective]
    rfl
  · rw [install_other _ _ _ _ (fun j => by revert j; decide)]
    simp only [CompactNativeInitialize.base, if_neg (by decide : (277 : Fin 440) ≠ 180),
      if_neg (by decide : (277 : Fin 440) ≠ 262), ↓reduceIte]
    rw [NearCubicWires.RepairSource.CloseoutFinal.C10SupplierRowInput.liveList_length]

/-- **At the request's geometry**: Header 3 / 283 / 277 are exactly `live_chain`'s words at ports 62, 68, 71. -/
theorem common_live_req (a : DecompositionAlgorithm) (r : Request) (g : Packets.Geometry (r.family a))
    (layout : Packets.Layout a (r.family a) g) :
    PCJ45bee56da9f34d5a_RowState.commonHeader a (r.family a) g layout 3 = UnaryTemplate.tape (complCount a r) ∧
    PCJ45bee56da9f34d5a_RowState.commonHeader a (r.family a) g layout 283 =
      UnaryTemplate.tape (liveCount a r+1) ∧
    PCJ45bee56da9f34d5a_RowState.commonHeader a (r.family a) g layout 277 =
      NearCubicWires.RepairSource.VerifierDecoding.CompareMachine.word (twoK a r) := by
  obtain ⟨h3, h283, h277⟩ := common_live a (r.family a) g layout
  refine ⟨?_, h283, h277⟩
  rw [h3, g.arity]
  rfl

end
end RowsInit

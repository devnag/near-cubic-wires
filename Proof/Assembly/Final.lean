import Lean
import Proof.Assembly.CertificateConstructionStep4
import Proof.Assembly.CompilerLawsConstructionStep4
import Proof.Assembly.FreeHolesConstructionStep2
import Proof.Assembly.KHolesConstructionStep2
import Proof.Assembly.MaskConstructionStep4
import Proof.Assembly.RowConstructionStep2
import Proof.Assembly.SourceGenHoles3BConstructionStep2
import Proof.Assembly.TableCertificateConstructionStep4

set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unusedVariables false
set_option linter.defProp false


namespace AssembledProof
set_option maxHeartbeats 4000000 in
noncomputable def application

    : NearCubicWires.RepairSource.EightSources → NearCubicWires.RepairSource.OrdinaryHeadlineTheorem25 :=
  (
    let neutral : (
      PCJ1fef9807c6954e94_Native.Target
    ) := (
      (
        let selector : (
          PCJ9eff70d512234a4c_Fixed.CyclicChoice.Laws
        ) := (
          (
            (by
              classical
              unfold PCJ9eff70d512234a4c_Fixed.CyclicChoice.Laws
              intro q m K support hK
              rcases Nat.eq_zero_or_pos q with rfl | hq
              · have hzero : K = 0 := by omega
                subst K
                constructor
                · simp [PCJ9eff70d512234a4c_Fixed.CyclicChoice.selectedLive,
                    PCJ9eff70d512234a4c_Fixed.CyclicChoice.window]
                · simp
              · let dist (a x : Nat) : Nat := (x + q - a % q) % q
                have hd (a x : Nat) (hx : x < q) :
                    dist a x = if x < a % q then x + q - a % q else x - a % q := by
                  have ha := Nat.mod_lt a hq
                  dsimp [dist]
                  split_ifs with h
                  · exact Nat.mod_eq_of_lt (by omega)
                  · rw [show x + q - a % q = (x - a % q) + q by omega,
                      Nat.add_mod_right, Nat.mod_eq_of_lt (by omega : x - a % q < q)]
                have hinj (a x y : Nat) (hx : x < q) (hy : y < q)
                    (h : dist a x = dist a y) : x = y := by
                  rw [hd a x hx, hd a y hy] at h
                  have ha := Nat.mod_lt a hq
                  split_ifs at h <;> omega
                have hsurj (a d : Nat) (hdq : d < q) :
                    ∃ x, x < q ∧ dist a x = d := by
                  have ha := Nat.mod_lt a hq
                  refine ⟨(d + a % q) % q, Nat.mod_lt _ hq, ?_⟩
                  dsimp [dist]
                  by_cases h : d + a % q < q
                  · rw [Nat.mod_eq_of_lt h,
                      show d + a % q + q - a % q = d + q by omega,
                      Nat.add_mod_right, Nat.mod_eq_of_lt hdq]
                  · rw [Nat.mod_eq_sub_mod (by omega : q ≤ d + a % q),
                      Nat.mod_eq_of_lt (by omega : d + a % q - q < q),
                      show d + a % q - q + q - a % q = d by omega,
                      Nat.mod_eq_of_lt hdq]
                have hmem (a : Nat) (x : Fin q) :
                    x ∈ PCJ9eff70d512234a4c_Fixed.CyclicChoice.window q K a ↔ dist a x.val < K := by
                  simp [PCJ9eff70d512234a4c_Fixed.CyclicChoice.window, dist]
                have hcard (a : Nat) :
                    (PCJ9eff70d512234a4c_Fixed.CyclicChoice.window q K a).card = K := by
                  apply Eq.trans ?_ (Finset.card_range K)
                  refine Finset.card_bij (fun x _ => dist a x.val) ?_ ?_ ?_
                  · intro x hx
                    exact Finset.mem_range.mpr ((hmem a x).mp hx)
                  · intro x hx y hy hxy
                    exact Fin.ext (hinj a x.val y.val x.isLt y.isLt hxy)
                  · intro d hdK
                    obtain ⟨x, hx, hxd⟩ := hsurj a d
                      (lt_of_lt_of_le (Finset.mem_range.mp hdK) hK)
                    exact ⟨⟨x, hx⟩, (hmem a ⟨x, hx⟩).mpr
                      (by rw [hxd]; exact Finset.mem_range.mp hdK), hxd⟩
                have hdinj (x : Fin q) (a b : Nat) (ha : a < q) (hb : b < q)
                    (h : dist a x.val = dist b x.val) : a = b := by
                  simp only [hd a x.val x.isLt, hd b x.val x.isLt,
                    Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb] at h
                  split_ifs at h <;> omega
                have hdsurj (x : Fin q) (d : Nat) (hdq : d < q) :
                    ∃ a, a < q ∧ dist a x.val = d := by
                  refine ⟨(x.val + q - d) % q, Nat.mod_lt _ hq, ?_⟩
                  have hx := x.isLt
                  dsimp [dist]
                  rw [Nat.mod_mod]
                  by_cases h : d ≤ x.val
                  · rw [show x.val + q - d = (x.val - d) + q by omega,
                      Nat.add_mod_right, Nat.mod_eq_of_lt (by omega : x.val - d < q),
                      show x.val + q - (x.val - d) = d + q by omega,
                      Nat.add_mod_right, Nat.mod_eq_of_lt hdq]
                  · rw [Nat.mod_eq_of_lt (by omega : x.val + q - d < q),
                      show x.val + q - (x.val + q - d) = d by omega,
                      Nat.mod_eq_of_lt hdq]
                have hdual (x : Fin q) :
                    ((Finset.range q).filter (fun a =>
                      x ∈ PCJ9eff70d512234a4c_Fixed.CyclicChoice.window q K a)).card = K := by
                  apply Eq.trans ?_ (Finset.card_range K)
                  refine Finset.card_bij (fun a _ => dist a x.val) ?_ ?_ ?_
                  · intro a ha
                    exact Finset.mem_range.mpr ((hmem a x).mp (Finset.mem_filter.mp ha).2)
                  · intro a ha b hb hab
                    exact hdinj x a b
                      (Finset.mem_range.mp (Finset.mem_filter.mp ha).1)
                      (Finset.mem_range.mp (Finset.mem_filter.mp hb).1) hab
                  · intro d hdK
                    obtain ⟨a, ha, had⟩ := hdsurj x d
                      (lt_of_lt_of_le (Finset.mem_range.mp hdK) hK)
                    exact ⟨a, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr ha,
                      (hmem a x).mpr (by rw [had]; exact Finset.mem_range.mp hdK)⟩, had⟩
                have hsum :
                    (Finset.sum (Finset.range q) (fun a =>
                      PCJ9eff70d512234a4c_Fixed.CyclicChoice.incidenceScore support K a)) =
                    K * NearCubicWires.SupplierTouching.supportIncidenceMass support := by
                  unfold PCJ9eff70d512234a4c_Fixed.CyclicChoice.incidenceScore
                    NearCubicWires.SupplierTouching.supportIncidenceMass
                  rw [Finset.sum_comm, Finset.mul_sum]
                  refine Finset.sum_congr rfl (fun i _ => ?_)
                  rw [Finset.sum_comm]
                  have hi : ∀ x ∈ support i,
                      (Finset.sum (Finset.range q) (fun a => if
                        x ∈ PCJ9eff70d512234a4c_Fixed.CyclicChoice.window q K a then 1 else 0)) = K := by
                    intro x _
                    rw [Finset.sum_boole]
                    exact hdual x
                  rw [Finset.sum_congr rfl hi, Finset.sum_const, smul_eq_mul, Nat.mul_comm]
                let score : Nat → Nat :=
                  PCJ9eff70d512234a4c_Fixed.CyclicChoice.incidenceScore support K
                let step (best : Nat × Nat) (a : Nat) : Nat × Nat :=
                  if score a < best.2 then (a, score a) else best
                have hfold : ∀ (xs : List Nat) (best : Nat × Nat),
                    best.2 = score best.1 →
                    (xs.foldl step best).2 = score (xs.foldl step best).1 ∧
                    (xs.foldl step best).2 ≤ best.2 ∧
                    ∀ a ∈ xs, (xs.foldl step best).2 ≤ score a := by
                  intro xs
                  induction xs with
                  | nil =>
                    intro best hb
                    exact ⟨hb, le_rfl, by simp⟩
                  | cons a xs ih =>
                    intro best hb
                    by_cases h : score a < best.2
                    · have hs : step best a = (a, score a) := by simp [step, h]
                      simp only [List.foldl_cons, hs]
                      obtain ⟨he, hl, hall⟩ := ih (a, score a) rfl
                      refine ⟨he, hl.trans h.le, ?_⟩
                      intro b hbx
                      rcases List.mem_cons.mp hbx with rfl | hbx
                      · exact hl
                      · exact hall b hbx
                    · have hs : step best a = best := by simp [step, h]
                      simp only [List.foldl_cons, hs]
                      obtain ⟨he, hl, hall⟩ := ih best hb
                      refine ⟨he, hl, ?_⟩
                      intro b hbx
                      rcases List.mem_cons.mp hbx with rfl | hbx
                      · exact hl.trans (Nat.le_of_not_lt h)
                      · exact hall b hbx
                have hmin (a : Nat) (ha : a < q) :
                    score (PCJ9eff70d512234a4c_Fixed.CyclicChoice.firstMinimumStart support K) ≤ score a := by
                  have h := hfold (List.range q) (0, score 0) rfl
                  change score ((List.range q).foldl step (0, score 0)).1 ≤ score a
                  rw [← h.1]
                  exact h.2.2 a (List.mem_range.mpr ha)
                refine ⟨hcard _, ?_⟩
                have htouch : NearCubicWires.SupplierTouching.touchingCost support
                    (PCJ9eff70d512234a4c_Fixed.CyclicChoice.selectedLive support K) ≤
                    score (PCJ9eff70d512234a4c_Fixed.CyclicChoice.firstMinimumStart support K) := by
                  unfold NearCubicWires.SupplierTouching.touchingCost
                    PCJ9eff70d512234a4c_Fixed.CyclicChoice.selectedLive
                  dsimp [score, PCJ9eff70d512234a4c_Fixed.CyclicChoice.incidenceScore]
                  exact Finset.sum_le_sum (fun i _ =>
                    NearCubicWires.SupplierTouching.touchIndicator_le_membershipSum _ _)
                calc
                  q * NearCubicWires.SupplierTouching.touchingCost support
                      (PCJ9eff70d512234a4c_Fixed.CyclicChoice.selectedLive support K)
                      ≤ q * score (PCJ9eff70d512234a4c_Fixed.CyclicChoice.firstMinimumStart support K) :=
                        Nat.mul_le_mul_left _ htouch
                  _ = Finset.sum (Finset.range q) (fun _a =>
                      score (PCJ9eff70d512234a4c_Fixed.CyclicChoice.firstMinimumStart support K)) := by
                        rw [Finset.sum_const, Finset.card_range, smul_eq_mul]
                  _ ≤ Finset.sum (Finset.range q) score :=
                        Finset.sum_le_sum (fun a ha => hmin a (Finset.mem_range.mp ha))
                  _ = K * NearCubicWires.SupplierTouching.supportIncidenceMass support := hsum
            )
          )
        );
        let compiler : (
          PCJ9eff70d512234a4c_Fixed.Packets.CompilerLaws
        ) := (
          (
            (@PCConstruction_d8d2a55d97139784d1c6190b.parent selector)
          )
        );
        let tables : (
          PCJ9eff70d512234a4c_Fixed.TableCertificate
        ) := (
          (
            (@PCConstruction_ff130191b384529c8fa196be.parent selector compiler)
          )
        );
        let semantics : (
          PCJ9eff70d512234a4c_Fixed.Certificate
        ) := (
          (
            (@PCConstruction_d1e68290e6c53d4f6be92ee1.parent selector compiler tables)
          )
        );
        let physical : (
          PCJ9eff70d512234a4c_Fixed.PreparedRecipe selector compiler tables semantics
        ) := (
          (
            let physical : (
              PCJ38fbfed565f64139_Physical.CachedRecipe selector compiler tables semantics
            ) := (
              (
                let packetConstruction : (
                  PCJd4d1d9d7d1fa4313_Production.PacketConstruction selector
                ) := (
                  (
                    let kHoles : (
                      ∀ a : NearCubicWires.RepairRepresentation.DecompositionAlgorithm, NearCubicWires.PacketsConstruction.Residual.KHoles a
                    ) := (
                      (
                        (@PCConstruction_d34d28037761decdb48e39b7.parent selector compiler tables semantics)
                      )
                    );
                    let freeHoles : (
                      ∀ a : NearCubicWires.RepairRepresentation.DecompositionAlgorithm, NearCubicWires.PacketsConstruction.Residual.FreeHoles a
                    ) := (
                      (
                        (@PCConstruction_891f967648e650b00f998ee1.parent selector compiler tables semantics kHoles)
                      )
                    );
                    (@PCConstruction_0e3a87699efe11080573df09.parent selector compiler tables semantics kHoles freeHoles)
                  )
                );
                let rowConstruction : (
                  PCJd4d1d9d7d1fa4313_Production.RowConstruction selector
                ) := (
                  (
                    (@PCConstruction_9c86553efa4f63ee0095bde1.parent selector compiler tables semantics packetConstruction)
                  )
                );
                let sourceAssembly : (
                  PCJd4d1d9d7d1fa4313_Production.SourceAssembly selector compiler tables semantics
                ) := (
                  (
                    let maskConstruction : (
                      PCJc4297ab269d8423a_Source.MaskConstruction
                    ) := (
                      (
                        (@PCConstruction_53152a91473677c597d4c75d.parent selector compiler tables semantics packetConstruction rowConstruction)
                      )
                    );
                    let remainingSource : (
                      PCJc4297ab269d8423a_Source.RemainingSource selector compiler tables semantics
                    ) := (
                      (
                        let genHoles3 : (
                          NearCubicWires.SourceSkeleton.SourceGenHoles3 selector compiler
                        ) := (
                          (
                            let genHoles3A : (
                              NearCubicWires.SourceSkeleton.SourceGenHoles3A selector compiler
                            ) := (
                              (
                                let genHoles3B : (
                                  NearCubicWires.SourceSkeleton.SourceGenHoles3B selector compiler
                                ) := (
                                  (
                                    (@PCConstruction_9553faaff0cfb7d00b45cfe8.parent selector compiler tables semantics packetConstruction rowConstruction maskConstruction)
                                  )
                                );
                                (@PCConstruction_2878f47681d7aa799ed6167e.parent selector compiler tables semantics packetConstruction rowConstruction maskConstruction genHoles3B)
                              )
                            );
                            (@PCConstruction_0c81e141587f19110d0d1c5d.parent selector compiler tables semantics packetConstruction rowConstruction maskConstruction genHoles3A)
                          )
                        );
                        (@PCConstruction_70e90472006370cbbf699f7d.parent selector compiler tables semantics packetConstruction rowConstruction maskConstruction genHoles3)
                      )
                    );
                    (@PCConstruction_97da1ff461e62949f624f846.parent selector compiler tables semantics packetConstruction rowConstruction maskConstruction remainingSource)
                  )
                );
                (@PCConstruction_dae1fd3c2242dc62707902d8.parent selector compiler tables semantics packetConstruction rowConstruction sourceAssembly)
              )
            );
            (@PCConstruction_0b1f3ca8719d5ef3064d6c5b.parent selector compiler tables semantics physical)
          )
        );
        (@PCConstruction_8c87b372610f47d82f1393a3.parent selector compiler tables semantics physical)
      )
    );
    (@PCConstruction_841fe97208b211aa2f652b37.parent neutral)
  )
end AssembledProof





/-! Theorem 2.5 from the closed proof: the proof term `AssembledProof.application` above, read through two
equivalences, yields the fully expanded paper Theorem 2.5 from exactly the ten source constituents. -/
namespace NearCubicWires.Paper
open NearCubicWires RepairSource RepairRepresentation SourceInterfaces
set_option autoImplicit false
set_option maxRecDepth 120000
set_option maxHeartbeats 250000

theorem theorem_2_5_iff : OrdinaryHeadlineTheorem25 ↔ theorem_2_5 := by
  simp only [OrdinaryHeadlineTheorem25, theorem_2_5, OrdinaryInENP, agreement,
    wireScale, logScale, SymmetricThresholdCircuit.wireCount,
    ThresholdThresholdCircuit.wireCount, Finset.sum_filter, ne_eq, ite_not]


end NearCubicWires.Paper


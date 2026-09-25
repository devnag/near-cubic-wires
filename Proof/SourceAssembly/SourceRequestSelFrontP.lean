import Proof.SourceAssembly.SourceRequestSelFrontA

set_option autoImplicit false
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace NearCubicWires.SourceRequest.SelFront
open NearCubicWires LocalBitMultitape ExtDecompositionBatch RepairOrdinary RepairRepresentation
open SourceInterfaces RecoveryRootRound RepairSource.VerifierDecoding
open NearCubicWires.RepairOrdinary.CloseoutRowsOriginalClause (index negative)
open NearCubicWires.SourceRequest.LitInfo
open PCJ6e421fabe2aa4155_SourceLiteralSupport (value)
open NearCubicWires.SourceRequest.CurComp (copyM copy_step)
open NearCubicWires.SourceFactorSel.Count (wordM word0_step)
noncomputable section

/-- **Front A at the site's clause cache**: `front_a` with the cache holding the queried pair `pw` on cache tape `15` (S: `natListWord [left, right]`,
`cdAt`). Front A never reads cache tape `15` (LitInfo's bank port `15` is the caller's scratch `115`), and `clauseData … pw j = clauseData … [] j` for
`j ≠ 15` (`LitInfo.clauseData_pair`). -/
theorem front_aP (a : PointwisePCPPAlgorithm) (r : PCPPRequest a.minimumArity)
    (ci : Fin (2 ^ (a.output r).clauseBits)) (Rc : Nat) (pw : List Bool) (E : Fin NF → List Bool)
    (hc : CloseoutRowsOriginalPair.budget (index ((a.output r).clauses ci).left)
      (index ((a.output r).clauses ci).right) (negative ((a.output r).clauses ci).left)
      (negative ((a.output r).clauses ci).right) + 1 ≤ PCPPQueryCachedBounds.capacity a (r.circuit.size + r.arity))
    (hwin : litCost a r ci (PCPPQueryCachedBounds.capacity a (r.circuit.size + r.arity)) + 1 ≤ Rc)
    (hQR : PCPPQueryCachedBounds.capacity a (r.circuit.size + r.arity) + 1 ≤ Rc)
    (hiL : index ((a.output r).clauses ci).left + 3 ≤ Rc) (hiR : index ((a.output r).clauses ci).right + 3 ≤ Rc)
    (hcache : ∀ j : Fin 19, E ⟨j.val, by unfold NF; omega⟩ = PCPPQueryIndexPadding.clauseData
      (pcppOutput r (a.output r)) r.arity ci.val (PCPPQueryCachedBounds.capacity a (r.circuit.size + r.arity)) pw j)
    (hblank : ∀ p : Fin NF, 37 ≤ p.val → E p = List.replicate Rc false) :
    ∃ A : Fin NF → List Bool, Step frontA (costA a r ci) (fun _ => 0) E (fun _ => 0) A ∧
      A 129 = ZeroPadding.pad Rc (List.replicate (index ((a.output r).clauses ci).left) true) ∧
      A 130 = ZeroPadding.pad Rc [negative ((a.output r).clauses ci).left] ∧
      A 141 = ZeroPadding.pad Rc (List.replicate (index ((a.output r).clauses ci).right) true) ∧
      A 142 = ZeroPadding.pad Rc [negative ((a.output r).clauses ci).right] ∧
      A 185 = ZeroPadding.pad Rc [decide ((a.output r).systematicBits ≤ index ((a.output r).clauses ci).left)] ∧
      A 189 = ZeroPadding.pad Rc [decide ((a.output r).systematicBits ≤ index ((a.output r).clauses ci).right)] ∧
      A 103 = ZeroPadding.pad Rc (value a r (index ((a.output r).clauses ci).left)) ∧
      A 104 = ZeroPadding.pad Rc (value a r (index ((a.output r).clauses ci).right)) ∧
      A 200 = ZeroPadding.pad Rc (CompareMachine.word (index ((a.output r).clauses ci).left)) ∧
      A 201 = ZeroPadding.pad Rc (CompareMachine.word (index ((a.output r).clauses ci).right)) ∧
      (∀ z : Fin NF, z.val < 100 ∨ 202 ≤ z.val → A z = E z) ∧
      (∀ z : Fin NF, 100 ≤ z.val → z.val < 202 → (A z).length ≤ Rc) := by
  set Q := PCPPQueryCachedBounds.capacity a (r.circuit.size + r.arity) with hQ
  set iL := index ((a.output r).clauses ci).left with hiLd
  set iR := index ((a.output r).clauses ci).right with hiRd
  -- the driver copy
  have e17 : E 17 = ZeroPadding.pad 0 (List.replicate Q true) := by
    rw [ZeroPadding.pad_zero]; exact (hcache 17).trans ((clauseData_pair _ _ _ _ _ 17 (by decide)).trans (cd17 _ _ _ _))
  set A1 := Function.update E 144 (ZeroPadding.pad Rc (List.replicate Q true)) with hA1
  have s1 := copy_step (17 : Fin NF) 144 37 (by decide) (by decide) (by decide) Q 0 Rc Rc (by omega)
    (fun _ => 0) E (fun _ _ => rfl) e17 (hblank 144 (by decide)) (hblank 37 (by decide))
  -- LitInfo
  have hA : ∀ b : Fin 91, A1 (litSl b) = ZeroPadding.pad (capOf Rc b) (PCJ6e421fabe2aa4155_SourceLiteralRefs.bank Q
      (PCPPQueryIndexPadding.clauseData (pcppOutput r (a.output r)) r.arity ci.val Q []) b) := by
    intro b
    by_cases hb : cacheSide b
    · have hcap : capOf Rc b = 0 := by simp [capOf, hb]
      have hb19 : b.val < 19 := hb.1
      have e : litSl b = ⟨b.val, by unfold NF; omega⟩ := by unfold litSl; rw [if_pos hb]
      rw [hcap, ZeroPadding.pad_zero, e, hA1, Function.update_of_ne (Fin.ne_of_val_ne (by show b.val ≠ 144; omega))]
      have hb' : b = (⟨b.val, hb19⟩ : Fin 19).castAdd 72 := Fin.ext rfl
      rw [hcache ⟨b.val, hb19⟩, clauseData_pair _ _ _ _ _ ⟨b.val, hb19⟩ (fun h => hb.2.2.2 (congrArg Fin.val h))]
      conv_rhs => rw [hb']
      rw [bank_cache]
    · have hcap : capOf Rc b = Rc := by simp [capOf, hb]
      have e : litSl b = ⟨100 + b.val, by unfold NF; omega⟩ := by unfold litSl; rw [if_neg hb]
      rw [hcap, e]
      by_cases h44 : b = 44
      · subst h44
        rw [bank_driver]
        exact Function.update_self _ _ _
      · rw [hA1, Function.update_of_ne (Fin.ne_of_val_ne (by
          show 100 + b.val ≠ 144
          intro h; apply h44; exact Fin.ext (by show b.val = 44; omega)))]
        obtain ⟨c3, c4, c15⟩ := cd_blank (pcppOutput r (a.output r)) r.arity ci.val Q
        rw [bank_blank Q Rc hQR _ c3 c4 c15 b hb h44]
        exact hblank _ (by simp; omega)
  obtain ⟨A2, s2, a3, a4, a29, a30, a41, a42, a85, a89, acache, aoff, alen⟩ :=
    lit_dock a r ci hc litSl litSl_inj Rc hwin hQR (fun _ => 0) A1 (fun _ => rfl) hA
  have off2 : ∀ z : Fin NF, (∀ b, litSl b ≠ z) → A2 z = A1 z := aoff
  have k2 : ∀ z : Fin NF, z.val < 100 ∨ 191 ≤ z.val → A2 z = A1 z := by
    intro z hz
    by_cases hp : ∃ b, litSl b = z
    · obtain ⟨b, rfl⟩ := hp
      have hr := litSl_range b
      have hcs : cacheSide b := by
        by_contra hn
        rw [litSl_val, if_neg hn] at hz hr
        omega
      exact acache b hcs
    · exact off2 z (fun b e => hp ⟨b, e⟩)
  have lit : ∀ b : Fin 91, ¬ cacheSide b → litSl b = ⟨100 + b.val, by unfold NF; omega⟩ := by
    intro b hb; unfold litSl; rw [if_neg hb]
  replace a29 : A2 129 = ZeroPadding.pad Rc (List.replicate iL true) := by
    rw [show (129 : Fin NF) = litSl 29 from (lit 29 (by unfold cacheSide; decide)).symm]; exact a29
  replace a30 : A2 130 = ZeroPadding.pad Rc [negative ((a.output r).clauses ci).left] := by
    rw [show (130 : Fin NF) = litSl 30 from (lit 30 (by unfold cacheSide; decide)).symm]; exact a30
  replace a41 : A2 141 = ZeroPadding.pad Rc (List.replicate iR true) := by
    rw [show (141 : Fin NF) = litSl 41 from (lit 41 (by unfold cacheSide; decide)).symm]; exact a41
  replace a42 : A2 142 = ZeroPadding.pad Rc [negative ((a.output r).clauses ci).right] := by
    rw [show (142 : Fin NF) = litSl 42 from (lit 42 (by unfold cacheSide; decide)).symm]; exact a42
  replace a85 : A2 185 = ZeroPadding.pad Rc [decide ((a.output r).systematicBits ≤ iL)] := by
    rw [show (185 : Fin NF) = litSl 85 from (lit 85 (by unfold cacheSide; decide)).symm]; exact a85
  replace a89 : A2 189 = ZeroPadding.pad Rc [decide ((a.output r).systematicBits ≤ iR)] := by
    rw [show (189 : Fin NF) = litSl 89 from (lit 89 (by unfold cacheSide; decide)).symm]; exact a89
  have l3 : litSl 3 = 103 := by unfold litSl; rw [if_neg (by unfold cacheSide; decide)]; rfl
  have l4 : litSl 4 = 104 := by unfold litSl; rw [if_neg (by unfold cacheSide; decide)]; rfl
  replace a3 : A2 103 = ZeroPadding.pad Rc (value a r iL) := by rw [← l3]; exact a3
  replace a4 : A2 104 = ZeroPadding.pad Rc (value a r iR) := by rw [← l4]; exact a4
  have h200 : A2 200 = List.replicate Rc false := by
    rw [k2 200 (by decide), hA1, Function.update_of_ne (by decide)]; exact hblank 200 (by decide)
  have h201 : A2 201 = List.replicate Rc false := by
    rw [k2 201 (by decide), hA1, Function.update_of_ne (by decide)]; exact hblank 201 (by decide)
  have h38 : A2 38 = List.replicate Rc false := by
    rw [k2 38 (by decide), hA1, Function.update_of_ne (by decide)]; exact hblank 38 (by decide)
  -- the two index words
  set A3 := Function.update A2 200 (ZeroPadding.pad Rc (CompareMachine.word iL)) with hA3
  have s3 := word0_step (129 : Fin NF) 200 38 (by decide) (by decide) (by decide) iL Rc Rc Rc (by omega) (by omega)
    (fun _ => 0) A2 (fun _ _ => rfl) a29 h200 h38
  set A4 := Function.update A3 201 (ZeroPadding.pad Rc (CompareMachine.word iR)) with hA4
  have s4 := word0_step (141 : Fin NF) 201 38 (by decide) (by decide) (by decide) iR Rc Rc Rc (by omega) (by omega)
    (fun _ => 0) A3 (fun _ _ => rfl) (by simp [A3, a41]) (by simp [A3, h201]) (by simp [A3, h38])
  refine ⟨A4, s1.seq (s2.seq (s3.seq s4)), by simp [A4, A3, a29], by simp [A4, A3, a30], by simp [A4, A3, a41],
    by simp [A4, A3, a42], by simp [A4, A3, a85], by simp [A4, A3, a89], by simp [A4, A3, a3], by simp [A4, A3, a4],
    by simp [A4, A3], by simp [A4], ?_, ?_⟩
  · intro z hz
    have n200 : z ≠ 200 := fun e => by rw [e] at hz; revert hz; decide
    have n201 : z ≠ 201 := fun e => by rw [e] at hz; revert hz; decide
    have n144 : z ≠ 144 := fun e => by rw [e] at hz; revert hz; decide
    rw [hA4, Function.update_of_ne n201, hA3, Function.update_of_ne n200, k2 z (by omega), hA1,
      Function.update_of_ne n144]
  · intro z h1 h2
    by_cases e200 : z = 200
    · subst e200; simp [A4, A3, CompareMachine.word]; omega
    by_cases e201 : z = 201
    · subst e201; simp [A4, CompareMachine.word]; omega
    rw [hA4, Function.update_of_ne e201, hA3, Function.update_of_ne e200]
    by_cases hp : ∃ b, litSl b = z
    · obtain ⟨b, rfl⟩ := hp
      by_cases hcs : cacheSide b
      · have := litSl_range b; rw [litSl_val, if_pos hcs] at h1; unfold cacheSide at hcs; omega
      · exact alen b hcs
    · rw [off2 z (fun b e => hp ⟨b, e⟩)]
      by_cases e144 : z = 144
      · subst e144; simp [A1]; omega
      · rw [hA1, Function.update_of_ne e144, hblank z (by omega)]; simp

end
end NearCubicWires.SourceRequest.SelFront


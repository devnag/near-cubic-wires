import Proof.SourceAssembly.SourcePairSupport
import Proof.SourceAssembly.SourceRequestCurClause

set_option autoImplicit false
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace NearCubicWires.SourceRequest.LitInfo
open NearCubicWires LocalBitMultitape ExtDecompositionBatch RepairOrdinary RepairRepresentation
open SourceInterfaces RecoveryRootRound
open NearCubicWires.RepairOrdinary.CloseoutRowsOriginalClause (index negative)
open PCJ6e421fabe2aa4155_SourceLiteralSupport (value result slots words outPort refPort flagPort)
noncomputable section

def litM := Composition.machine PCJ6e421fabe2aa4155_SourceLiteralRefs.bump
  (Composition.machine CloseoutRowsOriginalSource.machine
    (Composition.machine (PCJ6e421fabe2aa4155_SourceLiteralSupport.machine false)
      (Composition.machine (PCJ6e421fabe2aa4155_SourceLiteralSupport.machine true)
        PCJ6e421fabe2aa4155_SourcePairSupport.finish)))

def litCost (a : PointwisePCPPAlgorithm) (r : PCPPRequest a.minimumArity)
    (ci : Fin (2 ^ (a.output r).clauseBits)) (C : Nat) : Nat :=
  1 + 1 + (PCJ6e421fabe2aa4155_SourceLiteralRefs.sourceCost a r ci C + 1 +
    (PCPPQueryCachedBounds.callBudget a (r.circuit.size + r.arity) + 6 + 1 +
      (PCPPQueryCachedBounds.callBudget a (r.circuit.size + r.arity) + 6 + 1 + 1)))

/-- Away from the query tape `15` the clause cache does not depend on the query pair. -/
theorem clauseData_pair (source : List Bool) (arity idx Q : Nat) (pair : List Bool) (j : Fin 19) (hj : j ≠ 15) :
    PCPPQueryIndexPadding.clauseData source arity idx Q pair j =
      PCPPQueryIndexPadding.clauseData source arity idx Q [] j := by
  unfold PCPPQueryIndexPadding.clauseData
  fin_cases j <;> simp [PCPPQueryClauseReuse.data] at hj ⊢

/-- **LitInfo's local run** (heads `0` in and out). -/
theorem lit_run (a : PointwisePCPPAlgorithm) (r : PCPPRequest a.minimumArity)
    (ci : Fin (2 ^ (a.output r).clauseBits)) (C : Nat)
    (hc : CloseoutRowsOriginalPair.budget (index ((a.output r).clauses ci).left)
      (index ((a.output r).clauses ci).right) (negative ((a.output r).clauses ci).left)
      (negative ((a.output r).clauses ci).right) + 1 ≤ C) :
    ∃ D : Fin 91 → List Bool,
      Step litM (litCost a r ci C) (fun _ => 0)
        (PCJ6e421fabe2aa4155_SourceLiteralRefs.bank C (PCPPQueryIndexPadding.clauseData (pcppOutput r (a.output r))
          r.arity ci.val (PCPPQueryCachedBounds.capacity a (r.circuit.size + r.arity)) []))
        (fun _ => 0) D ∧
      D 3 = ZeroPadding.pad (PCPPQueryCachedBounds.capacity a (r.circuit.size + r.arity))
        (value a r (index ((a.output r).clauses ci).left)) ∧
      D 4 = ZeroPadding.pad (PCPPQueryCachedBounds.capacity a (r.circuit.size + r.arity))
        (value a r (index ((a.output r).clauses ci).right)) ∧
      (∀ j : Fin 19, j ≠ 3 → j ≠ 4 → j ≠ 15 → D (j.castAdd 72) = PCPPQueryIndexPadding.clauseData
        (pcppOutput r (a.output r)) r.arity ci.val (PCPPQueryCachedBounds.capacity a (r.circuit.size + r.arity)) [] j) ∧
      D 29 = ZeroPadding.pad C (List.replicate (index ((a.output r).clauses ci).left) true) ∧
      D 30 = ZeroPadding.pad C [negative ((a.output r).clauses ci).left] ∧
      D 41 = ZeroPadding.pad C (List.replicate (index ((a.output r).clauses ci).right) true) ∧
      D 42 = ZeroPadding.pad C [negative ((a.output r).clauses ci).right] ∧
      D 85 = ZeroPadding.pad C [decide ((a.output r).systematicBits ≤ index ((a.output r).clauses ci).left)] ∧
      D 89 = ZeroPadding.pad C [decide ((a.output r).systematicBits ≤ index ((a.output r).clauses ci).right)] := by
  let Q := PCPPQueryCachedBounds.capacity a (r.circuit.size + r.arity)
  let p := (a.output r).clauses ci
  have b := PCJ6e421fabe2aa4155_SourceLiteralRefs.bump_run
    (PCJ6e421fabe2aa4155_SourceLiteralRefs.bank C (PCPPQueryIndexPadding.clauseData (pcppOutput r (a.output r))
      r.arity ci.val Q []))
  obtain ⟨A, hr, cache, left, lsign, right, rsign, _sys, li, la, ri, ra, _driver⟩ :=
    CloseoutRowsOriginalSource.run a r ci C hc
  rw [← PCJ6e421fabe2aa4155_SourceLiteralRefs.bank_eq] at hr
  let B := result false Q (value a r (index p.left)) A
  let D := result true Q (value a r (index p.right)) B
  have lft := PCJ6e421fabe2aa4155_SourceLiteralSupport.run false a r (index p.left) C A
    (PCJ6e421fabe2aa4155_SourcePairSupport.projections false _ _ _ _ _ _ _ A cache li) la
  have rightInput : ∀ i, B (slots true i) = words (pcppOutput r (a.output r)) r.arity (index p.right) Q C [] i := by
    intro i
    have ne : slots true i ≠ outPort false := by fin_cases i <;> decide
    simpa only [B, result, ne, if_false] using
      PCJ6e421fabe2aa4155_SourcePairSupport.projections true _ _ _ _ _ _ _ A cache ri i
  have rgt := PCJ6e421fabe2aa4155_SourceLiteralSupport.run true a r (index p.right) C B rightInput ra
  have hall := b.seq (hr.seq (lft.seq (rgt.seq (PCJ6e421fabe2aa4155_SourcePairSupport.finish_run D))))
  have n29 : (29 : Fin 91) ≠ outPort false ∧ (29 : Fin 91) ≠ outPort true := by decide
  refine ⟨D, hall.enlarge (by simp only [litCost, PCJ6e421fabe2aa4155_SourceLiteralRefs.sourceCost]; omega), ?_, ?_, ?_,
    ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [D, B, result, outPort]; rfl
  · simp [D, result, outPort]; rfl
  · intro j h3 h4 h15
    have ne3 : j.castAdd 72 ≠ outPort false := by
      intro he; apply h3; apply Fin.ext; exact congrArg (fun i : Fin 91 => i.val) he
    have ne4 : j.castAdd 72 ≠ outPort true := by
      intro he; apply h4; apply Fin.ext; exact congrArg (fun i : Fin 91 => i.val) he
    have := cache j
    simp only [D, B, result, ne3, ne4, if_false]
    rw [this]
    exact clauseData_pair _ _ _ _ _ j h15
  · simp only [D, B, result, show (29 : Fin 91) ≠ outPort true by decide, show (29 : Fin 91) ≠ outPort false by decide,
      if_false]; exact left
  · simp only [D, B, result, show (30 : Fin 91) ≠ outPort true by decide, show (30 : Fin 91) ≠ outPort false by decide,
      if_false]; exact lsign
  · simp only [D, B, result, show (41 : Fin 91) ≠ outPort true by decide, show (41 : Fin 91) ≠ outPort false by decide,
      if_false]; exact right
  · simp only [D, B, result, show (42 : Fin 91) ≠ outPort true by decide, show (42 : Fin 91) ≠ outPort false by decide,
      if_false]; exact rsign
  · simp only [D, B, result, show (85 : Fin 91) ≠ outPort true by decide, show (85 : Fin 91) ≠ outPort false by decide,
      if_false]; exact la
  · simp only [D, B, result, show (89 : Fin 91) ≠ outPort true by decide, show (89 : Fin 91) ≠ outPort false by decide,
      if_false]; exact ra

/-! ## Docked and padded: the refill cache read in place, every other bank port on the caller's scratch -/

/-- Bank ports read from the caller's refill cache in place (their words and heads are returned). -/
def cacheSide (b : Fin 91) : Prop := b.val < 19 ∧ b.val ≠ 3 ∧ b.val ≠ 4 ∧ b.val ≠ 15

instance (b : Fin 91) : Decidable (cacheSide b) := by unfold cacheSide; infer_instance

/-- Padding caps of the dock: `0` on the in-place cache ports, `R` on the caller's scratch. -/
def capOf (R : Nat) (b : Fin 91) : Nat := if cacheSide b then 0 else R

theorem pad_pad (R Q : Nat) (w : List Bool) (h : Q ≤ R) :
    ZeroPadding.pad R (ZeroPadding.pad Q w) = ZeroPadding.pad R w := by
  unfold ZeroPadding.pad
  rw [List.append_assoc, ← List.replicate_add]
  simp only [List.length_append, List.length_replicate]
  congr 2
  omega

theorem pad_blank (R Q : Nat) (h : Q ≤ R) :
    ZeroPadding.pad R (List.replicate Q false) = List.replicate R false := by
  unfold ZeroPadding.pad
  rw [← List.replicate_add]
  simp only [List.length_replicate]
  congr 1
  omega

/-- The scratch side of the bank, padded to `R ≥ Q + 1`, is blank except the driver port `44` (`1^Q`). -/
theorem bank_blank (Q R : Nat) (hQ : Q + 1 ≤ R) (X : Fin 19 → List Bool)
    (hX3 : X 3 = List.replicate Q false) (hX4 : X 4 = List.replicate Q false) (hX15 : X 15 = List.replicate Q false)
    (b : Fin 91) (hb : ¬ cacheSide b) (h44 : b ≠ 44) :
    ZeroPadding.pad R (PCJ6e421fabe2aa4155_SourceLiteralRefs.bank Q X b) = List.replicate R false := by
  have hR0 : ZeroPadding.pad R [] = List.replicate R false := by simp [ZeroPadding.pad]
  have hRQ := pad_blank R Q (by omega)
  have hRQ1 := pad_blank R (Q + 1) hQ
  unfold cacheSide at hb
  fin_cases b <;> simp at hb h44 <;>
    first
    | exact hR0 | exact hRQ | exact hRQ1
    | exact (congrArg (ZeroPadding.pad R) hX3).trans hRQ
    | exact (congrArg (ZeroPadding.pad R) hX4).trans hRQ
    | exact (congrArg (ZeroPadding.pad R) hX15).trans hRQ

/-- The cache's tapes 3, 4 and 15 are blank at the refill (stated generically: instantiating is cheap for the kernel). -/
theorem cd_blank (source : List Bool) (ar idx C : Nat) :
    PCPPQueryIndexPadding.clauseData source ar idx C [] 3 = List.replicate C false ∧
    PCPPQueryIndexPadding.clauseData source ar idx C [] 4 = List.replicate C false ∧
    PCPPQueryIndexPadding.clauseData source ar idx C [] 15 = List.replicate C false := by
  refine ⟨?_, ?_, ?_⟩ <;> simp [PCPPQueryIndexPadding.clauseData, PCPPQueryClauseReuse.data, ZeroPadding.pad]

theorem bank_driver (Q R : Nat) (X : Fin 19 → List Bool) :
    ZeroPadding.pad R (PCJ6e421fabe2aa4155_SourceLiteralRefs.bank Q X 44) =
      ZeroPadding.pad R (List.replicate Q true) := rfl

theorem bank_cache (Q : Nat) (X : Fin 19 → List Bool) (j : Fin 19) :
    PCJ6e421fabe2aa4155_SourceLiteralRefs.bank Q X (j.castAdd 72) = X j := by
  simp [PCJ6e421fabe2aa4155_SourceLiteralRefs.bank]

/-- **LitInfo, docked**: the local run lifted to the caps `capOf R` and installed by any injective slot map. -/
theorem lit_dock {U : Nat} (a : PointwisePCPPAlgorithm) (r : PCPPRequest a.minimumArity)
    (ci : Fin (2 ^ (a.output r).clauseBits))
    (hc : CloseoutRowsOriginalPair.budget (index ((a.output r).clauses ci).left)
      (index ((a.output r).clauses ci).right) (negative ((a.output r).clauses ci).left)
      (negative ((a.output r).clauses ci).right) + 1 ≤ PCPPQueryCachedBounds.capacity a (r.circuit.size + r.arity))
    (sl : Fin 91 → Fin U) (hsl : Function.Injective sl) (R : Nat)
    (hwin : litCost a r ci (PCPPQueryCachedBounds.capacity a (r.circuit.size + r.arity)) + 1 ≤ R)
    (hQR : PCPPQueryCachedBounds.capacity a (r.circuit.size + r.arity) + 1 ≤ R)
    (H : Fin U → Nat) (A : Fin U → List Bool) (hH : ∀ b, H (sl b) = 0)
    (hA : ∀ b, A (sl b) = ZeroPadding.pad (capOf R b) (PCJ6e421fabe2aa4155_SourceLiteralRefs.bank
      (PCPPQueryCachedBounds.capacity a (r.circuit.size + r.arity))
      (PCPPQueryIndexPadding.clauseData (pcppOutput r (a.output r)) r.arity ci.val
        (PCPPQueryCachedBounds.capacity a (r.circuit.size + r.arity)) []) b)) :
    ∃ A' : Fin U → List Bool,
      Step (RecoveryFocus.machine sl litM) (litCost a r ci (PCPPQueryCachedBounds.capacity a (r.circuit.size + r.arity)))
        H A H A' ∧
      A' (sl 3) = ZeroPadding.pad R (value a r (index ((a.output r).clauses ci).left)) ∧
      A' (sl 4) = ZeroPadding.pad R (value a r (index ((a.output r).clauses ci).right)) ∧
      A' (sl 29) = ZeroPadding.pad R (List.replicate (index ((a.output r).clauses ci).left) true) ∧
      A' (sl 30) = ZeroPadding.pad R [negative ((a.output r).clauses ci).left] ∧
      A' (sl 41) = ZeroPadding.pad R (List.replicate (index ((a.output r).clauses ci).right) true) ∧
      A' (sl 42) = ZeroPadding.pad R [negative ((a.output r).clauses ci).right] ∧
      A' (sl 85) = ZeroPadding.pad R [decide ((a.output r).systematicBits ≤ index ((a.output r).clauses ci).left)] ∧
      A' (sl 89) = ZeroPadding.pad R [decide ((a.output r).systematicBits ≤ index ((a.output r).clauses ci).right)] ∧
      (∀ b, cacheSide b → A' (sl b) = A (sl b)) ∧
      (∀ z, (∀ b, sl b ≠ z) → A' z = A z) ∧
      (∀ b, ¬ cacheSide b → (A' (sl b)).length ≤ R) := by
  set Q := PCPPQueryCachedBounds.capacity a (r.circuit.size + r.arity) with hQ
  obtain ⟨D, st, d3, d4, dc, d29, d30, d41, d42, d85, d89⟩ := lit_run a r ci Q hc
  have padded := st.pad (capOf R)
  have dk := TermSeg.dock padded sl hsl H A hH (fun b => (hA b).trans rfl)
  refine ⟨install sl A (fun b => ZeroPadding.pad (capOf R b) (D b)), dk, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [install_slot sl hsl, d3]; simp only [capOf, cacheSide]; simp; exact pad_pad R Q _ (by omega)
  · rw [install_slot sl hsl, d4]; simp only [capOf, cacheSide]; simp; exact pad_pad R Q _ (by omega)
  · rw [install_slot sl hsl, d29]; simp only [capOf, cacheSide]; simp; exact pad_pad R Q _ (by omega)
  · rw [install_slot sl hsl, d30]; simp only [capOf, cacheSide]; simp; exact pad_pad R Q _ (by omega)
  · rw [install_slot sl hsl, d41]; simp only [capOf, cacheSide]; simp; exact pad_pad R Q _ (by omega)
  · rw [install_slot sl hsl, d42]; simp only [capOf, cacheSide]; simp; exact pad_pad R Q _ (by omega)
  · rw [install_slot sl hsl, d85]; simp only [capOf, cacheSide]; simp; exact pad_pad R Q _ (by omega)
  · rw [install_slot sl hsl, d89]; simp only [capOf, cacheSide]; simp; exact pad_pad R Q _ (by omega)
  · intro b hb
    rw [install_slot sl hsl, hA b]
    have hcap : capOf R b = 0 := by simp [capOf, hb]
    rw [hcap, ZeroPadding.pad_zero, ZeroPadding.pad_zero]
    obtain ⟨h19, h3, h4, h15⟩ := hb
    have e : b = (⟨b.val, h19⟩ : Fin 19).castAdd 72 := Fin.ext rfl
    rw [e, dc _ (fun h => h3 (congrArg Fin.val h)) (fun h => h4 (congrArg Fin.val h)) (fun h => h15 (congrArg Fin.val h)),
      bank_cache]
  · intro z hz
    exact install_other sl A _ z hz
  · intro b hb
    rw [install_slot sl hsl]
    have hcap : capOf R b = R := by simp [capOf, hb]
    have h1 : (ZeroPadding.pad (capOf R b) (PCJ6e421fabe2aa4155_SourceLiteralRefs.bank Q
        (PCPPQueryIndexPadding.clauseData (pcppOutput r (a.output r)) r.arity ci.val Q []) b)).length ≤ R := by
      rw [hcap]
      by_cases h44 : b = 44
      · subst h44; rw [bank_driver]; simp; omega
      · obtain ⟨c3, c4, c15⟩ := cd_blank (pcppOutput r (a.output r)) r.arity ci.val Q
        rw [bank_blank Q R hQR _ c3 c4 c15 b hb h44]; simp
    exact P1Closure.LocalSupport.step_fits padded b R h1 (by show 0 + _ + 1 ≤ R; omega)

end
end NearCubicWires.SourceRequest.LitInfo


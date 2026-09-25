import MainTheorem
open Lean Elab Command

/-! Run after `lake build`:  lake env lean Check.lean
It prints the paper's Theorem 2.5 written out in Lean, the main theorem, its axioms, the list of its hypotheses,
and PASS or FAIL. -/

-- (a) Theorem 2.5 with every definition expanded.
#print NearCubicWires.Paper.theorem_2_5

-- (b) The main theorem: published statements ⇒ Theorem 2.5.
#check @NearCubicWires.Bindings.near_cubic_wires_from_literature_expanded

-- (c) Its axioms. An unfinished proof would list `sorryAx` here.
#print axioms NearCubicWires.Bindings.near_cubic_wires_from_literature_expanded

/-- The hypotheses of a statement `∀ (h₁ : A₁) … (hₖ : Aₖ), B`, outermost first. -/
partial def checkBinderTypes : Expr → List Expr
  | .forallE _ t b _ => t :: checkBinderTypes b
  | _ => []

/-- The body `B` of a statement `∀ (h₁ : A₁) … (hₖ : Aₖ), B`. -/
partial def checkConclusion : Expr → Expr
  | .forallE _ _ b _ => checkConclusion b
  | e => e

-- (d) PASS only if the hypotheses are exactly the nine literal statements below, in this order, the conclusion is
-- Theorem 2.5, and the axioms are among Lean's standard three.
run_cmd do
  let thm := ``NearCubicWires.Bindings.near_cubic_wires_from_literature_expanded
  let target := ``NearCubicWires.Paper.theorem_2_5
  -- These are the only assumptions. Each is defined, with the paper sentence it transcribes, in Bindings/ and shown in SourceMapping/.
  let hypotheses : List Name := [
    `NearCubicWires.Bindings.CTW26.CTW26_Lemma3_2,
    `NearCubicWires.Bindings.CW19TM2.CW19_Proposition18_2_TM2,
    `NearCubicWires.Bindings.Williams14.Williams14_Corollary4_4,
    `NearCubicWires.Bindings.HLW06.HLW06_Theorem8_2,
    `NearCubicWires.Bindings.RS62.RS62_Theorem4_eq314,
    `NearCubicWires.Bindings.CLW20Lemma310TM2.CLW20_Lemma3_10_TM2,
    `NearCubicWires.Bindings.CLW20Lemma311TM2.CLW20_Lemma3_11_explicitEnc_TM2,
    `NearCubicWires.Bindings.CLW20Theorem113.CLW20_Theorem1_13,
    `NearCubicWires.Bindings.CLW20Lemma39TM2.CLW20_Lemma3_9_TM2]
  let axs ← liftCoreM <| collectAxioms thm
  let std := #[``propext, ``Classical.choice, ``Quot.sound]
  let some info := (← getEnv).find? thm | throwError "FAIL: theorem not found"
  let binders := checkBinderTypes info.type
  let found := binders.map fun t => (t.constName?).getD Name.anonymous
  for h in found do
    IO.println s!"assumes: {h}"
  let okHyps := binders.all (·.isConst) && found == hypotheses
  let okConcl := (checkConclusion info.type).isConstOf target
  let okAxioms := axs.all std.contains
  if okHyps && okConcl && okAxioms then
    IO.println s!"PASS: {thm} proves {target} from the {hypotheses.length} hypotheses above and depends only on {axs.toList}"
  else
    throwError "FAIL: hypotheses as listed: {okHyps}; conclusion is Theorem 2.5: {okConcl}; axioms {axs.toList}"

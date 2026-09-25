import Bindings.CLW20_Lemma3_10_TM2
import Bindings.CLW20_Lemma3_10_Wrapper
import Bindings.CLW20_Lemma3_11_TM2
import Bindings.CLW20_Lemma3_8
import Bindings.CLW20_Lemma3_9_TM2
import Bindings.CLW20_Theorem1_13
import Bindings.CTW26_Lemma3_2
import Bindings.CW19_Proposition18_2_TM2
import Bindings.HLW06_Theorem8_2
import Bindings.RS62_Theorem4
import Bindings.Williams14_Corollary4_4
import Proof.Assembly.Final

/-! # Theorem 2.5 from nine published statements

`near_cubic_wires_from_literature` proves paper Theorem 2.5 (`paper/paper.tex`, `thm:main-fixed`; in Lean
`OrdinaryHeadlineTheorem25`) from nine hypotheses. Each hypothesis is a Lean transcription of a statement printed in the
cited paper. Each transcription is defined, with its sentence quoted verbatim and its PDF page, in its own module under
`Bindings/`, and a Lean-proved adapter carries it into the form the proof uses (`EightSources`, whose closed proof is
`AssembledProof.application` in `Proof/Assembly/Final.lean`). The pages in `SourceMapping/` put each printed
sentence beside its Lean definition.

* CTW26 Lemma 3.2 (threshold normalization): literal.
* HLW06 Construction 8.1 / Theorem 8.2 (expander spectrum): literal; the bound is asserted exactly when λ₂ exists.
* RS62 Theorem 4, eq. (3.14) (prime θ bound): literal; proved equivalent to the import.
* CLW20 Lemma 3.9 (worst-case to average-case amplification): literal; its construction clause is stated in Mathlib's
  standard model (`Turing.TM2ComputableInTime`), carried to the repository's machine by a proved linear-time simulation.
* CLW20 Lemma 3.10 (projection PCP): literal (verifiers running in time T on every witness); the adapter wraps a verifier
  that is only clocked on witnesses of length T(n) with a guard machine (`Bindings/CLW20_Lemma3_10_Wrapper.lean`); the construction clause is
  stated in Mathlib's `Turing.TM2ComputableInPolyTime`; the quantified verifier stays in the repository's machine model.
* CW19 Proposition 18(2) (disjoint exact-threshold decomposition): literal; its polynomial-time construction is stated in
  Mathlib's `Turing.TM2ComputableInPolyTime`.
* CLW20 Lemma 3.11 (pointwise PCPP): the printed statement is false at n = 1 (`clw20_lemma3_11_asPrinted_false`); used for
  n ≥ 2 with the encoder's supports explicit, as in CW19 Lemma 27 and CLW20 p. 28; both algorithms are stated in Mathlib's
  `Turing.TM2ComputableInPolyTime`.

* Williams (JACM 2014) Corollary 4.4 / C.2 (rectangular integer matrix product): literal, stated for multitape machines
  with two input tapes (Williams, Appendix C: "even on a multitape TM"); the finitely many sizes below the corollary's
  onset are handled by a lookup gate proved in Lean.

* CLW20 Theorem 1.13 (refuter with an NP oracle): literal, read in the repository's multitape machine model (CLW20 p. 19:
  "the specific model does not really matter"; FS16 p. 13: O(t) universal multitape simulation); the import is proved
  equivalent to the literal restricted to the import's clocks.

The tenth imported result, CLW20 Lemma 3.8 (the XOR lemma), is not a hypothesis: `CLW20Lemma38.clw20_xor_source` proves it
in Lean, following the paper's own proof in CLW20 Appendix A.
-/
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

namespace NearCubicWires.Bindings
open NearCubicWires RepairSource RepairRepresentation SourceInterfaces

/-- Theorem 2.5 (`paper/paper.tex`, `thm:main-fixed`) from nine literal paper statements. -/
theorem near_cubic_wires_from_literature
    (ctw26 : CTW26.CTW26_Lemma3_2)
    (cw19 : CW19TM2.CW19_Proposition18_2_TM2)
    (williams : Williams14.Williams14_Corollary4_4)
    (hlw06 : HLW06.HLW06_Theorem8_2)
    (rs62 : RS62.RS62_Theorem4_eq314)
    (clw310 : CLW20Lemma310TM2.CLW20_Lemma3_10_TM2)
    (clw311 : CLW20Lemma311TM2.CLW20_Lemma3_11_explicitEnc_TM2)
    (clw113 : CLW20Theorem113.CLW20_Theorem1_13)
    (clw39 : CLW20Lemma39TM2.CLW20_Lemma3_9_TM2) :
    OrdinaryHeadlineTheorem25 :=
  AssembledProof.application
    ⟨CTW26.ctw26_to_import ctw26, CW19TM2.cw19_tm2_to_import cw19, Williams14.williams14_to_import williams, HLW06.hlw06_to_import hlw06,
      RS62.rs62_to_import rs62,
      ⟨CLW20Lemma310Guard.clw20_lemma3_10_to_import (CLW20Lemma310TM2.tier1_of_tier2 clw310),
        CLW20Lemma311TM2.clw20_lemma3_11_explicitEnc_tm2_to_import clw311⟩,
      ⟨CLW20Theorem113.clw20_theorem1_13_to_import clw113, CLW20Lemma38.clw20_xor_source⟩, CLW20Lemma39TM2.clw20_lemma3_9_tm2_to_import clw39⟩

/-- The same, with the conclusion written out in full: paper Theorem 2.5 with every definition expanded. -/
theorem near_cubic_wires_from_literature_expanded
    (ctw26 : CTW26.CTW26_Lemma3_2)
    (cw19 : CW19TM2.CW19_Proposition18_2_TM2)
    (williams : Williams14.Williams14_Corollary4_4)
    (hlw06 : HLW06.HLW06_Theorem8_2)
    (rs62 : RS62.RS62_Theorem4_eq314)
    (clw310 : CLW20Lemma310TM2.CLW20_Lemma3_10_TM2)
    (clw311 : CLW20Lemma311TM2.CLW20_Lemma3_11_explicitEnc_TM2)
    (clw113 : CLW20Theorem113.CLW20_Theorem1_13)
    (clw39 : CLW20Lemma39TM2.CLW20_Lemma3_9_TM2) :
    NearCubicWires.Paper.theorem_2_5 :=
  NearCubicWires.Paper.theorem_2_5_iff.mp
    (near_cubic_wires_from_literature ctw26 cw19 williams hlw06 rs62 clw310 clw311 clw113 clw39)

end NearCubicWires.Bindings


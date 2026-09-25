# Theorem 2.5

The main theorem concludes the Lean statement in the first row of the table below, `NearCubicWires.Paper.theorem_2_5`:
the paper's Theorem 2.5 with every definition written out. The other rows show the definitions it uses, beside the
paper's own definitions. The last section links two statement checks that Lean proves.

Paper: the paper's source is [`paper/paper.tex`](../paper/paper.tex); line numbers refer to that file. The quotations
are its LaTeX source, verbatim.

<table>
<tr><th>Paper (verbatim)</th><th>Lean (verbatim)</th></tr>
<tr><td>
<b>paper/paper.tex, lines 794–808</b>
<pre>
\begin{theorem}[Fixed advantage]\label{thm:main-fixed}
For every fixed
\(0&lt;\gamma&lt;1/2\), there exist a common language \(F_\gamma\in E^{NP}\)
and positive constants \(b_{\mathrm S,\gamma},b_{\mathrm T,\gamma}\)
such that, for every sufficiently large \(n\), agreement at least
\(1/2+\gamma\) with \((F_\gamma)_n\) implies
\[
W(C)&gt;b_{\mathrm S,\gamma}\frac{n^3}{L^5}
\]
for \(C\in\SYMTHR\), and
\[
W(C)&gt;b_{\mathrm T,\gamma}\frac{n^3}{L^9}
\]
for \(C\in\THRTHR\).
\end{theorem}
</pre>
<b>paper/paper.tex, lines 49–50</b>
<pre>
\newcommand{\SYMTHR}{\mathrm{SYM}\circ\mathrm{THR}}
\newcommand{\THRTHR}{\mathrm{THR}\circ\mathrm{THR}}
</pre>
</td><td>

[Statement.lean, lines 1727–1750](../Statement.lean#L1727-L1750)

<pre title="Statement.lean, lines 1727–1750">
/-- Paper Theorem 2.5 written with every local definition expanded. -/
noncomputable def theorem_2_5 : Prop :=
  ∀ gamma : ℝ, 0 &lt; gamma → gamma &lt; 1 / 2 →
    ∃ language : (n : ℕ) → (Fin n → Bool) → Bool,
    ∃ bS bT : ℝ,
      (∃ oracle : ℕ → Bool, Nonempty (EncodedNPVerifier oracle) ∧
        Nonempty (OrdinaryENPCertificate oracle language)) ∧
      0 &lt; bS ∧ 0 &lt; bT ∧
      ∃ onset : ℕ, ∀ n : ℕ, onset ≤ n →
        (∀ circuit : SymmetricThresholdCircuit n,
          1 / 2 + gamma ≤
            ((Finset.univ.filter fun x =&gt; circuit.eval x = language n x).card : ℝ) /
              (Fintype.card (Fin n → Bool) : ℝ) →
          bS * (n : ℝ) ^ 3 / (Nat.clog 2 (n + 2) : ℝ) ^ 5 &lt;
            (∑ i : Fin circuit.bottomCount,
              ((circuit.bottom i).support.card + 1) : ℕ)) ∧
        (∀ circuit : ThresholdThresholdCircuit n,
          1 / 2 + gamma ≤
            ((Finset.univ.filter fun x =&gt; circuit.eval x = language n x).card : ℝ) /
              (Fintype.card (Fin n → Bool) : ℝ) →
          bT * (n : ℝ) ^ 3 / (Nat.clog 2 (n + 2) : ℝ) ^ 9 &lt;
            (∑ i : Fin circuit.bottomCount,
              if circuit.topWeight i = 0 then 0
              else (circuit.bottom i).support.card + 1 : ℕ))
</pre>

</td></tr>
<tr><td>
<b>paper/paper.tex, lines 561–564</b>
<pre>
A threshold gate is \(\mathbf1[\sum_iw_ix_i\ge\theta]\), and a symmetric
gate is an arbitrary Boolean function of the unweighted number of its
accepting inputs. Both circuit classes have bottom threshold gates and
one top gate of the displayed type.
</pre>
<b>paper/paper.tex, line 586</b>
<pre>
Threshold gates may have arbitrary real weights semantically.
</pre>
</td><td>

[Statement.lean, lines 649–654](../Statement.lean#L649-L654)

<pre title="Statement.lean, line 641">
abbrev BitInput (n : ℕ) := Fin n → Bool
</pre>

<pre title="Statement.lean, line 643">
abbrev BoolFunction (n : ℕ) := BitInput n → Bool
</pre>

<pre title="Statement.lean, line 645">
abbrev Language := (n : ℕ) → BoolFunction n
</pre>

<pre title="Statement.lean, line 647">
def bitAsReal (bit : Bool) : ℝ := if bit then 1 else 0
</pre>

<pre title="Statement.lean, lines 649–654">
/-- A semantic threshold gate together with its exact retained support. -/
structure RealThresholdGate (n : ℕ) where
  weight : Fin n → ℝ
  threshold : ℝ
  support : Finset (Fin n)
  mem_support_iff : ∀ i, i ∈ support ↔ weight i ≠ 0
</pre>

<pre title="Statement.lean, lines 656–658">
noncomputable def RealThresholdGate.eval {n : ℕ} (gate : RealThresholdGate n)
    (input : BitInput n) : Bool :=
  decide (gate.threshold ≤ ∑ i, gate.weight i * bitAsReal (input i))
</pre>

[Statement.lean, lines 711–714](../Statement.lean#L711-L714)

<pre title="Statement.lean, lines 711–714">
structure SymmetricThresholdCircuit (n : ℕ) where
  bottomCount : ℕ
  bottom : Fin bottomCount → RealThresholdGate n
  top : ℕ → Bool
</pre>

<pre title="Statement.lean, lines 716–718">
noncomputable def SymmetricThresholdCircuit.eval {n : ℕ}
    (circuit : SymmetricThresholdCircuit n) (input : BitInput n) : Bool :=
  circuit.top ((Finset.univ.filter fun i =&gt; (circuit.bottom i).eval input).card)
</pre>

[Statement.lean, lines 720–724](../Statement.lean#L720-L724)

<pre title="Statement.lean, lines 720–724">
structure ThresholdThresholdCircuit (n : ℕ) where
  bottomCount : ℕ
  bottom : Fin bottomCount → RealThresholdGate n
  topWeight : Fin bottomCount → ℝ
  topThreshold : ℝ
</pre>

<pre title="Statement.lean, lines 726–729">
noncomputable def ThresholdThresholdCircuit.eval {n : ℕ}
    (circuit : ThresholdThresholdCircuit n) (input : BitInput n) : Bool :=
  decide (circuit.topThreshold ≤
    ∑ i, circuit.topWeight i * bitAsReal ((circuit.bottom i).eval input))
</pre>

</td></tr>
<tr><td>
<b>paper/paper.tex, lines 545–548</b>
<pre>
Physical wires count input-to-bottom incidences and top incidences in a
strictly layered simple-edge presentation. Parallel uses are explicit
occurrences, zero-weight inputs and zero top coefficients are deleted,
and constants are propagated before the resource is measured.
</pre>
<b>paper/paper.tex, lines 564–574</b>
<pre>
If bottom occurrence \(G_i\) has
support \(\operatorname{supp}(G_i)\) and a nonzero top incidence, then

\[
W(C)
{}={}
\sum_i
\bigl(
|\operatorname{supp}(G_i)|+1
\bigr).
\]
</pre>
</td><td>

[Proof/Foundations/Semantics.lean, lines 60–62](../Proof/Foundations/Semantics.lean#L60-L62)

<pre title="Proof/Foundations/Semantics.lean, lines 60–62">
def SymmetricThresholdCircuit.wireCount {n : ℕ}
    (circuit : SymmetricThresholdCircuit n) : ℕ :=
  ∑ i, ((circuit.bottom i).support.card + 1)
</pre>

<pre title="Proof/Foundations/Semantics.lean, lines 64–67">
noncomputable def ThresholdThresholdCircuit.wireCount {n : ℕ}
    (circuit : ThresholdThresholdCircuit n) : ℕ :=
  ∑ i with circuit.topWeight i ≠ 0,
    ((circuit.bottom i).support.card + 1)
</pre>

</td></tr>
<tr><td>
<b>paper/paper.tex, lines 576–582</b>
<pre>
Agreement means

\[
\operatorname{agr}(C,f)
{}={}
\Pr_{x\in\{0,1\}^n}[C(x)=f(x)].
\]
</pre>
</td><td>

[Proof/Foundations/Semantics.lean, lines 69–72](../Proof/Foundations/Semantics.lean#L69-L72)

<pre title="Proof/Foundations/Semantics.lean, lines 69–72">
/-- Uniform agreement on the Boolean cube. -/
noncomputable def agreement {n : ℕ} (left right : BoolFunction n) : ℝ :=
  ((Finset.univ.filter fun input =&gt; left input = right input).card : ℝ) /
    (Fintype.card (BitInput n) : ℝ)
</pre>

</td></tr>
<tr><td>
<b>paper/paper.tex, lines 539–543</b>
<pre>
All logarithms are base two, and

\[
L=L(n)=\lceil\log_2(n+2)\rceil.
\]
</pre>
</td><td>

[Statement.lean, lines 731–732](../Statement.lean#L731-L732)

<pre title="Statement.lean, lines 731–732">
/-- The manuscript's `L(n) = ceil(log₂(n+2))`, computed exactly on naturals. -/
def logScale (n : ℕ) : ℕ := Nat.clog 2 (n + 2)
</pre>

<pre title="Proof/Foundations/Semantics.lean, lines 74–75">
noncomputable def wireScale (coefficient : ℝ) (logExponent n : ℕ) : ℝ :=
  coefficient * (n : ℝ) ^ 3 / (logScale n : ℝ) ^ logExponent
</pre>

</td></tr>
<tr><td>
<b>paper/paper.tex, line 584</b>
<pre>
We use \(E^{NP}=\operatorname{DTIME}(2^{O(n)})^{NP}\).
</pre>
</td><td>

[Proof/Foundations/RecoveryOracleContracts.lean, lines 17–21](../Proof/Foundations/RecoveryOracleContracts.lean#L17-L21)

<pre title="Proof/Foundations/RecoveryOracleContracts.lean, lines 17–21">
/-- Literal ordinary exponential time with an NP oracle. The max convention
only fixes the finite zero-length cost; it changes no asymptotic class. -/
def OrdinaryInENP (language : Language) : Prop :=
  ∃ oracle : ℕ → Bool, Nonempty (EncodedNPVerifier oracle) ∧
    Nonempty (OrdinaryENPCertificate oracle language)
</pre>

<pre title="Statement.lean, lines 1572–1584">
/-- LOCAL NP witness for the actual numeric query predicate. Both ordinary
verifier time and witness length are polynomial in the ENCODED query length.
The input is binary code.bits; no unary numeric-code or prefix-count input. -/
structure EncodedNPVerifier (oracle : ℕ → Bool) where
  verifier : OrdinaryVerifier
  coefficient : ℕ
  coefficientPositive : 1 ≤ coefficient
  degree : ℕ
  correct : ∀ code : ℕ, oracle code = true ↔
    ∃ witness : List Bool,
      witness.length ≤ coefficient * (natBitLength code + 1) ^ degree ∧
      verifier.acceptsAt (coefficient * (natBitLength code + 1) ^ degree)
        code.bits witness
</pre>

<pre title="Statement.lean, lines 1586–1592">
structure OrdinaryENPCertificate (oracle : ℕ → Bool) (language : Language) where
  program : OrdinaryOracleProgram
  exponent : ℕ
  exponentPositive : 1 ≤ exponent
  computes : ∀ n (input : BitInput n),
    OrdinaryOracleRuns oracle program (List.ofFn input) (language n input).toNat.bits
      (2 ^ (exponent * max 1 n))
</pre>

[Statement.lean, lines 1561–1570](../Statement.lean#L1561-L1570)

<pre title="Statement.lean, lines 1561–1570">
/-- Inputs and outputs are framed, with a distinct initially blank output tape.
All data preparation, querying and final head movements inside the program
must be present in the counted trace. -/
def OrdinaryOracleRuns (oracle : ℕ → Bool) (program : OrdinaryOracleProgram)
    (input output : List Bool) (budget : ℕ) : Prop :=
  ∃ cost final, cost ≤ budget ∧
    OrdinaryOracleTrace oracle program cost
      (initialConfiguration program.base.machine (program.base.inputTapes input)) final ∧
    program.base.machine.halted final.control = true ∧
    final.tapes program.base.outputTape = frame output
</pre>

[Statement.lean, line 56](../Statement.lean#L56)

<pre title="Statement.lean, line 56">
def natBitLength (value : ℕ) : ℕ := Nat.log 2 value + 1
</pre>

</td></tr>
</table>

The machine model under `EncodedNPVerifier` and `OrdinaryENPCertificate` (the verifier, the oracle program and their
steps) is shown on page 7.

**What to check** (a few minutes):

1. The quantifier order: γ, then the language and both constants, then the onset, then n, then the circuits.
2. One common language serves both circuit classes (“a common language”).
3. 0 < γ < 1/2, and both constants are positive.
4. “agreement at least” 1/2 + γ is written out as 1/2 + γ ≤ (the number of x with C(x) = F(x)) / 2^n, which is
   `agreement` above.
5. The wire bound is strict: the paper's W(C) > b·n³/L⁵ is Lean's b·n³/L⁵ < W(C).
6. The exponents are n³/L⁵ for SYM∘THR and n³/L⁹ for THR∘THR. L is Mathlib's upper logarithm `Nat.clog` in base 2
   at n + 2, the least k with n + 2 ≤ 2^k, so L = ⌈log₂(n+2)⌉.
7. The circuits: a bottom gate is a threshold gate with real weights whose `support` is exactly its set of
   nonzero-weight inputs (`mem_support_iff`), so zero-weight inputs are deleted as the paper says. The symmetric top is
   an arbitrary function of the number of accepting bottom gates. The threshold top compares a real weighted sum of the
   bottom gates with a real threshold.
8. The wire count is the paper's W(C). For SYM∘THR every bottom gate has a top incidence, so the count is the sum of
   |supp Gᵢ| + 1 over all bottom gates. For THR∘THR the sum skips the bottom gates whose top weight is 0. Lean counts the
   wires of every presentation of a circuit, including one with constant bottom gates, while the paper counts them after
   “constants are propagated”. `headline_iff_prepared` (below) proves that the two readings give the same theorem.
9. E^NP: `OrdinaryInENP` asks for an oracle, a predicate on ℕ with an NP verifier (`EncodedNPVerifier`: witness length
   and verifier time polynomial in the bit length of the query), and for a deterministic oracle program that computes
   the language within 2^(e·max(1, n)) steps (`OrdinaryENPCertificate`). This is DTIME(2^{O(n)}) with an NP oracle. Each
   query costs its framed length plus one step, and max(1, n) only fixes the cost at length 0.

**Documented deviations:** none.

Lean proves two statement checks; you need not read them. The main theorem's conclusion is equivalent to the form the
proof works with, `OrdinaryHeadlineTheorem25`, which names `agreement`, `wireScale` and `wireCount` instead of writing
them out (`theorem_2_5_iff`):

[Proof/Assembly/Final.lean, lines 324–327](../Proof/Assembly/Final.lean#L324-L327)

<pre title="Proof/Foundations/SourceRegistry.lean, lines 33–50">
/-- Literal paper Theorem2.5, with ordinary E^NP membership. The source repair
changes no circuit class, common-language quantifier, strictness or exponent.
This is the target proposition, not a claim that it has been proved. -/
noncomputable def OrdinaryHeadlineTheorem25 : Prop :=
  ∀ fixedAdvantage : ℝ,
    0 &lt; fixedAdvantage → fixedAdvantage &lt; 1 / 2 →
    ∃ language : Language,
    ∃ symmetricCoefficient thresholdCoefficient : ℝ,
      OrdinaryInENP language ∧
      0 &lt; symmetricCoefficient ∧
      0 &lt; thresholdCoefficient ∧
      ∃ onset : ℕ, ∀ n : ℕ, onset ≤ n →
        (∀ circuit : SymmetricThresholdCircuit n,
          1 / 2 + fixedAdvantage ≤ agreement circuit.eval (language n) →
          wireScale symmetricCoefficient 5 n &lt; circuit.wireCount) ∧
        (∀ circuit : ThresholdThresholdCircuit n,
          1 / 2 + fixedAdvantage ≤ agreement circuit.eval (language n) →
          wireScale thresholdCoefficient 9 n &lt; circuit.wireCount)
</pre>

<pre title="Proof/Assembly/Final.lean, lines 324–327">
theorem theorem_2_5_iff : OrdinaryHeadlineTheorem25 ↔ theorem_2_5 := by
  simp only [OrdinaryHeadlineTheorem25, theorem_2_5, OrdinaryInENP, agreement,
    wireScale, logScale, SymmetricThresholdCircuit.wireCount,
    ThresholdThresholdCircuit.wireCount, Finset.sum_filter, ne_eq, ite_not]
</pre>

- The wire count is W(C). `headline_iff_prepared` shows that the theorem is unchanged when it is restricted to prepared
  presentations, with no constant bottom gate and no zero top coefficient. On those, `wireCount` is the paper's W(C).

  [StatementChecks/Theorem2_5_PreparedCircuits.lean, lines 201–219](../StatementChecks/Theorem2_5_PreparedCircuits.lean#L201-L219)

  [StatementChecks/Theorem2_5_PreparedCircuits.lean, lines 40–55](../StatementChecks/Theorem2_5_PreparedCircuits.lean#L40-L55)

- The statement is not trivially true. `constant_language_fails` shows that a constant language violates the wire bound
  at every length n ≥ 1: a symmetric circuit with no bottom gates and a constant top agrees with it everywhere and has
  no wires.

  [StatementChecks/Theorem2_5_Nontrivial.lean, lines 48–68](../StatementChecks/Theorem2_5_Nontrivial.lean#L48-L68)

**Class:** literal.

# 6. PCP: CLW20 Lemmas 3.10 and 3.11

The main theorem assumes the Lean statements in the first rows of the two tables below: `clw310` is CLW20 Lemma 3.10
(the projection PCP, which CLW20 takes from Ben-Sasson and Viola) and `clw311` is CLW20 Lemma 3.11 (the two-query PCP of
proximity, which CLW20 takes from CW19 and VW20). The other rows show every definition those statements use. In the
docstrings, "Tier 1" is the proof's own multitape machine model (the `OrdinaryMachine` section of `Statement.lean`) and "Tier 2" is
Mathlib's standard `Turing.TM2` model. Every algorithm that the two lemmas promise is stated in Tier 2.

Papers:
- L. Chen, X. Lyu, R. R. Williams, "Almost-Everywhere Circuit Lower Bounds from Non-Trivial Derandomization", ECCC
  TR20-150 (2020), https://eccc.weizmann.ac.il/report/2020/150/download/. Page numbers refer to that PDF,
  SHA-256 d760d3b8349b5e4cc118595767069c778315dd18499650a5fcc1870b085bc02c.
- L. Chen, R. R. Williams, "Stronger Connections Between Circuit Analysis and Circuit Lower Bounds, via PCPs of
  Proximity", CCC 2019, https://doi.org/10.4230/LIPIcs.CCC.2019.19. Page numbers refer to that PDF,
  SHA-256 c3c6ea6f80dbdf92a1887272fc2d618a4f63bd887d1cc1186dcf299a3aa99533.
- CLW20's source for Lemma 3.10 is E. Ben-Sasson, E. Viola, "Short PCPs with projection queries", ECCC TR14-017 (2014),
  Theorem 1.1 (PDF p. 3 of the PDF with SHA-256 5e2dba9087704b01e238477b815d9871dc9462f319fc9ddd4f463c5590386d71).

## Lemma 3.10: the projection PCP

<table>
<tr><th>Paper (verbatim)</th><th>Lean (verbatim)</th></tr>
<tr><td>
<b>CLW20, PDF p. 18</b>
<pre>
Lemma 3.10 ([BV14]). Let M be an algorithm running in time T = T(n) ≥ n on inputs of the form (x, y)
where |x| = n. Given x ∈ {0, 1}^n, one can output in poly(n, log T) time circuits Q: {0, 1}^r → {0, 1}^{rt}
for t = poly(r) and R: {0, 1}^t → {0, 1} such that:
• Proof length. 2^r ≤ T · polylogT.
• Completeness. If there is a y ∈ {0, 1}^{T(n)} such that M(x, y) accepts then there is a map π: {0, 1}^r →
{0, 1} such that for all z ∈ {0, 1}^r, R(π(q1), . . . , π(qt)) = 1 where (q1, . . . , qt) = Q(z).
• Soundness. If no y ∈ {0, 1}^{T(n)} causes M(x, y) to accept, then for every map π: {0, 1}^r → {0, 1},
at most 2^r/n^10 distinct z ∈ {0, 1}^r have R(π(q1), . . . , π(qt)) = 1 where (q1, . . . , qt) = Q(z).
• Complexity. Q is a projection, i.e., each output bit of Q is a bit of input, the negation of a bit, or a
constant. R is a 3CNF.
</pre>
</td><td>

[Statement.lean, lines 2067–2070](../Statement.lean#L2067-L2070)

<pre title="Statement.lean, lines 2067–2070">
/-- **CLW20 Lemma 3.10, literal (Tier 2)**: time `T` on every input `(x, y)`, properties for
`n ≥ 1`, the constructor a Mathlib polynomial-time TM2 machine. -/
def CLW20_Lemma3_10_TM2 : Prop :=
  lemma3_10CoreTM2 1 RunsInTime
</pre>

<pre title="Statement.lean, lines 2038–2065">
/-- CLW20 Lemma 3.10 (PDF p.18) with its properties claimed for `n ≥ n₀` and time hypothesis
`runsInTime`, the constructor in Mathlib's TM2 model. The conjuncts follow the printed order, as
in the Tier 1 `lemma3_10Core`. -/
def lemma3_10CoreTM2 (n₀ : ℕ) (runsInTime : OrdinaryVerifier → (ℕ → ℕ) → Prop) : Prop :=
  ∀ (M : OrdinaryVerifier) (T : ℕ → ℕ), (∀ n, n ≤ T n) → runsInTime M T →
  ∃ out : InputRequest → Circuits,
    -- "Given x ∈ {0,1}^n, one can output in poly(n, log T) time circuits Q … and R" (Tier 2;
    -- the time bound T(n) is supplied in binary)
    Nonempty (Turing.TM2ComputableInPolyTime
      (fun x : InputRequest =&gt; frame (List.ofFn x.2) ++ frame (T x.1).bits)
      (fun w : List Bool =&gt; w) (fun x =&gt; (out x).word)) ∧
    -- "for t = poly(r)"
    (∃ K e : ℕ, ∀ x : InputRequest, n₀ ≤ x.1 → (out x).t ≤ K * ((out x).r + 1) ^ e) ∧
    -- "Proof length. 2^r ≤ T · polylogT."
    (∃ K e : ℕ, ∀ x : InputRequest, n₀ ≤ x.1 →
      2 ^ (out x).r ≤ K * T x.1 * logScale (T x.1) ^ e) ∧
    -- "Completeness. If there is a y ∈ {0,1}^{T(n)} such that M(x, y) accepts then there is a
    -- map π: {0,1}^r → {0,1} such that for all z ∈ {0,1}^r, R(π(q1), …, π(qt)) = 1"
    (∀ x : InputRequest, n₀ ≤ x.1 →
      (∃ y : BitInput (T x.1), M.accepts (List.ofFn x.2) (List.ofFn y)) →
      ∃ π : BitInput (out x).r → Bool, ∀ z, (out x).accepts π z = true) ∧
    -- "Soundness. If no y ∈ {0,1}^{T(n)} causes M(x, y) to accept, then for every map π, at most
    -- 2^r/n^10 distinct z ∈ {0,1}^r have R(π(q1), …, π(qt)) = 1"
    (∀ x : InputRequest, n₀ ≤ x.1 →
      (¬ ∃ y : BitInput (T x.1), M.accepts (List.ofFn x.2) (List.ofFn y)) →
      ∀ π : BitInput (out x).r → Bool,
        ((Finset.univ.filter fun z =&gt; (out x).accepts π z = true).card : ℝ) ≤
          (2 : ℝ) ^ (out x).r / (x.1 : ℝ) ^ 10)
</pre>

</td></tr>
<tr><td>
<b>CLW20, PDF p. 18</b>
<pre>
Let M be an algorithm running in time T = T(n) ≥ n on inputs of the form (x, y)
where |x| = n.
</pre>
</td><td>

[Statement.lean, lines 2017–2021](../Statement.lean#L2017-L2021)

<pre title="Statement.lean, lines 2017–2021">
/-- "M … running in time T = T(n) … on inputs of the form (x, y) where |x| = n": on EVERY
`(x, y)`, M halts within `T(n)` steps. -/
def RunsInTime (M : OrdinaryVerifier) (T : ℕ → ℕ) : Prop :=
  ∀ n (x : BitInput n) (y : List Bool), ∃ receipt,
    run M.machine (T n) (M.inputTapes (List.ofFn x) y) = some receipt
</pre>

[Statement.lean, lines 1328–1333](../Statement.lean#L1328-L1333)

<pre title="Statement.lean, lines 1328–1333">
structure Verifier where
  tapeCount : ℕ
  stateCount : ℕ
  twoTapes : 2 ≤ tapeCount
  machine : Machine tapeCount stateCount
  accepting : Fin stateCount → Bool
</pre>

<pre title="Statement.lean, lines 1335–1338">
def Verifier.inputTapes (v : Verifier)
    (input witness : List Bool) : Fin v.tapeCount → List Bool :=
  fun i =&gt; if i.val = 0 then frame input
    else if i.val = 1 then frame witness else []
</pre>

<pre title="Statement.lean, lines 1340–1343">
def Verifier.acceptsAt (v : Verifier) (fuel : ℕ)
    (input witness : List Bool) : Prop :=
  ∃ receipt, run v.machine fuel (v.inputTapes input witness) = some receipt ∧
    v.accepting receipt.final.control = true
</pre>

<pre title="Statement.lean, lines 1345–1346">
def Verifier.accepts (v : Verifier) (input witness : List Bool) : Prop :=
  ∃ fuel, v.acceptsAt fuel input witness
</pre>

</td></tr>
<tr><td>
<b>CLW20, PDF p. 18</b>
<pre>
circuits Q: {0, 1}^r → {0, 1}^{rt}
for t = poly(r) and R: {0, 1}^t → {0, 1}
</pre>
<b>CLW20, PDF p. 18</b>
<pre>
Complexity. Q is a projection, i.e., each output bit of Q is a bit of input, the negation of a bit, or a
constant. R is a 3CNF.
</pre>
</td><td>

[Statement.lean, lines 1986–1994](../Statement.lean#L1986-L1994)

<pre title="Statement.lean, lines 1986–1994">
/-- "circuits Q: {0,1}^r → {0,1}^{rt} … and R: {0,1}^t → {0,1}", described as the Complexity
item says. "Q is a projection, i.e., each output bit of Q is a bit of input, the negation of a
bit, or a constant": `Q k` is that description of output bit `k`, over Q's input `z`.
"R is a 3CNF": `R` is the formula. -/
structure Circuits where
  r : ℕ
  t : ℕ
  Q : Fin (r * t) → ProjectedRandomBit r
  R : ThreeCNF t
</pre>

<pre title="Statement.lean, lines 1978–1984">
/-- Output bit `r·j + i` of `Q : {0,1}^r → {0,1}^{rt}` is bit `i` of `q_j`, where
"(q1, …, qt) = Q(z)". -/
def blockIndex {r t : ℕ} (j : Fin t) (i : Fin r) : Fin (r * t) :=
  ⟨r * j + i,
    calc r * (j : ℕ) + i &lt; r * (j + 1) :=
          (Nat.add_lt_add_left i.isLt _).trans_eq (by rw [Nat.mul_add, Nat.mul_one])
      _ ≤ r * t := Nat.mul_le_mul_left _ j.isLt⟩
</pre>

<pre title="Statement.lean, lines 1996–1998">
/-- `Q(z) ∈ {0,1}^{rt}`. -/
def Circuits.evalQ (P : Circuits) (z : BitInput P.r) : BitInput (P.r * P.t) :=
  fun k =&gt; (P.Q k).eval z
</pre>

<pre title="Statement.lean, lines 2000–2002">
/-- `q_j ∈ {0,1}^r`, where "(q1, …, qt) = Q(z)". -/
def Circuits.query (P : Circuits) (z : BitInput P.r) (j : Fin P.t) : BitInput P.r :=
  fun i =&gt; P.evalQ z (blockIndex j i)
</pre>

<pre title="Statement.lean, lines 2004–2006">
/-- `R(π(q1), …, π(qt))`. -/
def Circuits.accepts (P : Circuits) (π : BitInput P.r → Bool) (z : BitInput P.r) : Bool :=
  P.R.eval fun j =&gt; π (P.query z j)
</pre>

[Statement.lean, lines 993–996](../Statement.lean#L993-L996)

<pre title="Statement.lean, lines 993–996">
inductive ProjectedRandomBit (width : ℕ) where
  | bit (index : Fin width)
  | negatedBit (index : Fin width)
  | constant (value : Bool)
</pre>

<pre title="Statement.lean, lines 998–1003">
def ProjectedRandomBit.eval {width : ℕ} (projection : ProjectedRandomBit width)
    (randomness : BitInput width) : Bool :=
  match projection with
  | .bit index =&gt; randomness index
  | .negatedBit index =&gt; !(randomness index)
  | .constant value =&gt; value
</pre>

[Statement.lean, lines 986–987](../Statement.lean#L986-L987)

<pre title="Statement.lean, lines 976–978">
inductive Literal (arity : ℕ) where
  | positive (index : Fin arity)
  | negative (index : Fin arity)
</pre>

<pre title="Statement.lean, lines 980–984">
def Literal.eval {arity : ℕ} (literal : Literal arity)
    (assignment : BitInput arity) : Bool :=
  match literal with
  | .positive index =&gt; assignment index
  | .negative index =&gt; !(assignment index)
</pre>

<pre title="Statement.lean, lines 986–987">
structure ThreeCNF (arity : ℕ) where
  clauses : List (Fin 3 → Literal arity)
</pre>

<pre title="Statement.lean, lines 989–991">
def ThreeCNF.eval {arity : ℕ} (formula : ThreeCNF arity)
    (assignment : BitInput arity) : Bool :=
  formula.clauses.all fun clause =&gt; ∃ i, (clause i).eval assignment
</pre>

</td></tr>
<tr><td>
<b>CLW20, PDF p. 18</b>
<pre>
Given x ∈ {0, 1}^n, one can output in poly(n, log T) time circuits
</pre>
</td><td>

[Statement.lean, lines 2008–2015](../Statement.lean#L2008-L2015)

<pre title="Statement.lean, lines 2008–2015">
/-- Tier 1 output word: `r`, `t`, the projection code of each of the `r·t` output bits of Q in
order, then R's clauses (the explicit format of the import's `RawProjectionPCP.word`). -/
def Circuits.word (P : Circuits) : List Bool :=
  frame P.r.bits ++ frame P.t.bits ++
  (List.ofFn fun k : Fin (P.r * P.t) =&gt; frame (projectionCode (P.Q k)).bits).flatten ++
  frame P.R.clauses.length.bits ++
  (P.R.clauses.map fun clause =&gt;
    (List.ofFn fun i : Fin 3 =&gt; frame (literalCode (clause i)).bits).flatten).flatten
</pre>

[Statement.lean, line 1412](../Statement.lean#L1412)

<pre title="Statement.lean, line 1412">
abbrev InputRequest := Σ n : ℕ, BitInput n
</pre>

[Statement.lean, lines 1305–1307](../Statement.lean#L1305-L1307)

<pre title="Statement.lean, lines 1305–1307">
def frame : List Bool → List Bool
  | [] =&gt; [false]
  | b :: bs =&gt; true :: b :: frame bs
</pre>

</td></tr>
</table>

Superscripts are written with `^`, with `{…}` around a superscript of more than one symbol: `{0, 1}^{rt}` is
{0, 1}<sup>rt</sup>. The displayed fraction in the soundness item is written `2^r/n^10`.

**What to check** (a few minutes):

1. The order is the paper's: for every M and T such that T(n) ≥ n for every n and M runs in time T, there are circuits
   for each input x (`out`). Each clause has its own constants K and e, chosen after M and T. This is the weakest
   reading of the constants hidden in “poly(n, log T)”, “t = poly(r)” and “polylogT”.
2. “Given x ∈ {0, 1}^n, one can output in poly(n, log T) time circuits” is a Tier 2 machine
   (`Turing.TM2ComputableInPolyTime`). Its input is x framed, followed by T(n) in binary, framed. T is not assumed to be
   time-constructible, so T(n) is supplied, and a polynomial in the length of this input is poly(n, log T). Its output
   is `Circuits.word`: r, t, the code of each of the r·t output bits of Q, then the clauses of R.
3. “t = poly(r)” reads t ≤ K·(r+1)^e. “2^r ≤ T · polylogT” reads 2^r ≤ K·T(n)·L(T(n))^e, where L is `logScale`, the
   paper's ⌈log₂(·+2)⌉ (see the Theorem 2.5 page). With a plain log₂, polylog T would be 0 at T = 1.
4. Completeness and soundness: the proof π is a map from {0,1}^r to `Bool`; q_j is the j-th block of r output bits of
   Q(z) (`Circuits.query`); soundness counts the accepting z and compares the count with 2^r/n^10 in ℝ.
5. The Complexity item holds by the type `Circuits`: Q is a list of r·t projected bits of z (a bit, its negation, or a
   constant), and R is a `ThreeCNF`.
6. The properties are claimed for n ≥ 1: the `1` in `CLW20_Lemma3_10_TM2`.
7. M ranges over the Tier 1 verifiers (`OrdinaryVerifier`, which is `RepairOrdinary.Verifier`). Tape 0 holds x framed,
   tape 1 holds y framed, and “M(x, y) accepts” means that M halts in an accepting state. These machines are
   particular algorithms, so quantifying over them only weakens the assumption. This is why M and its running time
   stay in Tier 1, while the algorithm the lemma promises is in Tier 2.

**Documented deviations:** one, n ≥ 1. At n = 0 the printed soundness bound divides by zero, and
“2^r ≤ T · polylogT” fails when T(0) = 0. `clw20_lemma3_10_false_at_zero` proves that the statement with its
properties also claimed at n = 0 is false. The counterexample is a verifier that halts at once, with T(n) = n. The
theorem is stated for the Tier 1 form; the Tier 2 form implies the Tier 1 form (`core_tier1_of_tier2`), so the Tier 2
form claimed from n = 0 would be false as well. The assumption the main theorem uses is the Tier 2 form claimed from
n = 1 on (`CLW20_Lemma3_10_TM2 := lemma3_10CoreTM2 1 RunsInTime`), shown in the first row above.

[Bindings/CLW20_Lemma3_10.lean, lines 189–191](../Bindings/CLW20_Lemma3_10.lean#L189-L191)

<pre title="Bindings/CLW20_Lemma3_10.lean, lines 189–191">
/-- With the properties claimed at `n = 0` too, the literal is false. -/
theorem clw20_lemma3_10_false_at_zero : ¬ lemma3_10Core 0 RunsInTime :=
  lemma3_10Core_false_at_zero _ haltingVerifier_runsInTime
</pre>

Lean also proves that this statement gives what the proof uses; you need not read it. The printed hypothesis on M
(time T on every input (x, y)) and the hypothesis the proof uses (time T only on witnesses y of length T(n)) give
equivalent lemmas. From the printed form to the proof's form, M is wrapped in a guard machine that rejects as soon as it
reads past a witness of length T(n) (`guard`, `guard_runsInTime`, `guard_accepts_iff`). `tier1_of_tier2` turns the
Tier 2 machine into a Tier 1 machine (through `Bindings/TuringBridge`), and `clw20_lemma3_10_to_import` gives the
imported PCP.

[Bindings/CLW20_Lemma3_10_Wrapper.lean, lines 633–636](../Bindings/CLW20_Lemma3_10_Wrapper.lean#L633-L636)

<pre title="Bindings/CLW20_Lemma3_10_Wrapper.lean, lines 633–636">
/-- The two versions are equivalent. -/
theorem clw20_lemma3_10_iff_onWitnessLengthT :
    CLW20_Lemma3_10 ↔ CLW20_Lemma3_10_onWitnessLengthT :=
  ⟨clw20_lemma3_10_to_onWitnessLengthT, clw20_lemma3_10_onWitnessLengthT_to_literal⟩
</pre>

[Bindings/CLW20_Lemma3_10_TM2.lean, lines 74–76](../Bindings/CLW20_Lemma3_10_TM2.lean#L74-L76)

[Bindings/CLW20_Lemma3_10_Wrapper.lean, lines 629–631](../Bindings/CLW20_Lemma3_10_Wrapper.lean#L629-L631)

## Lemma 3.11: the two-query PCP of proximity

<table>
<tr><th>Paper (verbatim)</th><th>Lean (verbatim)</th></tr>
<tr><td>
<b>CLW20, PDF p. 18</b>
<pre>
Lemma 3.11 ([CW19, VW20]). There are constants 0 &lt; s_pcpp &lt; c_pcpp &lt; 1 and a polynomial-time
transformation that, given a circuit D on n inputs of size m ≥ n, outputs a 2-SAT instance F on the
variable set Y ∪ Z where |Y| ≤ poly(n), |Z| ≤ poly(m), and the following hold for all x ∈ {0, 1}^n:
• If D(x) = 1, then F|Y=Enc(x) on variable set Z has a satisfying assignment Z_x such that at least
c_pcpp-fraction of the clauses are satisfied. Furthermore, there is a poly(m) time algorithm that given
x outputs Z_x.
• If D(x) = 0, then there is no assignment to the Z variables in F|Y=Enc(x) satisfies more than s_pcpp-
fraction of the clauses.
Moreover, the number of clauses in the 2-SAT instance F is a power of 2, and for each i ∈ [|Y|], Enc_i(x)
is a parity function depending on at most n/2 bits of x.
</pre>
</td><td>

[Statement.lean, lines 2490–2491](../Statement.lean#L2490-L2491)

<pre title="Statement.lean, lines 2490–2491">
/-- CLW20 Lemma 3.11 with `n ≥ 2` and the explicit-Enc output (Tier 2), the target form. -/
def CLW20_Lemma3_11_explicitEnc_TM2 : Prop := lemma3_11CoreTM2 2 (fun _ F =&gt; F.formulaEncWord)
</pre>

<pre title="Statement.lean, lines 2463–2488">
/-- CLW20 Lemma 3.11 (PDF p.18) on circuits with at least `n₀` inputs, with the transformation's
output word `outputWord`, the two algorithms in Mathlib's TM2 model. The conjuncts follow the
printed order, as in the Tier 1 `lemma3_11Core`. -/
def lemma3_11CoreTM2 (n₀ : ℕ) (outputWord : (n : ℕ) → Instance n → List Bool) : Prop :=
  ∃ s c : ℝ, 0 &lt; s ∧ s &lt; c ∧ c &lt; 1 ∧
  ∃ F : (C : CircuitFrom n₀) → Instance C.1.n,
    -- "a polynomial-time transformation that, given a circuit D …, outputs … F" (Tier 2)
    Nonempty (Turing.TM2ComputableInPolyTime (fun C : CircuitFrom n₀ =&gt; C.1.word)
      (fun w : List Bool =&gt; w) (fun C =&gt; outputWord C.1.n (F C))) ∧
    -- "|Y| ≤ poly(n)"
    (∃ K e : ℕ, ∀ C, (F C).Ybits ≤ K * (C.1.n + 1) ^ e) ∧
    -- "|Z| ≤ poly(m)"
    (∃ K e : ℕ, ∀ C, (F C).Zbits ≤ K * (C.1.m + 1) ^ e) ∧
    ∃ Zx : (C : CircuitFrom n₀) → BitInput C.1.n → BitInput (F C).Zbits,
      -- "If D(x) = 1, then F|Y=Enc(x) … has … Z_x such that at least c-fraction of the clauses
      -- are satisfied."
      (∀ C x, C.1.D.eval x = true → (F C).fraction x (Zx C x) ≥ c) ∧
      -- "there is a poly(m) time algorithm that given x outputs Z_x" (Tier 2)
      Nonempty (Turing.TM2ComputableInPolyTime
        (fun p : (Σ C : CircuitFrom n₀, BitInput C.1.n) =&gt; p.1.1.word ++ List.ofFn p.2)
        (fun w : List Bool =&gt; w) (fun p =&gt; List.ofFn (Zx p.1 p.2))) ∧
      -- "If D(x) = 0, then there is no assignment to the Z variables in F|Y=Enc(x) [that]
      -- satisfies more than s-fraction of the clauses."
      (∀ C x, C.1.D.eval x = false → ∀ z, (F C).fraction x z ≤ s) ∧
      -- "for each i ∈ [|Y|], Enc_i(x) is a parity function depending on at most n/2 bits of x"
      (∀ C i, ((F C).encSupport i).card ≤ C.1.n / 2)
</pre>

</td></tr>
<tr><td>
<b>CLW20, PDF p. 18</b>
<pre>
given a circuit D on n inputs of size m ≥ n
</pre>
</td><td>

[Statement.lean, lines 2115–2119](../Statement.lean#L2115-L2119)

<pre title="Statement.lean, lines 2115–2119">
/-- "a circuit D on n inputs of size m ≥ n". -/
structure Circuit where
  n : ℕ
  D : BooleanCircuit n
  sizeAtLeast : n ≤ D.size
</pre>

<pre title="Statement.lean, lines 2121–2122">
/-- The size `m` of `D`: its number of nodes. -/
def Circuit.m (C : Circuit) : ℕ := C.D.size
</pre>

<pre title="Statement.lean, lines 2124–2125">
/-- The circuits the lemma is read on: those with at least `n₀` inputs. -/
abbrev CircuitFrom (n₀ : ℕ) := {C : Circuit // n₀ ≤ C.n}
</pre>

<pre title="Statement.lean, lines 2127–2129">
/-- Tier 1: the circuit as the transformation reads it (the import's `pcppInput` layout). -/
def Circuit.word (C : Circuit) : List Bool :=
  natWord C.n ++ (encodeBooleanCircuit C.D).bits
</pre>

[Statement.lean, lines 689–697](../Statement.lean#L689-L697)

<pre title="Statement.lean, lines 660–669">
/-- One node in a topologically ordered fan-in-two Boolean DAG.  Child
references are natural-number node addresses; `BooleanCircuit.wellFormed`
requires every child to precede the node that uses it. -/
inductive BooleanNode (n : ℕ) where
  | const (value : Bool)
  | input (index : Fin n)
  | not (child : ℕ)
  | and (left right : ℕ)
  | or (left right : ℕ)
  deriving Repr
</pre>

<pre title="Statement.lean, lines 671–677">
def BooleanNode.WellFormedAt {n : ℕ} (index : ℕ) :
    BooleanNode n → Prop
  | .const _ =&gt; True
  | .input _ =&gt; True
  | .not child =&gt; child &lt; index
  | .and left right =&gt; left &lt; index ∧ right &lt; index
  | .or left right =&gt; left &lt; index ∧ right &lt; index
</pre>

<pre title="Statement.lean, lines 679–687">
def BooleanNode.eval {n : ℕ} (input : BitInput n)
    (prior : Array Bool) : BooleanNode n → Bool
  | .const value =&gt; value
  | .input index =&gt; input index
  | .not child =&gt; !(prior[child]?.getD false)
  | .and left right =&gt;
      prior[left]?.getD false &amp;&amp; prior[right]?.getD false
  | .or left right =&gt;
      prior[left]?.getD false || prior[right]?.getD false
</pre>

<pre title="Statement.lean, lines 689–697">
/-- Ordinary Boolean circuits are finite DAGs with a topological node order.
Gate count—not formula-tree unfolding—is the source theorem's size measure. -/
structure BooleanCircuit (n : ℕ) where
  nodes : List (BooleanNode n)
  output : Fin nodes.length
  wellFormed :
    ∀ index : Fin nodes.length,
      (nodes.get index).WellFormedAt index.val
  deriving Repr
</pre>

<pre title="Statement.lean, lines 699–702">
def BooleanCircuit.values {n : ℕ} (circuit : BooleanCircuit n)
    (input : BitInput n) : Array Bool :=
  circuit.nodes.foldl
    (fun prior node =&gt; prior.push (node.eval input prior)) #[]
</pre>

<pre title="Statement.lean, lines 704–706">
def BooleanCircuit.eval {n : ℕ} (circuit : BooleanCircuit n)
    (input : BitInput n) : Bool :=
  (circuit.values input)[circuit.output.val]?.getD false
</pre>

<pre title="Statement.lean, lines 708–709">
def BooleanCircuit.size {n : ℕ} (circuit : BooleanCircuit n) : ℕ :=
  circuit.nodes.length
</pre>

</td></tr>
<tr><td>
<b>CLW20, PDF p. 18</b>
<pre>
outputs a 2-SAT instance F on the
variable set Y ∪ Z
</pre>
<b>CLW20, PDF p. 18</b>
<pre>
Moreover, the number of clauses in the 2-SAT instance F is a power of 2, and for each i ∈ [|Y|], Enc_i(x)
is a parity function depending on at most n/2 bits of x.
</pre>
</td><td>

[Statement.lean, lines 2131–2141](../Statement.lean#L2131-L2141)

<pre title="Statement.lean, lines 2131–2141">
/-- "a 2-SAT instance F on the variable set Y ∪ Z", together with `Enc`.
`Ybits = |Y|` and `Zbits = |Z|`, and the Y variables are the indices below `|Y|`.
"the number of clauses in the 2-SAT instance F is a power of 2": there are `2 ^ clauseBits`
clauses, and each one is an OR of two literals.
"Enc_i(x) is a parity function": `Enc_i(x)` is the XOR of `x` over `encSupport i`. -/
structure Instance (n : ℕ) where
  Ybits : ℕ
  Zbits : ℕ
  clauseBits : ℕ
  clauses : Fin (2 ^ clauseBits) → TwoLiteralClause (Ybits + Zbits)
  encSupport : Fin Ybits → Finset (Fin n)
</pre>

<pre title="Statement.lean, lines 2143–2145">
/-- `Enc(x) ∈ {0,1}^|Y|`, with `Enc_i(x) = ⊕_{j ∈ encSupport i} x_j`. -/
noncomputable def Instance.enc {n : ℕ} (F : Instance n) (x : BitInput n) : BitInput F.Ybits :=
  fun i =&gt; parityOn (F.encSupport i) x
</pre>

<pre title="Statement.lean, lines 2147–2150">
/-- The assignment behind "F|Y=Enc(x)" with the Z variables set to `z`. -/
noncomputable def Instance.restrict {n : ℕ} (F : Instance n) (x : BitInput n)
    (z : BitInput F.Zbits) : BitInput (F.Ybits + F.Zbits) :=
  Fin.addCases (F.enc x) z
</pre>

<pre title="Statement.lean, lines 2152–2156">
/-- The fraction of the clauses of `F|Y=Enc(x)` that the Z-assignment `z` satisfies. -/
noncomputable def Instance.fraction {n : ℕ} (F : Instance n) (x : BitInput n)
    (z : BitInput F.Zbits) : ℝ :=
  ((Finset.univ.filter fun i =&gt; (F.clauses i).eval (F.restrict x z)).card : ℝ) /
    (2 ^ F.clauseBits : ℝ)
</pre>

[Statement.lean, lines 1013–1015](../Statement.lean#L1013-L1015)

<pre title="Statement.lean, lines 1013–1015">
noncomputable def parityOn {n : ℕ} (support : Finset (Fin n))
    (input : BitInput n) : Bool :=
  support.toList.foldl (fun parity i =&gt; xor parity (input i)) false
</pre>

[Statement.lean, lines 1005–1007](../Statement.lean#L1005-L1007)

<pre title="Statement.lean, lines 1005–1007">
structure TwoLiteralClause (arity : ℕ) where
  left : Literal arity
  right : Literal arity
</pre>

<pre title="Statement.lean, lines 1009–1011">
def TwoLiteralClause.eval {arity : ℕ} (clause : TwoLiteralClause arity)
    (assignment : BitInput arity) : Bool :=
  clause.left.eval assignment || clause.right.eval assignment
</pre>

</td></tr>
</table>

Subscripts are written with `_` (`s_pcpp` is s<sub>pcpp</sub>), and the restriction bar is written `F|Y=Enc(x)`.

**What to check** (a few minutes):

1. The order is the paper's: first the constants s and c with 0 < s < c < 1, then the transformation F (one instance
   for each circuit), then the polynomial bounds. Each bound has its own constants K and e, chosen after F: the weakest
   reading of the hidden constants.
2. The transformation is a Tier 2 machine (`Turing.TM2ComputableInPolyTime`) from the circuit's word (`Circuit.word`:
   n, then the repository's canonical code of D) to the instance's word. Its time is polynomial in the input length.
3. |Y| ≤ K·(n+1)^e and |Z| ≤ K·(m+1)^e, where m is the number of nodes of D (`Circuit.m`).
4. Completeness: if D(x) = 1, then Z_x satisfies at least a c fraction of the clauses. `Instance.fraction` sets the Y
   variables to Enc(x) and the Z variables to z, counts the satisfied clauses, and divides by their number.
5. “there is a poly(m) time algorithm that given x outputs Z_x” is one Tier 2 polynomial-time machine on pairs (D, x),
   the same machine for every D. If the algorithm could depend on D, the clause would say nothing, because a machine
   built for one D computes any function of x by table lookup. Its input has length at most K·(m+1)^10
   (`zxInput_length_le`), so a polynomial in the input length is a polynomial in m.
6. Soundness: if D(x) = 0, every z satisfies at most an s fraction of the clauses.
7. “Moreover”: there are 2^k clauses for some k (`clauseBits`, part of the type `Instance`). Enc_i(x) is the parity of x
   on the set `encSupport i`, which has at most n/2 elements (division in ℕ, so ⌊n/2⌋). Enc may depend on D, because the
   sentence does not fix Enc before D.

**Documented deviations:** two.

*First: n ≥ 2 instead of every n.* The printed lemma is false at n = 1. Take D(x) = x₁. Each Enc_i depends on at most
⌊1/2⌋ = 0 bits, so Enc is constant, and F|Y=Enc(x) is the same instance for x = 0 and x = 1. Completeness at x = 1 then
contradicts soundness at x = 0, because s < c. Lean proves this for the lemma as printed (in Tier 1), and for the Tier 2
form with either output word.

[Bindings/CLW20_Lemma3_11.lean, lines 220–222](../Bindings/CLW20_Lemma3_11.lean#L220-L222)

<pre title="Bindings/CLW20_Lemma3_11.lean, lines 152–154">
/-- **(a)** CLW20 Lemma 3.11 as printed (PDF p.18), for every `n ≥ 1`. The output is `F`. -/
def CLW20_Lemma3_11_asPrinted : Prop :=
  lemma3_11Core 1 (fun _ F =&gt; F.formulaWord)
</pre>

<pre title="Bindings/CLW20_Lemma3_11.lean, lines 220–222">
/-- **(b)** CLW20 Lemma 3.11 as printed is false (at `n = 1`, `D(x) = x₁`). -/
theorem clw20_lemma3_11_asPrinted_false : ¬ CLW20_Lemma3_11_asPrinted :=
  lemma3_11Core_false_at_one _
</pre>

[Bindings/CLW20_Lemma3_11_TM2.lean, lines 134–138](../Bindings/CLW20_Lemma3_11_TM2.lean#L134-L138)

<pre title="Bindings/CLW20_Lemma3_11_TM2.lean, lines 134–138">
/-- As in Tier 1, the statement on circuits with `n ≥ 1` inputs is false, for every output
format (the counterexample `D(x) = x₁` does not involve the algorithms). -/
theorem lemma3_11CoreTM2_false_at_one (outputWord : (n : ℕ) → Instance n → List Bool) :
    ¬ lemma3_11CoreTM2 1 outputWord :=
  fun h =&gt; lemma3_11Core_false_at_one outputWord (core_tier1_of_tier2 1 outputWord h)
</pre>

CW19 Lemma 27 supports the fix n ≥ 2. CW19 is one of the two papers CLW20 cites for Lemma 3.11, and its Lemma 27 builds
a code with the same “at most n/2 bits” property. In that construction each codeword bit depends on at most ⌈n/3⌉ input
bits, and ⌈n/3⌉ ≤ ⌊n/2⌋ exactly when n ≥ 2 or n = 0:

<table>
<tr><th>Paper (verbatim)</th><th>Lean (verbatim)</th></tr>
<tr><td>
<b>CW19, PDF p. 16</b>
<pre>
Lemma 27. There is a constant δ &gt; 0 such that there is a constant-rate linear error
correcting code ECC with minimum relative distance δ, an efficient encoder Enc and an
efficient decoder Dec recovering error up to c1 · δ, where c1 is a universal constant. Moreover,
each bit of the codeword depends on at most n/2 bits of the input.
Proof. Given a message x ∈ {0, 1}^n, we split it into three parts x1, x2, x3, each of length
between ⌊n/3⌋ and ⌈n/3⌉. Let Enc′ and Dec′ be the corresponding encoder and decoder of
Lemma 26.
We construct our new error correcting code by setting Enc(x) := Enc′(x1) ◦ Enc′(x2) ◦
Enc′(x3).
</pre>
</td><td>

[Bindings/CLW20_Lemma3_11.lean, lines 230–233](../Bindings/CLW20_Lemma3_11.lean#L230-L233)

<pre title="Bindings/CLW20_Lemma3_11.lean, lines 230–233">
/-- CW19 Lemma 27's split supports `n ≥ 2`: a third, rounded up, is at most a half, rounded
down, for every `n ≥ 2` (and `n = 0`). At `n = 1` it fails (`1 &gt; 0`). -/
theorem ceil_third_le_floor_half (n : ℕ) : (n + 2) / 3 ≤ n / 2 ↔ 2 ≤ n ∨ n = 0 := by
  omega
</pre>

</td></tr>
</table>

*Second: the encoder is written out.* The printed transformation “outputs a 2-SAT instance F” (`Instance.formulaWord`).
The hypothesis asks it to output the support of every Enc_i as well (`Instance.formulaEncWord`), because the proof needs
the supports and they cannot be recovered from F. The papers support the addition: CLW20's own algorithm enumerates the
bits that Enc_s depends on, and CW19's encoder is linear and efficient. A linear code with an efficient encoder has
computable supports: j is in the support of Enc_i exactly when bit i of Enc(e_j) is 1. Lean does not derive this
addition from the printed lemma; it rests on the sentences below.

<table>
<tr><th>Paper (verbatim)</th><th>Lean (verbatim)</th></tr>
<tr><td>
<b>CLW20, PDF p. 28</b>
<pre>
Recall that Enc : {0, 1}^ℓ → {0, 1}^{|Y|} is the fixed F2-linear error correcting code
used in Lemma 3.11.
</pre>
<b>CLW20, PDF p. 29</b>
<pre>
Enc_s(x) depends on at most ℓ/2 bits (the moreover part
of Lemma 3.11). We can then enumerate all these bits
</pre>
<b>CW19, PDF p. 16</b>
<pre>
an efficient encoder Enc
</pre>
</td><td>

[Bindings/CLW20_Lemma3_11.lean, lines 113–118](../Bindings/CLW20_Lemma3_11.lean#L113-L118)

<pre title="Bindings/CLW20_Lemma3_11.lean, lines 113–118">
/-- Tier 1 output word of the literal: `F` alone (the counts, then every clause as two literal
indices). -/
def Instance.formulaWord {n : ℕ} (F : Instance n) : List Bool :=
  natListWord [F.Ybits, F.Zbits, F.clauseBits] ++
    natListWord ((List.ofFn fun i : Fin (2 ^ F.clauseBits) =&gt;
      [literalIndex (F.clauses i).left, literalIndex (F.clauses i).right]).flatten)
</pre>

<pre title="Statement.lean, lines 2158–2165">
/-- Tier 1 output word of the explicit-Enc reading: `F` with the support of every `Enc_i`
listed between the counts and the clauses (the import's `pcppOutput` layout). -/
def Instance.formulaEncWord {n : ℕ} (F : Instance n) : List Bool :=
  natListWord [F.Ybits, F.Zbits, F.clauseBits] ++
    (List.ofFn (fun i : Fin F.Ybits =&gt;
      List.ofFn (fun j : Fin n =&gt; decide (j ∈ F.encSupport i)))).flatten ++
    natListWord ((List.ofFn fun i : Fin (2 ^ F.clauseBits) =&gt;
      [literalIndex (F.clauses i).left, literalIndex (F.clauses i).right]).flatten)
</pre>

</td></tr>
</table>

Lean also proves that this statement gives what the proof uses (`clw20_lemma3_11_explicitEnc_tm2_to_import`); you need
not read it.

[Bindings/CLW20_Lemma3_11_TM2.lean, lines 129–132](../Bindings/CLW20_Lemma3_11_TM2.lean#L129-L132)

**Class:** Lemma 3.10 is literal, with its algorithm in Tier 2 (the verifier M it quantifies over stays in Tier 1).
Lemma 3.11 is literal + documented fix (n ≥ 2, and the encoder written out), with both of its algorithms in Tier 2.

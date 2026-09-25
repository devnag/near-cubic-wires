# 8. Amplifier: CLW20 Lemma 3.9 (STV01 Theorem 24)

The main theorem assumes the Lean statement in the first row of the table below (`clw39`). It is CLW20 Lemma 3.9,
worst-case to average-case hardness amplification, which CLW20 takes from Sudan, Trevisan and Vadhan (STV01, Theorem 24).
The other rows show every definition that statement uses. In the docstrings, "Tier 1" is the proof's own multitape
machine model (the `OrdinaryMachine` section of `Statement.lean`) and "Tier 2" is Mathlib's standard `Turing.TM2` model. The algorithm
the lemma promises is stated in Tier 2 (`Turing.TM2ComputableInTime`).

Papers:
- L. Chen, X. Lyu, R. R. Williams, "Almost-Everywhere Circuit Lower Bounds from Non-Trivial Derandomization", ECCC
  TR20-150 (2020), https://eccc.weizmann.ac.il/report/2020/150/download/. Page numbers refer to that PDF,
  SHA-256 d760d3b8349b5e4cc118595767069c778315dd18499650a5fcc1870b085bc02c.
- (STV01) M. Sudan, L. Trevisan, S. Vadhan, "Pseudorandom Generators without the XOR Lemma", Journal of Computer and
  System Sciences 62 (2001) 236–266, https://doi.org/10.1006/jcss.2000.1730. Page numbers refer to that PDF,
  SHA-256 5517c11166fd93a05e6fddcb9f986b8d1b7ac103925a843d366e16568fdb1e94. Its text layer garbles the symbols, so its
  quotations were checked against the page image.

<table>
<tr><th>Paper (verbatim)</th><th>Lean (verbatim)</th></tr>
<tr><td>
<b>CLW20, PDF p. 18</b>
<pre>
Lemma 3.9 ([STV01]). There is a constant c ≥ 1 such that, for any time-constructible function S(n)
and every f : {0, 1}^n → {0, 1} that does not have (general) circuits of size S(n). There is a function
g : {0, 1}^{O(n)} → {0, 1} that cannot be (1/2 + S(n)^{−1/c})-approximated by circuits of size S(n)^{1/c}. Furthermore,
given the 2^n-length truth table of f, the truth table of g can be constructed in 2^{O(n)}
time.
</pre>
</td><td>

[Statement.lean, lines 2218–2221](../Statement.lean#L2218-L2221)

<pre title="Statement.lean, lines 2218–2221">
/-- **CLW20 Lemma 3.9, literal (Tier 2).** "There is a constant c ≥ 1 such that, for any
time-constructible function S(n) and every f ..." -/
def CLW20_Lemma3_9_TM2 : Prop :=
  ∃ c : ℝ, 1 ≤ c ∧ ∀ S : ℕ → ℕ, TimeConstructible S → Nonempty (Lemma3_9AtTM2 c S)
</pre>

<pre title="Statement.lean, lines 2198–2216">
/-- What the sentence asserts for one constant `c` and one time-constructible `S` (Tier 2). All
fields but `construction` are those of the Tier 1 `Lemma3_9At`. -/
structure Lemma3_9AtTM2 (c : ℝ) (S : ℕ → ℕ) where
  /-- `g` for the input `f` on `n` bits. -/
  g : (n : ℕ) → BoolFunction n → AmplifierOutput
  /-- The hidden constant of `O(n)`. -/
  arityFactor : ℕ
  /-- The hidden onset of `O(n)`. -/
  arityOnset : ℕ
  /-- "every f ... that does not have (general) circuits of size S(n). There is a function
  g : {0,1}^{O(n)} → {0,1} that cannot be (1/2 + S(n)^{−1/c})-approximated by circuits of size
  S(n)^{1/c}." -/
  amplifies : ∀ (n : ℕ) (f : BoolFunction n), ¬ HasCircuitOfSize f (S n) →
    (arityOnset ≤ n → (g n f).arity ≤ arityFactor * n) ∧
    CannotBeApproximated (g n f).function
      ((S n : ℝ) ^ (-(1 : ℝ) / c)) ((S n : ℝ) ^ ((1 : ℝ) / c))
  /-- "Furthermore, given the 2^n-length truth table of f, the truth table of g can be
  constructed in 2^{O(n)} time." (Tier 2: Mathlib's TM2 model.) -/
  construction : TruthTableConstructionTM2 g
</pre>

</td></tr>
<tr><td>
<b>CLW20, PDF p. 18</b>
<pre>
g : {0, 1}^{O(n)} → {0, 1} that cannot be (1/2 + S(n)^{−1/c})-approximated by circuits of size S(n)^{1/c}
</pre>
<b>CLW20, PDF p. 3</b>
<pre>
We say
that a function f : {0, 1}^n → {0, 1} cannot be (1/2 + ε)-approximated by circuits of type C, if every circuit
from C computes f correctly on less than (1/2 + ε)2^n of the n-bit inputs.
</pre>
</td><td>

[Statement.lean, lines 2092–2097](../Statement.lean#L2092-L2097)

<pre title="Statement.lean, lines 2092–2097">
/-- CLW20 PDF p.3: "cannot be (1/2 + ε)-approximated by circuits of type C, if every circuit from
C computes f correctly on less than (1/2 + ε)2^n of the n-bit inputs", with "circuits of size s"
read as size at most `s` (PDF p.17). -/
def CannotBeApproximated {m : ℕ} (g : BoolFunction m) (ε s : ℝ) : Prop :=
  ∀ circuit : BooleanCircuit m, (circuit.size : ℝ) ≤ s →
    ((Finset.univ.filter fun x =&gt; circuit.eval x = g x).card : ℝ) &lt; (1 / 2 + ε) * 2 ^ m
</pre>

</td></tr>
<tr><td>
<b>CLW20, PDF p. 18</b>
<pre>
every f : {0, 1}^n → {0, 1} that does not have (general) circuits of size S(n)
</pre>
<b>CLW20, PDF p. 17</b> (Lemma 3.6)
<pre>
(general) circuits of size s. That is, for all circuit C of size at most s
</pre>
</td><td>

[Statement.lean, lines 2088–2090](../Statement.lean#L2088-L2090)

<pre title="Statement.lean, lines 2088–2090">
/-- "f ... has (general) circuits of size s": some circuit of size at most `s` computes `f`. -/
def HasCircuitOfSize {n : ℕ} (f : BoolFunction n) (s : ℕ) : Prop :=
  ∃ circuit : BooleanCircuit n, circuit.size ≤ s ∧ ∀ x, circuit.eval x = f x
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
given the 2^n-length truth table of f, the truth table of g can be constructed in 2^{O(n)}
time
</pre>
<b>STV01, PDF p. 21</b> (checked against the page image)
<pre>
Moreover, P′ can be evaluated in time 2^{O(ℓ)} with access to the entire truth table of P.
</pre>
</td><td>

[Statement.lean, lines 2186–2196](../Statement.lean#L2186-L2196)

<pre title="Statement.lean, lines 2186–2196">
/-- TIER 2 ALGORITHMIC CLAUSE. "given the 2^n-length truth table of f, the truth table of g can
be constructed in 2^{O(n)} time": a Mathlib `TM2ComputableInTime` machine from the truth table of
`f` (with its framed arity) to the truth table of `g` (with its framed arity), whose step bound
is at most `2^(timeExponent · n)` from the onset `timeOnset` on. -/
structure TruthTableConstructionTM2 (g : (n : ℕ) → BoolFunction n → AmplifierOutput) where
  machine : Turing.TM2ComputableInTime amplifierInput amplifierOutputWord
    (fun request : AmplifierRequest =&gt; g request.inputArity request.function)
  timeExponent : ℕ
  timeOnset : ℕ
  exponentialTime : ∀ request : AmplifierRequest, timeOnset ≤ request.inputArity →
    machine.time (amplifierInput request).length ≤ 2 ^ (timeExponent * request.inputArity)
</pre>

<pre title="Statement.lean, lines 2182–2184">
/-- The output word: the framed arity of `g`, then the full truth table of `g`. -/
def amplifierOutputWord (o : AmplifierOutput) : List Bool :=
  RepairOrdinary.frame o.arity.bits ++ boolFunctionTable o.function
</pre>

[Statement.lean, lines 1678–1680](../Statement.lean#L1678-L1680)

<pre title="Statement.lean, lines 1678–1680">
/-- The outer ordinary carrier additionally frames this complete payload. -/
def amplifierInput (request : AmplifierRequest) : List Bool :=
  RepairOrdinary.frame request.inputArity.bits ++ boolFunctionTable request.function
</pre>

<pre title="Statement.lean, lines 1674–1676">
structure AmplifierOutput where
  arity : ℕ
  function : BoolFunction arity
</pre>

[Statement.lean, lines 1084–1086](../Statement.lean#L1084-L1086)

<pre title="Statement.lean, lines 1084–1086">
structure AmplifierRequest where
  inputArity : ℕ
  function : BoolFunction inputArity
</pre>

<pre title="Statement.lean, lines 1061–1063">
def boolFunctionTable {n : ℕ} (function : BoolFunction n) : List Bool :=
  (List.range (2 ^ n)).map fun code =&gt;
    function fun index =&gt; code.testBit index.val
</pre>

</td></tr>
<tr><td>
<b>CLW20, PDF p. 18</b>
<pre>
for any time-constructible function S(n)
</pre>
</td><td>

[Statement.lean, lines 1017–1042](../Statement.lean#L1017-L1042)

<pre title="Statement.lean, lines 1017–1042">
structure TimeConstructible (bound : ℕ → ℕ) where
  program : NPOracleProgram
  coefficient : ℕ
  coefficientPositive : 0 &lt; coefficient
  oracleFree : program.all (fun instruction =&gt; match instruction with
    | .halt _ =&gt; true
    | .set _ _ _ =&gt; true
    | .copy _ _ _ =&gt; true
    | .increment _ _ =&gt; true
    | .decrement _ _ =&gt; true
    | .add _ _ _ _ =&gt; true
    | .subtract _ _ _ _ =&gt; true
    | .pair _ _ _ _ =&gt; true
    | .unpairLeft _ _ _ =&gt; true
    | .unpairRight _ _ _ =&gt; true
    | .branchZero _ _ _ =&gt; true
    | .encodeNat _ _ _ =&gt; true
    | .shiftRight _ _ _ _ =&gt; true
    | .shiftLeft _ _ _ _ =&gt; true
    | .testBit _ _ _ _ =&gt; true
    | .sat _ _ _ =&gt; false
    ) = true
  computesBound : ∀ n,
    runNPOracleProgram program (coefficient * (bound n + 1))
      (coefficient * (bound n + 1))
      (initialNPOracleState n n) = some (bound n)
</pre>

</td></tr>
</table>

Superscripts are written with `^`, with `{…}` around a superscript of more than one symbol: `S(n)^{1/c}` is
S(n)<sup>1/c</sup>.

The result CLW20 cites begins as follows; its hypothesis on P is the same worst-case hardness:

<b>STV01, PDF p. 20</b> (checked against the page image)
<pre>
Theorem 24. Let 𝒞 be a nice family of binary codes. Then there exists a constant
c such that the following is true. Let P: {0, 1}^ℓ → {0, 1} be a function such that no
circuit of size s computes P.
</pre>

**What to check** (a few minutes):

1. The order is the paper's: “There is a constant c ≥ 1” comes first, so one real number c serves every S. Then comes
   every time-constructible S. Everything the sentence does not state explicitly after that may depend on S: the function g, the
   constant and onset of O(n), the algorithm, and the constant and onset of 2^{O(n)}.
2. “does not have (general) circuits of size S(n)”: no circuit with at most S(n) nodes computes f on every input
   (`HasCircuitOfSize`, read with “size at most s” as on PDF p. 17).
3. Inapproximability: every circuit with at most S(n)^{1/c} nodes is correct on strictly fewer than
   (1/2 + S(n)^{−1/c})·2^m of the m-bit inputs. This is the PDF p. 3 definition, strict as printed. The powers are real
   powers (`Real.rpow`).
4. “g : {0, 1}^{O(n)} → {0, 1}”: for the hard f that the sentence speaks about, the arity of g is at most
   `arityFactor`·n once n ≥ `arityOnset`.
5. The algorithm is one Tier 2 machine (`Turing.TM2ComputableInTime`) from n and the truth table of f to the arity of g
   and the truth table of g. Its step bound is at most 2^(`timeExponent`·n) once n ≥ `timeOnset`. It runs on every
   truth table, and hardness is claimed only for hard f. STV01's P′ is likewise defined for every P and evaluated
   “with access to the entire truth table of P”.
6. Circuit size: CLW20 does not define it. The transcription counts nodes, input nodes included
   (`BooleanCircuit.size`). A gate count differs from it by at most the n input nodes and two constants, and for large
   S(n) the constant c absorbs the difference.
7. “time-constructible” is on the input side of the lemma, so it stays in Tier 1: `SourceInterfaces.TimeConstructible`
   is a register program without oracle calls that returns S(n) from n within K·(S(n)+1) steps and K·(S(n)+1) register
   bits. CLW20 uses the standard notion without defining it. The two agree up to polynomial overhead, and the lemma
   uses the hypothesis only so that its algorithm can learn S(n).

Items 6 and 7 read terms that CLW20 does not define. Lean does not check these two readings.

**Documented deviations:** none.

Lean also proves that this statement gives what the proof uses (`clw20_lemma3_9_tm2_to_import`); you need not read it.
The Tier 2 machine becomes a Tier 1 machine through the bridge `tm2ToOrdinary`, at linear overhead;
`tm2ToOrdinaryOutputFree` removes the output length from the budget, and `tier1_of_tier2` applies it to this lemma. The
adapter rounds c up to an integer and uses the proof's fixed hardness schedule for S.

[Bindings/TuringBridge/Bridge.lean, lines 141–159](../Bindings/TuringBridge/Bridge.lean#L141-L159)

[Bindings/TuringBridge/OutputFree.lean, lines 135–144](../Bindings/TuringBridge/OutputFree.lean#L135-L144)

[Bindings/CLW20_Lemma3_9_TM2.lean, lines 108–111](../Bindings/CLW20_Lemma3_9_TM2.lean#L108-L111)

[Bindings/CLW20_Lemma3_9_TM2.lean, lines 113–115](../Bindings/CLW20_Lemma3_9_TM2.lean#L113-L115)

**Class:** literal, with its algorithm in Tier 2 (the hypothesis “time-constructible function S(n)” stays in Tier 1).

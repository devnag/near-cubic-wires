# 7. Refuter: CLW20 Theorem 1.13

The main theorem assumes the Lean statement in the first row of the table below (`clw113`). It is CLW20 Theorem 1.13, a
refuter with an NP oracle for the almost-everywhere nondeterministic time hierarchy of Fortnow and Santhanam. The other
rows show every definition that statement uses. In the docstrings, "Tier 1" is the proof's own multitape machine model
(the `OrdinaryMachine` section of `Statement.lean`) and "Tier 2" is Mathlib's standard `Turing.TM2` model; this statement is read in
Tier 1. The group's other result, CLW20 Lemma 3.8 (the XOR lemma, PDF p. 17), is not assumed: `clw20_xor_source` proves
it in Lean, following the paper's proof in CLW20 Appendix A.

[Bindings/CLW20_Lemma3_8.lean, lines 73–76](../Bindings/CLW20_Lemma3_8.lean#L73-L76)

Papers:
- L. Chen, X. Lyu, R. R. Williams, "Almost-Everywhere Circuit Lower Bounds from Non-Trivial Derandomization", ECCC
  TR20-150 (2020), https://eccc.weizmann.ac.il/report/2020/150/download/. Page numbers refer to that PDF,
  SHA-256 d760d3b8349b5e4cc118595767069c778315dd18499650a5fcc1870b085bc02c.
- L. Fortnow, R. Santhanam, "New Non-Uniform Lower Bounds for Uniform Classes", CCC 2016,
  https://doi.org/10.4230/LIPIcs.CCC.2016.19. Page numbers refer to that PDF,
  SHA-256 04c27d5f5641fa236119825d40c29ff9d7ef7cb192ce8002a05e7b27f6e00dcb.

<table>
<tr><th>Paper (verbatim)</th><th>Lean (verbatim)</th></tr>
<tr><td>
<b>CLW20, PDF p. 6</b>
<pre>
Theorem 1.13 (Refuter with an NP Oracle, Informal). For every time-constructible function T(n) such that
n ≤ T(n) ≤ 2^{poly(n)}, there is a language L ∈ NTIME[T(n)] and an algorithm R such that:
1. Input. The input to R is a pair (M, 1^n), with the promise that M describes a nondeterministic Turing
machine running in o(T(n)) time and guessing at most n/10 bits.
2. Output. For every fixed M and every sufficiently large n, R(M, 1^n) outputs a string x ∈ {0, 1}^n such
that M(x) ≠ L(x).
3. Complexity. R runs in poly(T(n)) time with adaptive access to an SAT oracle.
</pre>
</td><td>

[Statement.lean, lines 2274–2285](../Statement.lean#L2274-L2285)

<pre title="Statement.lean, lines 2274–2285">
/-- **CLW20 Theorem 1.13, PDF page 6 (printed p.5), verbatim:**
"Theorem 1.13 (Refuter with an NP Oracle, Informal). For every time-constructible function T(n)
such that n ≤ T(n) ≤ 2^{poly(n)}, there is a language L ∈ NTIME[T(n)] and an algorithm R such that:
1. Input. The input to R is a pair (M, 1^n), with the promise that M describes a nondeterministic
Turing machine running in o(T(n)) time and guessing at most n/10 bits.
2. Output. For every fixed M and every sufficiently large n, R(M, 1^n) outputs a string
x ∈ {0,1}^n such that M(x) ≠ L(x).
3. Complexity. R runs in poly(T(n)) time with adaptive access to an SAT oracle."
The module docstring records each reading, including the one step Lean does not check: the
multitape machine model. -/
def CLW20_Theorem1_13 : Prop :=
  ∀ T : ℕ → ℕ, TimeConstructible T → InClockRange T → Theorem1_13At T
</pre>

<pre title="Statement.lean, lines 2261–2272">
/-- The conclusion of Theorem 1.13 at one clock `T`: "there is a language L ∈ NTIME[T(n)] and an
algorithm R such that" items 1–3 hold. The degree `d` of "poly(T(n))" belongs to `R`. The
coefficient `C` and the onset of "every sufficiently large n" may depend on the fixed `M`. -/
def Theorem1_13At (T : ℕ → ℕ) : Prop :=
  ∃ L : Language, InNTIME T L ∧
    ∃ (R : OrdinaryOracleProgram) (d : ℕ),
      ∀ M : OrdinaryWeakMachine, OrdinaryLittleO M T →
        ∃ C onset : ℕ, ∀ n, onset ≤ n →
          ∃ x : BitInput n,
            OrdinaryOracleRuns RecoveryOracle.sourceSAT R (pairInput M n) (List.ofFn x)
              (C * (T n + 1) ^ d) ∧
            machineValue M n x ≠ L n x
</pre>

</td></tr>
<tr><td>
<b>CLW20, PDF p. 6</b>
<pre>
For every time-constructible function T(n) such that
n ≤ T(n) ≤ 2^{poly(n)}
</pre>
</td><td>

[Statement.lean, lines 2236–2240](../Statement.lean#L2236-L2240)

<pre title="Statement.lean, lines 2236–2240">
/-- "time-constructible" (standard notion, Tier 1 multitape model): a program that, given the word
`1^n`, outputs the binary digits of `T(n)` within `C·(T(n)+1)` steps. -/
def TimeConstructible (T : ℕ → ℕ) : Prop :=
  ∃ C : ℕ, 0 &lt; C ∧ Nonempty (OrdinaryWordFunction ℕ (fun n =&gt; List.replicate n true)
    (fun n =&gt; (T n).bits) (fun n =&gt; C * (T n + 1)))
</pre>

<pre title="Statement.lean, lines 2242–2244">
/-- "n ≤ T(n) ≤ 2^{poly(n)}". -/
def InClockRange (T : ℕ → ℕ) : Prop :=
  (∀ n, n ≤ T n) ∧ ∃ C k : ℕ, ∀ n, T n ≤ 2 ^ (C * (n + 1) ^ k)
</pre>

</td></tr>
<tr><td>
<b>CLW20, PDF p. 6</b>
<pre>
there is a language L ∈ NTIME[T(n)]
</pre>
<b>CLW20, PDF p. 6</b>
<pre>
Let NTIMEGUESS[t(n), g(n)] be the class of languages
decided by nondeterministic algorithms running in O(t(n)) steps and guessing at most g(n) bits.
</pre>
</td><td>

[Statement.lean, lines 2246–2250](../Statement.lean#L2246-L2250)

<pre title="Statement.lean, lines 2246–2250">
/-- "L ∈ NTIME[T(n)]" (nondeterministic `O(T(n))` time, Tier 1 multitape model): `L` is the
language of a verifier that halts within `c·(T(n)+1)` steps on every witness of length
`c·(T(n)+1)`. -/
def InNTIME (T : ℕ → ℕ) (L : Language) : Prop :=
  ∃ H : OrdinaryHierarchy T, ∀ n (x : BitInput n), L n x = true ↔ H.verifier.language H.time n x
</pre>

[Statement.lean, lines 1377–1383](../Statement.lean#L1377-L1383)

<pre title="Statement.lean, lines 1377–1383">
structure OrdinaryHierarchy (T : ℕ → ℕ) where
  verifier : OrdinaryVerifier
  coefficient : ℕ
  coefficientPositive : 0 &lt; coefficient
  halts : ∀ n (x : BitInput n) (w : BitInput (coefficient*(T n+1))),
    ∃ receipt, run verifier.machine (coefficient*(T n+1))
      (verifier.inputTapes (List.ofFn x) (List.ofFn w)) = some receipt
</pre>

<pre title="Statement.lean, lines 1385–1386">
def OrdinaryHierarchy.time {T : ℕ → ℕ} (H : OrdinaryHierarchy T) (n : ℕ) : ℕ :=
  H.coefficient*(T n+1)
</pre>

</td></tr>
<tr><td>
<b>CLW20, PDF p. 6</b>
<pre>
The input to R is a pair (M, 1^n), with the promise that M describes a nondeterministic Turing
machine running in o(T(n)) time and guessing at most n/10 bits.
</pre>
</td><td>

[Statement.lean, lines 2252–2254](../Statement.lean#L2252-L2254)

<pre title="Statement.lean, lines 2252–2254">
/-- "The input to R is a pair (M, 1^n)": the framed description of `M`, then the framed `1^n`. -/
def pairInput (M : OrdinaryWeakMachine) (n : ℕ) : List Bool :=
  frame (VerifierEncoding.code M.verifier) ++ frame (List.replicate n true)
</pre>

[Statement.lean, lines 1388–1393](../Statement.lean#L1388-L1393)

<pre title="Statement.lean, lines 1388–1393">
structure OrdinaryWeakMachine where
  verifier : OrdinaryVerifier
  runtime : ℕ → ℕ
  halts : ∀ n (x : BitInput n) (w : BitInput (n/16)),
    ∃ receipt, run verifier.machine (runtime n)
      (verifier.inputTapes (List.ofFn x) (List.ofFn w)) = some receipt
</pre>

<pre title="Statement.lean, lines 1395–1397">
def OrdinaryWeakMachine.accepts (M : OrdinaryWeakMachine)
    (n : ℕ) (x : BitInput n) : Prop :=
  M.verifier.language (fun n =&gt; n/16) n x
</pre>

<pre title="Statement.lean, lines 1399–1401">
def OrdinaryLittleO (M : OrdinaryWeakMachine) (T : ℕ → ℕ) : Prop :=
  ∀ multiplier : ℕ, 0 &lt; multiplier →
    ∃ onset, ∀ n, onset ≤ n → multiplier*M.runtime n ≤ T n
</pre>

</td></tr>
<tr><td>
<b>CLW20, PDF p. 6</b>
<pre>
R(M, 1^n) outputs a string x ∈ {0, 1}^n such
that M(x) ≠ L(x).
</pre>
<b>CLW20, PDF p. 19</b> (the big OR is over the witnesses w)
<pre>
Note that for an M using o(T(n)) time and g(n) guesses, we have
M(x) = 1 ⇔ ∨_{w∈{0,1}^{g(n)}} V_M(x, T(n), w) = 1.
</pre>
</td><td>

[Statement.lean, lines 2256–2259](../Statement.lean#L2256-L2259)

<pre title="Statement.lean, lines 2256–2259">
/-- `M(x)`, the truth value of "some witness makes `M` accept `x`" (CLW20 p.19). -/
noncomputable def machineValue (M : OrdinaryWeakMachine) (n : ℕ) (x : BitInput n) : Bool := by
  classical
  exact decide (M.accepts n x)
</pre>

</td></tr>
<tr><td>
<b>CLW20, PDF p. 6</b>
<pre>
R runs in poly(T(n)) time with adaptive access to an SAT oracle.
</pre>
</td><td>

[Statement.lean, lines 1561–1570](../Statement.lean#L1561-L1570)

<pre title="Statement.lean, lines 1520–1522">
structure OracleReturn (stateCount : ℕ) where
  onFalse : Fin stateCount
  onTrue : Fin stateCount
</pre>

<pre title="Statement.lean, lines 1524–1528">
structure OrdinaryOracleProgram where
  base : OrdinaryProgram
  queryTape : Fin base.tapeCount
  queryFresh : queryTape.val ≠ 0
  query : Fin base.stateCount → Option (OracleReturn base.stateCount)
</pre>

<pre title="Statement.lean, lines 1533–1550">
/-- Literal costs are fixed by the local/query constructors; no arbitrary
counter attached to a semantic computation is accepted as execution evidence. -/
inductive OrdinaryOracleStep (oracle : ℕ → Bool) (program : OrdinaryOracleProgram) :
    ℕ → program.Config → program.Config → Prop where
  | local (before after : program.Config)
      (notHalted : program.base.machine.halted before.control = false)
      (notQuery : program.query before.control = none)
      (transition : step program.base.machine before = some after) :
      OrdinaryOracleStep oracle program 1 before after
  | ask (before : program.Config) (bits padding : List Bool)
      (rule : OracleReturn program.base.stateCount)
      (notHalted : program.base.machine.halted before.control = false)
      (atQuery : program.query before.control = some rule)
      (rewound : before.heads program.queryTape = 0)
      (writtenQuery : before.tapes program.queryTape = frame bits ++ padding) :
      OrdinaryOracleStep oracle program ((frame bits).length + 1) before
        { before with control := if oracle (CanonicalBinary.bitsValue bits)
            then rule.onTrue else rule.onFalse }
</pre>

<pre title="Statement.lean, lines 1552–1559">
inductive OrdinaryOracleTrace (oracle : ℕ → Bool) (program : OrdinaryOracleProgram) :
    ℕ → program.Config → program.Config → Prop where
  | refl (configuration : program.Config) :
      OrdinaryOracleTrace oracle program 0 configuration configuration
  | cons {cost rest : ℕ} {before middle after : program.Config}
      (step : OrdinaryOracleStep oracle program cost before middle)
      (tail : OrdinaryOracleTrace oracle program rest middle after) :
      OrdinaryOracleTrace oracle program (cost + rest) before after
</pre>

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

[Statement.lean, lines 1612–1615](../Statement.lean#L1612-L1615)

<pre title="Statement.lean, lines 1612–1615">
noncomputable def sourceSAT (code : Nat) : Bool :=
  match decodeSourceSAT code with
  | some formula =&gt; formula.all (fun clause =&gt; clause.length = 3) &amp;&amp; mathSat formula
  | none =&gt; false
</pre>

</td></tr>
<tr><td>
<b>CLW20, PDF p. 19</b>
<pre>
We fix a natural enumeration of all (multitape) nondeterministic Turing machines. Note that the specific
model does not really matter, see the discussion in [Wil13], Section 2.1.
</pre>
<b>FS16, PDF p. 13</b>
<pre>
Since we can universally simulate t(n)-time nondeterministic multitape Turing machines
on an O(t(n))-time 2-tape nondeterministic Turing machine
</pre>
</td><td>

[Statement.lean, lines 1148–1155](../Statement.lean#L1148-L1155)

<pre title="Statement.lean, lines 1139–1146">
/-- A finite local action: one replacement bit and one unit head move per
tape, plus the next finite control state. -/
structure Action (tapeCount stateCount : ℕ) where
  nextControl : Fin stateCount
  /-- `none` leaves a tape unchanged; `some bit` writes exactly its scanned
  cell. -/
  write : Fin tapeCount → Option Bool
  move : Fin tapeCount → HeadMove
</pre>

<pre title="Statement.lean, lines 1148–1155">
/-- The transition function has a finite domain (`Fin stateCount` and one bit
per tape), so it is extensionally a finite transition table. -/
structure Machine (tapeCount stateCount : ℕ) where
  descriptionBits : ℕ
  start : Fin stateCount
  halted : Fin stateCount → Bool
  rule : Fin stateCount → (Fin tapeCount → Bool) →
    Option (Action tapeCount stateCount)
</pre>

<pre title="Statement.lean, lines 1170–1176">
def step
    {tapeCount stateCount : ℕ}
    (machine : Machine tapeCount stateCount)
    (configuration : Configuration tapeCount stateCount) :
    Option (Configuration tapeCount stateCount) :=
  (machine.rule configuration.control configuration.scanned).map
    (applyAction configuration)
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

<pre title="Statement.lean, lines 1345–1346">
def Verifier.accepts (v : Verifier) (input witness : List Bool) : Prop :=
  ∃ fuel, v.acceptsAt fuel input witness
</pre>

<pre title="Statement.lean, lines 1348–1354">
/-- A bare witness-length function is a semantic parameter, not evidence of
    computable nondeterminism; executable source packages must supply its
    computer and its ordinary cost separately. -/
def Verifier.language (v : Verifier) (witnessLength : ℕ → ℕ) :
    (n : ℕ) → BitInput n → Prop :=
  fun n x =&gt; ∃ w : BitInput (witnessLength n),
    v.accepts (List.ofFn x) (List.ofFn w)
</pre>

</td></tr>
</table>

Superscripts are written with `^`, with `{…}` around a superscript of more than one symbol (`2^{poly(n)}` is
2<sup>poly(n)</sup>), and subscripts with `_`.

**The one step Lean does not check: the machine model.** Lean checks everything on this page except one reading. The
paper's “Turing machine”, “NTIME” and “algorithm R” are read in Tier 1: finite control, one-sided binary tapes, one
scanned bit per tape, and in each step one write and a head move of at most one cell on each tape (last row of the
table). CLW20 (“the specific model does not really matter”) and FS16's universal multitape simulation support this
reading. The reading also covers the oracle: “SAT” is read as satisfiability of 3-CNF formulas in a fixed explicit
encoding (`RecoveryOracle.sourceSAT`). The Tseitin reduction makes the two interreducible in polynomial time, and the
poly(T(n)) budget absorbs that cost.

This is also why the transcription uses Theorem 1.13 and not the paper's formal Theorem 4.6 (PDF p. 22). Section 4
states:

<b>CLW20, PDF p. 19</b>
<pre>
For simplicity, we assume all machines are
random-access machines in the following.
</pre>

Theorem 4.6 refutes one specific language, whose definition runs random-access machines. Theorem 1.13 asks only for
some L ∈ NTIME[T(n)]. In the multitape reading, L can be a clocked variant of the hard language: FS16's universal 2-tape
simulation, run for O(T(n)) of its own steps. Each fixed promise machine runs in time o(T(n)), so its simulation
finishes for every large n, and every guarantee of the theorem is claimed only for large n.

**What to check** (a few minutes):

1. The order is the paper's: for every T (time-constructible, with n ≤ T(n) ≤ 2^{poly(n)}) there are L ∈ NTIME[T], an
   algorithm R and one degree d, such that for every M satisfying the promise there are a coefficient C and an onset,
   and for every n past the onset there is an x ∈ {0,1}^n. The degree belongs to R, because item 3 is a property of
   the one algorithm R. The coefficient C and the onset of “every sufficiently large n” may depend on the fixed M,
   whose description is part of R's input.
2. CLW20 does not define time-constructible. The standard notion is used: a machine that, given 1^n, writes T(n) in
   binary within C·(T(n)+1) steps.
3. The range: n ≤ T(n) for every n, and T(n) ≤ 2^(C·(n+1)^k) for some constants C and k.
4. “L ∈ NTIME[T(n)]” says that L is the language of a verifier that halts within c·(T(n)+1) steps on every witness
   of that length and accepts x exactly when some such witness is accepted.
5. The promise: M is a verifier with a witness of exactly ⌊n/16⌋ bits and a step bound (`runtime n`) that holds on
   every input and every witness. “o(T(n))” is `OrdinaryLittleO`: for every m > 0, eventually m·runtime(n) ≤ T(n).
   M(x) is true when some witness is accepted, as on PDF p. 19.
6. The input (M, 1^n) is the framed code of M followed by 1^n framed. The code determines everything that a run of M
   reads, so two machines with the same code have the same language: an encoding clash cannot make the statement
   false.
7. The output: R halts within C·(T(n)+1)^d steps with x on its output tape (`OrdinaryOracleRuns`), and
   “M(x) ≠ L(x)” is the Boolean inequality `machineValue M n x ≠ L n x`.
8. The oracle: R is a deterministic multitape program with query states. Its next state depends on the oracle's
   answer, so its access is adaptive. A query costs its framed length plus one step.

**Documented deviations:** one, the promise class is smaller than printed. The machines M guess exactly ⌊n/16⌋ bits,
which is within the printed “at most n/10 bits”. With fewer machines M, the assumed statement claims less, never more.

[Bindings/CLW20_Theorem1_13.lean, lines 124–126](../Bindings/CLW20_Theorem1_13.lean#L124-L126)

<pre title="Bindings/CLW20_Theorem1_13.lean, lines 124–126">
/-- The promise machines guess ⌊n/16⌋ bits, within the printed "at most n/10 bits". -/
theorem witness_bits_within_promise (n : ℕ) : n / 16 ≤ n / 10 :=
  actualWitnessBound n
</pre>

Lean also proves that this statement gives what the proof uses (`clw20_theorem1_13_to_import`); you need not read it.
The import is equivalent to the conclusion of Theorem 1.13 on the import's clocks: time bounds T with T(n) ≥ n that
are polynomially bounded and computable by a Tier 1 machine in O(T(n)) steps (`import_iff_on_clocks`). So the proof
narrows only the range of T; it does not change what the refuter guarantees.

[Bindings/CLW20_Theorem1_13.lean, lines 217–220](../Bindings/CLW20_Theorem1_13.lean#L217-L220)

[Bindings/CLW20_Theorem1_13.lean, lines 222–231](../Bindings/CLW20_Theorem1_13.lean#L222-L231)

<pre title="Bindings/CLW20_Theorem1_13.lean, lines 222–231">
/-- The import is exactly the literal's conclusion on the import's clocks: it narrows only the
T-domain (polynomially bounded ordinary clocks with `T n ≥ n`), not the refuter's guarantee. -/
theorem import_iff_on_clocks :
    HierarchyRefuterSource ↔ ∀ T : ℕ → ℕ, OrdinaryClock T → Theorem1_13At T := by
  constructor
  · intro source T clock
    obtain ⟨A⟩ := source T clock
    exact algorithm_to_at clock A
  · intro h T clock
    exact at_to_algorithm (h T clock)
</pre>

<pre title="Proof/Foundations/SourceCore.lean, lines 16–22">
structure OrdinaryClock (T : ℕ → ℕ) where
  atLeastInput : ∀ n, n ≤ T n
  polynomial : PolynomiallyBounded T
  coefficient : ℕ
  coefficientPositive : 0 &lt; coefficient
  computer : OrdinaryWordFunction ℕ (fun n =&gt; List.replicate n true)
    (fun n =&gt; (T n).bits) (fun n =&gt; coefficient*(T n+1))
</pre>

**Class:** literal, multitape reading.

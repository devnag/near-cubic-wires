# 3. Matrix product: Williams (J. ACM 2014) Corollary 4.4 / C.2

The main theorem assumes the Lean statement in the first row of the table below. It is Corollary 4.4 of Williams's
paper, which Appendix C restates as Corollary C.2. The other rows show every definition that statement uses. The
algorithm is a multitape Turing machine with two input tapes, one for each matrix.

"Tier 1" in the Lean comments means the proof's own multitape machine model (the `LocalBitMultitapeCore` section of `Statement.lean`,
last row). The statement is stated in that model, which is the model Williams names on p. 26 (“even on a multitape
TM”).

Paper: R. Williams, "Nonuniform ACC Circuit Lower Bounds", Journal of the ACM 61(1), Article 2 (2014),
https://doi.org/10.1145/2559903. Page numbers refer to the journal PDF, SHA-256
78d7c472224906600e31369914d4210d875af894b92903c362c3c1cf680b021c.

<table>
<tr><th>Paper (verbatim)</th><th>Lean (verbatim)</th></tr>
<tr><td>
<b>PDF p. 17</b>
<pre>
COROLLARY 4.4. For all sufficiently large N, two
0-1 matrices of dimensions N × N^{.1} and N^{.1} × N
can be multiplied over the integers in
O(N² · poly(log N)) time.
</pre>
<b>PDF p. 29</b>
<pre>
COROLLARY C.2. For all sufficiently large N, two
0-1 matrices of dimensions N × N^{.1} and N^{.1} × N
can be multiplied over the integers in
O(N² · poly(log N)) time.
</pre>
</td><td>

[Statement.lean, lines 2339–2347](../Statement.lean#L2339-L2347)

<pre title="Statement.lean, lines 2339–2347">
/-- **Williams, JACM 2014, Corollary 4.4 (PDF p.17) = Corollary C.2 (PDF p.29), verbatim:**
"For all sufficiently large N, two 0-1 matrices of dimensions N × N^{.1} and N^{.1} × N can be
multiplied over the integers in O(N² · poly(log N)) time."

Read with the conventions of the module docstring: an onset `N₀` and constants `C`, `e`, all
existential, and one multitape machine (Tier 1) that is correct and within `C · N² · (log₂ N)^e`
for every `N = k^10 ≥ N₀`. -/
def Williams14_Corollary4_4 : Prop :=
  ∃ N₀ C e : ℕ, Nonempty (MultitapeMultiplier N₀ C e)
</pre>

</td></tr>
<tr><td>
<b>PDF p. 26</b>
<pre>
Prima facie, it could be that Coppersmith's
algorithm is nonuniform, making it difficult to
apply. For the sake of completeness, here we
verify using standard ideas that Coppersmith's
algorithm can indeed be implemented to run (even
on a multitape TM) in O(N² · poly(log N)) time, on
matrices over any field of poly(N) elements.
</pre>
</td><td>

[Statement.lean, lines 2322–2337](../Statement.lean#L2322-L2337)

<pre title="Statement.lean, lines 2322–2337">
/-- TIER 1 ALGORITHMIC CLAUSE (separable). One deterministic multitape machine (at least three
tapes; the output tape is neither input tape) that, for every `N = k^10 ≥ N₀` and every pair of
0-1 matrices of dimensions `N × N^{.1}` and `N^{.1} × N`, halts within `C · N² · (log₂ N)^e` steps
with their integer product on the output tape. -/
structure MultitapeMultiplier (N₀ C e : ℕ) where
  tapeCount : ℕ
  stateCount : ℕ
  threeTapes : 3 ≤ tapeCount
  machine : Machine tapeCount stateCount
  outputTape : Fin tapeCount
  outputFreshLeft : outputTape.val ≠ 0
  outputFreshRight : outputTape.val ≠ 1
  multiplies : ∀ (k : ℕ) (A : BitMatrix (k ^ 10) k) (B : BitMatrix k (k ^ 10)), N₀ ≤ k ^ 10 →
    ∃ receipt, run machine (C * (k ^ 10) ^ 2 * Nat.log 2 (k ^ 10) ^ e) (inputTapes (k ^ 10) A B) =
        some receipt ∧
      receipt.final.tapes outputTape = outputWord (k ^ 10) (product A B)
</pre>

</td></tr>
<tr><td>
<b>PDF p. 17</b>
<pre>
two 0-1 matrices of dimensions N × N^{.1} and
N^{.1} × N can be multiplied over the integers
</pre>
</td><td>

[Statement.lean, lines 2307–2309](../Statement.lean#L2307-L2309)

<pre title="Statement.lean, line 972">
abbrev BitMatrix (rows columns : ℕ) := Fin rows → Fin columns → Bool
</pre>

<pre title="Statement.lean, line 974">
abbrev NatMatrix (rows columns : ℕ) := Fin rows → Fin columns → ℕ
</pre>

<pre title="Statement.lean, lines 2304–2305">
/-- A 0-1 matrix entry as the integer `0` or `1`. -/
def bit (b : Bool) : ℕ := if b then 1 else 0
</pre>

<pre title="Statement.lean, lines 2307–2309">
/-- "multiplied over the integers": `(A · B)(i, j) = Σ_l A(i, l) · B(l, j)`. -/
def product {n m p : ℕ} (A : BitMatrix n m) (B : BitMatrix m p) : NatMatrix n p :=
  fun i j =&gt; ∑ l, bit (A i l) * bit (B l j)
</pre>

</td></tr>
<tr><td>
The layout of input and output on the tapes. The paper fixes none. Tape 0 holds N in self-delimiting binary
followed by the first matrix row by row, tape 1 holds the second matrix row by row, and the product is written
row by row on a separate output tape, each entry in ⌊log₂ N⌋ + 1 binary digits.
</td><td>

[Statement.lean, lines 2311–2315](../Statement.lean#L2311-L2315)

<pre title="Statement.lean, lines 2311–2315">
/-- Tier 1 input tapes: tape 0 = `N` in self-delimiting binary, then `A` row by row;
tape 1 = `B` row by row; every other tape blank. -/
def inputTapes {t m : ℕ} (N : ℕ) (A : BitMatrix N m) (B : BitMatrix m N) : Fin t → List Bool :=
  fun tape =&gt; if tape.val = 0 then natWord N ++ rowMajorBitMatrix A
    else if tape.val = 1 then rowMajorBitMatrix B else []
</pre>

<pre title="Statement.lean, lines 2317–2320">
/-- Tier 1 output: the `N × N` product row by row, each entry in `⌊log₂ N⌋ + 1` binary digits
(least significant first). -/
def outputWord (N : ℕ) (P : NatMatrix N N) : List Bool :=
  encodedNatCellTape (natBitLength N) (rowMajorNatMatrix P)
</pre>

[Statement.lean, lines 1262–1264](../Statement.lean#L1262-L1264)

<pre title="Statement.lean, lines 1262–1264">
def rowMajorBitMatrix {rows columns : ℕ}
    (matrix : BitMatrix rows columns) : List Bool :=
  (List.ofFn fun row =&gt; List.ofFn fun column =&gt; matrix row column).flatten
</pre>

<pre title="Statement.lean, lines 1266–1267">
def fixedWidthNatBits (width value : ℕ) : List Bool :=
  List.ofFn fun bit : Fin width =&gt; value.testBit bit.val
</pre>

<pre title="Statement.lean, lines 1269–1270">
def encodedNatCellTape (width : ℕ) (cells : List ℕ) : List Bool :=
  cells.flatMap (fixedWidthNatBits width)
</pre>

[Statement.lean, lines 1246–1250](../Statement.lean#L1246-L1250)

<pre title="Statement.lean, lines 1246–1250">
/-- A matrix as a sequential row-major cell tape.  This is a `List` in the
logic, not a balanced codec and not a single machine register. -/
def rowMajorNatMatrix {rows columns : ℕ}
    (matrix : NatMatrix rows columns) : List ℕ :=
  (List.ofFn fun row =&gt; List.ofFn fun column =&gt; matrix row column).flatten
</pre>

[Statement.lean, line 56](../Statement.lean#L56)

<pre title="Statement.lean, line 56">
def natBitLength (value : ℕ) : ℕ := Nat.log 2 value + 1
</pre>

[Statement.lean, line 1698](../Statement.lean#L1698)

<pre title="Statement.lean, line 1698">
def natWord (n : ℕ) : List Bool := framedNatBits n
</pre>

[Statement.lean, lines 1286–1290](../Statement.lean#L1286-L1290)

<pre title="Statement.lean, lines 1286–1290">
/-- A self-delimiting binary word.  Its length prefix makes concatenation of
the variable-width fields unambiguous. -/
def framedNatBits (value : ℕ) : List Bool :=
  List.replicate (natBitLength value) true ++
    false :: fixedWidthNatBits (natBitLength value) value
</pre>

</td></tr>
<tr><td>
<b>PDF p. 26</b>
<pre>
(even on a multitape TM)
</pre>
The machine model: finitely many control states; each step reads the one scanned bit of every tape, may write
that cell, and moves each head by at most one cell. One rule application is one step.
</td><td>

[Statement.lean, lines 1148–1155](../Statement.lean#L1148-L1155)

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

<pre title="Statement.lean, lines 1157–1168">
def applyAction
    {tapeCount stateCount : ℕ}
    (configuration : Configuration tapeCount stateCount)
    (action : Action tapeCount stateCount) :
    Configuration tapeCount stateCount where
  control := action.nextControl
  heads := fun tape =&gt; (action.move tape).apply (configuration.heads tape)
  tapes := fun tape =&gt;
    match action.write tape with
    | none =&gt; configuration.tapes tape
    | some value =&gt;
        writeTapeBit (configuration.tapes tape) (configuration.heads tape) value
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

<pre title="Statement.lean, lines 1178–1187">
/-- Explicit tapes are the standard source input.  Any conversion from a
compact request to these tapes must be a separately executed loader. -/
def initialConfiguration
    {tapeCount stateCount : ℕ}
    (machine : Machine tapeCount stateCount)
    (inputTapes : Fin tapeCount → List Bool) :
    Configuration tapeCount stateCount where
  control := machine.start
  heads := fun _tape =&gt; 0
  tapes := inputTapes
</pre>

<pre title="Statement.lean, lines 1194–1223">
def runFrom
    {tapeCount stateCount : ℕ}
    (machine : Machine tapeCount stateCount) :
    ℕ → Configuration tapeCount stateCount →
      Option (ExecutionReceipt tapeCount stateCount)
  | 0, configuration =&gt;
      if machine.halted configuration.control then
        some
          { final := configuration
            steps := 0
            peakTapeCells := configuration.tapeCells }
      else none
  | fuel + 1, configuration =&gt;
      if machine.halted configuration.control then
        some
          { final := configuration
            steps := 0
            peakTapeCells := configuration.tapeCells }
      else
        match step machine configuration with
        | none =&gt; none
        | some next =&gt;
            match runFrom machine fuel next with
            | none =&gt; none
            | some suffix =&gt;
                some
                  { final := suffix.final
                    steps := suffix.steps + 1
                    peakTapeCells := max configuration.tapeCells
                      suffix.peakTapeCells }
</pre>

<pre title="Statement.lean, lines 1225–1230">
def run
    {tapeCount stateCount : ℕ}
    (machine : Machine tapeCount stateCount)
    (fuel : ℕ) (inputTapes : Fin tapeCount → List Bool) :
    Option (ExecutionReceipt tapeCount stateCount) :=
  runFrom machine fuel (initialConfiguration machine inputTapes)
</pre>

</td></tr>
</table>

Superscripts are written with `^`: `N^{.1}` is N<sup>.1</sup> = N<sup>1/10</sup>.

**What to check** (a few minutes):

1. The quantifiers: there are an onset N₀ and constants C and e, all chosen together with one machine, such that
   for every N ≥ N₀ of the form N = k^10 and every pair of 0-1 matrices of dimensions N × k and k × N the machine
   halts within C · N² · (log₂ N)^e steps with their product on the output tape. “For all sufficiently large N” is
   the onset N₀; O(N² · poly(log N)) is C · N² · (log₂ N)^e.
2. N^{.1} is a whole number exactly when N = k^10, and then it is k. The statement asks only for these N, where
   every rounding convention for N^{.1} agrees, so every reading of the printed corollary implies it.
3. “multiplied over the integers”: entry (i, j) of the product is Σ_l A(i, l) · B(l, j), with each 0-1 entry read
   as the integer 0 or 1 (`bit`, `product`). It is the integer product, not the Boolean or mod-2 one. It is stated
   in ℕ because every entry is nonnegative; Lean checks it equals the product over ℤ (`product_cast`).
4. The machine is a multitape Turing machine over bits (last row). The run function returns a result only if the
   machine halts within the given number of steps, so the time bound is a bound on steps.
5. The output width ⌊log₂ N⌋ + 1 loses nothing: every entry is at most k ≤ N (`product_lt`).

   [Bindings/Williams14_Corollary4_4.lean, lines 85–88](../Bindings/Williams14_Corollary4_4.lean#L85-L88)

   [Bindings/Williams14_Corollary4_4.lean, lines 90–99](../Bindings/Williams14_Corollary4_4.lean#L90-L99)

6. Below the onset N₀ the statement says nothing, as in the paper. The proof handles the finitely many smaller
   sizes itself, with a lookup gate placed in front of the paper's machine. The gate is proved correct in Lean
   (`table_small`, `table_large`, `Gate.combined_small_run`, `Gate.combined_large_run`); it is not an assumption.

   [Bindings/Williams14_Corollary4_4.lean, lines 313–323](../Bindings/Williams14_Corollary4_4.lean#L313-L323)

   [Bindings/Williams14_Corollary4_4_PrefixLookup.lean, lines 393–396](../Bindings/Williams14_Corollary4_4_PrefixLookup.lean#L393-L396)

**Documented deviations:** none.

Lean also proves that this statement gives what the proof uses (`williams14_to_import`); you need not read it.

[Bindings/Williams14_Corollary4_4.lean, lines 431–447](../Bindings/Williams14_Corollary4_4.lean#L431-L447)

**Class:** literal, multitape reading.

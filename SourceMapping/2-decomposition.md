# 2. Decomposition: CW19 Proposition 18(2)

The main theorem assumes the Lean statement in the first row of the table below. It is CW19 Proposition 18,
item 2, together with the proposition's closing sentence on constructions. The other rows show every definition
that statement uses. The construction clause is stated in Mathlib's standard Turing machine model,
`Turing.TM2ComputableInPolyTime`.

Two labels appear in the Lean comments. "Tier 1" is the proof's own multitape machine model
(the `LocalBitMultitapeCore` section of `Statement.lean`, with the word-function wrapper in its `OrdinaryMachine` section).
"Tier 2" is Mathlib's standard `Turing.TM2` model. The main theorem assumes the Tier 2 statement; Lean proves that
it implies the Tier 1 one.

Paper: L. Chen, R. R. Williams, "Stronger Connections Between Circuit Analysis and Circuit Lower Bounds, via PCPs
of Proximity", 34th Computational Complexity Conference (CCC 2019), LIPIcs 137, Article 19,
https://doi.org/10.4230/LIPIcs.CCC.2019.19. Page numbers refer to the PDF at
https://drops.dagstuhl.de/storage/00lipics/lipics-vol137-ccc2019/LIPIcs.CCC.2019.19/LIPIcs.CCC.2019.19.pdf,
SHA-256 c3c6ea6f80dbdf92a1887272fc2d618a4f63bd887d1cc1186dcf299a3aa99533.

<table>
<tr><th>Paper (verbatim)</th><th>Lean (verbatim)</th></tr>
<tr><td>
<b>PDF p. 14</b>
<pre>
Proposition 18. The following hold:
…
2. THR ⊆ DOR ◦ ETHR [24]. (also see Appendix B)
…
Moreover, all the above have corresponding
polynomial-time, deterministic constructions.
</pre>
</td><td>

[Statement.lean, lines 2441–2446](../Statement.lean#L2441-L2446)

<pre title="Statement.lean, lines 2441–2446">
/-- **CW19 Proposition 18(2), PDF page 14, verbatim:** "2. THR ⊆ DOR ◦ ETHR [24]. (also see
Appendix B)" … "Moreover, all the above have corresponding polynomial-time, deterministic
constructions." (Tier 2: the construction in Mathlib's TM2 model; everything else as Tier 1.) -/
def CW19_Proposition18_2_TM2 : Prop :=
  ∃ dor : (n : ℕ) → THRGate n → DORofETHR n,
    (∀ (n : ℕ) (G : THRGate n), (dor n G).Computes G) ∧ PolynomialTimeConstructionTM2 dor
</pre>

</td></tr>
<tr><td>
<b>PDF p. 14</b>
<pre>
Moreover, all the above have corresponding
polynomial-time, deterministic constructions.
</pre>
The paper fixes no encoding of gates and circuits. The Lean statement uses the explicit binary descriptions in the
last row.
</td><td>

[Statement.lean, lines 2434–2439](../Statement.lean#L2434-L2439)

<pre title="Statement.lean, lines 2434–2439">
/-- TIER 2 ALGORITHMIC CLAUSE. "polynomial-time, deterministic constructions": a Mathlib
`TM2ComputableInPolyTime` machine from the description of every THR gate `G` to the description
of `dor G`. -/
def PolynomialTimeConstructionTM2 (dor : (n : ℕ) → THRGate n → DORofETHR n) : Prop :=
  Nonempty (Turing.TM2ComputableInPolyTime (fun G : (n : ℕ) × THRGate n =&gt; gateWord G.2)
    (fun w : List Bool =&gt; w) (fun G =&gt; circuitWord (dor G.1 G.2)))
</pre>

</td></tr>
<tr><td>
<b>PDF p. 41</b> (checked against the page image; the text layer drops the Σ)
<pre>
Lemma 49. Let G be a THR gate on n bits,
G(x) := [Σ_{i=1}^n w_i · x_i &gt; T], such that all
w_i's and T are integers from [−W, W] for some
W ∈ ℕ.
</pre>
</td><td>

[Statement.lean, lines 2368–2372](../Statement.lean#L2368-L2372)

<pre title="Statement.lean, lines 2368–2372">
/-- CW19 Appendix B, Lemma 49, p.41: "Let G be a THR gate on n bits,
G(x) := [Σ_{i=1}^n w_i · x_i &gt; T], such that all w_i's and T are integers". -/
structure THRGate (n : ℕ) where
  w : Fin n → ℤ
  T : ℤ
</pre>

<pre title="Statement.lean, lines 2374–2376">
/-- `G(x) := [Σ_{i=1}^n w_i · x_i &gt; T]` (Lemma 49, p.41). -/
def THRGate.eval {n : ℕ} (G : THRGate n) (x : Fin n → ℤ) : Bool :=
  decide (∑ i, G.w i * x i &gt; G.T)
</pre>

</td></tr>
<tr><td>
<b>PDF p. 13</b>
<pre>
Let x ∈ {0, 1}^n. For w ∈ R^n and t ∈ R, we define
THR_{w,t}(x) (the threshold function) to be the
indicator function for the condition w · x ≥ t.
Similarly, ETHR_{w,t}(x) (the exact threshold
function) is the indicator function for the
condition w · x = t.
</pre>
</td><td>

[Statement.lean, lines 2378–2382](../Statement.lean#L2378-L2382)

<pre title="Statement.lean, lines 2365–2366">
/-- CW19 p.13: "Let x ∈ {0, 1}^n." The 0-1 vectors in `ℤ^n`. -/
def IsBoolVec {n : ℕ} (x : Fin n → ℤ) : Prop := ∀ i, x i = 0 ∨ x i = 1
</pre>

<pre title="Statement.lean, lines 2378–2382">
/-- CW19 p.13: "ETHR_{w,t}(x) (the exact threshold function) is the indicator function for the
condition w · x = t." Integral, as every ETHR gate built in Appendix B. -/
structure ETHRGate (n : ℕ) where
  w : Fin n → ℤ
  t : ℤ
</pre>

<pre title="Statement.lean, lines 2384–2386">
/-- `ETHR_{w,t}(x) = [w · x = t]`. -/
def ETHRGate.eval {n : ℕ} (E : ETHRGate n) (x : Fin n → ℤ) : Bool :=
  decide (∑ i, E.w i * x i = E.t)
</pre>

<pre title="Bindings/CW19_Proposition18_2.lean, lines 134–137">
/-- §2.1 (p.13): "THR_{w,t}(x) … the indicator function for the condition w · x ≥ t", with
integer realizations. -/
def nonStrictEval {n : ℕ} (w : Fin n → ℤ) (t : ℤ) (x : Fin n → ℤ) : Bool :=
  decide (∑ i, w i * x i ≥ t)
</pre>

</td></tr>
<tr><td>
<b>PDF p. 13</b> (the sentence continues on p. 14)
<pre>
We use DOR_n to denote the disjoint OR function,
that is, an OR function with the promise that at
most
</pre>
<b>PDF p. 14</b>
<pre>
one input bit is true over all inputs.
</pre>
<b>PDF p. 14</b>
<pre>
For two classes of functions like THR and MAJ, we
use THR ◦ MAJ to denote the corresponding class of
depth-two circuits.
</pre>
</td><td>

[Statement.lean, lines 2388–2391](../Statement.lean#L2388-L2391)

<pre title="Statement.lean, lines 2388–2391">
/-- A DOR ◦ ETHR circuit on `n` inputs: one top DOR gate whose inputs are the ETHR gates
`E_1, …, E_m` (in order, repetitions kept). -/
structure DORofETHR (n : ℕ) where
  gates : List (ETHRGate n)
</pre>

<pre title="Statement.lean, lines 2393–2396">
/-- CW19 p.14: "DOR_n … an OR function with the promise that at most one input bit is true over
all inputs": at most one `E_j(x)` is true, on every `x ∈ {0,1}^n`. -/
def DORofETHR.Promise {n : ℕ} (C : DORofETHR n) : Prop :=
  ∀ x : Fin n → ℤ, IsBoolVec x → (C.gates.filter fun E =&gt; E.eval x).length ≤ 1
</pre>

<pre title="Statement.lean, lines 2398–2400">
/-- The value of the circuit: the OR of `E_1(x), …, E_m(x)`. -/
def DORofETHR.eval {n : ℕ} (C : DORofETHR n) (x : Fin n → ℤ) : Bool :=
  C.gates.any fun E =&gt; E.eval x
</pre>

<pre title="Statement.lean, lines 2402–2405">
/-- "THR ⊆ DOR ◦ ETHR", for one gate: `C` is a legal DOR ◦ ETHR circuit (the DOR promise holds)
and computes the same function as `G` on `{0,1}^n`. -/
def DORofETHR.Computes {n : ℕ} (C : DORofETHR n) (G : THRGate n) : Prop :=
  C.Promise ∧ ∀ x : Fin n → ℤ, IsBoolVec x → C.eval x = G.eval x
</pre>

</td></tr>
<tr><td>
The descriptions that the construction reads and writes. The paper fixes none; any standard binary encoding of the
integers serves, and these are such encodings: a number in self-delimiting binary (its bit length in unary, then
its bits), an integer as a sign bit followed by its absolute value.
</td><td>

[Statement.lean, lines 2407–2410](../Statement.lean#L2407-L2410)

<pre title="Statement.lean, lines 2407–2410">
/-- Tier 1 description of a THR gate: `n`, then `w_1, …, w_n`, then `T` (self-delimiting binary
naturals `natWord`, signed integers `intWord` = sign bit then `natWord |z|`). -/
def gateWord {n : ℕ} (G : THRGate n) : List Bool :=
  natWord n ++ (List.ofFn G.w).flatMap intWord ++ intWord G.T
</pre>

<pre title="Statement.lean, lines 2412–2414">
/-- Tier 1 description of one ETHR gate: its weights, then its threshold. -/
def ethrWord {n : ℕ} (E : ETHRGate n) : List Bool :=
  (List.ofFn E.w).flatMap intWord ++ intWord E.t
</pre>

<pre title="Statement.lean, lines 2416–2418">
/-- Tier 1 description of a DOR ◦ ETHR circuit: `m`, then `E_1, …, E_m`. -/
def circuitWord {n : ℕ} (C : DORofETHR n) : List Bool :=
  natWord C.gates.length ++ C.gates.flatMap ethrWord
</pre>

[Statement.lean, line 1698](../Statement.lean#L1698)

<pre title="Statement.lean, line 1698">
def natWord (n : ℕ) : List Bool := framedNatBits n
</pre>

<pre title="Statement.lean, line 1700">
def intWord (z : ℤ) : List Bool := decide (z &lt; 0) :: natWord z.natAbs
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
</table>

Superscripts are written with `^` and subscripts with `_`: `THR_{w,t}` is THR<sub>w,t</sub>, `{0, 1}^n` is
{0, 1}<sup>n</sup>.

**What to check** (a few minutes):

1. One construction serves every gate: there is a single function `dor` from THR gates to DOR ◦ ETHR circuits
   such that, for every number of inputs n (including n = 0) and every gate G, the circuit `dor n G` computes G,
   and `dor` itself is computable in polynomial time.
2. `DORofETHR.Computes` is containment in DOR ◦ ETHR: on every 0-1 input at most one ETHR gate is true
   (the DOR promise, `DORofETHR.Promise`), and the OR of the ETHR gates equals G(x).
3. An ETHR gate outputs [w · x = t] (`ETHRGate.eval`), as on p. 13.
4. The construction clause is Mathlib's `Turing.TM2ComputableInPolyTime`: a Turing machine with finitely many
   states and stacks that, on the description of G, halts with the description of `dor n G` within p(ℓ) steps,
   where p is a fixed polynomial and ℓ the length of the input description. Mathlib's definition, at the version
   this repository pins:
   https://github.com/leanprover-community/mathlib4/blob/81a5d257c8e410db227a6665ed08f64fea08e997/Mathlib/Computability/TuringMachine/Computable.lean#L177-L188
5. The statement claims no sharp bounds (neither Lemma 49's gate count O(n · log W) nor its weight range); only
   the polynomial-time construction is assumed.

**Documented deviations** (each has a Lean proof; you need not read it):

- The input gate has integer weights and threshold and the strict comparison [Σ w_i · x_i > T], as in Appendix B,
  Lemma 49, the construction the proposition points to. §2.1 (p. 13) writes THR with real weights and ≥. For
  integer weights, [w · x ≥ t] is [w · x > t − 1], so the class is the same: Lean proves that the statement
  (through `tier1_of_tier2`) also yields a DOR ◦ ETHR circuit for every integer gate with ≥
  (`nonStrict_integral_containment`). Real weights reduce to integer ones by the “without loss of generality”
  remark on p. 13; that fact is CTW26 Lemma 3.2 (page 1), which the main theorem assumes separately.

  [Bindings/CW19_Proposition18_2.lean, lines 139–150](../Bindings/CW19_Proposition18_2.lean#L139-L150)

  [Bindings/CW19_Proposition18_2_TM2.lean, lines 50–53](../Bindings/CW19_Proposition18_2_TM2.lean#L50-L53)

Lean also proves that this statement gives what the proof uses (`cw19_tm2_to_import`). It carries the Mathlib
machine into the proof's own machine model with the proved simulation `tm2ToOrdinary`. You need not read either.

[Bindings/CW19_Proposition18_2_TM2.lean, lines 55–57](../Bindings/CW19_Proposition18_2_TM2.lean#L55-L57)

[Bindings/TuringBridge/Bridge.lean, lines 141–159](../Bindings/TuringBridge/Bridge.lean#L141-L159)

**Class:** literal in Mathlib's machine model.

# 1. Threshold normalization: CTW26 Lemma 3.2 (MTT61)

The main theorem assumes the Lean statement in the first row of the table below. It is CTW26 Lemma 3.2, which
CTW26 attributes to Muroga, Toda and Takasu (1961). The other rows show every definition that statement uses.

Paper: L. Chen, A. Tal, Y. Wang, "Super-quadratic Lower Bounds for Depth-2 Linear Threshold Circuits", ECCC
TR26-039 (2026), https://eccc.weizmann.ac.il/report/2026/039/download/. Page numbers refer to that PDF,
SHA-256 b461919916161705a41f43866538d954bd100ca1d4c89451ba734d1caff9987d.

<table>
<tr><th>Paper (verbatim)</th><th>Lean (verbatim)</th></tr>
<tr><td>
<b>PDF p. 10</b>
<pre>
Lemma 3.2 ([MTT61]). For any THR gate on m input
bits, there is an equivalent THR gate where all
parameters are integers in range ±m^m.
</pre>
</td><td>

[Statement.lean, lines 1790–1799](../Statement.lean#L1790-L1799)

<pre title="Statement.lean, lines 1790–1799">
/-- **CTW26 Lemma 3.2 ([MTT61]), PDF page 10, verbatim:**
"For any THR gate on m input bits, there is an equivalent THR gate where all parameters are
integers in range ±m^m."

Every `m : ℕ` is quantified (no positivity; Lean's `0 ^ 0 = 1`). "All parameters" are the
weights `w i` and the threshold `t` of Definition 3.1. -/
def CTW26_Lemma3_2 : Prop :=
  ∀ (m : ℕ) (g : THRGate m), ∃ h : THRGate m,
    Equivalent g h ∧
      (∀ i, IsIntegerInRange (h.w i) (m ^ m)) ∧ IsIntegerInRange h.t (m ^ m)
</pre>

</td></tr>
<tr><td>
<b>PDF p. 9</b>
<pre>
Definition 3.1. (Gates) We define the following
gates (on input (x1, x2, · · · , xm) ∈ {0, 1}^m):
…
THR: This gate has parameters w1, w2, · · · , wm,
t ∈ R, and outputs
I[w1x1 + w2x2 + · · · + wmxm ≥ t].
(Replacing ≥ by &gt;, &lt; or ≤ gives the same
definition.)
</pre>
</td><td>

[Statement.lean, lines 1770–1773](../Statement.lean#L1770-L1773)

<pre title="Statement.lean, lines 1770–1773">
/-- CTW26 Definition 3.1, PDF p.9: "THR: This gate has parameters w1, w2, · · · , wm, t ∈ R". -/
structure THRGate (m : ℕ) where
  w : Fin m → ℝ
  t : ℝ
</pre>

<pre title="Statement.lean, lines 1775–1777">
/-- CTW26 Definition 3.1, PDF p.9: the THR gate "outputs I[w1x1 + w2x2 + · · · + wmxm ≥ t]". -/
noncomputable def THRGate.output {m : ℕ} (g : THRGate m) (x : Fin m → ℝ) : ℕ :=
  I (∑ i, g.w i * x i ≥ g.t)
</pre>

<pre title="Statement.lean, lines 1779–1780">
/-- CTW26 Definition 3.1, PDF p.9: "on input (x1, x2, · · · , xm) ∈ {0, 1}^m". -/
def IsInput {m : ℕ} (x : Fin m → ℝ) : Prop := ∀ i, x i = 0 ∨ x i = 1
</pre>

</td></tr>
<tr><td>
<b>PDF p. 9</b>
<pre>
For any mathematical statement α, let I[α] be the
indicator that α holds, i.e., it equals 1 if α holds
and 0 otherwise.
</pre>
</td><td>

[Statement.lean, lines 1766–1768](../Statement.lean#L1766-L1768)

<pre title="Statement.lean, lines 1766–1768">
/-- CTW26 §3, PDF p.9: "let I[α] be the indicator that α holds, i.e., it equals 1 if α holds
and 0 otherwise." -/
def I (α : Prop) [Decidable α] : ℕ := if α then 1 else 0
</pre>

</td></tr>
<tr><td>
<b>PDF p. 10</b>
<pre>
there is an equivalent THR gate
</pre>
The paper does not define “equivalent” separately; it is read as "gives the same output on every input in
{0, 1}^m".
</td><td>

[Statement.lean, lines 1782–1784](../Statement.lean#L1782-L1784)

<pre title="Statement.lean, lines 1782–1784">
/-- "an equivalent THR gate": the same output on every input in `{0,1}^m`. -/
def Equivalent {m : ℕ} (g h : THRGate m) : Prop :=
  ∀ x : Fin m → ℝ, IsInput x → g.output x = h.output x
</pre>

</td></tr>
<tr><td>
<b>PDF p. 10</b>
<pre>
all parameters are integers in range ±m^m
</pre>
</td><td>

[Statement.lean, lines 1786–1788](../Statement.lean#L1786-L1788)

<pre title="Statement.lean, lines 1786–1788">
/-- "an integer in range ±R": `p = k` for an integer `k` with `-R ≤ k ≤ R`. -/
def IsIntegerInRange (p : ℝ) (R : ℕ) : Prop :=
  ∃ k : ℤ, p = (k : ℝ) ∧ -(R : ℤ) ≤ k ∧ k ≤ (R : ℤ)
</pre>

</td></tr>
</table>

Superscripts are written with `^`: `±m^m` is ±m<sup>m</sup>.

**What to check** (a few minutes):

1. The quantifiers are in the paper's order: for every number of inputs m and every THR gate g on m inputs, there
   is a gate h that is equivalent to g and whose parameters are all integers in range ±m^m.
2. A THR gate has real weights w1, …, wm and a real threshold t, and it outputs I[w1x1 + · · · + wmxm ≥ t]. The
   comparison in `THRGate.output` is ≥, as printed in Definition 3.1.
3. The inputs are the 0-1 vectors (`IsInput`), and “equivalent” means the same output on every such input
   (`Equivalent`).
4. “all parameters” covers the weights and the threshold, since Definition 3.1 lists both: the statement bounds
   every weight of h and its threshold.
5. “integers in range ±m^m”: each is an integer k with −m^m ≤ k ≤ m^m (`IsIntegerInRange`).
6. m ranges over every natural number, including m = 0, where Lean reads 0^0 as 1. Lean proves that the statement
   holds at m = 0 (`ctw26_lemma3_2_at_zero`), and that it would be false there if 0^0 were read as 0
   (`ctw26_at_zero_needs_zero_pow_zero_eq_one`); so the convention used is the true one.

   [Bindings/CTW26_Lemma3_2.lean, lines 48–69](../Bindings/CTW26_Lemma3_2.lean#L48-L69)

   [Bindings/CTW26_Lemma3_2.lean, lines 71–85](../Bindings/CTW26_Lemma3_2.lean#L71-L85)

**Documented deviations:** none.

Lean also proves that this statement gives what the proof uses (`ctw26_to_import`); you need not read it.

[Bindings/CTW26_Lemma3_2.lean, lines 94–126](../Bindings/CTW26_Lemma3_2.lean#L94-L126)

**Class:** literal.

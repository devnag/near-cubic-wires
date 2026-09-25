# 5. Prime theta bound: RS62 Theorem 4, (3.14)

The main theorem assumes the Lean statement in the first row of the table below. It is inequality (3.14) of
Theorem 4 of Rosser and Schoenfeld. The other rows show the definition it uses. Lean also proves that this
statement is equivalent to the form the proof uses (last section).

Paper: J. B. Rosser, L. Schoenfeld, "Approximate Formulas for Some Functions of Prime Numbers", Illinois Journal
of Mathematics 6(1), 64–94 (1962), https://doi.org/10.1215/ijm/1255631807. Page numbers refer to the PDF scan
of the article (31 pages, printed pp. 64–94) from https://denisevellachemla.eu/Rosser-Schoenfeld-1962.pdf,
SHA-256 8e37b06f82e09421bceb2502578c47b61469141f0287e6acedb70e01765ab556. The scan's text layer is garbled, so
every quotation below was checked against the page image.

<table>
<tr><th>Paper (verbatim)</th><th>Lean (verbatim)</th></tr>
<tr><td>
<b>PDF p. 7</b> (printed p. 70; checked against the page image)
<pre>
THEOREM 4. We have
(3.14)  x(1 − 1/(2 log x)) &lt; ϑ(x)  for 563 ≦ x,
</pre>
</td><td>

[Statement.lean, lines 1959–1962](../Statement.lean#L1959-L1962)

<pre title="Statement.lean, lines 1959–1962">
/-- **RS62 Theorem 4, eq. (3.14), PDF page 7 (printed p.70), verbatim:**
"THEOREM 4. We have (3.14) x(1 − 1/(2 log x)) &lt; ϑ(x) for 563 ≦ x," -/
def RS62_Theorem4_eq314 : Prop :=
  ∀ x : ℝ, 563 ≤ x → x * (1 - 1 / (2 * Real.log x)) &lt; theta x
</pre>

</td></tr>
<tr><td>
<b>PDF p. 1</b> (printed p. 64; checked against the page image)
<pre>
Counting 2 as the first prime, we denote by π(x),
ϑ(x), and ψ(x), respectively, the number of primes
≦ x, the logarithm of the product of all primes
≦ x, and the logarithm of the least common multiple
of all positive integers ≦ x; if x &lt; 2, we take
π(x) = ϑ(x) = ψ(x) = 0. … Throughout, n shall
denote a positive integer, p a prime, and x a real
number.
</pre>
<b>PDF p. 3</b> (printed p. 66; checked against the page image)
<pre>
Let us define the logarithmic integral li(x) by
(2.15)  li(x) = Ei(log x),
where Ei(y) is the exponential integral, defined by
(2.16)  Ei(y) = lim_{ε→0+} {∫_{−∞}^{−ε} e^t dt/t
                            + ∫_ε^y e^t dt/t}.
Then
(2.17)  ∫_2^x dy/log y = li(x) − li(2).
</pre>
</td><td>

[Statement.lean, lines 1954–1957](../Statement.lean#L1954-L1957)

<pre title="Statement.lean, lines 1954–1957">
/-- RS62 §2, PDF p.1 (printed p.64): `ϑ(x)` is "the logarithm of the product of all primes
≦ x" (natural logarithm, see the module docstring for (2.15)-(2.17)). -/
noncomputable def theta (x : ℝ) : ℝ :=
  Real.log (∏ᶠ p ∈ {p : ℕ | p.Prime ∧ (p : ℝ) ≤ x}, (p : ℝ))
</pre>

[Bindings/RS62_Theorem4.lean, lines 62–72](../Bindings/RS62_Theorem4.lean#L62-L72)

<pre title="Bindings/RS62_Theorem4.lean, lines 62–72">
/-- RS62's convention "if x &lt; 2, we take ϑ(x) = 0" holds for the literal definition. -/
theorem theta_eq_zero_of_lt_two {x : ℝ} (hx : x &lt; 2) : theta x = 0 := by
  rw [rs62_theta_eq]
  unfold chebyshevTheta
  refine Finset.sum_eq_zero fun p hp =&gt; ?_
  exfalso
  obtain ⟨hr, hprime⟩ := Finset.mem_filter.mp hp
  have hfl : ⌊x⌋₊ &lt; 2 := (Nat.floor_lt' (by norm_num)).mpr (by exact_mod_cast hx)
  have h2 := hprime.two_le
  have hlt := Finset.mem_range.mp hr
  omega
</pre>

</td></tr>
</table>

Superscripts are written with `^` and subscripts with `_`: `∫_2^x` is the integral from 2 to x.

**What to check** (a few minutes):

1. The statement is (3.14) with its range: for every real x with 563 ≤ x, x(1 − 1/(2 log x)) &lt; ϑ(x). The
   inequality is strict, as printed.
2. x is a real number, as the paper says on p. 1.
3. ϑ(x) is the logarithm of the product of all primes p ≤ x (`theta`). The set of such primes is finite, and the
   product is taken over exactly that set.
4. log is the natural logarithm (Mathlib's `Real.log`). The paper does not say so in words, but (2.15)–(2.17)
   force it: differentiating (2.17), with Ei′(y) = e^y / y from (2.16), gives
   1/log x = li′(x) = e^(log x) · (log x)′ / log x, so e^(log x) · (log x)′ = 1. That holds for the natural
   logarithm and for no other base.
5. The paper's convention ϑ(x) = 0 for x &lt; 2 is a consequence of the definition (`theta_eq_zero_of_lt_two`). The
   statement never uses it, since x ≥ 563.

**Documented deviations:** none.

**The proved equivalence** (you need not read it). The proof uses the form below: (3.14) for the finite-sum
theta, together with the weaker bound x/3 ≤ ϑ(x). For x ≥ 563 we have log x > 1, so (3.14) gives
ϑ(x) > x/2 ≥ x/3. Lean proves that the two forms are equivalent: the paper's statement implies the form the proof
uses (`rs62_to_import`), and the converse also holds (`import_to_rs62`). So the assumption says no more than
(3.14).

[Proof/Foundations/SourceInterfaces.lean, lines 234–237](../Proof/Foundations/SourceInterfaces.lean#L234-L237)

<pre title="Proof/Foundations/SourceInterfaces.lean, lines 231–232">
noncomputable def chebyshevTheta (x : ℝ) : ℝ :=
  ∑ p ∈ (Finset.range (⌊x⌋₊ + 1)).filter Nat.Prime, Real.log p
</pre>

<pre title="Proof/Foundations/SourceInterfaces.lean, lines 234–237">
def PrimeThetaBoundContract : Prop :=
  ∀ x : ℝ, 563 ≤ x →
    x * (1 - 1 / (2 * Real.log x)) &lt; chebyshevTheta x ∧
    x / 3 ≤ chebyshevTheta x
</pre>

[Bindings/RS62_Theorem4.lean, lines 100–107](../Bindings/RS62_Theorem4.lean#L100-L107)

<pre title="Bindings/RS62_Theorem4.lean, lines 100–107">
/-- **Adapter.** The literal RS62 (3.14) implies the imported `PrimeThetaBoundContract`
(its extra `x / 3 ≤ ϑ(x)` clause is an elementary consequence on `x ≥ 563`). -/
theorem rs62_to_import : RS62_Theorem4_eq314 → PrimeThetaBoundContract := by
  intro h
  refine rs62_prime_contract_iff.mpr ?_
  intro x hx
  rw [← rs62_theta_eq]
  exact h x hx
</pre>

<pre title="Bindings/RS62_Theorem4.lean, lines 109–113">
/-- The converse also holds: the import says no more than (3.14). -/
theorem import_to_rs62 : PrimeThetaBoundContract → RS62_Theorem4_eq314 := by
  intro h x hx
  rw [rs62_theta_eq]
  exact rs62_prime_contract_iff.mp h x hx
</pre>

**Class:** literal.

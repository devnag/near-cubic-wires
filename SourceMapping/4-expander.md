# 4. Expander: HLW06 Construction 8.1 / Theorem 8.2

The main theorem assumes the Lean statement in the first row of the table below. It is Theorem 8.2 of the survey
by Hoory, Linial and Wigderson (due to Gabber and Galil), for the graphs of their Construction 8.1. The other rows
show every definition that statement uses.

Paper: S. Hoory, N. Linial, A. Wigderson, "Expander Graphs and Their Applications", Bulletin of the American
Mathematical Society 43(4), 439–561 (2006), https://doi.org/10.1090/S0273-0979-06-01126-8. Page numbers refer to
the PDF at
https://www.math.ias.edu/~avi/PUBLICATIONS/MYPAPERS/HLW06/hlw06.pdf, SHA-256
b733e23c10bb94448e86e86cd2a7300e7469b3a8c393214e0fdd14ba90661bd4.

<table>
<tr><th>Paper (verbatim)</th><th>Lean (verbatim)</th></tr>
<tr><td>
<b>PDF p. 65</b>
<pre>
Theorem 8.2 (Gabber-Galil [GG81]). The graph Gn
satisfies λ(Gn) ≤ 5√2 &lt; 8 for every positive
integer n.
</pre>
</td><td>

[Statement.lean, lines 1920–1938](../Statement.lean#L1920-L1938)

<pre title="Statement.lean, lines 1920–1938">
/-- **HLW06 Theorem 8.2 (Gabber–Galil [GG81]), PDF p.65, verbatim:**
"The graph Gn satisfies λ(Gn) ≤ 5√2 &lt; 8 for every positive integer n."

`[NeZero n]` says that `n` is a positive integer. `λ(G_n) = max(|λ2|, |λn|)` is asserted
whenever `λ2` exists (`2 ≤ |V| = n²`, i.e. `n ≥ 2`).

**The edge `n = 1`.** `G_1` has one vertex and eight
loops, so its adjacency matrix is `(8)`. Its only eigenvalue is `λ1 = λn = 8`
(`G1_eigenvalue`), and `λ2` does not exist. The printed formula `max(|λ2|, |λn|)` is therefore
undefined at `n = 1`. A transcription that reads `λ(G_1)` as `|λn|` would make the theorem
FALSE there (`G1_naive_lambda_false`: `¬ |λn(G_1)| ≤ 5√2`). HLW's own words, "λ is the largest
absolute value of an eigenvalue other than λ1 = d" (PDF p.16), give the empty maximum at a
single vertex. So this literal asserts the bound exactly when `λ2` exists, which is the weakest
faithful reading. The imported `ExpanderSpectrumContract` is vacuous at `m = 1`, because a
mean-zero vector on one vertex is zero, and `hlw06_to_import` handles that case directly. -/
def HLW06_Theorem8_2 : Prop :=
  ∀ (n : ℕ) [NeZero n] (h2 : 2 ≤ Fintype.card (V n)),
    hlwLambda (adjacency n) (adjacency_isHermitian n) h2 ≤ 5 * Real.sqrt 2 ∧
      5 * Real.sqrt 2 &lt; 8
</pre>

</td></tr>
<tr><td>
<b>PDF p. 65</b>
<pre>
Construction 8.1. Define the following 8-regular
graph Gn = G = (V,E) on the vertex set
V = Zn × Zn. Let
…
Each vertex v = (x, y) is adjacent to the four
vertices T1v, T2v, T1v + e1, T2v + e2, and the
other four neighbors of v obtained by the four
inverse transformations. Note that all
calculations are mod n and that this is an
undirected 8-regular graph (that may have multiple
edges and self loops).
</pre>
<b>PDF p. 65</b> (checked against the page image; the text layer loses the matrix layout)
<pre>
T1 = (1 2; 0 1), T2 = (1 0; 2 1),
e1 = (1; 0), e2 = (0; 1).
</pre>
Matrices are written row by row, rows separated by ";".
</td><td>

[Statement.lean, lines 1815–1816](../Statement.lean#L1815-L1816)

<pre title="Statement.lean, lines 1815–1816">
/-- HLW Construction 8.1: "the vertex set V = Zn × Zn". -/
abbrev V (n : ℕ) := ZMod n × ZMod n
</pre>

<pre title="Statement.lean, lines 1818–1819">
/-- HLW Construction 8.1: "T1 = (1 2; 0 1)". -/
def T1 {n : ℕ} : Matrix (Fin 2) (Fin 2) (ZMod n) := !![1, 2; 0, 1]
</pre>

<pre title="Statement.lean, lines 1821–1822">
/-- HLW Construction 8.1: "T2 = (1 0; 2 1)". -/
def T2 {n : ℕ} : Matrix (Fin 2) (Fin 2) (ZMod n) := !![1, 0; 2, 1]
</pre>

<pre title="Statement.lean, lines 1824–1825">
/-- HLW Construction 8.1: "e1 = (1; 0)". -/
def e1 {n : ℕ} : V n := (1, 0)
</pre>

<pre title="Statement.lean, lines 1827–1828">
/-- HLW Construction 8.1: "e2 = (0; 1)". -/
def e2 {n : ℕ} : V n := (0, 1)
</pre>

<pre title="Statement.lean, lines 1830–1832">
/-- `T v` for the vertex `v = (x, y)` read as the column vector `(x; y)`, mod n. -/
def act {n : ℕ} (T : Matrix (Fin 2) (Fin 2) (ZMod n)) (v : V n) : V n :=
  ((T *ᵥ ![v.1, v.2]) 0, (T *ᵥ ![v.1, v.2]) 1)
</pre>

<pre title="Statement.lean, lines 1834–1837">
/-- The four transformations of Construction 8.1, in HLW's order:
`v ↦ T1v, T2v, T1v + e1, T2v + e2`. -/
def forward {n : ℕ} (i : Fin 4) (v : V n) : V n :=
  ![act T1 v, act T2 v, act T1 v + e1, act T2 v + e2] i
</pre>

[Statement.lean, lines 1861–1863](../Statement.lean#L1861-L1863)

<pre title="Statement.lean, lines 1861–1863">
/-- The four transformations as bijections of `V`. -/
noncomputable def transformation {n : ℕ} (i : Fin 4) : V n ≃ V n :=
  Equiv.ofBijective (forward i) (forward_bijective i)
</pre>

<pre title="Statement.lean, lines 1865–1870">
/-- **HLW Construction 8.1, the neighbours of `v`:** "the four vertices T1v, T2v, T1v + e1,
T2v + e2, and the other four neighbors of v obtained by the four inverse transformations". -/
noncomputable def neighbor {n : ℕ} (k : Fin 8) (v : V n) : V n :=
  ![transformation 0 v, transformation 1 v, transformation 2 v, transformation 3 v,
    (transformation 0).symm v, (transformation 1).symm v, (transformation 2).symm v,
    (transformation 3).symm v] k
</pre>

<pre title="Statement.lean, lines 1872–1874">
/-- The neighbour multiset of `v` (loops and multiple edges kept). -/
noncomputable def neighbors {n : ℕ} (v : V n) : Multiset (V n) :=
  Finset.univ.val.map fun k : Fin 8 =&gt; neighbor k v
</pre>

</td></tr>
<tr><td>
<b>PDF p. 14</b>
<pre>
Unless we say otherwise, a graph G = (V,E) is
undirected and d-regular (all vertices have the
same degree d; that is each vertex is incident to
exactly d edges). Self loops and multiple edges
are allowed.
</pre>
<b>PDF p. 15</b>
<pre>
The Adjacency Matrix of an n-vertex graph G,
denoted A = A(G), is an n × n matrix whose (u, v)
entry is the number of edges in G between vertex u
and vertex v.
</pre>
</td><td>

[Statement.lean, lines 1876–1879](../Statement.lean#L1876-L1879)

<pre title="Statement.lean, lines 1876–1879">
/-- **HLW §2.3 adjacency matrix of `G_n`:** the `(u, w)` entry is "the number of edges in G
between vertex u and vertex w", the multiplicity of `w` among the neighbours of `u`. -/
noncomputable def adjacency (n : ℕ) : Matrix (V n) (V n) ℝ :=
  fun u w =&gt; ((neighbors u).count w : ℝ)
</pre>

[Statement.lean, lines 1908–1910](../Statement.lean#L1908-L1910)

<pre title="Statement.lean, lines 1908–1910">
/-- HLW §2.3: "Being real and symmetric". -/
theorem adjacency_isHermitian (n : ℕ) : (adjacency n).IsHermitian :=
  Matrix.IsHermitian.ext fun i j =&gt; by rw [star_trivial]; exact adjacency_symm j i
</pre>

</td></tr>
<tr><td>
<b>PDF p. 15</b>
<pre>
Being real and symmetric, the matrix A has n real
eigenvalues which we denote by
λ1 ≥ λ2 ≥ · · · ≥ λn.
</pre>
<b>PDF p. 16</b>
<pre>
Given a d-regular graph G with n vertices, we
denote λ = λ(G) = max(|λ2|, |λn|). In words, λ is
the largest absolute value of an eigenvalue other
than λ1 = d.
</pre>
</td><td>

[Statement.lean, lines 1912–1918](../Statement.lean#L1912-L1918)

<pre title="Statement.lean, lines 1912–1918">
/-- HLW §2.4, PDF p.16: "λ = λ(G) = max(|λ2|, |λn|)", where (§2.3) "λ1 ≥ λ2 ≥ · · · ≥ λn" are the
eigenvalues of the real symmetric adjacency matrix. HLW's `λi` is `eigenvalues₀ ⟨i - 1, _⟩`,
so `λ2 = eigenvalues₀ ⟨1, _⟩` and `λn = eigenvalues₀ ⟨|V| - 1, _⟩`. The hypothesis `2 ≤ |V|`
is what makes `λ2` exist. -/
noncomputable def hlwLambda {W : Type*} [Fintype W] [DecidableEq W] (A : Matrix W W ℝ)
    (hA : A.IsHermitian) (h2 : 2 ≤ Fintype.card W) : ℝ :=
  max |hA.eigenvalues₀ ⟨1, by omega⟩| |hA.eigenvalues₀ ⟨Fintype.card W - 1, by omega⟩|
</pre>

<pre title="Bindings/HLW06_Theorem8_2.lean, lines 134–137">
/-- The index list `λ1, …, λn` is non-increasing, as HLW write it. -/
theorem eigenvalues₀_sorted {W : Type*} [Fintype W] [DecidableEq W] (A : Matrix W W ℝ)
    (hA : A.IsHermitian) : Antitone hA.eigenvalues₀ :=
  hA.eigenvalues₀_antitone
</pre>

<pre title="Bindings/HLW06_Theorem8_2.lean, lines 139–144">
/-- The list `[λ1, …, λn]` is the multiset of roots of the characteristic polynomial (the
eigenvalues, with multiplicity) sorted non-increasingly. -/
theorem eigenvalues₀_sorted_roots {W : Type*} [Fintype W] [DecidableEq W] (A : Matrix W W ℝ)
    (hA : A.IsHermitian) :
    List.ofFn hA.eigenvalues₀ = (A.charpoly.roots.map RCLike.re).sort (· ≥ ·) :=
  hA.sort_roots_charpoly_eq_eigenvalues₀.symm
</pre>

</td></tr>
</table>

In the paper's text Gn, Zn, T1, λ2 are G<sub>n</sub>, Z<sub>n</sub>, T<sub>1</sub>, λ<sub>2</sub>. The graph
G<sub>n</sub> has n² vertices, so in §2.3–2.4 "n" (the number of vertices) is n² here.

**What to check** (a few minutes):

1. The vertex set is Z<sub>n</sub> × Z<sub>n</sub> (`V`), so all arithmetic is mod n. The four maps
   are v ↦ T1v, T2v, T1v + e1, T2v + e2 (`forward`), with T1, T2, e1, e2 as printed.
2. The other four neighbours are the images of v under the inverses of these four maps. The Lean definition takes
   the inverse of each bijection (`transformation`), and no inverse formula is written into the graph.
3. The (u, w) entry of the adjacency matrix is the number of the eight neighbour slots of u that equal w
   (`adjacency`). Self loops and multiple edges are kept, as §2.1 allows. Lean proves that every row sums to 8
   (`adjacency_row`) and that the matrix is symmetric (`adjacency_symm`).
4. λ1 ≥ λ2 ≥ · · · are Mathlib's eigenvalues of the real symmetric matrix, sorted non-increasingly
   (`eigenvalues₀`, indexed from 0, so λ2 is index 1). Lean proves they are the roots of the characteristic
   polynomial with multiplicity, in that order (`eigenvalues₀_sorted_roots`).
5. λ(G) = max(|λ2|, |λ<sub>last</sub>|), as on p. 16 (`hlwLambda`). The statement asserts λ(Gn) ≤ 5√2 and
   5√2 < 8 for every positive n (`NeZero n`) whose graph has a second eigenvalue: see the deviation below.

**Documented deviations** (each has a Lean proof; you need not read it):

- n = 1. G<sub>1</sub> has one vertex with eight self loops; its adjacency matrix is (8), its only eigenvalue is
  λ1 = 8 (`G1_eigenvalue`), and λ2 does not exist. The printed formula max(|λ2|, |λn|) is then undefined, and
  HLW's own words, “the largest absolute value of an eigenvalue other than λ1 = d”, give an empty maximum. The
  Lean statement asserts the bound exactly when λ2 exists (at least two vertices, that is n ≥ 2). Reading
  λ(G<sub>1</sub>) as |λn| = 8 instead would make the printed theorem false at n = 1 (`G1_naive_lambda_false`).
  The proof never needs n = 1: there the property it uses holds trivially, and the adapter treats that case
  directly.

  [Bindings/HLW06_Theorem8_2.lean, lines 151–178](../Bindings/HLW06_Theorem8_2.lean#L151-L178)

  [Bindings/HLW06_Theorem8_2.lean, lines 180–188](../Bindings/HLW06_Theorem8_2.lean#L180-L188)

Lean also proves that this statement gives what the proof uses (`hlw06_to_import`); you need not read it.

[Bindings/HLW06_Theorem8_2.lean, lines 355–376](../Bindings/HLW06_Theorem8_2.lean#L355-L376)

**Class:** literal.

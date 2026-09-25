# Near-cubic wire lower bounds for SYM∘THR and THR∘THR: a Lean proof of Theorem 2.5

This repository contains a complete Lean 4 proof of Theorem 2.5 of "Almost-Everywhere Near-Cubic Wire Lower
Bounds for SYM∘THR and THR∘THR" (Dev Nag; ECCC [TR26-167](https://eccc.weizmann.ac.il/report/2026/167/);
[doi:10.5281/zenodo.21984711](https://doi.org/10.5281/zenodo.21984711)). [`paper/paper.tex`](paper/paper.tex) is
version 1 (17 August 2026, [doi:10.5281/zenodo.21984712](https://doi.org/10.5281/zenodo.21984712)), the version this
proof was checked against; Theorem 2.5 is unchanged in version 2 (15 September 2026,
[doi:10.5281/zenodo.22773981](https://doi.org/10.5281/zenodo.22773981)):

> For every fixed 0<γ<1/2, there exist a common language F_γ ∈ E^NP and positive constants b_{S,γ}, b_{T,γ}
> such that, for every sufficiently large n, agreement at least 1/2+γ with (F_γ)_n implies
> W(C) > b_{S,γ} n³/L⁵ for C ∈ SYM∘THR, and W(C) > b_{T,γ} n³/L⁹ for C ∈ THR∘THR.

The proof assumes nine published results. Each is written in Lean as a transcription of the published sentence,
and Lean checks: those nine statements ⇒ Theorem 2.5, using only Lean's three standard axioms.

## Verify it

1. Install Lean (Linux or macOS, one line):

   ```
   curl -sSfL https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh | sh -s -- -y --default-toolchain none && . ~/.elan/env
   ```

2. In this directory run `make`. It downloads prebuilt Mathlib (about 5 GB), builds the proof and runs
   `Check.lean`. It takes about 2½ hours on a large machine (measured: 2 h 13 min on 90 cores). The build is
   limited by a long chain of dependent modules, so fewer cores add less time than you might expect. It needs about
   65 GB of disk; 32 GB of RAM is recommended.
3. While it runs, check the pages in [`SourceMapping/`](SourceMapping/): eight pages for the nine published
   statements (page 6 covers two), plus one for Theorem 2.5. Each puts a published sentence beside the Lean definition that must say the same
   thing, with a short list of what to check.

## Reading the output

The run ends by printing (a) Theorem 2.5 written out in Lean, (b) the main theorem, published statements ⇒
Theorem 2.5, (c) its axioms, which must be exactly `[propext, Classical.choice, Quot.sound]` (an unfinished proof
would show `sorryAx`), (d) one `assumes:` line per hypothesis, and (e) `PASS` or `FAIL`. `PASS` means the
hypotheses are exactly the nine below, in this order, and the conclusion is Theorem 2.5.

## What is assumed

| # | Hypothesis | Published result | Class | Page |
|---|---|---|---|---|
| 1 | `CTW26_Lemma3_2` | Chen, Tal, Wang (ECCC TR26-039) Lemma 3.2, after Muroga, Toda, Takasu (1961); PDF p. 10 | literal | [1](SourceMapping/1-threshold-normalization.md) |
| 2 | `CW19_Proposition18_2_TM2` | Chen, Williams (CCC 2019) Proposition 18(2); PDF p. 14 | literal, construction in Mathlib's machine model | [2](SourceMapping/2-decomposition.md) |
| 3 | `Williams14_Corollary4_4` | Williams (J. ACM 2014) Corollary 4.4 = C.2; PDF pp. 17, 29 | literal, multitape reading | [3](SourceMapping/3-matrix-product.md) |
| 4 | `HLW06_Theorem8_2` | Hoory, Linial, Wigderson (Bull. AMS 2006) Construction 8.1 / Theorem 8.2; PDF p. 65 | literal | [4](SourceMapping/4-expander.md) |
| 5 | `RS62_Theorem4_eq314` | Rosser, Schoenfeld (1962) Theorem 4, (3.14); PDF p. 7 | literal | [5](SourceMapping/5-prime-theta.md) |
| 6 | `CLW20_Lemma3_10_TM2` | Chen, Lyu, Williams (ECCC TR20-150) Lemma 3.10, after Ben-Sasson, Viola; PDF p. 18 | literal, algorithm in Mathlib's machine model | [6](SourceMapping/6-pcp.md) |
| 7 | `CLW20_Lemma3_11_explicitEnc_TM2` | Chen, Lyu, Williams Lemma 3.11, after CW19 and VW20; PDF p. 18 | literal + documented fix (n ≥ 2, encoder written out) | [6](SourceMapping/6-pcp.md) |
| 8 | `CLW20_Theorem1_13` | Chen, Lyu, Williams Theorem 1.13 (refuter with an NP oracle); PDF p. 6 | literal, multitape reading | [7](SourceMapping/7-refuter.md) |
| 9 | `CLW20_Lemma3_9_TM2` | Chen, Lyu, Williams Lemma 3.9, after Sudan, Trevisan, Vadhan Theorem 24; PDF p. 18 | literal, algorithm in Mathlib's machine model | [8](SourceMapping/8-amplifier.md) |

Hypotheses 6 and 7 share page 6: CLW20 Lemmas 3.10 and 3.11 are used together as one PCP step. The conclusion,
`NearCubicWires.Paper.theorem_2_5`, is compared with the paper on
[`SourceMapping/theorem-2-5.md`](SourceMapping/theorem-2-5.md). CLW20 Lemma 3.8 (the XOR lemma) is not assumed:
Lean proves it, following the paper's proof in CLW20 Appendix A.

## What to read

Read `Challenge.lean`, `Statement.lean`, `StatementChecks/` and `SourceMapping/`. `Statement.lean` holds every
definition the theorem's statement uses, with the nine published statements last. `StatementChecks/` proves that
the statement is not trivially satisfiable and that its wire count is the paper's W(C). `Bindings/` and `Proof/`
are checked by Lean; you need not read them. Declaration names inside `Proof/` keep their original names, some from
the development (for example the `Repair…` namespaces); renaming them is a large mechanical change that would not affect any statement, and was not made.

## Caveats

- The published results are assumed, not formalized.
- Docstrings say "Tier 1" for the proof's own multitape machine model (the `LocalBitMultitapeCore` section of
  `Statement.lean`, with the word-function wrapper in its `OrdinaryMachine` section) and "Tier 2" for Mathlib's
  standard `Turing.TM2` model. Where a published result promises an algorithm, the algorithm is stated in Tier 2,
  except for Williams's multiplication and the CLW20 refuter, which are read in the multitape model those papers
  name. Machines a result quantifies over (hypotheses about them) stay in Tier 1, which only weakens the
  assumption.
- Documented deviations, each with a Lean proof, are on the pages: CLW20 Lemma 3.11 as printed is false at n = 1
  (`clw20_lemma3_11_asPrinted_false`), so it is assumed for n ≥ 2 with the encoder's supports written out; Lemma
  3.10 is claimed for n ≥ 1 (at n = 0 the printed bound divides by zero); HLW06 Theorem 8.2 is asserted when λ2
  exists (n ≥ 2); CW19 Proposition 18(2) takes integer gates with the appendix's strict comparison; the CLW20
  refuter's promise machines guess ⌊n/16⌋ bits, within the printed n/10.
- E^NP is ordinary exponential time with an NP oracle, and L = ⌈log₂(n+2)⌉ (page "Theorem 2.5").

## Optional extra checks

- `make kernel-replay`: re-check every declaration with Lean's independent `leanchecker` (slow; parallel).
- To avoid prebuilt Mathlib binaries, remove `lake exe cache get` from the Makefile (Mathlib then builds from
  source, adding 1–3 hours).
- `python3 scripts/check_names.py .`: the naming check used by CI.
- **comparator** ([leanprover/comparator](https://github.com/leanprover/comparator), Linux only). `Challenge.lean`
  states the main theorem from `Statement.lean` and Mathlib alone: the nine published statements imply Theorem 2.5.
  Its proof is a deliberate `sorry`, the only one in the repository: it is the statement comparator checks the proof
  against. `Check.lean` does not import it. `Solution.lean` proves the same statement with the main theorem.
  Comparator builds both inside a sandbox and compares them. It then replays the proof through Lean's kernel and,
  if enabled, through the independent nanoda kernel.

  Install the four tools in user space (needs Go from go.dev, Rust from rustup.rs, and elan):
  ```
  git clone https://github.com/Zouuup/landrun && (cd landrun && git checkout 5e9a0d1 && go build -o landrun ./cmd/landrun)
  git clone --branch v4.32.0 https://github.com/leanprover/lean4export && (cd lean4export && lake build)
  git clone --branch v4.32.0 https://github.com/leanprover/comparator && (cd comparator && lake build)
  git clone https://github.com/ammkrn/nanoda_lib && (cd nanoda_lib && cargo build --release)
  export PATH="$PWD/landrun:$PWD/lean4export/.lake/build/bin:$PWD/nanoda_lib/target/release:$PATH"
  ```
  landrun is pinned because later landrun commits drop the `--` that comparator v4.32.0 passes to lean4export
  (comparator v4.33.0 adapts to them).

  Run it in a fresh clone of this repository, so that the proof is built only inside comparator's sandbox:
  ```
  lake exe cache get
  systemd-run --property=RestrictAddressFamilies=~AF_UNIX --user --pty -E PATH="$PATH" --working-directory $(pwd) -- bash -c 'ulimit -s unlimited && lake env /path/to/comparator/.lake/build/bin/comparator comparator.json'
  ```
  `make comparator COMPARATOR=/path/to/comparator/.lake/build/bin/comparator` does the same. `ulimit -s unlimited`
  is needed because nanoda recurses deeply. `systemd-run --user --pty` needs a user D-Bus session; desktop Linux has
  one, and on a minimal server install `dbus-user-session`.

  Cost, measured on one machine: with Lean's kernel only (`"enable_nanoda": false` in `comparator.json`, as shipped)
  the export, comparison and kernel replay take about 3.5 hours and 64 GB of RAM, after comparator's sandboxed build of
  the proof (in a fresh clone, add the build time above). The nanoda check (set `"enable_nanoda": true`) needs more than
  150 GB of RAM; it did not complete on this machine within that limit.

  Success ends with `Your solution is okay!`. The theorem `NearCubicWires.theorem_2_5_from_literature` in
  `Solution.lean` then
  1. proves the same statement as in `Challenge.lean`;
  2. uses no axioms beyond `propext`, `Quot.sound` and `Classical.choice`;
  3. is accepted by the Lean kernel, and by nanoda when it is enabled.

  What to read: `Challenge.lean` (24 lines) and `Statement.lean` (2,495 lines, every definition the
  statement uses, with the nine published statements last). Comparator's trusted import closure is `Statement` plus
  Mathlib. You also trust `lakefile.toml`, the sandbox and the kernels.

License: Apache-2.0 ([LICENSE](LICENSE)), except `paper/`, which is CC BY 4.0. Quotations of other papers in
`SourceMapping/` and in docstrings are short quotations for verification and remain their authors'. How to cite:
[CITATION.cff](CITATION.cff).

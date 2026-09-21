# Private Math Research

Personal research notes, draft papers, and computational experiments by Thomas Scheuerle.

---

## Repository layout

| Folder | Purpose |
|--------|---------|
| [`drafts/`](drafts/) | Papers and notes in active development |
| `notes/` | Short observations, scratch calculations, open questions |
| `code/` | Standalone computational scripts (PARI/GP, Python, …) |
| `references/` | BibTeX files, OEIS links, reference lists |

> Files graduate from `notes/` → `drafts/` → (submitted/published) as they mature.

---

## Index of current files

### Lean Formalization

#### [`A328596/`](A328596/)
Lean 4 / Mathlib formalization of the binary Lyndon-word interpretation of OEIS A328596.

Current development status:
- reversed binary words are formalized via `Nat.bits`, using least-significant-bit first order;
- Lyndon words are defined transparently by comparison with all nontrivial rotations;
- an auxiliary suffix-based Lyndon formulation is proved equivalent and used for the core structural lemmas;
- powers of two are shown to lie in A328596;
- clearing the least-significant set bit preserves membership in the non-power-of-two branch;
- the main additive theorem is formalized:

```lean
theorem a328596_additive {n : Nat} (hn : 1 < n) (hA : InA328596 n) :
	∃ a b, InA328596 a ∧ InA328596 b ∧ n = a + b
```

Key project files:
- [`A328596/BinaryWords.lean`](A328596/BinaryWords.lean): reversed-binary arithmetic lemmas
- [`A328596/Lyndon.lean`](A328596/Lyndon.lean): Lyndon and suffix-Lyndon theory
- [`A328596/Sequence.lean`](A328596/Sequence.lean): sequence predicate, sanity check, and additive theorem
- [`A328596.lean`](A328596.lean): root import file

Build with:

```bash
lake build
```

### Drafts

#### [`drafts/somos_hankel_jacobi_revised5.tex`](drafts/somos_hankel_jacobi_revised5.tex)
**"A Somos-Type Constraint on Hankel Determinants and Jacobi Recurrence Coefficients"**
*Thomas Scheuerle and Michael Somos — September 2, 2026*

Starting from rational Somos-4 sequences, this paper identifies the orthogonal-polynomial meaning of the Somos quartic relation. The main result: the shifted Hankel determinants satisfy the Somos biquadratic if and only if consecutive off-diagonal Jacobi coefficients $\widehat{b}_n$ satisfy a fixed symmetric biquadratic equation. The diagonal Jacobi coefficients do not appear. The paper also studies the resulting two-dimensional symplectic map, whose invariant curves are genus-one (elliptic). A connection to OEIS A377264 and Stieltjes continued fractions is worked out in detail.

**Key topics:** Somos-4 sequences · Hankel determinants · Jacobi/three-term recurrences · orthogonal polynomials · continued fractions · elliptic curves · integrable maps

**Companion code:** [`drafts/somos_hankel_jacobi.gp`](drafts/somos_hankel_jacobi.gp)

---

#### [`drafts/gamma2.tex`](drafts/gamma2.tex)
**"Gamma-Function Representations of Selected Algebraic Numbers"**
*Thomas Scheuerle*

A computationally discovered reference catalogue. Each entry gives an algebraic number (described by its minimal polynomial and a chosen real root) together with an explicit expression as a product or quotient of $\Gamma$ values at rational arguments. The connection to cyclotomic fields via Euler's reflection formula is noted. No claim of completeness is made; the collection is intended as a reference resource and source of examples.

**Key topics:** Gamma function · special values · algebraic numbers · cyclotomic fields · reflection formula

---

### Code

#### [`drafts/somos_hankel_jacobi.gp`](drafts/somos_hankel_jacobi.gp)
PARI/GP companion script to the Somos–Hankel–Jacobi paper above (dated 31 August 2026).
Given Somos parameters $(p_1, p_2, p_3, p_4)$ and an optional starting root $r_0$, it:
- computes Stieltjes continued-fraction coefficients $d(k)$,
- constructs monic orthogonal polynomials from moments,
- verifies the Somos-4 recurrence on the shifted Hankel determinants,
- optionally guesses an algebraic generating function via `seralgdep`,
- prints Jacobi $\alpha/\beta$ coefficients and norms.

**Usage example** (classical seed $1,1,2,3$):
```gp
\r somos_hankel_jacobi.gp
somos_hankel_jacobi(1,1,-3,4,8,2)
```

---

## Open threads / TODO

- [ ] Lift the Somos constraint to a Volterra- or modified-Volterra-type transformation at the continued-fraction level (conjectural, flagged in paper).
- [ ] Extend the Gamma catalogue to cubic and higher-degree entries.
- [ ] Add a `references/` BibTeX file consolidating citations across drafts.

---

## Notes on conventions

- LaTeX source uses `\documentclass[11pt]{article}` with AMS packages.
- PARI/GP scripts set `\p 80` (80-digit precision) by default.
- File names use `_` as word separator; revision suffixes like `_revised5` are kept until submission.


/-
Copyright (c) 2026 Brandon Yates. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib

/-!
# Challenge: exact identities for the kicked Kloosterman map

This file is the human-auditable statement. It imports only Mathlib.

## The object

Fix a prime `p` and a nontrivial additive character `ψ : AddChar (ZMod p) ℂ`. The *Kloosterman
Hamiltonian* on `ℓ²(𝔽_p)` is the circulant matrix with entries `ψ((z − y)⁻¹)` off the diagonal
and `0` on it; in the additive-character (momentum) basis it is diagonal with eigenvalues the
Kloosterman sums `K(a; p) = ∑_{x ≠ 0} ψ(a x + x⁻¹)`. Its exponential
`U_{0,τ} = exp(−i τ 𝒦_p / √p)` is the *free propagator*, and multiplying it by a diagonal phase
`D_f |x⟩ = ψ(f(x))|x⟩` gives the *kicked Kloosterman map* `U_{f,τ} = D_f U_{0,τ}` — a quantized
map on a finite phase space whose free dispersion relation is a family of Kloosterman sums.

Kloosterman sums are due to Kloosterman (Acta Math. **49** (1926), 407–464). The square-root
bound `|K(a;p)| ≤ 2√p` for `a ≠ 0` is Weil's (Proc. Nat. Acad. Sci. U.S.A. **34** (1948),
204–207), and the monodromy of the associated sheaves is the subject of Katz's monograph
(*Gauss Sums, Kloosterman Sums, and Monodromy Groups*, Ann. of Math. Stud. 116, Princeton Univ.
Press, 1988). **No theorem in this file uses the Weil bound, or any étale-cohomological,
equidistribution or asymptotic input.** Every statement below is an exact identity at a fixed
finite prime, provable by rearrangement of finite sums and elementary counting.

Mathlib contains no Kloosterman sums (checked by name across the pinned revision), so
`kloostermanSum` and `kloostermanMatrix` are defined below from `AddChar` primitives. Each
definition carries its ordinary mathematical meaning and is used with no other.

Throughout, the manuscript's parameter combination `τ/√p` is carried by a single real
parameter `s`. Every statement is universally quantified over `s : ℝ`, hence covers every `τ`.

## What is compared

Eight theorems, in two groups.

*The first-moment package* (six theorems). `trace_floquet` factors the trace of the kicked
propagator as `Tr U_{f,τ} = φ_p(τ) · ∑_x ψ(f(x))`, where `φ_p(τ)` is the common diagonal entry
of the free propagator. `firstMoment` and `firstMoment_expectation` evaluate the average of
`|Tr U_{γg,τ}|²` over the kick strength `γ ∈ 𝔽_p^×` exactly, in terms of the fiber count
`N_g = #{(x,y) : g(x) = g(y)}`. `firstMoment_sq`, `firstMoment_cube_one_mod_three` and
`firstMoment_cube_two_mod_three` are its three arithmetic instantiations: `p|φ_p(τ)|²` for the
quadratic kick, `2p|φ_p(τ)|²` for the cubic kick when `p ≡ 1 (mod 3)`, and **exactly zero** for
the cubic kick when `p ≡ 2 (mod 3)`.

*Two corollaries of the affine-reflection classification* (two theorems).
`monomial_reflection_iff'` says a monomial kick `γx^d` over a prime field of odd characteristic
admits an affine reflection centre if and only if `d` is even. `no_antiunitary_sq_neg_one` says
that in odd dimension no antiunitary — written in the standard form `Θ = W ∘ (complex
conjugation)`, so that `Θ² = W · conj(W)` — squares to `−I`.

## What is NOT claimed — read this before the statements

**No statement in this file is a random-matrix, Sato–Tate, equidistribution or
spectral-statistics claim, and no such claim is made anywhere in this project.** Concretely:

* nothing here asserts that the spectrum of `U_{f,τ}` obeys a Wigner–Dyson law, a Poisson law,
  or any other level-spacing law; no gap-ratio statistic, spectral form factor, or symmetry-class
  assignment is formalized, and none is used;
* nothing here is an asymptotic statement. There is no limit in `p`, none in `τ`, and no error
  term. `firstMoment` is an identity at each fixed prime, not the leading term of one;
* `no_antiunitary_sq_neg_one` is a determinant fact about odd-dimensional complex matrices. It
  rules out one algebraic possibility; it does **not** assert that any particular ensemble,
  symmetry class or statistic *is* realized by these operators;
* the two primed theorems are strictly stronger than the manuscript statements they replace
  (see their docstrings), so each is proved without a hypothesis the manuscript carries. Nothing
  else is strengthened, weakened, or silently generalized.

The source of record is the author's manuscript *"Arithmetic control of Wigner–Dyson symmetry
classes in kicked Kloosterman maps"* (unpublished; submitted to a journal). Its internal labels
appear below: `prop:spec`, `cor:monomial` and `cor:nosymplectic` from the manuscript itself,
and `prop:firstmoment` with its equations `eq:tracefact` and `eq:firstmoment` from the
post-submission addition. The manuscript's numerical sections are not formalized here and
nothing below depends on them.

Dyson's terminology for the symmetry classes ("symplectic", used in the manuscript's own name
for `cor:nosymplectic`) is that of *The Threefold Way*, J. Math. Phys. **3** (1962), 1199–1215;
it is used here only to identify the corollary, not to assert anything about ensembles.
-/

namespace KickedKloosterman

open Finset Matrix

variable {p : ℕ}

section Operators

variable [NeZero p]

/-- The diagonal kick-phase operator `D_f |x⟩ = ψ(f(x)) |x⟩` — a unitary diagonal matrix whose
`x`-th entry is the character value `ψ(f x)` (manuscript eq. `eq:floquet`). -/
noncomputable def phaseMat (ψ : AddChar (ZMod p) ℂ) (f : ZMod p → ZMod p) :
    Matrix (ZMod p) (ZMod p) ℂ :=
  Matrix.diagonal fun x => ψ (f x)

/-- The **Kloosterman sum** `K(a; p) = ∑_{x ≠ 0} ψ(a x + x⁻¹)`, the classical exponential sum of
Kloosterman (1926), here written with `Finset.univ.erase 0` for the sum over `𝔽_p^×` and with
`x⁻¹` the field inverse in `ZMod p`. Mathlib has no Kloosterman sums, so this is the inline
definition from `AddChar` primitives. Its Weil bound is not used anywhere below. -/
noncomputable def kloostermanSum (ψ : AddChar (ZMod p) ℂ) (a : ZMod p) : ℂ :=
  ∑ x ∈ Finset.univ.erase (0 : ZMod p), ψ (a * x + x⁻¹)

/-- The **Kloosterman Hamiltonian** `𝒦_p = ∑_{x ≠ 0} ψ(x⁻¹) T_x`, where `T_x` is translation by
`x` (manuscript Definition `def:Kop`). As a matrix it is the circulant with symbol
`d ↦ ψ(d⁻¹)` off the diagonal and `0` on it: `(𝒦_p)_{z,y} = ψ((z − y)⁻¹)` for `z ≠ y`.
`Matrix.circulant v i j = v (i - j)` is stock Mathlib. Manuscript `prop:spec` identifies its
eigenvalues as the Kloosterman sums `K(a;p)`; that spectral fact is used in the proofs but is
not itself among the compared statements. -/
noncomputable def kloostermanMatrix (ψ : AddChar (ZMod p) ℂ) : Matrix (ZMod p) (ZMod p) ℂ :=
  Matrix.circulant fun d => if d = 0 then 0 else ψ (d⁻¹)

/-- The **free propagator** `U_{0,τ} = exp(−i τ 𝒦_p / √p)` (manuscript eq. `eq:floquet`), as the
matrix exponential `NormedSpace.exp` of `(−i s) · 𝒦_p`. The real parameter `s` carries the
manuscript's `τ/√p`; every theorem below quantifies over all `s : ℝ`. -/
noncomputable def freeProp (ψ : AddChar (ZMod p) ℂ) (s : ℝ) : Matrix (ZMod p) (ZMod p) ℂ :=
  NormedSpace.exp ((-(s : ℂ) * Complex.I) • kloostermanMatrix ψ)

/-- The scalar `φ_p(τ) = p⁻¹ ∑_a e^{−i τ K(a;p)/√p}` (manuscript `prop:firstmoment`, eq.
`eq:tracefact`), the momentum-space average of the free phases. It is the common value of every
diagonal entry of `freeProp`, which is why it factors out of the trace. Again `s` carries
`τ/√p`. -/
noncomputable def varphi (ψ : AddChar (ZMod p) ℂ) (s : ℝ) : ℂ :=
  (p : ℂ)⁻¹ * ∑ a : ZMod p, Complex.exp (-(s : ℂ) * Complex.I * kloostermanSum ψ a)

/-- The **kicked Floquet propagator** `U_{f,τ} = D_f U_{0,τ}` (manuscript eq. `eq:floquet`): one
free step followed by the kick phase. This is the operator whose traces are computed below. -/
noncomputable def floquet (ψ : AddChar (ZMod p) ℂ) (f : ZMod p → ZMod p) (s : ℝ) :
    Matrix (ZMod p) (ZMod p) ℂ :=
  phaseMat ψ f * freeProp ψ s

end Operators

/-- The **fiber count** `N_g = #{(x,y) ∈ 𝔽_p × 𝔽_p : g(x) = g(y)}` (manuscript
`prop:firstmoment`, eq. `eq:firstmoment`). It is a natural number; the statements below cast it
into `ℝ`. For a bijection `N_g = p`; for the squaring map on an odd prime field `N_g = 2p − 1`.
-/
def fiberCount [NeZero p] (g : ZMod p → ZMod p) : ℕ :=
  (Finset.univ.filter fun xy : ZMod p × ZMod p => g xy.1 = g xy.2).card

section FirstMoment

variable [Fact p.Prime]
variable (ψ : AddChar (ZMod p) ℂ) (hψ : ψ ≠ 1)

include hψ

/-- **Trace factorization** (manuscript `prop:firstmoment`, eq. `eq:tracefact`):

`Tr U_{f,τ} = φ_p(τ) · ∑_{x ∈ 𝔽_p} ψ(f(x))`.

The kick and the free step separate completely in the trace: the free propagator contributes
only through the single scalar `φ_p(τ)`, and the kick only through the complete character sum
of its phase function. The hypothesis `ψ ≠ 1` is needed and is not cosmetic — at the trivial
character the free propagator is not the one described here. Exact at every prime; no
asymptotics, and no claim about the individual eigenvalues of `U_{f,τ}`. -/
theorem trace_floquet (f : ZMod p → ZMod p) (s : ℝ) :
    (floquet ψ f s).trace = varphi ψ s * ∑ x : ZMod p, ψ (f x) := by
  sorry

/-- **The exact first moment, unnormalized** (manuscript `prop:firstmoment`, eq.
`eq:firstmoment`, before dividing by `#𝔽_p^× = p − 1`):

`∑_{γ ≠ 0} |Tr U_{γg,τ}|² = |φ_p(τ)|² · (p·N_g − p²)`.

The sum over the kick strength `γ` of the squared trace modulus depends on the kick function
`g` only through its fiber count `N_g`. This is an identity between real numbers at a fixed
prime — not a variance, not an expectation over any random ensemble, and not an asymptotic
statement. -/
theorem firstMoment (g : ZMod p → ZMod p) (s : ℝ) :
    ∑ γ ∈ Finset.univ.erase (0 : ZMod p), ‖(floquet ψ (fun x => γ * g x) s).trace‖ ^ 2
      = ‖varphi ψ s‖ ^ 2 * ((p : ℝ) * fiberCount g - (p : ℝ) ^ 2) := by
  sorry

/-- **The exact first moment, in the manuscript's normalized form** (manuscript
`prop:firstmoment`, eq. `eq:firstmoment`):

`𝔼_γ |Tr U_{γg,τ}|² = |φ_p(τ)|² · (p·N_g − p²)/(p − 1)`,

with `𝔼_γ` the uniform average over `γ ∈ 𝔽_p^×`, written here as `(p − 1)⁻¹ ∑_{γ ≠ 0}`. The
"expectation" is a finite uniform average over a deterministic index set; no probability space,
random matrix, or ensemble is involved. -/
theorem firstMoment_expectation (g : ZMod p → ZMod p) (s : ℝ) :
    (((p : ℝ) - 1)⁻¹ *
        ∑ γ ∈ Finset.univ.erase (0 : ZMod p), ‖(floquet ψ (fun x => γ * g x) s).trace‖ ^ 2)
      = ‖varphi ψ s‖ ^ 2 * (((p : ℝ) * fiberCount g - (p : ℝ) ^ 2) / ((p : ℝ) - 1)) := by
  sorry

/-- **Quadratic kick** (manuscript `prop:firstmoment`, "In particular `N_{x²} = 2p − 1`, so the
quadratic moment equals `p|φ_p(τ)|²`"):

`𝔼_γ |Tr U_{γx²,τ}|² = p · |φ_p(τ)|²`.

`p ≠ 2` is required: in characteristic two the squaring map is a bijection and the fiber count
is different. Exact at every odd prime. -/
theorem firstMoment_sq (hp2 : p ≠ 2) (s : ℝ) :
    (((p : ℝ) - 1)⁻¹ *
        ∑ γ ∈ Finset.univ.erase (0 : ZMod p),
          ‖(floquet ψ (fun x => γ * x ^ 2) s).trace‖ ^ 2)
      = (p : ℝ) * ‖varphi ψ s‖ ^ 2 := by
  sorry

/-- **Cubic kick at `p ≡ 1 (mod 3)`** (manuscript `prop:firstmoment`, "`N_{x³} = 3p − 2` for
`p ≡ 1 (mod 3)`, so the cubic moment equals `2p|φ_p(τ)|²`"):

`𝔼_γ |Tr U_{γx³,τ}|² = 2p · |φ_p(τ)|²`.

The residue condition is a genuine hypothesis, not a convenience: the companion theorem below
gives a different value in the other class. -/
theorem firstMoment_cube_one_mod_three (h3 : p % 3 = 1) (s : ℝ) :
    (((p : ℝ) - 1)⁻¹ *
        ∑ γ ∈ Finset.univ.erase (0 : ZMod p),
          ‖(floquet ψ (fun x => γ * x ^ 3) s).trace‖ ^ 2)
      = 2 * (p : ℝ) * ‖varphi ψ s‖ ^ 2 := by
  sorry

/-- **Cubic kick at `p ≡ 2 (mod 3)`** (manuscript `prop:firstmoment`, "for `p ≡ 2 (mod 3)` the
cube map is a bijection, the sum `∑_x ψ(γx³)` vanishes identically, and the moment is exactly
zero"):

`𝔼_γ |Tr U_{γx³,τ}|² = 0`.

Exactly zero, at every such prime and every `s` — not "zero to leading order" and not "zero on
average". Each individual trace `Tr U_{γx³,τ}` vanishes, because for `p ≡ 2 (mod 3)` cubing is
a bijection of `𝔽_p` and the complete character sum `∑_x ψ(γx³) = ∑_x ψ(γx)` is `0`. -/
theorem firstMoment_cube_two_mod_three (h3 : p % 3 = 2) (s : ℝ) :
    (((p : ℝ) - 1)⁻¹ *
        ∑ γ ∈ Finset.univ.erase (0 : ZMod p),
          ‖(floquet ψ (fun x => γ * x ^ 3) s).trace‖ ^ 2)
      = 0 := by
  sorry

end FirstMoment

section Reflection

variable [Fact p.Prime]

/-- **Monomial parity and the affine-reflection criterion** (manuscript `cor:monomial`):

over a prime field of odd characteristic, a monomial kick `γx^d` with `γ ≠ 0` admits an affine
reflection centre — a `β` with `γx^d = γ(β − x)^d` for **every** `x` — if and only if `d` is
even. The "only if" direction is the substance: for odd `d` the criterion fails at every `β`,
not merely at `β = 0`.

**Strengthening, stated plainly.** The manuscript carries the hypothesis `p > d`, used there to
identify a polynomial with the function it induces. It is dropped here: the statement holds for
**every** `d : ℕ`, including `d ≥ p`, where a polynomial and its induced function need no longer
agree. This is a strictly stronger statement than the manuscript's, in the direction of fewer
hypotheses, and the proof does not proceed by degree. The parity of `d` is the parity of the
natural number exponent (`Even d`), not of `d` modulo anything. -/
theorem monomial_reflection_iff' (hp2 : p ≠ 2) {d : ℕ} {γ : ZMod p} (hγ : γ ≠ 0) :
    (∃ β : ZMod p, ∀ x : ZMod p, γ * x ^ d = γ * (β - x) ^ d) ↔ Even d := by
  sorry

end Reflection

/-- **No antiunitary squares to `−I` in odd dimension** (manuscript `cor:nosymplectic`).

An antiunitary operator is written in the standard form `Θ = W ∘ C` with `C` entrywise complex
conjugation in the position basis, so that `Θ² = W · conj(W)`, where `conj(W)` is
`W.map (starRingEnd ℂ)`. The claim is that on a space of odd dimension no such square equals
`−I`.

**Strengthening, stated plainly.** The manuscript states this for a **unitary** `W`. Unitarity
is never used — the argument takes determinants, and `det W · conj(det W) = ‖det W‖² ≥ 0` while
`det(−I) = −1` in odd dimension — so it is proved here for an arbitrary complex matrix over an
arbitrary odd-cardinality index type. This is strictly stronger than the manuscript's statement.

**What this does not say.** It is a statement about matrices, not about the kicked Kloosterman
map or any ensemble: applied to `ℓ²(𝔽_p)`, which has odd dimension `p`, it excludes one
algebraic possibility. It asserts nothing about which symmetry class, if any, is realized, and
it makes no random-matrix claim. -/
theorem no_antiunitary_sq_neg_one {n : Type*} [Fintype n] [DecidableEq n]
    (hodd : Odd (Fintype.card n)) (W : Matrix n n ℂ) :
    W * W.map (starRingEnd ℂ) ≠ -1 := by
  sorry

end KickedKloosterman

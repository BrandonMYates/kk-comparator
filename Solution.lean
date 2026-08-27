/-
Copyright (c) 2026 Brandon Yates. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import KKLab

/-!
# Solution

The proof development lives in the `KKLab` library, pinned by commit in `lakefile.toml`. This
file restates the Challenge's seven definitions and eight theorems verbatim and discharges each
theorem by direct application of the corresponding library theorem.

The seven `example`s below are the bridge: each Challenge definition is *definitionally* equal
to its `KKLab` counterpart, checked by `rfl` at the level of the fully applied constant
(`@`-form, so the implicit `{p : ℕ}` and the `[NeZero p]` instance are compared too). No
translation step is involved anywhere.
-/

namespace KickedKloosterman

open Finset Matrix

variable {p : ℕ}

section Operators

variable [NeZero p]

noncomputable def phaseMat (ψ : AddChar (ZMod p) ℂ) (f : ZMod p → ZMod p) :
    Matrix (ZMod p) (ZMod p) ℂ :=
  Matrix.diagonal fun x => ψ (f x)

noncomputable def kloostermanSum (ψ : AddChar (ZMod p) ℂ) (a : ZMod p) : ℂ :=
  ∑ x ∈ Finset.univ.erase (0 : ZMod p), ψ (a * x + x⁻¹)

noncomputable def kloostermanMatrix (ψ : AddChar (ZMod p) ℂ) : Matrix (ZMod p) (ZMod p) ℂ :=
  Matrix.circulant fun d => if d = 0 then 0 else ψ (d⁻¹)

noncomputable def freeProp (ψ : AddChar (ZMod p) ℂ) (s : ℝ) : Matrix (ZMod p) (ZMod p) ℂ :=
  NormedSpace.exp ((-(s : ℂ) * Complex.I) • kloostermanMatrix ψ)

noncomputable def varphi (ψ : AddChar (ZMod p) ℂ) (s : ℝ) : ℂ :=
  (p : ℂ)⁻¹ * ∑ a : ZMod p, Complex.exp (-(s : ℂ) * Complex.I * kloostermanSum ψ a)

noncomputable def floquet (ψ : AddChar (ZMod p) ℂ) (f : ZMod p → ZMod p) (s : ℝ) :
    Matrix (ZMod p) (ZMod p) ℂ :=
  phaseMat ψ f * freeProp ψ s

end Operators

def fiberCount [NeZero p] (g : ZMod p → ZMod p) : ℕ :=
  (Finset.univ.filter fun xy : ZMod p × ZMod p => g xy.1 = g xy.2).card

/-! ### Definitional bridges -/

example : @phaseMat = @KKLab.phaseMat := rfl
example : @kloostermanSum = @KKLab.kloostermanSum := rfl
example : @kloostermanMatrix = @KKLab.kloostermanMatrix := rfl
example : @freeProp = @KKLab.freeProp := rfl
example : @varphi = @KKLab.varphi := rfl
example : @floquet = @KKLab.floquet := rfl
example : @fiberCount = @KKLab.fiberCount := rfl

section FirstMoment

variable [Fact p.Prime]
variable (ψ : AddChar (ZMod p) ℂ) (hψ : ψ ≠ 1)

include hψ

theorem trace_floquet (f : ZMod p → ZMod p) (s : ℝ) :
    (floquet ψ f s).trace = varphi ψ s * ∑ x : ZMod p, ψ (f x) :=
  KKLab.trace_floquet ψ hψ f s

theorem firstMoment (g : ZMod p → ZMod p) (s : ℝ) :
    ∑ γ ∈ Finset.univ.erase (0 : ZMod p), ‖(floquet ψ (fun x => γ * g x) s).trace‖ ^ 2
      = ‖varphi ψ s‖ ^ 2 * ((p : ℝ) * fiberCount g - (p : ℝ) ^ 2) :=
  KKLab.firstMoment ψ hψ g s

theorem firstMoment_expectation (g : ZMod p → ZMod p) (s : ℝ) :
    (((p : ℝ) - 1)⁻¹ *
        ∑ γ ∈ Finset.univ.erase (0 : ZMod p), ‖(floquet ψ (fun x => γ * g x) s).trace‖ ^ 2)
      = ‖varphi ψ s‖ ^ 2 * (((p : ℝ) * fiberCount g - (p : ℝ) ^ 2) / ((p : ℝ) - 1)) :=
  KKLab.firstMoment_expectation ψ hψ g s

theorem firstMoment_sq (hp2 : p ≠ 2) (s : ℝ) :
    (((p : ℝ) - 1)⁻¹ *
        ∑ γ ∈ Finset.univ.erase (0 : ZMod p),
          ‖(floquet ψ (fun x => γ * x ^ 2) s).trace‖ ^ 2)
      = (p : ℝ) * ‖varphi ψ s‖ ^ 2 :=
  KKLab.firstMoment_sq ψ hψ hp2 s

theorem firstMoment_cube_one_mod_three (h3 : p % 3 = 1) (s : ℝ) :
    (((p : ℝ) - 1)⁻¹ *
        ∑ γ ∈ Finset.univ.erase (0 : ZMod p),
          ‖(floquet ψ (fun x => γ * x ^ 3) s).trace‖ ^ 2)
      = 2 * (p : ℝ) * ‖varphi ψ s‖ ^ 2 :=
  KKLab.firstMoment_cube_one_mod_three ψ hψ h3 s

theorem firstMoment_cube_two_mod_three (h3 : p % 3 = 2) (s : ℝ) :
    (((p : ℝ) - 1)⁻¹ *
        ∑ γ ∈ Finset.univ.erase (0 : ZMod p),
          ‖(floquet ψ (fun x => γ * x ^ 3) s).trace‖ ^ 2)
      = 0 :=
  KKLab.firstMoment_cube_two_mod_three ψ hψ h3 s

end FirstMoment

section Reflection

variable [Fact p.Prime]

theorem monomial_reflection_iff' (hp2 : p ≠ 2) {d : ℕ} {γ : ZMod p} (hγ : γ ≠ 0) :
    (∃ β : ZMod p, ∀ x : ZMod p, γ * x ^ d = γ * (β - x) ^ d) ↔ Even d :=
  KKLab.monomial_reflection_iff' hp2 hγ

end Reflection

theorem no_antiunitary_sq_neg_one {n : Type*} [Fintype n] [DecidableEq n]
    (hodd : Odd (Fintype.card n)) (W : Matrix n n ℂ) :
    W * W.map (starRingEnd ℂ) ≠ -1 :=
  KKLab.no_antiunitary_sq_neg_one hodd W

end KickedKloosterman

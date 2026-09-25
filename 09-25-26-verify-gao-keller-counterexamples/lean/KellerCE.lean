/-!
# Two Keller maps of ℚ³ that are not injective, checked in Lean 4 core

The Jacobian conjecture says that a polynomial map `ℂⁿ → ℂⁿ` whose Jacobian determinant is a nonzero constant (a Keller map) is injective. This file checks two counterexamples in dimension three from Shuhong Gao, "Counterexamples to the Jacobian conjecture in dimensions greater than two", arXiv:2608.00222v1 (July 31, 2026), https://arxiv.org/abs/2608.00222:

* `F`, Alpöge's map (Section 3.4 of the paper), with `det J(F) = -2` and the paper's collision `F(0, 0, -1/4) = F(1, -3/2, 13/2) = F(-1, 3/2, 13/2) = (-1/4, 0, 0)`;
* `G`, the paper's degree-four map (Section 3.5), with `det J(G) = 2`. The paper's Theorem A.1 describes the fibers of `G` over `v₁ = 0`, but the paper prints no explicit collision. The one used here, `G(0, 1/2, -9/4) = G(2, -1/2, 3/2) = G(-2, 5/6, 13/6) = (0, 1, 0)`, is the target `v = (0, 1, 0)` of that theorem, worked out for this repository.

Only Lean core is used: no Mathlib, no `native_decide`, no axioms beyond `propext`, `Classical.choice` and `Quot.sound`. The `#print axioms` lines at the end show this in an editor. `check_lean.py` does not rely on them, because code in a file can fake its own output: it reads the axioms from the compiled module in a separate process.

## What has to be trusted

Everything below is proved except the definitions, which a reader has to check against the mathematics:

* `Dual`: the dual numbers `a + b ε` with `ε² = 0`. The ε-part of `f(x + ε, y, z)` is `∂f/∂x (x, y, z)`. This is the product rule, built into `Dual.mul`, so no derivative is written by hand.
* `deriv`, `det3` and `jacDet`: the columns of the Jacobian matrix are the derivatives along the three coordinate axes, and `det3` is the cofactor expansion along the first row.
* `F` and `G`: the components as printed in the paper. `check_lean.py` in the parent folder compares them, as polynomials, with the paper's LaTeX source.

A polynomial is written once, for any carrier with `+ - * / ^` and numerals. It is then run on dual numbers to get its derivatives, and on `α` itself to get its values. So `jacDet F` is the Jacobian determinant of the same `F` that `F_not_injective` evaluates.

`F_keller` holds over every commutative ring, in the sense of Lean core's `Lean.Grind.CommRing`. `G` has coefficients such as `3/8`, so `G_keller` is stated over every field of characteristic zero (`Lean.Grind.Field` with `Lean.Grind.IsCharP α 0`). Both are proved by `grind`'s commutative-ring normalizer. The corollaries over `ℚ` also cover `ℂ`: an identity between polynomials with rational coefficients that holds at every rational point holds as a polynomial identity, and so over every field of characteristic zero. Two distinct rational points with one image are also two distinct complex points with one image.
-/

namespace KellerCE

/-- Dual numbers `re + eps ε` with `ε² = 0`. -/
structure Dual (α : Type) where
  re : α
  eps : α

section Dual
variable {α : Type}

instance [Add α] : Add (Dual α) := ⟨fun a b => ⟨a.re + b.re, a.eps + b.eps⟩⟩
instance [Sub α] : Sub (Dual α) := ⟨fun a b => ⟨a.re - b.re, a.eps - b.eps⟩⟩
instance [Neg α] : Neg (Dual α) := ⟨fun a => ⟨-a.re, -a.eps⟩⟩
/-- `(a + a' ε)(b + b' ε) = ab + (ab' + a'b) ε`, because `ε² = 0`. -/
instance [Add α] [Mul α] : Mul (Dual α) := ⟨fun a b => ⟨a.re * b.re, a.re * b.eps + a.eps * b.re⟩⟩
/-- The quotient rule. `G` divides only numerals by numerals, where this is `⟨p / q, 0⟩`. -/
instance [Sub α] [Mul α] [Div α] : Div (Dual α) :=
  ⟨fun a b => ⟨a.re / b.re, (a.eps * b.re - a.re * b.eps) / (b.re * b.re)⟩⟩
/-- Numerals are constants: their ε-part is `0`. -/
instance {n : Nat} [∀ k, OfNat α k] : OfNat (Dual α) n := ⟨⟨OfNat.ofNat n, 0⟩⟩
/-- `a ^ n` is `n`-fold multiplication, so powers need no derivative rule of their own. -/
def Dual.pow [Add α] [Mul α] [∀ k, OfNat α k] (a : Dual α) : Nat → Dual α
  | 0 => 1
  | n + 1 => Dual.pow a n * a
instance [Add α] [Mul α] [∀ k, OfNat α k] : HPow (Dual α) Nat (Dual α) := ⟨Dual.pow⟩

/-- The arithmetic of `Dual`, one rewrite rule per operation, all true by definition. -/
@[simp] theorem add_re [Add α] (a b : Dual α) : (a + b).re = a.re + b.re := rfl
@[simp] theorem add_eps [Add α] (a b : Dual α) : (a + b).eps = a.eps + b.eps := rfl
@[simp] theorem sub_re [Sub α] (a b : Dual α) : (a - b).re = a.re - b.re := rfl
@[simp] theorem sub_eps [Sub α] (a b : Dual α) : (a - b).eps = a.eps - b.eps := rfl
@[simp] theorem neg_re [Neg α] (a : Dual α) : (-a).re = -a.re := rfl
@[simp] theorem neg_eps [Neg α] (a : Dual α) : (-a).eps = -a.eps := rfl
@[simp] theorem mul_re [Add α] [Mul α] (a b : Dual α) : (a * b).re = a.re * b.re := rfl
@[simp] theorem mul_eps [Add α] [Mul α] (a b : Dual α) : (a * b).eps = a.re * b.eps + a.eps * b.re := rfl
@[simp] theorem div_re [Sub α] [Mul α] [Div α] (a b : Dual α) : (a / b).re = a.re / b.re := rfl
@[simp] theorem div_eps [Sub α] [Mul α] [Div α] (a b : Dual α) :
    (a / b).eps = (a.eps * b.re - a.re * b.eps) / (b.re * b.re) := rfl
@[simp] theorem ofNat_re {n : Nat} [∀ k, OfNat α k] : (no_index (OfNat.ofNat n : Dual α)).re = OfNat.ofNat n := rfl
@[simp] theorem ofNat_eps {n : Nat} [∀ k, OfNat α k] : (no_index (OfNat.ofNat n : Dual α)).eps = 0 := rfl
@[simp] theorem pow_zero' [Add α] [Mul α] [∀ k, OfNat α k] (a : Dual α) : a ^ 0 = 1 := rfl
@[simp] theorem pow_succ' [Add α] [Mul α] [∀ k, OfNat α k] (a : Dual α) (n : Nat) : a ^ (n + 1) = a ^ n * a := rfl

end Dual

section Jacobian
variable {α : Type} [Add α] [Sub α] [Mul α]

/-- The derivative of `f` at `(x, y, z)` in the direction `(dx, dy, dz)`: the ε-part of `f(x + dx ε, y + dy ε, z + dz ε)`. -/
def deriv (f : Dual α → Dual α → Dual α → Dual α × Dual α × Dual α) (x y z dx dy dz : α) : α × α × α :=
  let r := f ⟨x, dx⟩ ⟨y, dy⟩ ⟨z, dz⟩
  (r.1.eps, r.2.1.eps, r.2.2.eps)

/-- The determinant of the 3 × 3 matrix with columns `u`, `v`, `w`, by cofactor expansion along the first row. -/
def det3 (u v w : α × α × α) : α :=
  u.1 * (v.2.1 * w.2.2 - w.2.1 * v.2.2) - v.1 * (u.2.1 * w.2.2 - w.2.1 * u.2.2) + w.1 * (u.2.1 * v.2.2 - v.2.1 * u.2.2)

/-- The Jacobian determinant of `f` at `(x, y, z)`. Column `j` of the Jacobian matrix is `∂f/∂x_j`. -/
def jacDet [∀ k, OfNat α k] (f : Dual α → Dual α → Dual α → Dual α × Dual α × Dual α) (x y z : α) : α :=
  det3 (deriv f x y z 1 0 0) (deriv f x y z 0 1 0) (deriv f x y z 0 0 1)

end Jacobian

/-- Alpöge's map, as printed in Section 3.4 of the paper. -/
def F {α : Type} [Add α] [Sub α] [Mul α] [HPow α Nat α] [∀ k, OfNat α k] (x y z : α) : α × α × α :=
  ((1 + x*y)^3 * z + y^2 * (1 + x*y) * (4 + 3*x*y),
   y + 3*x*(1 + x*y)^2 * z + 3*x*y^2 * (4 + 3*x*y),
   2*x - 3*x^2*y - x^3*z)

/-- Gao's degree-four map, as printed in Section 3.5 of the paper. -/
def G {α : Type} [Add α] [Sub α] [Neg α] [Mul α] [Div α] [HPow α Nat α] [∀ k, OfNat α k] (x y z : α) : α × α × α :=
  (-x^3*z - 4*x^2*y + 2*x,
   x^6*y^3*z^2 + 8*x^5*y^4*z + 3*x^5*y^2*z^2 + 16*x^4*y^5 + 20*x^4*y^3*z + 3*x^4*y*z^2 + 32*x^3*y^4 + 18*x^3*y^2*z + x^3*z^2 + 28*x^2*y^3 + 8*x^2*y*z + 16*x*y^2 + 2*x*z + 2*y,
   3/8*x^6*y^4*z^2 + 3*x^5*y^5*z + 3/2*x^5*y^3*z^2 + 6*x^4*y^6 + 21/2*x^4*y^4*z + 9/4*x^4*y^2*z^2 + 18*x^3*y^5 + 14*x^3*y^3*z + 3/2*x^3*y*z^2 + 43/2*x^2*y^4 + 9*x^2*y^2*z + 3/8*x^2*z^2 + 14*x*y^3 + 3*x*y*z + 9/2*y^2 + 1/2*z)

set_option linter.unusedSimpArgs false in
/-- `F` is a Keller map over every commutative ring. -/
theorem F_keller {α : Type} [Lean.Grind.CommRing α] (x y z : α) : jacDet F x y z = -2 := by
  simp only [jacDet, det3, deriv, F, add_re, add_eps, sub_re, sub_eps, neg_re, neg_eps, mul_re, mul_eps, div_re, div_eps, ofNat_re, ofNat_eps, pow_zero', pow_succ']
  grind

set_option linter.unusedSimpArgs false in
/-- `G` is a Keller map over every field of characteristic zero. -/
theorem G_keller {α : Type} [Lean.Grind.Field α] [Lean.Grind.IsCharP α 0] (x y z : α) : jacDet G x y z = 2 := by
  simp only [jacDet, det3, deriv, G, add_re, add_eps, sub_re, sub_eps, neg_re, neg_eps, mul_re, mul_eps, div_re, div_eps, ofNat_re, ofNat_eps, pow_zero', pow_succ']
  grind

theorem F_collision :
    F (0 : Rat) 0 (-1/4) = (-1/4, 0, 0) ∧ F (1 : Rat) (-3/2) (13/2) = (-1/4, 0, 0) ∧
      F (-1 : Rat) (3/2) (13/2) = (-1/4, 0, 0) := by
  decide +kernel

theorem G_collision :
    G (0 : Rat) (1/2) (-9/4) = (0, 1, 0) ∧ G (2 : Rat) (-1/2) (3/2) = (0, 1, 0) ∧
      G (-2 : Rat) (5/6) (13/6) = (0, 1, 0) := by
  decide +kernel

theorem F_not_injective : ¬ Function.Injective (fun p : Rat × Rat × Rat => F p.1 p.2.1 p.2.2) := by
  intro h
  have := @h (0, 0, -1/4) (1, -3/2, 13/2) (by decide +kernel)
  exact absurd this (by decide +kernel)

theorem G_not_injective : ¬ Function.Injective (fun p : Rat × Rat × Rat => G p.1 p.2.1 p.2.2) := by
  intro h
  have := @h (0, 1/2, -9/4) (2, -1/2, 3/2) (by decide +kernel)
  exact absurd this (by decide +kernel)

/-- Alpöge's `F` is a counterexample to the Jacobian conjecture in dimension three. -/
theorem F_counterexample :
    (∀ x y z : Rat, jacDet F x y z = -2) ∧ ¬ Function.Injective (fun p : Rat × Rat × Rat => F p.1 p.2.1 p.2.2) :=
  ⟨fun x y z => F_keller x y z, F_not_injective⟩

/-- Gao's `G` is a counterexample to the Jacobian conjecture in dimension three. -/
theorem G_counterexample :
    (∀ x y z : Rat, jacDet G x y z = 2) ∧ ¬ Function.Injective (fun p : Rat × Rat × Rat => G p.1 p.2.1 p.2.2) :=
  ⟨fun x y z => G_keller x y z, G_not_injective⟩

end KellerCE

#print axioms KellerCE.F_keller
#print axioms KellerCE.G_keller
#print axioms KellerCE.F_collision
#print axioms KellerCE.G_collision
#print axioms KellerCE.F_counterexample
#print axioms KellerCE.G_counterexample

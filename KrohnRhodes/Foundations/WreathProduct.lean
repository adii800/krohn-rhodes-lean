/-
Copyright (c) 2026 Aditya Rao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aditya Rao
-/
module

public import KrohnRhodes.Defs
public import Mathlib

/-!
# The monoid structure of the wreath product

`SgDiv` and `WreathProduct` with its multiplication are defined in `KrohnRhodes.Defs`. This
file adds the identity, the lemmas `WreathProduct.mul_func` / `mul_base` / `one_func` /
`one_base`, and the `Monoid` and `Finite` instances: the monoid of the transformation wreath
product `(A, A) ≀ (X, B)`.

## References

* [Krohn, Rhodes, *Algebraic Theory of Machines. I.*, Trans. AMS 1965]
* [Eilenberg, *Automata, Languages, and Machines, Vol. B*, 1976]
-/

@[expose] public section

universe u v w



namespace WreathProduct

variable {A : Type u} {B : Type v} {X : Type w}
variable [Monoid A] [Monoid B] [MulAction B X]


/-- The identity element of the wreath product. -/
instance : One (WreathProduct A B X) where
  one := ⟨fun _ => 1, 1⟩

@[simp]
theorem mul_func (p q : WreathProduct A B X) (x : X) :
    (p * q).func x = p.func (q.base • x) * q.func x := rfl

@[simp]
theorem mul_base (p q : WreathProduct A B X) :
    (p * q).base = p.base * q.base := rfl

@[simp]
theorem one_func (x : X) : (1 : WreathProduct A B X).func x = 1 := rfl

@[simp]
theorem one_base : (1 : WreathProduct A B X).base = (1 : B) := rfl

/-- The wreath product of monoids is a monoid. -/
instance instMonoid : Monoid (WreathProduct A B X) where
  mul_assoc p q r := by
    ext x
    · -- LHS: ((p*q)*r).func x = (p*q).func (r.base • x) * r.func x
      --     = p.func (q.base • (r.base • x)) * q.func (r.base • x) * r.func x
      -- RHS: (p*(q*r)).func x = p.func ((q*r).base • x) * (q*r).func x
      --     = p.func ((q.base * r.base) • x) * (q.func (r.base • x) * r.func x)
      -- These are equal by mul_smul and mul_assoc
      simp only [mul_func, mul_base, mul_smul, mul_assoc]
    · simp [mul_assoc]
  one_mul p := by
    ext x
    · simp only [mul_func, one_func, one_mul]
    · simp
  mul_one p := by
    ext x
    · simp only [mul_func, one_func, one_base, one_smul, mul_one]
    · simp

/-- The wreath product of finite types is finite. -/
instance instFinite [Finite X] [Finite A] [Finite B] : Finite (WreathProduct A B X) := by
  have : Finite ((X → A) × B) := inferInstance
  exact Finite.of_injective (fun w => (w.func, w.base))
    (fun a b h => by
      have h1 : a.func = b.func := (Prod.mk.inj h).1
      have h2 : a.base = b.base := (Prod.mk.inj h).2
      exact WreathProduct.ext h1 h2)

end WreathProduct


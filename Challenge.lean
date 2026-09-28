/-
Copyright (c) 2026 Aditya Rao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aditya Rao
-/
module

public import Mathlib

/-!
# The Krohn–Rhodes prime decomposition theorem

For a finite monoid `M` (in `Type`), `krohn_rhodes_prime_decomposition` asserts that there is
a `KRFactorTowerGrp M`: a list `[F₁, …, Fₖ]` of finite monoids, each either aperiodic (every
`H`-class is trivial) or a simple group, such that `M` divides the right-iterated wreath product
`F₁ ≀ (F₂ ≀ (⋯ ≀ (Fₖ ≀ 1)))`, and every simple-group factor divides `M`. The division is stated
one level at a time (`DivTowerWreath`, each level acting on a finite set); the docstring of
`DivTowerWreath` explains why this is equivalent to a single division, an equivalence that is
not formalized.

Division is semigroup division (`SgDiv`, a homomorphic image of a subsemigroup) for the tower,
and monoid division (`KrohnRhodes.MonoidDivides`, a quotient of a submonoid) for the group
factors.

The aperiodic factors are only required to be aperiodic; the classical statement takes each of
them to be the flip-flop monoid (`U₂` in the notation of Diekert, Kufleitner and Steinberg). For
an aperiodic `M` the statement therefore holds with `M` as its only factor; in general it
separates the group structure of `M`, as simple groups dividing `M`, from aperiodic factors.

The definitions below are the library's `KrohnRhodes.Defs`, repeated verbatim.
-/

@[expose] public section

universe u v w

/-! ## Green's relations -/

namespace Green

variable {M : Type*} [Monoid M]

/-! ### Green's L-relation -/

/-- Green's L-relation: `a` and `b` generate the same principal left ideal.
    In a monoid, `a L b` iff there exist `s, t` with `s * a = b` and `t * b = a`. -/
def L (a b : M) : Prop :=
  ∃ s t : M, s * a = b ∧ t * b = a

/-! ### Green's R-relation -/

/-- Green's R-relation: `a` and `b` generate the same principal right ideal.
    In a monoid, `a R b` iff there exist `s, t` with `a * s = b` and `b * t = a`. -/
def R (a b : M) : Prop :=
  ∃ s t : M, a * s = b ∧ b * t = a

/-! ### Green's H-relation -/

/-- Green's H-relation: intersection of L and R.
    `a H b` iff `a L b` and `a R b`. -/
def H (a b : M) : Prop :=
  L a b ∧ R a b

/-! ### Aperiodic elements and monoids -/

/-- `IsAperiodicElem a` says that the `H`-class of `a` is trivial: `a H b → a = b` for every
    `b`. A finite monoid all of whose elements satisfy this is aperiodic (all of its subgroups are
    trivial). For a single element this is not the usual notion of an aperiodic element
    (`a ^ n = a ^ (n + 1)` for some `n`): in the monoid `{1, a, a², a³}` with `a⁴ = a²`, the
    `H`-class of `a` is `{a}`, but `a ^ n ≠ a ^ (n + 1)` for every `n`. -/
def IsAperiodicElem (a : M) : Prop :=
  ∀ b : M, H a b → a = b

end Green

/-! ### Semigroup division -/

/-- Semigroup `S` divides `T` if `S` is a homomorphic image of a subsemigroup of `T`. -/
def SgDiv (S T : Type*) [Mul S] [Mul T] : Prop :=
  ∃ (U : Subsemigroup T) (φ : U →ₙ* S), Function.Surjective φ

/-! ### Wreath product construction -/

/-- The wreath product of monoids `A` and `B` relative to an action of `B` on a type `X`.
    Elements are pairs `(f, b)` where `f : X → A` and `b : B`.

    Multiplication: `(f₁, b₁) * (f₂, b₂) = (fun x => f₁ (b₂ • x) * f₂ x, b₁ * b₂)` -/
@[ext]
structure WreathProduct (A : Type u) (B : Type v) (X : Type w)
    [Monoid A] [Monoid B] [MulAction B X] where
  /-- The decoration function mapping each point of `X` to an element of `A`. -/
  func : X → A
  /-- The component in `B`, which acts on `X`. -/
  base : B

namespace WreathProduct

variable {A : Type u} {B : Type v} {X : Type w}
variable [Monoid A] [Monoid B] [MulAction B X]

/-- Multiplication in the wreath product:
    `(f₁, b₁) * (f₂, b₂) = (x ↦ f₁ (b₂ • x) * f₂ x, b₁ * b₂)`.

    This is the convention for a left action of `B` on `X`: the base component of the **right**
    factor acts on the argument of the **left** factor's decoration. Letting `(f, b)` act on
    `A × X` by `(a, x) ↦ (f x * a, b • x)`, the product `p * q` acts as `p` after `q`. The
    right-action convention `(f₁, b₁) * (f₂, b₂) = (x ↦ f₁ x * f₂ (x · b₁), b₁ * b₂)`, used for
    example by Diekert, Kufleitner and Steinberg, is its left-right mirror image. -/
instance : Mul (WreathProduct A B X) where
  mul p q := ⟨fun x => p.func (q.base • x) * q.func x, p.base * q.base⟩

end WreathProduct

namespace KrohnRhodes

/-! ## Monoid division -/

/-- A monoid `M` divides a monoid `N` if `M` is a quotient of a submonoid of `N`.
Equivalently, there exists a surjective monoid homomorphism from a submonoid of `N` onto `M`. -/
def MonoidDivides (M : Type*) (N : Type*) [Monoid M] [Monoid N] : Prop :=
  ∃ (S : Submonoid N) (φ : S →* M), Function.Surjective φ

end KrohnRhodes

/-! ## Krohn–Rhodes factors and factor towers -/

open Green

/-- The two kinds of Krohn-Rhodes factor: a factor is either an **aperiodic** monoid or a
    **simple group**. -/
inductive KRFactorKind where
  /-- The factor is a finite aperiodic monoid. -/
  | aperiodic : KRFactorKind
  /-- The factor is a finite simple group. -/
  | simpleGroup : KRFactorKind
  deriving DecidableEq, Repr

/-- A single **Krohn-Rhodes factor**: a finite monoid `carrier` together with a
    flag `kind` and a *proof* that `carrier` really satisfies its flag.  The
    proof field is what makes the decomposition genuinely informative (not a
    vacuous existential): an `aperiodic` factor must actually be aperiodic
    (every element has a trivial `H`-class), and a `simpleGroup` factor must
    actually carry a `Group` instance that is `IsSimpleGroup`. -/
structure KRFactor where
  /-- The carrier monoid of the factor. -/
  carrier : Type u
  /-- The factor's monoid structure. -/
  [mon : Monoid carrier]
  /-- The factor is finite. -/
  [fin : Finite carrier]
  /-- Whether the factor is an aperiodic atom or a simple-group atom. -/
  kind : KRFactorKind
  /-- The flag is *witnessed*: an `aperiodic`-flagged factor is genuinely
      aperiodic; a `simpleGroup`-flagged factor genuinely carries a finite
      simple-group structure on `carrier` **whose underlying monoid is the
      factor's own monoid field** (`g.toMonoid = mon`).  Recording the
      `g.toMonoid = mon` compatibility lets one transport monoid-indexed data
      between `F.mon` and the witnessed group instance `g`. -/
  isKind :
    (kind = KRFactorKind.aperiodic ∧ (∀ a : carrier, IsAperiodicElem a)) ∨
    (kind = KRFactorKind.simpleGroup ∧
      ∃ (g : Group carrier), g.toMonoid = mon ∧ @IsSimpleGroup carrier g)

attribute [instance] KRFactor.mon KRFactor.fin

/-- **The recursive division predicate of a factor tower.**

    `DivTowerWreath M factors` says that `M` divides the **right-iterated
    wreath product** of the factor list `factors`:

    * `[]`           — `M` divides the trivial monoid `PUnit` (the empty product),
                       so `M` has exactly one element.
    * `F :: rest`    — there is a finite base monoid `B` that itself decomposes
                       via the *tail* `rest` (`DivTowerWreath B rest`), and `M`
                       divides `WreathProduct F.carrier B Y` for some finite type
                       `Y` on which `B` acts: the head atom `F.carrier` sits in
                       the decoration slot over the base `B`.

    Unfolding the recursion, `DivTowerWreath M [F₁, …, Fₖ]` gives finite monoids `B₁, …, Bₖ`
    acting on finite types `Y₁, …, Yₖ` with `M ≼ F₁ ≀_{Y₁} B₁`, `Bᵢ ≼ Fᵢ₊₁ ≀_{Yᵢ₊₁} Bᵢ₊₁` for
    `1 ≤ i < k`, and `Bₖ` trivial, where `A ≀_Y B` is `WreathProduct A B Y`. Since
    `A ≀_Y B ≼ A ≀_{W × Y} W` whenever `B ≼ W` (with `W` acting on `W × Y` by left multiplication
    on the first coordinate), this is equivalent to `M ≼ F₁ ≀ (F₂ ≀ (⋯ ≀ (Fₖ ≀ 1)))` for suitable
    finite actions at each level; this equivalence is not formalized. -/
def DivTowerWreath : (M : Type u) → [Monoid M] → [Finite M] → List KRFactor.{u} → Prop
  | M, _, _, [] => SgDiv M PUnit.{u + 1}
  | M, _, _, (F :: rest) =>
      ∃ (B : Type u) (_ : Monoid B) (_ : Finite B)
        (Y : Type u) (_ : Fintype Y) (_ : MulAction B Y),
        DivTowerWreath B rest ∧
        SgDiv M (WreathProduct F.carrier B Y)

namespace KrohnRhodes

/-- **The Krohn-Rhodes factor tower with the prime-divisor guarantee.** For a finite monoid `M`:
a list of `KRFactor` atoms (each a finite monoid flagged and witnessed as aperiodic or as a simple
group), together with (i) a proof `DivTowerWreath M factors` that `M` divides the right-iterated
wreath product of the list, and (ii) the guarantee that every simple-group factor divides `M` as
a monoid (`MonoidDivides`). Aperiodic factors are only required to be aperiodic; the classical
statement (Krohn-Rhodes 1965; Theorem 4.1 of Diekert-Kufleitner-Steinberg, arXiv:1111.1585v1)
takes each of them to be the flip-flop monoid (`U₂` in the notation of Diekert, Kufleitner and
Steinberg). Stated for `M : Type`, with factors in `KRFactor.{0}`. -/
structure KRFactorTowerGrp (M : Type) [Monoid M] [Finite M] where
  /-- The explicit list of factors, each flagged and witnessed as aperiodic or as a simple
      group. -/
  factors : List KRFactor.{0}
  /-- `M` divides the right-iterated wreath product of `factors`. -/
  divides : DivTowerWreath M factors
  /-- Every SIMPLE-GROUP factor divides `M` (the Krohn-Rhodes prime-divisor guarantee;
      aperiodic factors are only required to be aperiodic). -/
  groupFactorsDivide : ∀ F ∈ factors, F.kind = KRFactorKind.simpleGroup →
    KrohnRhodes.MonoidDivides F.carrier M

end KrohnRhodes

namespace KrohnRhodes

/-- **The Krohn-Rhodes prime decomposition theorem, with aperiodic factors.** Every finite
monoid `M` in `Type` has a factor tower `KRFactorTowerGrp M`: a list of finite monoids, each
aperiodic or a simple group, such that `M` divides their right-iterated wreath product, level by
level (`DivTowerWreath`), and every simple-group factor divides `M`.

The classical theorem (Krohn-Rhodes 1965; Theorem 4.1 of Diekert-Kufleitner-Steinberg,
arXiv:1111.1585v1) moreover takes every aperiodic factor to be the flip-flop monoid (`U₂` in
their notation); here the aperiodic factors are arbitrary finite aperiodic monoids. The proof
follows the local-divisor proof of Diekert, Kufleitner and Steinberg (their Theorem 3.1 and
Corollary 3.2). No `DecidableEq M` hypothesis is needed; decidability is obtained classically
inside the proof. -/
theorem krohn_rhodes_prime_decomposition (M : Type) [Monoid M] [Finite M] :
    Nonempty (KRFactorTowerGrp M) := by
  sorry

end KrohnRhodes

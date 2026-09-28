/-
Copyright (c) 2026 Aditya Rao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aditya Rao
-/
module

public import KrohnRhodes

/-!
# The Krohn–Rhodes prime decomposition theorem: proof

This module restates `KrohnRhodes.krohn_rhodes_prime_decomposition` from `Challenge.lean` and
proves it from the library (`KrohnRhodes.dks_aux` and Cayley's theorem). Comparator checks that
the statement is identical to the Challenge's and that the proof uses only `propext`,
`Classical.choice` and `Quot.sound`.
-/

@[expose] public section

namespace KrohnRhodes

open Green

/-- **The Krohn-Rhodes prime decomposition theorem, with aperiodic factors.** Every finite
monoid `M` in `Type` has a factor tower `KRFactorTowerGrp M`: a list of finite monoids, each
aperiodic or a simple group, such that `M` divides their right-iterated wreath product, level by
level (`DivTowerWreath`), and every simple-group factor divides `M`.

The classical theorem (Krohn-Rhodes 1965; Theorem 4.1 of Diekert-Kufleitner-Steinberg,
arXiv:1111.1585v1) moreover takes every aperiodic factor to be the flip-flop monoid (`U₂` in
their notation); here the aperiodic factors are arbitrary finite aperiodic monoids. The proof
follows the local-divisor proof of Diekert, Kufleitner and Steinberg (their Theorem 3.1 and
Corollary 3.2). No `DecidableEq M` hypothesis is needed; decidability is obtained classically
inside the proof.

*Proof sketch.* Cayley + the closure induction (DKS Theorem 3.1 and Corollary 3.2; the group
leaves are decomposed as in the proof of DKS Theorem 4.1, by Lemma 2.9 and Corollary 2.8,
without its reduction to `U₂`). Set $Q := M$
(`Fintype.ofFinite`) with the left regular representation
$\mathrm{act} := \texttt{MulAction.toEndHom}$, injective by
`monoid_faithful_self`. `dks_aux` at $n := \mathrm{Nat.card}\,M$
yields a factor list, a tower for the constants closure $\overline{(M,M)}$, and the simple-group
divisibility into $M$. `sgdiv_closure_monoid` gives $M \preceq \overline{(M,M)}$, and
`divTowerWreath_of_sgDiv` transfers the tower from the closure to $M$; the `groupFactorsDivide`
field carries over unchanged. Package as `KRFactorTowerGrp`. -/
theorem krohn_rhodes_prime_decomposition (M : Type) [Monoid M] [Finite M] :
    Nonempty (KRFactorTowerGrp M) := by
  classical
  have : Fintype M := Fintype.ofFinite M
  -- Cayley: the left regular representation `M →* End M` is injective
  -- (`monoid_faithful_self`).
  have hf : Function.Injective (MulAction.toEndHom (M := M) (α := M)) :=
    KrohnRhodes.monoid_faithful_self M
  -- The DKS induction at `n := Nat.card M`: a factor list, a tower for the constants
  -- closure `(M,M)‾`, and the simple-group divisibility into `M`.
  obtain ⟨factors, towC, hdiv⟩ :=
    dks_aux (Nat.card M) M M (MulAction.toEndHom (M := M) (α := M)) hf le_rfl
  -- `M ≼ (M,M)‾` pulls the tower back to `M` (`divTowerWreath_of_sgDiv`);
  -- the `groupFactorsDivide` field carries over unchanged.
  exact ⟨⟨factors,
    divTowerWreath_of_sgDiv (sgdiv_closure_monoid _ hf) towC, hdiv⟩⟩

/-! ## A chosen factor tower -/

/-- **The chosen Krohn-Rhodes factor tower of a finite monoid.** For a finite monoid $M$, a
chosen factor tower with the prime-divisor guarantee (`KRFactorTowerGrp`), extracted from the
existence theorem `krohn_rhodes_prime_decomposition` by `Nonempty.some`. -/
noncomputable def krFactorTowerGrpOf (M : Type) [Monoid M] [Finite M] :
    KRFactorTowerGrp M :=
  (krohn_rhodes_prime_decomposition M).some

end KrohnRhodes

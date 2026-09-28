# Krohn–Rhodes prime decomposition in Lean 4

**Theorem.** Let *M* be a finite monoid. There are finite monoids *F*₁, …, *F*ₖ, each either
aperiodic or a simple group, such that

> *M* ≺ *F*₁ ≀ (*F*₂ ≀ (⋯ ≀ *F*ₖ))

and every *F*ᵢ that is a simple group divides *M*.

Here *A* ≺ *B* (*A* divides *B*) means that *A* is a homomorphic image of a subsemigroup of *B*.
A monoid is aperiodic if all of its subgroups are trivial. ≀ is the wreath product of monoids,
with each level acting on a finite set.

In Lean, in [`KrohnRhodes/PrimeDecomposition.lean`](KrohnRhodes/PrimeDecomposition.lean) (namespace `KrohnRhodes`):

```lean
theorem krohn_rhodes_prime_decomposition (M : Type) [Monoid M] [Finite M] :
    Nonempty (KRFactorTowerGrp M)
```

A `KRFactorTowerGrp M` consists of:

- `factors : List KRFactor`: each factor is a finite monoid with a proof that it is either
  aperiodic (every element has a trivial H-class) or a simple group (a simple group structure
  whose underlying monoid is the factor's monoid);
- `divides : DivTowerWreath M factors`: *M* divides the right-iterated wreath product of the
  factors;
- `groupFactorsDivide`: every simple-group factor divides *M*.

The theorem depends only on the axioms `propext`, `Classical.choice` and `Quot.sound`, with no
`sorry`.

## Source

The theorem is due to K. Krohn and J. Rhodes, *Algebraic theory of machines. I. Prime
decomposition theorem for finite semigroups and machines*, Trans. Amer. Math. Soc. 116 (1965),
450–464.

The proof formalized here is the local-divisor proof of V. Diekert, M. Kufleitner and
B. Steinberg, *The Krohn–Rhodes Theorem and Local Divisors*, Fundamenta Informaticae 116 (2012),
[arXiv:1111.1585](https://arxiv.org/abs/1111.1585): their Theorem 3.1, Corollary 3.2 and
Theorem 4.1, written for left actions.

## What it does not cover

- **Aperiodic factors are not reduced to the flip-flop.** The classical statement takes every
  aperiodic factor to be the flip-flop monoid *U*₂; this statement only requires the factors to
  be aperiodic. For an aperiodic *M* it therefore holds with *M* itself as the only factor, so
  its content is the group part. The proof's aperiodic factors are reset monoids (the identity
  together with all constant maps on a finite set). Each of these embeds in a direct power of
  *U*₂, but that step is not part of the formal statement.
- **Monoids, not semigroups.** The statement is for finite monoids. Finite semigroups are not
  treated separately.
- **Universe 0.** *M* ranges over `Type`.

## Conventions

- `Function.End Q` multiplies by composition, `(f * g) x = f (g x)`, so constant maps are left
  zeros.
- In `WreathProduct A B X`, `(p * q).func x = p.func (q.base • x) * q.func x` and
  `(p * q).base = p.base * q.base`.
- The tower condition uses semigroup division (`SgDiv`). The simple-group factors divide *M* as
  monoids (`KrohnRhodes.MonoidDivides`: a quotient of a submonoid).

## Building

Requires [elan](https://github.com/leanprover/elan). The toolchain (Lean 4.28.0) and Mathlib
(`v4.28.0`) are pinned in `lean-toolchain` and `lake-manifest.json`.

```sh
lake exe cache get        # fetch Mathlib and its prebuilt cache (~1 GB download, ~7 GB on disk)
lake build
lake env lean Check.lean  # prints the statement and its axioms
```

## Files

All paths are under `KrohnRhodes/`.

| File | Contents |
|---|---|
| `PrimeDecomposition.lean` | The proof and the main theorem |
| `FactorTower.lean` | `KRFactor`, `DivTowerWreath`, wreath associativity, the group tower |
| `Foundations/WreathProduct.lean` | `SgDiv`, `WreathProduct` |
| `Foundations/GreenRelations.lean` | Green's relations `L`, `R`, `H`; `IsAperiodicElem` |
| `Foundations/LocalDivisor.lean` | `MonoidDivides`; the local divisor `M_c` |
| `Foundations/KrasnerKaloujnine.lean` | The Krasner–Kaloujnine embedding |
| `Foundations/MonoidWreathBridge.lean` | Mathlib's regular wreath product → `WreathProduct` |
| `Foundations/ConstantMaps.lean` | Constant maps; aperiodicity of reset monoids |
| `Foundations/Cayley.lean` | Cayley's theorem for monoids |
| `Foundations/Division.lean` | Semigroup-division lemmas |

## Authorship

The proofs were written by Claude Code agents under the direction of Aditya Rao.

## License

Apache-2.0; see [`LICENSE`](LICENSE). Citation metadata is in [`CITATION.cff`](CITATION.cff).

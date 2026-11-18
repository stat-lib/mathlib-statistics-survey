---
title: "Convergence in distribution of random variables"
source_module: "Mathlib.MeasureTheory.Function.ConvergenceInDistribution"
source_path: "Mathlib/MeasureTheory/Function/ConvergenceInDistribution.lean"
mathlib_commit: "https://github.com/leanprover-community/mathlib4/blob/a2f96aabcf72be9e18bece4b5c7c54fcc0c029f4/Mathlib/MeasureTheory/Function/ConvergenceInDistribution.lean"
last_update: "2026-11-01"
topics:
  - "convergence in distribution"
  - "weak convergence"
  - "continuous mapping theorem"
  - "Slutsky's theorem"
---

# Convergence in distribution of random variables

Mathlib source: [Mathlib.MeasureTheory.Function.ConvergenceInDistribution](https://github.com/leanprover-community/mathlib4/blob/a2f96aabcf72be9e18bece4b5c7c54fcc0c029f4/Mathlib/MeasureTheory/Function/ConvergenceInDistribution.lean)

## 1. Mathematical results and Lean translation

### 1.1 Core definition

**Mathematics.**

Let (X_i) be random variables with values in a topological measurable space (E). The random
variables may be defined on different probability spaces
((\Omega_i,\mathcal F_i,\mu_i)). Let (Z) be an (E)-valued random variable on another
probability space ((\Omega',\mathcal F',\mu')). We say that (X_i) converges in distribution to
(Z) along a filter (l) when their laws converge weakly:

\[
  (\mu_i)_{X_i} \Longrightarrow (\mu')_Z.
\]

Equivalently, for every bounded continuous real- or complex-valued function (f),

\[
  \int f(X_i)\,d\mu_i \longrightarrow \int f(Z)\,d\mu'.
\]

For an ordinary sequence, take the index type to be `ℕ` and the filter to be `atTop`.

**Lean.**

```lean
structure TendstoInDistribution [OpensMeasurableSpace E]
    (X : (i : ι) → Ω i → E) (l : Filter ι)
    (Z : Ω' → E) (μ : (i : ι) → Measure (Ω i))
    [∀ i, IsProbabilityMeasure (μ i)]
    (μ' : Measure Ω' := by volume_tac) [IsProbabilityMeasure μ'] : Prop where
  forall_aemeasurable : ∀ i, AEMeasurable (X i) (μ i)
  aemeasurable_limit : AEMeasurable Z μ' := by fun_prop
  tendsto : Tendsto (β := ProbabilityMeasure E)
      (fun n ↦ ⟨(μ n).map (X n), inferInstance⟩) l
      (𝓝 ⟨μ'.map Z, inferInstance⟩)
```

The three fields have distinct roles.

1. `forall_aemeasurable` makes every pushforward `(μ i).map (X i)` a genuine law.
2. `aemeasurable_limit` does the same for `μ'.map Z`.
3. `tendsto` is the mathematical convergence statement: the pushforward probability measures
   converge in the weak topology carried by `ProbabilityMeasure E`.

The use of a dependent family `Ω : ι → Type*` is important. The sample space and its probability
measure may change with the index; only the state space `E` is fixed.

The file exposes the bounded-continuous-function formulation as a theorem:

```lean
theorem tendstoInDistribution_iff_forall_integral_rclike_tendsto
    (𝕜 : Type*) [RCLike 𝕜] [OpensMeasurableSpace E]
    (hX : ∀ i, AEMeasurable (X i) (μ i)) (hZ : AEMeasurable Z μ') :
    TendstoInDistribution X l Z μ μ' ↔
      ∀ f : E →ᵇ 𝕜,
        Tendsto (fun i ↦ ∫ ω, f (X i ω) ∂(μ i)) l
          (𝓝 (∫ ω, f (Z ω) ∂μ'))
```

Here `E →ᵇ 𝕜` is the type of bounded continuous functions and `RCLike 𝕜` allows either real or
complex test functions. The proof applies the corresponding characterization for
`ProbabilityMeasure` and uses `integral_map` to rewrite integrals against pushforward measures as
expectations of compositions.

### 1.2 Continuous mapping theorem

**Mathematics.** If (X_i \Rightarrow Z) and (g:E\to F) is continuous, then
(g(X_i)\Rightarrow g(Z)).

**Lean.**

```lean
theorem TendstoInDistribution.continuous_comp {F : Type*}
    [OpensMeasurableSpace E] [TopologicalSpace F]
    [MeasurableSpace F] [BorelSpace F] {g : E → F}
    (hg : Continuous g) (h : TendstoInDistribution X l Z μ μ') :
    TendstoInDistribution (fun n ↦ g ∘ X n) l (g ∘ Z) μ μ'
```

The proof uses continuity of pushforward on `ProbabilityMeasure`. The hypothesis `hg` is also used
to prove almost-everywhere measurability of the compositions. `BorelSpace F` connects the topology
on the target with its measurable structure, so that continuity supplies measurability.

### 1.3 Relations with stronger modes of convergence

The file proves the standard implication chain relevant here:

\[
  X_i \to Z \text{ almost surely}
  \quad\Longrightarrow\quad
  X_i \to Z \text{ in probability}
  \quad\Longrightarrow\quad
  X_i \Rightarrow Z.
\]

The two distributional conclusions are exported as follows.

```lean
theorem tendstoInDistribution_of_ae_tendsto [l.IsCountablyGenerated]
    [OpensMeasurableSpace E] {X : ι → Ω' → E}
    (hX₁ : ∀ i, AEMeasurable (X i) μ') (hZ : AEMeasurable Z μ')
    (hX₂ : ∀ᵐ ω ∂μ', Tendsto (fun i ↦ X i ω) l (𝓝 (Z ω))) :
    TendstoInDistribution X l Z (fun _ ↦ μ') μ'
```

```lean
theorem TendstoInMeasure.tendstoInDistribution
    [PseudoEMetricSpace E] [BorelSpace E]
    [l.IsCountablyGenerated] [l.NeBot] {X : ι → Ω' → E}
    (h : TendstoInMeasure μ' X l Z)
    (hX : ∀ i, AEMeasurable (X i) μ') :
    TendstoInDistribution X l Z (fun _ ↦ μ') μ'
```

The almost-sure theorem tests weak convergence against bounded continuous nonnegative functions and
uses dominated convergence. This is where countable generation of `l` is required by the
filter-indexed dominated convergence theorem.

The convergence-in-probability theorem uses the subsequence principle: every subsequence of a
sequence converging in probability has a further subsequence converging almost surely. The previous
theorem then gives convergence in distribution along that further subsequence, and the subsequence
criterion gives convergence of the original laws. `l.IsCountablyGenerated` and `l.NeBot` support
these subsequence results. The metric structure is needed to state convergence in measure.

### 1.4 A negligible-perturbation theorem

This is the main technical result used to prove the later Slutsky API.

**Mathematics.** Suppose (X_i\Rightarrow Z) and (Y_i-X_i\to 0) in probability. Then
(Y_i\Rightarrow Z).

**Lean.**

```lean
lemma tendstoInDistribution_of_tendstoInMeasure_sub
    {X : ι → Ω'' → E} [l.IsCountablyGenerated]
    (Y : ι → Ω'' → E) (Z : Ω' → E)
    (hXZ : TendstoInDistribution X l Z (fun _ ↦ μ'') μ')
    (hXY : TendstoInMeasure μ'' (Y - X) l 0)
    (hY : ∀ i, AEMeasurable (Y i) μ'') :
    TendstoInDistribution Y l Z (fun _ ↦ μ'') μ'
```

The ambient assumptions for this declaration are

```lean
[SeminormedAddCommGroup E] [SecondCountableTopology E] [BorelSpace E]
```

They provide subtraction and a norm, measurable additive operations, and the bounded-Lipschitz
characterization of weak convergence.

**Proof.** Let (F:E\to\mathbb R) be bounded and (L)-Lipschitz. For any
(\varepsilon>0), split according to whether
(\lVert Y_i-X_i\rVert<\varepsilon/2). The file proves an inequality of the form

\[
\begin{aligned}
\left|\int F\,d\mathcal L(Y_i)-\int F\,d\mathcal L(Z)\right|
&\le L\frac{\varepsilon}{2}
 + M\,\mu''\!\left\{\lVert Y_i-X_i\rVert\ge\frac{\varepsilon}{2}\right\}\\
&\quad+
\left|\int F\,d\mathcal L(X_i)-\int F\,d\mathcal L(Z)\right|.
\end{aligned}
\]

The probability term tends to zero by `hXY`, and the final integral difference tends to zero by
`hXZ`. Hence all bounded Lipschitz test integrals converge, which implies weak convergence.

The hypotheses are used as follows.

| Hypothesis | Use in the proof |
| --- | --- |
| `hXZ` | Supplies measurability of `X` and `Z`, and convergence of bounded Lipschitz test integrals. |
| `hXY` | Makes the probability of the large-difference event tend to zero. |
| `hY` | Supplies measurability of `Y`, needed for pushforwards and integral manipulations. |
| `SeminormedAddCommGroup E` | Provides `Y - X`, the norm, and the metric estimate. |
| `SecondCountableTopology E`, `BorelSpace E` | Support measurable algebraic operations and the measurable/topological compatibility used by the Portmanteau API. |
| `l.IsCountablyGenerated` | Required by the bounded-Lipschitz characterization for a general filter. |
| Probability-measure instances for `μ'` and `μ''` | Bound total mass by one and place the laws in `ProbabilityMeasure`. |

### 1.5 Slutsky's theorem

**Mathematics.** If (X_i\Rightarrow Z) and (Y_i\to c) in probability, then
((X_i,Y_i)\Rightarrow(Z,c)). Consequently, for every continuous (g),
(g(X_i,Y_i)\Rightarrow g(Z,c)).

**Lean.**

```lean
theorem TendstoInDistribution.prodMk_of_tendstoInMeasure_const
    {E' : Type*} [SeminormedAddCommGroup E']
    [SecondCountableTopology E'] [BorelSpace E']
    [l.IsCountablyGenerated]
    (X : ι → Ω'' → E) (Y : ι → Ω'' → E') (Z : Ω' → E)
    {c : E'}
    (hXZ : TendstoInDistribution X l Z (fun _ ↦ μ'') μ')
    (hY : TendstoInMeasure μ'' Y l (fun _ ↦ c))
    (hY_meas : ∀ i, AEMeasurable (Y i) μ'') :
    TendstoInDistribution (fun n ω ↦ (X n ω, Y n ω)) l
      (fun ω ↦ (Z ω, c)) (fun _ ↦ μ'') μ'
```

The proof first obtains
((X_i,c)\Rightarrow(Z,c)) from the continuous mapping theorem applied to
(x\mapsto(x,c)). It then observes that

\[
  (X_i,Y_i)-(X_i,c)=(0,Y_i-c)\to 0
\]

in probability and applies the negligible-perturbation theorem.

The continuous-function version is:

```lean
theorem TendstoInDistribution.continuous_comp_prodMk_of_tendstoInMeasure_const
    {g : E × E' → F} (hg : Continuous g) ... :
    TendstoInDistribution (fun n ω ↦ g (X n ω, Y n ω)) l
      (fun ω ↦ g (Z ω, c)) (fun _ ↦ μ'') μ'
```

Finally, `add_of_tendstoInMeasure_const` specializes this theorem to
`g (x,y) = x + y`.

### 1.6 Assumption map

The file uses several topological and measurable-space typeclasses. The following table records
their mathematical and proof-theoretic roles instead of treating them as background boilerplate.

| Assumption | Where it is used |
| --- | --- |
| `∀ i, IsProbabilityMeasure (μ i)`, `IsProbabilityMeasure μ'`, `IsProbabilityMeasure μ''` | Packages pushforwards as `ProbabilityMeasure`; supplies total mass one in integral bounds. |
| `OpensMeasurableSpace E` | Relates the measurable structure of `E` to its topology, allowing the weak topology on laws and bounded-continuous test-function theorems. |
| `AEMeasurable` hypotheses | Justify `Measure.map`, `integral_map`, and `lintegral_map'`; are transferred through almost-everywhere equality and continuous composition. |
| `RCLike 𝕜` | Lets the integral characterization use either real or complex bounded continuous test functions. |
| `Continuous g` and `BorelSpace F` | Make `g` measurable and make pushforward by `g` continuous on probability measures. |
| `HasOuterApproxClosed E`, `BorelSpace E`, `l.NeBot` in the uniqueness theorem | Give the separation/uniqueness properties for weak limits and exclude the bottom filter, along which every function would vacuously converge. |
| `l.IsCountablyGenerated` in the almost-sure theorem | Required by filter-indexed dominated convergence. |
| `l.IsCountablyGenerated`, `l.NeBot` in `TendstoInMeasure.tendstoInDistribution` | Required by extraction of an almost-surely convergent subsubsequence and the subsequence convergence criterion. |
| `PseudoEMetricSpace E` | Supplies the distance used in convergence in measure. |
| `SeminormedAddCommGroup E` | Supplies subtraction, zero, norm, and translation-invariant metric estimates in the perturbation and Slutsky results. |
| `SecondCountableTopology E`, `BorelSpace E` | Supply standard measurable algebra/product instances and the bounded-Lipschitz Portmanteau interface used in the perturbation and product results. |

Some assumptions enter through typeclass inference rather than appearing as named proof terms.
For example, the proof does not write `SecondCountableTopology E` explicitly, but `fun_prop` and the
product/additive measurable-space infrastructure use instances that depend on it.

## 2. Core definitions and imported infrastructure

This file introduces one new mathematical structure, `TendstoInDistribution`. It relies on the
following existing definitions.

### 2.1 Law as a pushforward measure

For `X : Ω → E`, its law under `μ` is `μ.map X`. If `s` is measurable, this is mathematically

\[
  (\mu\mathbin{\mathrm{map}}X)(s)=\mu(X^{-1}(s)).
\]

Almost-everywhere measurability is included in `TendstoInDistribution` because the useful behavior
of `Measure.map` requires it.

### 2.2 `ProbabilityMeasure E`

`ProbabilityMeasure E` packages a measure on `E` together with the fact that its total mass is one.
When `E` has compatible topology and measurable structure, this type carries the weak topology.
Consequently, the third structure field can use ordinary topological `Tendsto`.

### 2.3 Filters

`l : Filter ι` describes how the index approaches its limit. The common sequential choice is
`ι = ℕ` and `l = atTop`, but the definition is not restricted to sequences.

### 2.4 Measurable/topological compatibility

- `OpensMeasurableSpace E` means open subsets of `E` are measurable.
- `BorelSpace E` identifies the measurable structure with the Borel sigma-algebra.
- `SecondCountableTopology E` supplies a countable topological basis and is useful for measurable
  product and algebraic constructions.
- `AEMeasurable X μ` says that `X` agrees almost everywhere with a measurable function.

## 3. Other public declarations

| Mathematical role | Lean declaration |
| --- | --- |
| Definition of convergence in distribution as weak convergence of laws | `TendstoInDistribution` |
| Bounded continuous test-function characterization | `tendstoInDistribution_iff_forall_integral_rclike_tendsto` |
| A constant family converges to itself | `tendstoInDistribution_const` |
| Variables all having the same law converge in distribution to that law | `tendstoInDistribution_of_identDistrib` |
| Replace variables and limit by almost-everywhere equal versions | `TendstoInDistribution.congr` |
| Automatic result for an empty state space | `tendstoInDistribution_of_isEmpty` |
| Uniqueness of the limiting law | `tendstoInDistribution_unique` |
| Continuous mapping theorem | `TendstoInDistribution.continuous_comp` |
| Almost-sure convergence implies convergence in distribution | `tendstoInDistribution_of_ae_tendsto` |
| Convergence in probability implies convergence in distribution | `TendstoInMeasure.tendstoInDistribution` |
| A negligible-in-probability perturbation preserves a distributional limit | `tendstoInDistribution_of_tendstoInMeasure_sub` |
| Alternative implication from convergence in probability with explicit limit measurability | `TendstoInMeasure.tendstoInDistribution_of_aemeasurable` |
| Pair form of Slutsky's theorem | `TendstoInDistribution.prodMk_of_tendstoInMeasure_const` |
| Continuous-function form of Slutsky's theorem | `TendstoInDistribution.continuous_comp_prodMk_of_tendstoInMeasure_const` |
| Additive Slutsky corollary | `TendstoInDistribution.add_of_tendstoInMeasure_const` |

Two design details are worth noting.

First, `tendstoInDistribution_unique` concludes equality of limiting laws,

```lean
μ'.map Z = μ''.map W
```

rather than equality of `Z` and `W` as functions. This is the correct uniqueness statement for
convergence in distribution. `l.NeBot` rules out the degenerate bottom filter, while
`HasOuterApproxClosed E` and `BorelSpace E` provide the separation properties needed for uniqueness
of weak limits.

Second, `tendstoInDistribution_of_identDistrib` works even when the variables live on different
sample spaces. It proves convergence because all mapped measures are literally equal to the limit
law.

## 4. Boundary conditions and scope

- The state space `E` can be much more general than `ℝ`; assumptions become stronger only for
  metric, additive, or Slutsky results.
- The basic definition allows the source probability space and measure to depend on the index.
- The almost-sure, convergence-in-probability, perturbation, and Slutsky theorems in this file use a
  fixed source space and fixed source measure.
- The continuous mapping theorem requires a globally continuous function.
- The file gives integral and bounded-Lipschitz characterizations, but it does not give a direct
  real-line characterization through convergence of cumulative distribution functions at
  continuity points.
- The empty-state-space lemma is a formal boundary case. In a nonempty probabilistic application it
  normally disappears by typeclass inference.

## 5. Discussion

The main design choice is to define convergence in distribution by reusing the weak topology on
`ProbabilityMeasure E`, instead of introducing a separate ad hoc convergence relation on random
variables. This makes the continuous mapping and uniqueness results short consequences of the
measure-level API.

The longest proof is the negligible-perturbation theorem. Its bounded-Lipschitz argument is then
reused to build Slutsky's theorem and the additive corollary. Thus the file has a clear dependency
structure: one definition, basic transport lemmas, stronger-to-weaker convergence implications, a
perturbation lemma, and Slutsky-style downstream API.

From an applied asymptotics perspective, the perturbation lemma is particularly useful. It separates
an argument into a tractable leading term with a known distributional limit and a remainder that
vanishes in probability. The conclusion is equality of the *asymptotic* distributional limit; it
does not assert that the two statistics are identically distributed at each finite index.

## 6. References

- Mathlib source at the recorded revision:
  [ConvergenceInDistribution.lean](https://github.com/leanprover-community/mathlib4/blob/a2f96aabcf72be9e18bece4b5c7c54fcc0c029f4/Mathlib/MeasureTheory/Function/ConvergenceInDistribution.lean).
- Mathlib generated documentation:
  [Mathlib.MeasureTheory.Function.ConvergenceInDistribution](https://leanprover-community.github.io/mathlib4_docs/Mathlib/MeasureTheory/Function/ConvergenceInDistribution.html).
- Billingsley, P. *Convergence of Probability Measures*, 2nd ed., Wiley, 1999.
- Kallenberg, O. *Foundations of Modern Probability*, 3rd ed., Springer, 2021.


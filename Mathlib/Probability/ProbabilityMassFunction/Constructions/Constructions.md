---
title: Specific constructions of probability mass functions
source_module: Mathlib.Probability.ProbabilityMassFunction.Constructions
source_path: Mathlib/Probability/ProbabilityMassFunction/Constructions.lean
mathlib_commit: https://github.com/leanprover-community/mathlib4/commits/1001f9283405e049c5f2a92378a181ddc311ccd1/Mathlib/Probability/ProbabilityMassFunction/Constructions.lean
last_update: 2026-09-21
topics:
  - probability mass functions
  - pushforward measures
  - finite distributions
  - normalization and filtering
---

# Specific constructions of probability mass functions

Mathlib source: [Mathlib.Probability.ProbabilityMassFunction.Constructions][source]

## 1. Mathemetical results and LEAN translation

- what is the core theorem/definition this file trying to build?

The file constructs new PMFs by transforming distributions, specifying finite probability tables, and normalizing weights. Its `Map` section connects the discrete image distribution to the pushforward of a measure.

**Theorem 1.** Let $(\alpha,\mathcal A)$ and $(\beta,\mathcal B)$ be measurable spaces, $p$ a PMF on $\alpha$, and $f:\alpha\to\beta$ measurable. The probability measure associated with the image PMF equals the pushforward of the measure associated with $p$:

```math
\mu_{p.\mathrm{map}\,f}=f_\#\mu_p.
```

In other words, mapping a PMF and then converting it to a measure gives the same result as
converting it to a measure first and then applying `Measure.map`.

$$
\begin{array}{ccc}
\mathrm{PMF}\,\alpha
&
\overset{\mathtt{PMF.map}\,f}{\longrightarrow}
&
\mathrm{PMF}\,\beta
\\
&&\\
\scriptstyle{\mathtt{toMeasure}}\downarrow
&&
\downarrow\scriptstyle{\mathtt{toMeasure}}
\\
&&\\
\mathrm{Measure}\,\alpha
&
\overset{\mathtt{Measure.map}\,f}{\longrightarrow}
&
\mathrm{Measure}\,\beta
\end{array}
$$

- how is this in LEAN

**Theorem 1 (Lean).** The measurable spaces are specified by `{mα : MeasurableSpace α}` and `{mβ : MeasurableSpace β}`. For `f : α → β`, `p : PMF α`, and `hf : Measurable f`, the statement and proof are:

```lean
@[simp]
lemma toMeasure_map (p : PMF α) (hf : Measurable f) : p.toMeasure.map f = (p.map f).toMeasure := by
  ext s hs : 1; rw [PMF.toMeasure_map_apply _ _ _ hf hs, Measure.map_apply hf hs]
```

- what was the proof

**Proof.** Write $q=p.\mathrm{map}\,f$. Its point masses are

```math
q(b)=\sum_{a:f(a)=b}p(a).
```

For a measurable set $B\subseteq\beta$, regrouping nonnegative sums gives

```math
\begin{aligned}
\mu_q(B)
&=\sum_{b\in B}q(b)\\
&=\sum_{b\in B}\sum_{a:f(a)=b}p(a)\\
&=\sum_{a:f(a)\in B}p(a)\\
&=\mu_p(f^{-1}(B))\\
&=(f_\#\mu_p)(B).
\end{aligned}
```

The measurability of $f$ ensures that $f^{-1}(B)$ is measurable. Since the two measures agree on every measurable set, they are equal.

The source first proves this identity for `toOuterMeasure`, where no measurability assumptions are needed, and then obtains `toMeasure_map_apply`. In the final proof, `ext s hs : 1` reduces measure equality to equality on a measurable set; the two rewrite rules turn both sides into `p.toMeasure (f ⁻¹' s)`.

## 2. Core definitions

A PMF is a function $p:\alpha\to[0,\infty]$ whose masses sum to $1$. In [Basic.lean][basic], this is represented by `{f : α → ℝ≥0∞ // HasSum f 1}`. Its support is $\{a:p(a)\ne0\}$.

**Definition 1.** The image PMF is the distribution of $f(X)$ when $X$ has distribution $p$.

```lean
def map (f : α → β) (p : PMF α) : PMF β :=
  bind p (pure ∘ f)
```

Remark 1. The operations `pure` and `bind` come from [Monad.lean][monad]. Here `pure a` assigns mass $1$ to $a$, and

```math
(p.\mathrm{bind}\,q)(b)=\sum_a p(a)q(a)(b).
```

Thus `bind p (pure ∘ f)` samples according to $p$ and applies the deterministic function $f$.

**Definition 2.** Given a distribution $q$ over functions and a distribution $p$ over inputs, `seq q p` is the distribution of $F(X)$ with $F\sim q$ and $X\sim p$ sampled independently:

```math
(q.\mathrm{seq}\,p)(b)
=\sum_f\sum_a\mathbf1_{\{f(a)=b\}}q(f)p(a).
```

```lean
def seq (q : PMF (α → β)) (p : PMF α) : PMF β :=
  q.bind fun m => p.bind fun a => pure (m a)
```

**Definition 3.** Let $s\subseteq\alpha$ be finite. If $f:\alpha\to[0,\infty]$ satisfies

```math
\sum_{a\in s}f(a)=1,
\qquad f(a)=0\quad\text{for }a\notin s,
```

then $f$ defines a PMF.

```lean
def ofFinset (f : α → ℝ≥0∞) (s : Finset α) (h : ∑ a ∈ s, f a = 1)
    (h' : ∀ (a) (_ : a ∉ s), f a = 0) : PMF α :=
  ⟨f, h ▸ hasSum_sum_of_ne_finset_zero h'⟩
```

The condition `h'` reduces the infinite sum to the finite sum in `h`. This constructor keeps the original function; it does not automatically set its values outside $s$ to zero.

**Definition 4.** When the entire type $\alpha$ is finite, the condition $\sum_a f(a)=1$ suffices.

```lean
def ofFintype [Fintype α] (f : α → ℝ≥0∞) (h : ∑ a, f a = 1) : PMF α :=
  ofFinset f Finset.univ h fun a ha => absurd (Finset.mem_univ a) ha
```

This uses `ofFinset` with the full finite set. There are no elements outside `Finset.univ`.

**Definition 5.** For weights $f:\alpha\to[0,\infty]$ with $0<Z=\sum_a f(a)<\infty$, normalization gives $p(a)=f(a)/Z$.

```lean
def normalize (f : α → ℝ≥0∞) (hf0 : tsum f ≠ 0) (hf : tsum f ≠ ∞) : PMF α :=
  ⟨fun a => f a * (∑' x, f x)⁻¹,
    ENNReal.summable.hasSum_iff.2 (ENNReal.tsum_mul_right.trans (ENNReal.mul_inv_cancel hf0 hf))⟩
```

The proof carried by the definition is $\sum_a f(a)Z^{-1}=ZZ^{-1}=1$. Both hypotheses are needed for the cancellation.

**Definition 6.** Filtering retains the mass on a set $s$ and renormalizes it:

```math
(p.\mathrm{filter}\,s)(a)
=\frac{\mathbf1_s(a)p(a)}{\sum_{x\in s}p(x)}.
```

```lean
def filter (p : PMF α) (s : Set α) (h : ∃ a ∈ s, a ∈ p.support) : PMF α :=
  PMF.normalize (s.indicator p) (by simpa using h) (p.tsum_coe_indicator_ne_top s)
```

The hypothesis supplies a point in $s$ with positive mass, so the denominator is nonzero. Its finiteness follows because the retained mass is at most $1$.

**Definition 7.** The Bernoulli PMF assigns mass $p$ to `true` and $1-p$ to `false`, for $0\le p\le1$.

```lean
@[deprecated ProbabilityTheory.bernoulliMeasure +typeChanged (since := "2026-04-07")]
def bernoulli (p : ℝ≥0) (h : p ≤ 1) : PMF Bool :=
  ofFintype (fun b => cond b p (1 - p)) (by simp [h])
```

Nonnegativity is built into `ℝ≥0`; the upper bound is supplied by `h`. The two masses sum to $1$.

## 3 Public declaration

- except the core definition and main theorems, what are the other related things we would like to consider?

| Declaration | Role |
|---|---|
| `PMF.map` | Definition of the image PMF. |
| `PMF.toMeasure_map` | Compatibility with measure pushforward. |
| `PMF.map_apply` | Computes image point masses by summing over preimages. |
| `PMF.support_map` | The image support is `f '' p.support`. |
| `PMF.map_id`, `PMF.map_comp` | Identity and composition laws for image distributions. |
| `PMF.map_bind`, `PMF.bind_map` | Relate deterministic transformations to two-stage sampling. |
| `PMF.seq_apply`, `PMF.support_seq` | Describe the masses and support of random function application. |
| `PMF.ofFinset_apply`, `PMF.ofFintype_apply` | Recover the supplied probability masses. |
| `PMF.support_ofFinset`, `PMF.support_ofFintype` | Identify the nonzero entries of finite probability tables. |
| `PMF.map_ofFintype` | Constructs a transformed finite table by summing over fibers. |
| `PMF.normalize_apply`, `PMF.support_normalize` | Give normalized masses and show that support is unchanged. |
| `PMF.filter_apply`, `PMF.support_filter` | Give filtered masses and the restricted support. |
| `PMF.bernoulli_apply`, `PMF.support_bernoulli` | Describe Bernoulli masses and their boundary cases. |

Consider three of these results.

```lean
theorem map_comp (g : β → γ) : (p.map f).map g = p.map (g ∘ f) := by simp [map, Function.comp_def]
```

Transforming first by $f$ and then by $g$ gives the same distribution as transforming once by $g\circ f$. Expanding `map` reduces the proof to the associativity of `bind` and the identity law for `pure`.

```lean
open scoped Classical in
@[simp]
lemma map_ofFintype [Fintype β] (f : α → ℝ≥0∞) (h : ∑ a, f a = 1) (g : α → β) :
    (ofFintype f h).map g = ofFintype (fun b ↦ ∑ a with g a = b, f a)
      (by simpa [Finset.sum_fiberwise_eq_sum_filter univ univ g f]) := by
  ext b : 1
  simp only [sum_filter, eq_comm, map_apply, ofFintype_apply]
  exact tsum_eq_sum fun _ h ↦ (h <| mem_univ _).elim
```

The section already assumes `[Fintype α]`. The new mass at $b$ is $\sum_{a:g(a)=b}f(a)$. Summing over all fibers counts each original mass once, so the new table also sums to $1$. The proof compares the point masses and converts `tsum` into a finite sum.

```lean
@[simp]
theorem support_filter : (p.filter s h).support = s ∩ p.support :=
  Set.ext fun _ => mem_support_filter_iff _
```

A point retains positive mass exactly when it belongs to $s$ and originally had positive mass. `Set.ext` turns the equality of supports into this pointwise equivalence.

The file also supplies `LawfulFunctor PMF`, `LawfulMonad PMF`, and `ULiftable PMF.{u} PMF.{v}` instances. The first two package the operation laws; the third transports PMFs across universe levels. `monad_map_eq_map` and `monad_seq_eq_seq` identify the generic notations `<$>` and `<*>` with the explicitly defined `PMF.map` and `PMF.seq`.

## 4. Scope and limitations

The ambient type need not be countable: a PMF may be defined on an uncountable type, but its nonzero support is countable, as established in [Basic.lean][basic]. These constructions describe discrete distributions, not continuous probability densities.

`map` itself needs no measurable-space structure. Its comparison with `Measure.map` assumes that $f$ is measurable. The associated measure formulas are stated on measurable sets.

`ofFinset` requires zero mass outside the specified finite set. `normalize` excludes zero and infinite total weight. `filter` requires positive retained mass and does not define conditioning on a zero-mass event.

The Bernoulli constructor includes $p=0$ and $p=1$, when only `false` or `true`, respectively, has positive mass. In this revision it is deprecated in favor of [ProbabilityTheory.bernoulliMeasure][bernoulli]. The `+typeChanged` annotation indicates a change of type, not merely a renamed declaration.

## Reference

[Constructions.lean][source]. Mathlib, commit `1001f9283405e049c5f2a92378a181ddc311ccd1`.

[Basic.lean][basic]. PMFs, support, and associated measures, same commit.

[Monad.lean][monad]. Pure distributions and two-stage sampling, same commit.

[Bernoulli.lean][bernoulli]. The measure-based Bernoulli distribution, same commit.

[source]: https://github.com/leanprover-community/mathlib4/blob/1001f9283405e049c5f2a92378a181ddc311ccd1/Mathlib/Probability/ProbabilityMassFunction/Constructions.lean
[basic]: https://github.com/leanprover-community/mathlib4/blob/1001f9283405e049c5f2a92378a181ddc311ccd1/Mathlib/Probability/ProbabilityMassFunction/Basic.lean
[monad]: https://github.com/leanprover-community/mathlib4/blob/1001f9283405e049c5f2a92378a181ddc311ccd1/Mathlib/Probability/ProbabilityMassFunction/Monad.lean
[bernoulli]: https://github.com/leanprover-community/mathlib4/blob/1001f9283405e049c5f2a92378a181ddc311ccd1/Mathlib/Probability/Distributions/Bernoulli.lean

---
title: Bernoulli distribution
source_module: Mathlib.Probability.Distributions.Bernoulli
source_path: Mathlib/Probability/Distributions/Bernoulli.lean
mathlib_commit: https://github.com/leanprover-community/mathlib4/blob/7d32461ad224e921eb05ead7ac02156702f4aa59/Mathlib/Probability/Distributions/Bernoulli.lean
last_update: 2026-11-27
topics:
  - "Bernoulli distribution"
  - "Dirac measures"
  - "probability measures"
  - "indicator functions"
---

# Bernoulli distribution

Mathlib source: [Bernoulli distribution](https://github.com/leanprover-community/mathlib4/blob/7d32461ad224e921eb05ead7ac02156702f4aa59/Mathlib/Probability/Distributions/Bernoulli.lean)

## 1. Mathematical result and Lean translation

### Main result

Given a measurable space $X$, two points $x, y \in X$, and a parameter $p \in [0,1]$, the Bernoulli measure $\mathrm{Ber}(x,y,p)$ is the probability measure that assigns mass $p$ to $x$ and mass $1-p$ to $y$:

$$
\mathrm{Ber}(x,y,p) = p\,\delta_x + (1-p)\,\delta_y,
$$

where $\delta_x$ is the Dirac measure concentrated at $x$. This is the abstract formalization of the Bernoulli law: an experiment with two possible outcomes, with probabilities $p$ and $1-p$.

**Lean.** The main declaration in the file is:

```lean
@[expose] noncomputable def bernoulliMeasure (x y : X) (p : I) : Measure X :=
  toNNReal p • dirac x + toNNReal (σ p) • dirac y
```

Here:
- `X` is a type with `[MeasurableSpace X]`; it is not required that $X$ be $\mathbb{R}$ or $\{0,1\}$, so the definition is general over an arbitrary measurable space.
- `p : I` is an element of `unitInterval`, so the condition $0 \le p \le 1$ is guaranteed by the type.
- `toNNReal p` converts $p$ to $\mathbb{R}_{\ge 0}$.
- `σ p` is the complement $1-p$ in `unitInterval`.
- `dirac x` and `dirac y` are Dirac measures.
- `•` is scalar multiplication of a measure by a nonnegative coefficient.

The notation `Ber(x, y, p)` is syntactic sugar for `bernoulliMeasure x y p`:

```lean
@[inherit_doc] scoped notation "Ber(" x ", " y ", " p ")" => bernoulliMeasure x y p
```

Implicit assumptions: The type `I` carries the proof that $0 \le p \le 1$. It is not required that $x \neq y$: if $x = y$, the measure degenerates to $\delta_x$ (see `bernoulliMeasure_self_eq_dirac`). It is not required that $X$ be finite or discrete; the definition works for any measurable space.

### Proof

There is no single main theorem with an elaborate proof: the file is built around the definition and lemmas that make its behavior explicit. The mathematically significant result is that $\mathrm{Ber}(x,y,p)$ is indeed a probability measure, established by the instance:

```lean
instance : IsProbabilityMeasure Ber(x, y, p) where
  measure_univ := by simp [bernoulliMeasure_def]
```

Explanation of the `by` block: In Lean, `by` enters a tactic mode: instead of writing an explicit proof term, one lists commands (`simp`, `rw`, `split_ifs`, etc.) that transform the goal until it is closed. Here `simp [bernoulliMeasure_def]` rewrites `Ber(x,y,p) univ` as `toNNReal p * 1 + toNNReal (σ p) * 1`, and since `p + σ p = 1` in `unitInterval`, the goal closes. The `by` block builds the proof, not the mathematical object. The definition `bernoulliMeasure` contains no `by`: it is a direct term.

## 2. Core definitions

### Definition 1: `bernoulliMeasure`

**Mathematics.** For $x, y \in X$ and $p \in [0,1]$,

$$
\mathrm{Ber}(x,y,p)(A) = p\,\mathbf{1}_{x \in A} + (1-p)\,\mathbf{1}_{y \in A}
$$

for every measurable set $A \subseteq X$. Equivalently, it is the linear combination of two Dirac measures.

**Lean.**

```lean
@[expose] noncomputable def bernoulliMeasure (x y : X) (p : I) : Measure X :=
  toNNReal p • dirac x + toNNReal (σ p) • dirac y
```

**Infoview.** `#check bernoulliMeasure` displays:

```text
bernoulliMeasure : {X : Type u_1} → [MeasurableSpace X] → X → X → I → Measure X
```

The lemma `bernoulliMeasure_def` is the bridge that reduces the notation to the explicit definition:

```lean
lemma bernoulliMeasure_def (x y : X) (p : I) :
    Ber(x, y, p) = toNNReal p • dirac x + toNNReal (σ p) • dirac y := rfl
```

It is proved by `rfl` because it is simply the unfolding of the definition.

## 3. Other public declarations

The following table lists all public declarations in the file, with their precise mathematical translation. For each lemma, the Lean type is shown in simplified but faithful form.

| Declaration | Mathematical role |
|---|---|
| `bernoulliMeasure_zero` | $\mathrm{Ber}(x,y,0)=\delta_y$. Degenerate case $p=0$. |
| `bernoulliMeasure_one` | $\mathrm{Ber}(x,y,1)=\delta_x$. Degenerate case $p=1$. |
| `bernoulliMeasure_apply` | Explicit formula for $\mathrm{Ber}(x,y,p)(s)$ with $s$ measurable: the four cases of membership of $x$ and $y$ in $s$. |
| `bernoulliMeasure_real_apply` | Version with `.real` (real measure, not $\mathbb{R}_{\ge 0}\infty$) of the previous formula. |
| `bernoulliMeasure_apply_of_mem_of_mem` | If $x,y\in s$, then $\mathrm{Ber}(x,y,p)(s)=1$. |
| `bernoulliMeasure_apply_of_mem_of_notMem` | If $x\in s$ and $y\notin s$, then $\mathrm{Ber}(x,y,p)(s)=p$. |
| `bernoulliMeasure_apply_of_notMem_of_mem` | If $x\notin s$ and $y\in s$, then $\mathrm{Ber}(x,y,p)(s)=1-p$. |
| `bernoulliMeasure_apply_of_notMem_of_notMem` | If $x,y\notin s$, then $\mathrm{Ber}(x,y,p)(s)=0$. |
| `bernoulliMeasure_real_apply_of_*` | Real versions of the four preceding lemmas. |
| `bernoulliMeasure_self_eq_dirac` | $\mathrm{Ber}(x,x,p)=\delta_x$. |
| `map_bernoulliMeasure` | If $f$ is measurable (or even only a.e. measurable with respect to Dirac measures), then $f_*\mathrm{Ber}(x,y,p)=\mathrm{Ber}(f(x),f(y),p)$. |
| `map_bernoulliMeasure'` | Version with explicit `Measurable f` hypothesis. |
| `eq_bernoulliMeasure` | Uniqueness criterion: if a measure $\mu$ takes the correct four values on measurable sets separating $x$ and $y$, then $\mu=\mathrm{Ber}(x,y,p)$. |
| `integrable_bernoulliMeasure` | Every function $f:X\to E$ (with $E$ a normed space) is integrable with respect to $\mathrm{Ber}(x,y,p)$. |
| `integral_bernoulliMeasure` | $\int f\,d\mathrm{Ber}(x,y,p)=p\,f(x)+(1-p)\,f(y)$. |
| `hasLaw_indicator_bernoulliMeasure` | The indicator $s\cdot c$ has law $\mathrm{Ber}(c,0,\langle P(s),\cdot\rangle)$ under $P$. |
| `hasLaw_indicator_one_bernoulliMeasure` | Special case $c=1$: the indicator of $s$ has law $\mathrm{Ber}(1,0,P(s))$. |

### Detailed API and mathematical translation

#### `bernoulliMeasure_apply`

This is the central lemma for computing the measure of a set.

```lean
lemma bernoulliMeasure_apply (p : I) {s : Set X} (hs : MeasurableSet s)
    [DecidablePred (· ∈ s)] :
    Ber(x, y, p) s = if x ∈ s then if y ∈ s then (1 : ℝ≥0∞) else toNNReal p
                    else if y ∈ s then toNNReal (σ p) else 0 := by
  split_ifs <;> simp_all [bernoulliMeasure_def, ← ENNReal.coe_add]
```

Mathematically:

$$
\mathrm{Ber}(x,y,p)(s) =
\begin{cases}
1 & x \in s,\ y \in s,\\
p & x \in s,\ y \notin s,\\
1-p & x \notin s,\ y \in s,\\
0 & x \notin s,\ y \notin s.
\end{cases}
$$

The `by` block uses `split_ifs` to separate the cases $x \in s$ and $y \in s$, and `simp_all` to reduce each case using the definition and the fact that $p + (1-p) = 1$. The `by` block is a proof by cases, not part of the definition.

#### `integral_bernoulliMeasure`

This lemma is the analogue of the expected value for a function $f$:

```lean
lemma integral_bernoulliMeasure [MeasurableSingletonClass X]
    (x y : X) (p : I) (f : X → E) :
    ∫ z, f z ∂Ber(x, y, p) = (p : ℝ) • (f x) + (1 - p : ℝ) • (f y) := by
  rw [bernoulliMeasure_def, integral_add_measure]
  · simp [NNReal.smul_def]
  all_goals exact (integrable_dirac (by simp)).smul_measure_nnreal
```

Mathematically:

$$
\int_X f \, d\mathrm{Ber}(x,y,p) = p\,f(x) + (1-p)\,f(y).
$$

This is the bridge between the abstract measure and concrete computation: the expected value of a function with respect to a Bernoulli measure is the weighted average of its values at the two points.

#### `hasLaw_indicator_bernoulliMeasure`

This theorem connects the abstract measure to indicator random variables:

```lean
theorem hasLaw_indicator_bernoulliMeasure [IsProbabilityMeasure P]
    {M : Type*} [Zero M] [MeasurableSpace M] (c : M) {s : Set Ω}
    (hs : NullMeasurableSet s P) :
    HasLaw (s.indicator (fun _ ↦ c)) Ber(c, 0, ⟨P.real s, by simp⟩) P := by
  ...
```

Mathematically: if $s$ is null-measurable with respect to $P$ (a.e. measurable) and $c$ is a constant, then the random variable $X(\omega) = c \cdot \mathbf{1}_s(\omega)$ has law $\mathrm{Ber}(c,0,P(s))$. In particular, the indicator of an event $s$ has law $\mathrm{Ber}(1,0,P(s))$: this is the formal model of “success/failure” with probability $P(s)$.

## 4. Boundary conditions

The file explicitly handles degenerate cases:

- $p = 0$: `bernoulliMeasure_zero` proves that $\mathrm{Ber}(x,y,0) = \delta_y$. All mass is at $y$.
- $p = 1$: `bernoulliMeasure_one` proves that $\mathrm{Ber}(x,y,1) = \delta_x$. All mass is at $x$.
- $x = y$: `bernoulliMeasure_self_eq_dirac` proves that $\mathrm{Ber}(x,x,p) = \delta_x$, independently of $p$. The definition does not require $x \neq y$, and the degenerate case is handled by linearity of measures.
- Sets containing neither $x$ nor $y$: the measure is $0$, as established by `bernoulliMeasure_apply_of_notMem_of_notMem`.

There are no finiteness or positivity conditions to handle, because the definition is a finite linear combination of Dirac measures.

## 5. Discussion

The file defines the Bernoulli distribution in an abstract and general way, without passing through $\{0,1\}$ or a probability mass function. This is in line with Kallenberg’s approach, which treats distributions as probability measures on arbitrary measurable spaces and uses Dirac measures as fundamental building blocks. The main difference is that Mathlib parametrizes the Bernoulli distribution by two arbitrary points $x$ and $y$, whereas the classical treatment focuses on $\{0,1\}$. This generalization is useful because it allows modeling experiments with any two outcomes without changing the underlying space.

**Possible next steps.** The file does not contain a notion of density with respect to a reference measure (there is no `pdf_eq` as for the uniform distribution), because the Bernoulli distribution is a discrete measure on two points and has no density with respect to Lebesgue measure. A possible development would be to connect `hasLaw_indicator_bernoulliMeasure` to an abstract version of the Bernoulli process (sequences of independent indicator variables), but this would require a separate file.

## 6. References

Kallenberg, O. (2021). *Foundations of Modern Probability* (3rd ed.). Probability Theory and Stochastic Modelling, Vol. 99. Springer, Cham. https://doi.org/10.1007/978-3-030-61871-1
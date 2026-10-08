---
title: "The central limit theorem in one dimension"
source_module: "Mathlib.Probability.CentralLimitTheorem"
source_path: "Mathlib/Probability/CentralLimitTheorem.lean"
mathlib_commit: "https://github.com/leanprover-community/mathlib4/blob/f7b0818b53d52ed1c795f727fe5c4c734dc41047/Mathlib/Probability/CentralLimitTheorem.lean"
last_update: "2026-10-08"
topics:
  - "central limit theorem"
  - "characteristic functions"
  - "convergence in distribution"
---

# The central limit theorem in one dimension

Mathlib source: [Mathlib.Probability.CentralLimitTheorem](https://github.com/leanprover-community/mathlib4/blob/f7b0818b53d52ed1c795f727fe5c4c734dc41047/Mathlib/Probability/CentralLimitTheorem.lean)

The goal is to explain the mathematics in this Lean file and how its code expresses it.

## 1. Mathematical result and Lean translation

### Main result

Let $(X_n)_{n\geq 0}$ be independent and identically distributed real random variables with finite second moment, common mean $\mu$, and variance $v$. Then

$$\frac{1}{\sqrt n}\sum_{k=0}^{n-1}(X_k-\mu)$$

converges in distribution to a centered Gaussian random variable with variance $v$. The statement includes the degenerate case $v=0$, when the limit is the point mass at zero.

The theorem allows the variables $X_n$ and the Gaussian limit $Y$ to live on different probability spaces. It specifies the law of $Y$, rather than requiring a construction of the limit on the same space as the sequence.

### Lean statement

The main declaration is `ProbabilityTheory.tendstoInDistribution_inv_sqrt_mul_sum_sub`:

```lean
theorem tendstoInDistribution_inv_sqrt_mul_sum_sub
    (hY : HasLaw Y (gaussianReal 0 (Var[X 0; P]).toNNReal) P')
    (hX : MemLp (X 0) 2 P) (hindep : iIndepFun X P)
    (hident : ∀ (i : ℕ), IdentDistrib (X i) (X 0) P P) :
    TendstoInDistribution
      (fun (n : ℕ) ω ↦ (√n)⁻¹ * (∑ k ∈ Finset.range n, X k ω - n * P[X 0]))
      atTop Y (fun _ ↦ P) P'
```

The ambient variables are `{Ω Ω' : Type*}`, measurable spaces `mΩ` and `mΩ'`, measures `P : Measure Ω` and `P' : Measure Ω'`, a sequence `X : ℕ → Ω → ℝ`, and `Y : Ω' → ℝ`. The theorem is in a context with `[IsProbabilityMeasure P]` and `[IsProbabilityMeasure P']`.

`P[X 0]` is the expectation of `X 0` under `P`. `Var[X 0; P]` is its variance. `MemLp (X 0) 2 P` is the finite-second-moment assumption. `iIndepFun X P` says the whole family is independent, and `IdentDistrib (X i) (X 0) P P` says each variable has the same distribution as `X 0`.

`TendstoInDistribution` states convergence of the laws of the sequence of functions under the measures `fun _ ↦ P` to the law of `Y` under `P'`. Thus `atTop` indexes the sample size tending to infinity; it does not require the random variables to share a sample space with `Y`.

The type of the limit law is written `gaussianReal 0 (Var[X 0; P]).toNNReal`. Gaussian variance is parameterized by a nonnegative real, so the real variance is converted to `ℝ≥0` with `.toNNReal`.

### Proof structure

The proof has three mathematical stages.

1. **Centered, unit-variance case.** `tendstoInDistribution_inv_sqrt_mul_sum` proves convergence to `gaussianReal 0 1`. Independence makes the characteristic function of the sum a product; identical distribution makes every factor the same. The normalized sum therefore has characteristic function $\varphi(t/\sqrt n)^n$.
2. **Positive variance.** A private helper standardizes each variable as $(X_i-\mu)/\sqrt v$, applies the unit-variance theorem, and then rescales the limit by continuity. The relation between the normalized sums is
   $$\frac{1}{\sqrt n}\sum_{k<n}(X_k-\mu)=\sqrt v\left(\frac{1}{\sqrt n}\sum_{k<n}\frac{X_k-\mu}{\sqrt v}\right).$$
3. **Zero variance.** If $v=0$, each variable equals its mean almost everywhere. The normalized centered sums consequently have the point-mass law at zero, which is also `gaussianReal 0 0`. This handles the case without dividing by a zero standard deviation.

### Characteristic-function argument

The key intermediate identity is `charFun_inv_sqrt_mul_sum`:

```lean
lemma charFun_inv_sqrt_mul_sum (hindep : iIndepFun X P)
    (hident : ∀ (i : ℕ), IdentDistrib (X i) (X 0) P P) {n : ℕ} {t : ℝ} :
    charFun (P.map (fun ω ↦ (√n)⁻¹ * ∑ k ∈ Finset.range n, X k ω)) t =
      (charFun (P.map (X 0)) ((√n)⁻¹ * t)) ^ n
```

Here `P.map f` is the distribution of `f` under `P`, and `charFun` is its characteristic function. Independence gives the product formula for the characteristic function of the finite sum; the identical-distribution hypothesis identifies the factors. The scaling by `(√n)⁻¹` changes the argument from `t` to `t / √n`.

For a centered random variable of variance one, the Taylor expansion at zero gives

$$\varphi(u)=1-\frac{u^2}{2}+o(u^2).$$

Putting $u=t/\sqrt n$ yields $\varphi(t/\sqrt n)^n\to e^{-t^2/2}$. The lemma `tendsto_charFun_inv_sqrt_mul_pow` formalizes this limit using the characteristic-function Taylor expansion and a power-limit theorem. The main unit-variance theorem then invokes `ProbabilityMeasure.tendsto_iff_tendsto_charFun`, the characteristic-function criterion for convergence in distribution, and identifies $e^{-t^2/2}$ as the characteristic function of `gaussianReal 0 1`.

## 2. Core notions used by the file

### Independence and identical distribution

The hypotheses concern a sequence of random variables rather than an abstract sequence of probability measures.

- `iIndepFun X P` expresses independence of the family `X` under `P`.
- `IdentDistrib (X i) (X 0) P P` expresses that `X i` and `X 0` have the same pushforward distribution.

Together, these hypotheses are the Lean formulation of an independent, identically distributed sequence.

### Second moment, mean, and variance

`MemLp (X 0) 2 P` ensures the common random variable is square-integrable. Identical distribution transfers this property to every `X i`. The mean and variance are then expressed by the integral notation `P[X 0]` and `Var[X 0; P]`.

The file first proves the theorem under the more concrete moment hypotheses `P[X] = 0` and `P[X ^ 2] = 1`. For a centered variable, the second moment is its variance. The general theorem derives the needed mean and variance facts from `MemLp` and standardizes when variance is positive.

### Law and convergence in distribution

`HasLaw Y μ P'` records that `Y` has distribution `μ` under `P'`. `TendstoInDistribution` expresses convergence of the pushforward probability measures. The unit theorem uses the characteristic-function characterization of this convergence; the general theorem reuses it after affine transformations.

### Gaussian law

`gaussianReal 0 v` is the real Gaussian law with mean zero and variance `v`. The target in the main theorem uses the variance of `X 0`; `gaussianReal` takes a nonnegative variance parameter, hence the conversion to `ℝ≥0`.

## 3. Other public declarations

| Mathematical role | Lean declaration |
| --- | --- |
| Characteristic function of a normalized independent, identically distributed finite sum factors into an nth power | `charFun_inv_sqrt_mul_sum` |
| The characteristic functions of normalized sums converge to the standard Gaussian characteristic function, assuming mean zero and variance one | `tendsto_charFun_inv_sqrt_mul_pow` |
| Central limit theorem for centered variables with variance one | `tendstoInDistribution_inv_sqrt_mul_sum` |
| Main central limit theorem for arbitrary finite-variance real variables, including variance zero | `tendstoInDistribution_inv_sqrt_mul_sum_sub` |

The variance-positive standardization result is declared `private`, so it is an internal proof helper rather than part of the public API.

## 4. Boundary conditions and scope

- **Dimension:** This file proves the real-valued, one-dimensional central limit theorem. 
It does not state a multivariate version.
- **Moment assumption:** The theorem assumes a finite second moment, not higher moments.

## 5. Discussion

The proof follows the classical characteristic-function route. Its API separates the analytic part of the argument (Taylor expansion and the nth-power limit) from the probability part (independence, identical laws, and the characteristic-function criterion). 
It then reuses the normalized theorem to handle arbitrary mean and variance.

Potential task is to prove CLT via other methods.

## 6. References

- Mathlib source at the recorded revision: [CentralLimitTheorem.lean](https://github.com/leanprover-community/mathlib4/blob/f7b0818b53d52ed1c795f727fe5c4c734dc41047/Mathlib/Probability/CentralLimitTheorem.lean).
- [Other method to prove CLT](https://terrytao.wordpress.com/2010/01/05/254a-notes-2-the-central-limit-theorem/)
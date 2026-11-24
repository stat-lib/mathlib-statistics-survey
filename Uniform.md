---
title: Uniform distributions and probability mass functions
source_module: Mathlib.Probability.Distributions.Uniform
source_path: Mathlib/Probability/Distributions/Uniform.lean
mathlib_commit: https://github.com/leanprover-community/mathlib4/blob/0fa18d49e3c34d2b7766fe0cb6016e3bd68cd15a/Mathlib/Probability/Distributions/Uniform.lean
last_update: 2026-08-26
topics:
  - "uniform distributions"
  - "probability mass functions"
---

# Uniform distributions and probability mass functions

Mathlib source: [Uniform distributions and probability mass functions](https://github.com/leanprover-community/mathlib4/blob/0fa18d49e3c34d2b7766fe0cb6016e3bd68cd15a/Mathlib/Probability/Distributions/Uniform.lean)

## 1. Mathematical result and Lean translation

- What is the main theorem or definition?

**Theorem 1.** Given measurable spaces $(\Omega,\mathcal{F})$ and $(E,\mathcal{E})$, measures $P$ on $\Omega$ and $\mu$ on $E$, and a measurable set $s \subseteq E$, suppose that $X:\Omega\to E$ has uniform distribution on $s$ with respect to $\mu$ under $P$. Then $\mathrm{pdf}_{X,P,\mu}(x)=(\mu(s))^{-1}\mathbf{1}_s(x)$ for $\mu$-almost every $x\in E$, where $\mathbf{1}_s$ is the indicator function of $s$ and the arithmetic is interpreted in $[0,\infty]$.

- What is its exact Lean statement?

**Theorem 1 (Lean).** Let $\Omega$ and $E$ be measurable spaces (`[MeasurableSpace Ω] [MeasurableSpace E]`), let $P$ be a measure on $\Omega$ (`{P : Measure Ω}`), and let $\mu$ be a measure on $E$ (`{μ : Measure E}`). Let $X:\Omega\to E$ (`{X : Ω → E}`) and $s\subseteq E$ (`{s : Set E}`). If $s$ is measurable (`hms : MeasurableSet s`) and $X$ has uniform distribution on $s$ with respect to $\mu$ under $P$ (`hu : IsUniform X s P μ`), then the density of $X$ with respect to $\mu$ is $\mu$-almost everywhere equal to the normalized indicator function of $s$ (`pdf X P μ =ᵐ[μ] s.indicator ((μ s)⁻¹ • (1 : E → ℝ≥0∞))`).

```lean
theorem pdf_eq {X : Ω → E} {s : Set E} (hms : MeasurableSet s)
    (hu : IsUniform X s P μ) : pdf X P μ =ᵐ[μ] s.indicator ((μ s)⁻¹ • (1 : E → ℝ≥0∞)) 
```

```lean
Ω  : Type u_1
E  : Type u_2
mΩ : MeasurableSpace Ω
mE : MeasurableSpace E
P  : Measure Ω
μ  : Measure E
X  : Ω → E
s  : Set E
hms : MeasurableSet s
hu  : MeasureTheory.pdf.IsUniform X s P μ
⊢ MeasureTheory.pdf X P μ =ᵐ[μ]
    s.indicator ((μ s)⁻¹ • (1 : E → ℝ≥0∞))
```


- what was the proof

**Proof.**
Write $\nu=P\circ X^{-1}$ and $f=\mathrm{pdf}_{X,P,\mu}$.
By uniformity,

```math
\nu=(\mu(s))^{-1}\mu|_s.
```

Set $g=(\mu(s))^{-1}\mathbf{1}_s$. All arithmetic below is in $[0,\infty]$.

**Case 1: $\mu(s)=\infty$.**
Since $\infty^{-1}=0$,

```math
\nu=0\cdot\mu|_s=0,
\qquad
f=0\quad\mu\text{-a.e.}
```

Also, for every $x\in E$,

```math
g(x)=
\begin{cases}
\infty^{-1}=0, & x\in s,\\
0, & x\notin s.
\end{cases}
```

Thus $f=g$ $\mu$-almost everywhere.

**Case 2: $\mu(s)=0$.**
For every measurable $A\subseteq E$,

```math
0\leq(\mu|_s)(A)=\mu(A\cap s)\leq\mu(s)=0.
```

Hence $\mu|_s=0$. Using $0^{-1}=\infty$ and $\infty\cdot0=0$,

```math
\nu=\infty\cdot0=0,
\qquad
f=0\quad\mu\text{-a.e.}
```

Meanwhile,

```math
g(x)=
\begin{cases}
\infty, & x\in s,\\
0, & x\notin s,
\end{cases}
\qquad
\mu\bigl(\{x:g(x)\neq0\}\bigr)=\mu(s)=0.
```

Therefore $g=0=f$ $\mu$-almost everywhere.

**Case 3: $0<\mu(s)<\infty$.**
The function $g$ is measurable because $s$ is measurable.
For every measurable $A\subseteq E$,

```math
\begin{aligned}
\int_A g(x)\,\mu(dx)
&=(\mu(s))^{-1}\int_A\mathbf{1}_s(x)\,\mu(dx)\\
&=(\mu(s))^{-1}\mu(A\cap s)\\
&=\bigl((\mu(s))^{-1}\mu|_s\bigr)(A)\\
&=\nu(A).
\end{aligned}
```

Thus $g$ is a density of $\nu$ with respect to $\mu$.
By almost-everywhere uniqueness of the density,

```math
f(x)=g(x)=(\mu(s))^{-1}\mathbf{1}_s(x)
\qquad\mu\text{-a.e.}
```

## 2. Core definitions
**Definition 1.** A random variable $X:\Omega\to E$ is uniformly distributed on $s$ with respect to $\mu$ under $P$ if $X$ is $P$-almost everywhere measurable and its distribution satisfies
```math
P\circ X^{-1}=(\mu(s))^{-1}\mu|_s.
```
Under the same almost-everywhere measurability assumption on $X$, this distribution equality is equivalent to the following identity for every measurable set $B\subseteq E$:
```math
P(X^{-1}(B))
=
(\mu(s))^{-1}\mu(s\cap B).
```
```lean
def IsUniform (X : Ω → E) (s : Set E) (P : Measure Ω)
    (μ : Measure E := by volume_tac) :=
  HasLaw X μ[|s] P
```
**Remark 1.** The notation `μ[|s]` denotes the normalized restricted measure $(\mu(s))^{-1}\mu|_s$. In [`Mathlib.Probability.HasLaw`](https://github.com/leanprover-community/mathlib4/blob/0fa18d49e3c34d2b7766fe0cb6016e3bd68cd15a/Mathlib/Probability/HasLaw.lean), `HasLaw X μ P` is defined by two fields (with `X` and `μ` in scope):

```lean
@[fun_prop]
structure HasLaw (P : Measure Ω := by volume_tac) : Prop where
  protected aemeasurable : AEMeasurable X P := by fun_prop
  protected map_eq : P.map X = μ
```

Here the source uses `μ` for the proposed law; in `IsUniform`, that argument is `μ[|s]`. Thus `HasLaw X μ[|s] P` requires both that $X$ is $P$-almost everywhere measurable and that its push-forward measure satisfies
```math
P\circ X^{-1}=(\mu(s))^{-1}\mu|_s.
```
The definition applies to general measurable spaces, with arithmetic interpreted in $[0,\infty]$. It does not itself require $s$ to be measurable or $0<\mu(s)<\infty$. When $0<\mu(s)<\infty$, the normalized measure is a probability measure; when $\mu(s)=0$ or $\mu(s)=\infty$, it is the zero measure. The density theorem `pdf_eq` additionally assumes that $s$ is measurable.

The following definitions construct discrete distributions directly as probability mass functions：`PMF.uniformOfFinset` assigns equal probability to elements of a finite nonempty set and zero outside it; `PMF.uniformOfFintype` assigns equal probability to every element of a finite nonempty type; and `PMF.ofMultiset` assigns each value a probability equal to its number of occurrences divided by the total size of the nonempty multiset.

**Definition 2.** Given a nonempty finite set $s\subseteq\alpha$, the uniform probability mass function on $s$ assigns equal probability to each element of $s$ and zero to every element outside $s$:
```math
p(a)=
\begin{cases}
\dfrac{1}{|s|}, & a\in s,\\
0, & a\notin s.
\end{cases}
```
In the `PMF` namespace, the full definition is:
```lean
def uniformOfFinset (s : Finset α) (hs : s.Nonempty) : PMF α := by
  classical
  refine ofFinset (fun a => if a ∈ s then s.card⁻¹ else 0) s ?_ ?_
  · simp only [Finset.sum_ite_mem, Finset.inter_self, Finset.sum_const, nsmul_eq_mul]
    have : (s.card : ℝ≥0∞) ≠ 0 := by
      simpa only [Ne, Nat.cast_eq_zero, Finset.card_eq_zero] using
        Finset.nonempty_iff_ne_empty.1 hs
    exact ENNReal.mul_inv_cancel this <| ENNReal.natCast_ne_top s.card
  · exact fun x hx => by simp only [hx, ite_false]
```

The `by` block constructs a value of type `PMF α` using tactics; this remains a definition. The two `?_` in the call to `ofFinset` are proof obligations. The first proves that the point probabilities sum to `1`. Here `hs : s.Nonempty` gives `(s.card : ℝ≥0∞) ≠ 0`, while a finite cardinality is not `∞`, so `ENNReal.mul_inv_cancel` yields
```math
\sum_{a\in s}p(a)=|s|\cdot\frac{1}{|s|}=1.
```
The second proves that the point probability is `0` outside `s`: given `hx : x ∉ s`, the `if` expression reduces to `0`. The `classical` tactic supplies the decidability needed to test membership `a ∈ s` for an arbitrary type `α`. Once these obligations are proved, `ofFinset` produces a valid probability mass function. This models drawing one element uniformly from a nonempty finite set: a measurable event $t$ has probability $|s\cap t|/|s|$ (see Section 3). `uniformOfFintype` also reuses this definition with `s = Finset.univ`.

**Definition 3.** Given a finite nonempty type $\alpha$, the uniform probability mass function on $\alpha$ assigns the same probability to every element:
```math
p(a)=\frac{1}{|\alpha|}
\qquad\text{for every }a\in\alpha.
```
```lean
def uniformOfFintype (α : Type*) [Fintype α] [Nonempty α] : PMF α :=
  uniformOfFinset Finset.univ Finset.univ_nonempty
```
Here, `[Fintype α]` specifies that $\alpha$ is finite, and `[Nonempty α]` ensures that $|\alpha|>0$. This definition applies `uniformOfFinset` to `Finset.univ`, the finite set of all elements of $\alpha$.

**Definition 4.** Given a nonempty multiset $s$ of elements of $\alpha$, `ofMultiset` constructs a probability mass function by weighting each value according to its number of occurrences.
In the `PMF` namespace, the full definition is:
```lean
open scoped Classical in
def ofMultiset (s : Multiset α) (hs : s ≠ 0) : PMF α :=
  ⟨fun a => s.count a / (Multiset.card s),
    ENNReal.summable.hasSum_iff.2
      (calc
        (∑' b : α, (s.count b : ℝ≥0∞) / (Multiset.card s))
          = (Multiset.card s : ℝ≥0∞)⁻¹ * ∑' b, (s.count b : ℝ≥0∞) := by
            simp_rw [ENNReal.div_eq_inv_mul, ENNReal.tsum_mul_left]
        _ = (Multiset.card s : ℝ≥0∞)⁻¹ * ∑ b ∈ s.toFinset, (s.count b : ℝ≥0∞) :=
          (congr_arg (fun x => (Multiset.card s : ℝ≥0∞)⁻¹ * x)
            (tsum_eq_sum fun a ha =>
              Nat.cast_eq_zero.2 <| by rwa [Multiset.count_eq_zero, ← Multiset.mem_toFinset]))
        _ = 1 := by
          rw [← Nat.cast_sum, Multiset.toFinset_sum_count_eq s,
            ENNReal.inv_mul_cancel (Nat.cast_ne_zero.2 (hs ∘ Multiset.card_eq_zero.1))
              (ENNReal.natCast_ne_top _)]
        )⟩
```
Here `PMF α` consists of a point-probability function together with a proof that its values sum to `1`. The pair `⟨..., ...⟩` supplies these two components: `fun a => s.count a / (Multiset.card s)` gives the probability of `a`, and `ENNReal.summable.hasSum_iff.2` turns the following calculation into the required summation proof. The `by` blocks inside `calc` justify individual equalities; this declaration remains a definition.

The calculation first factors out `(Multiset.card s)⁻¹`. It then replaces the infinite sum with a finite sum over `s.toFinset`, since values outside the multiset have count `0`. Although `s.toFinset` lists each distinct value only once, `s.count b` retains its multiplicity. Finally, the sum of all counts is `Multiset.card s`; `hs : s ≠ 0` makes this denominator nonzero, so the normalized sum is `1`. This definition models drawing one occurrence uniformly from a nonempty multiset and then observing its value. Repeated values therefore receive more probability: for $s=[a,a,b]$ with $a\neq b$, the probability of $a$ is $2/3$. It also lets us compute a measurable event's probability by counting all occurrences whose values lie in the event (see Section 3).

The public theorem `ofMultiset_apply` exposes the point-probability formula for direct use. In the `PMF` namespace, the source states:
```lean
variable {s : Multiset α} (hs : s ≠ 0)

open scoped Classical in
@[simp]
theorem ofMultiset_apply (a : α) : ofMultiset s hs a = s.count a / (Multiset.card s) :=
  rfl
```
Mathematically, for every $a\in\alpha$,
```math
p_s(a)=\frac{\mathrm{count}_s(a)}{|s|}.
```
Here, $|s|$ counts all occurrences, including duplicates. The assumption `hs : s ≠ 0` ensures that the multiset is nonempty. Values appearing more often receive greater probability. This pointwise formula requires no measurable-event assumption. The proof is `rfl` because the formula follows directly from the definition; `@[simp]` lets Lean use it when simplifying expressions involving `ofMultiset`.

## 3. Other public declarations

- What other mathematical declarations are defined in the file?

| Declaration | Role |
| --- | --- |
| `IsUniform.measure_preimage` | Computes the measure of a measurable event's preimage as the measure of its intersection with the uniform set divided by the measure of that set. |
| `IsUniform.hasPDF` | Establishes that a uniform random variable has a density with respect to the reference measure when the uniform set has finite measure   including zero measure. |
| `IsUniform.pdf_toReal_ae_eq` | Gives the real-valued version of the uniform density formula. |
| `IsUniform.integral_eq` | Expresses the integral of a real uniform random variable as a scaled Lebesgue integral over the set. |
| `IsUniform.cond` | Shows that the identity map is uniformly distributed under the normalized restricted measure. |
| `uniformPDF` | Defines the uniform density independently of a particular random variable. |
| `uniformPDF_eq_pdf` | Identifies `uniformPDF` with the density of any uniform random variable, almost everywhere. |
| `uniformPDF_ite` | Expresses `uniformPDF` as a piecewise function inside and outside the set. |
| `PMF.toMeasure_uniformOfFinset_apply` | Computes a measurable event's probability as the proportion of elements of the finite set that belong to the event. |
| `PMF.toMeasure_uniformOfFintype_apply` | Computes a measurable event's probability as its cardinality divided by the cardinality of the finite type. |
| `PMF.ofMultiset_apply` | Computes the probability of a value as its occurrence count divided by the multiset's total size. |
| `PMF.toMeasure_ofMultiset_apply` | Computes a measurable event's probability by counting occurrences in the multiset, including duplicates. |

- What does each one say mathematically?
- Why is it useful?
- Does its proof or Lean design contain something worth explaining?

### Density formulas and a canonical uniform random variable

#### `IsUniform.pdf_toReal_ae_eq`

**Mathematical statement.** If $s$ is measurable and $X$ is uniformly distributed on $s$, then
```math
\bigl(\mathrm{pdf}_{X,P,\mu}(x)\bigr).\mathrm{toReal}
=
\bigl((\mu(s))^{-1}\mathbf{1}_s(x)\bigr).\mathrm{toReal}
\qquad \mu\text{-a.e.}
```

**Use.** This gives a real-valued density formula for use in real-valued integrals.

**Proof and design.** Apply `ENNReal.toReal` to both sides of `pdf_eq`. This preserves almost-everywhere equality. Note that `toReal` maps $\infty$ to $0$.

#### `uniformPDF`

**Mathematical statement.** This defines the function
```math
g_{s,\mu}(x)=(\mu(s))^{-1}\mathbf{1}_s(x).
```

**Use.** It names a density formula depending only on $s$ and $\mu$, independently of a particular random variable or sample space.

**Design.** The function is defined without assuming that $s$ is measurable or has positive finite measure. Additional conditions are imposed when establishing its properties as a probability density.

#### `uniformPDF_eq_pdf`

**Mathematical statement.** If $s$ is measurable and $X$ is uniformly distributed on $s$, then
```math
g_{s,\mu}(x)=\mathrm{pdf}_{X,P,\mu}(x)
\qquad \mu\text{-a.e.}
```

**Use.** This connects the explicit function `uniformPDF` with the density of a particular random variable.

**Proof and design.** This is `pdf_eq` with the equality reversed and the formula named `uniformPDF`. The equality is almost everywhere because densities need not agree at every point.

#### `uniformPDF_ite`

**Mathematical statement.** For every $x\in E$,
```math
g_{s,\mu}(x)=
\begin{cases}
(\mu(s))^{-1}, & x\in s,\\
0, & x\notin s.
\end{cases}
```

**Use.** This form is convenient for evaluating the function inside and outside $s$.

**Proof and design.** The formula follows directly from the definition of the indicator function. Unlike the equality with `pdf`, it holds at every point.

#### `IsUniform.cond`

**Mathematical statement.** Let $\nu=(\mu(s))^{-1}\mu|_s$. Under $\nu$, the identity map on $E$ is uniformly distributed on $s$ with respect to $\mu$:
```math
\nu\circ\mathrm{id}^{-1}=\nu.
```

**Use.** This gives a canonical realization of the uniform distribution. When $0<\mu(s)<\infty$, $\nu$ is a probability measure.

**Proof and design.** The identity map is measurable and its push-forward leaves the measure unchanged. The result therefore follows from the general identity-map property of `HasLaw`.


### Integral formula

#### `IsUniform.integral_eq`

**Mathematical statement.** Let $X:\Omega\to\mathbb{R}$ be uniformly distributed on $s\subseteq\mathbb{R}$ with respect to Lebesgue measure $\lambda$ under $P$. Then
```math
\int_\Omega X(\omega)\,P(d\omega)
=
\bigl(\lambda(s)^{-1}\bigr).\mathrm{toReal}
\int_s x\,\lambda(dx).
```

**Use.** This reduces integration of $X$ over the sample space to integration of the identity function over $s$. When $0<\lambda(s)<\infty$ and $X$ is integrable, it gives the expectation formula
```math
\mathbb{E}_P[X]
=
\frac{1}{\lambda(s)}\int_s x\,\lambda(dx).
```

**Proof and design.** By uniformity, the distribution of $X$ is the normalized restriction of $\lambda$ to $s$. Changing variables to this distribution and extracting the scaling factor gives
```math
\begin{aligned}
\int_\Omega X(\omega)\,P(d\omega)
&=\int_{\mathbb{R}}x\,(P\circ X^{-1})(dx)\\
&=\int_{\mathbb{R}}x\,d\bigl(\lambda(s)^{-1}\lambda|_s\bigr)\\
&=\bigl(\lambda(s)^{-1}\bigr).\mathrm{toReal}
  \int_s x\,\lambda(dx).
\end{aligned}
```

The theorem has no integrability assumption. Mathlib's Bochner integral is defined to be zero for nonintegrable functions, so this equality alone does not establish the existence of a finite expectation.

### Discrete event probabilities

#### `PMF.toMeasure_uniformOfFinset_apply`

**Mathematical statement.** Let $s$ be a nonempty finite set, and let $t\subseteq\alpha$ be measurable. Under the uniform distribution on $s$,
```math
\Pr(t)=\frac{|\{a\in s:a\in t\}|}{|s|}.
```

**Use.** This computes an event's probability by counting the elements of $s$ that satisfy the event.

**Proof and design.** Each element of $s$ has probability $1/|s|$, so
```math
\Pr(t)
=
\sum_{\substack{a\in s\\a\in t}}\frac{1}{|s|}
=
\frac{|\{a\in s:a\in t\}|}{|s|}.
```
The Lean proof uses the corresponding outer-measure formula. Measurability of $t$ allows the induced measure to be evaluated using that formula.

#### `PMF.toMeasure_uniformOfFintype_apply`

**Mathematical statement.** Let $\alpha$ be a finite nonempty type, and let $s\subseteq\alpha$ be measurable. Under the uniform distribution on $\alpha$,
```math
\Pr(s)=\frac{|s|}{|\alpha|}.
```

**Use.** This gives the usual ratio of favorable outcomes to all outcomes in a finite uniform probability space.

**Proof and design.** This is the finite-set formula applied to the set of all elements of $\alpha$. In Lean, `Fintype.card s` counts the elements of the subtype corresponding to $s$; the declaration includes `[Fintype s]` to provide this finite enumeration.

#### `PMF.toMeasure_ofMultiset_apply`

**Mathematical statement.** Let $s$ be a nonempty multiset, and let $t\subseteq\alpha$ be measurable. Write $s_t$ for the multiset obtained by retaining the occurrences whose values belong to $t$. Then
```math
\Pr(t)
=
\frac{\sum_{a\in\alpha}\mathrm{count}_{s_t}(a)}{|s|}
=
\frac{|s_t|}{|s|}.
```
The first expression corresponds to the sum in the Lean statement; the second is its mathematical simplification. All sizes count occurrences, including duplicates.

**Use.** This computes event probabilities when repeated values carry additional weight. For example, for $s=[a,a,b]$ with $a\neq b$ and measurable $\{a\}$,
```math
\Pr(\{a\})=\frac{2}{3}.
```

**Proof and design.** Summing the point probabilities over the event gives
```math
\begin{aligned}
\Pr(t)
&=\sum_{a\in\alpha}\mathbf{1}_t(a)
  \frac{\mathrm{count}_s(a)}{|s|}\\
&=\frac{\sum_{a\in\alpha}\mathrm{count}_{s_t}(a)}{|s|}.
\end{aligned}
```
The outer-measure proof splits according to whether $a\in t$. The measurable-event formula then follows by identifying the induced measure with the outer measure on $t$.

## 4. Boundary conditions

The theorem `pdf_eq` does not assume $0<\mu(s)<\infty$.
The proof explicitly separates the two degenerate cases.

**Infinite measure.** If $\mu(s)=\infty$, then $(\mu(s))^{-1}=0$.
The normalized restricted measure is zero, and the proposed density
is identically zero. The proof handles this case with:
```lean
  by_cases hnt : μ s = ∞
  · simp [pdf_eq_zero_of_measure_eq_zero_or_top hu (Or.inr hnt), hnt]
```

**Zero measure.** If $\mu(s)=0$, the restricted measure is zero.
The proposed density is infinite on $s$ and zero outside it, but
$s$ is a null set. Thus both densities are zero almost everywhere:
```lean
  by_cases hns : μ s = 0
  · filter_upwards [measure_eq_zero_iff_ae_notMem.mp hns,
      pdf_eq_zero_of_measure_eq_zero_or_top hu (Or.inl hns)] with x hx h'x
    simp [hx, h'x, hns]
```
Here, `hx` states that $x\notin s$, and `h'x` states that the density
is zero. `filter_upwards` makes both facts available almost everywhere.

**Positive finite measure.** In the remaining branch,
`hnt : μ s ≠ ∞` and `hns : μ s ≠ 0`. The proof establishes:
```lean
  have : HasPDF X P μ := hasPDF hnt hu
  have : IsProbabilityMeasure P := isProbabilityMeasure hns hnt hu
```
It then identifies the proposed density with the density of the
distribution. The measurability assumption on $s$ is used, in
particular, to establish the candidate's almost-everywhere measurability:
```lean
  · exact (measurable_one.aemeasurable.const_smul (μ s)⁻¹).indicator hms
```
The assumption `hms` is also used by `withDensity_indicator` to identify the measure with the proposed density as a scaled restriction of $\mu$.


**Empty discrete inputs.** The discrete PMF constructions exclude
empty inputs through `s.Nonempty`, `[Nonempty α]`, or `s ≠ 0`,
ensuring that their cardinality denominators are nonzero.

For `uniformOfFinset`, the assumption `hs : s.Nonempty` is used
to prove that the cardinality is nonzero:
```lean
    have : (s.card : ℝ≥0∞) ≠ 0 := by
      simpa only [Ne, Nat.cast_eq_zero, Finset.card_eq_zero] using
        Finset.nonempty_iff_ne_empty.1 hs
    exact ENNReal.mul_inv_cancel this <| ENNReal.natCast_ne_top s.card
```
This justifies $|s|\cdot |s|^{-1}=1$. The second condition required
for cancellation holds because a natural-number cardinality is finite.

For `uniformOfFintype`, `[Nonempty α]` ensures that `Finset.univ`
is nonempty. The construction therefore reuses `uniformOfFinset`:
```lean
def uniformOfFintype (α : Type*) [Fintype α] [Nonempty α] : PMF α :=
  uniformOfFinset Finset.univ Finset.univ_nonempty
```

For `ofMultiset`, the assumption `hs : s ≠ 0` excludes the empty
multiset. At the end of the normalization proof, the source uses:
```lean
        _ = 1 := by
          rw [← Nat.cast_sum, Multiset.toFinset_sum_count_eq s,
            ENNReal.inv_mul_cancel (Nat.cast_ne_zero.2 (hs ∘ Multiset.card_eq_zero.1))
              (ENNReal.natCast_ne_top _)]
```
The sum of occurrence counts equals the total size of the multiset.
The assumption `hs` makes this size nonzero, allowing cancellation
in $|s|^{-1}\cdot |s|=1$.


## 5. Discussion

The file defines uniform distributions through normalized restricted measures, while its discrete PMF constructions are defined separately. Its TODO proposes deriving these PMFs from a `uniformMeasure` on a `Finset`, `Fintype`, or `Multiset`.

A measure-theoretic interpretation helps explain this connection. For a measurable set $s$ with $0<\mu(s)<\infty$, normalization gives
```math
\nu(A)=\frac{\mu(A\cap s)}{\mu(s)}.
```
Lebesgue measure yields the continuous uniform distribution, while counting measure yields the uniform distribution on a finite nonempty set. For a multiset with $N\geq1$ entries, normalization of the sum of Dirac measures gives
```math
\nu=\frac{1}{N}\sum_{i=1}^{N}\delta_{x_i}.
```
Repeated values contribute repeatedly, explaining the occurrence-based probabilities in `PMF.ofMultiset`.

This interpretation uses the counting measures, sums of measures, and restrictions described by Kallenberg (2021, Chapter 1, pp. 19–20). It clarifies the existing constructions rather than introducing a new mathematical result. A Lean refactor would still need to establish agreement with the existing PMF definitions.

## 6. References

Kallenberg, O. (2021). *Foundations of Modern Probability* (3rd ed.). Probability Theory and Stochastic Modelling, Vol. 99. Springer, Cham. https://doi.org/10.1007/978-3-030-61871-1

Relevant passages: Chapter 1, p. 19 (Dirac measures, counting measures, and Proposition 1.16 on sums of measures); p. 20 (restriction of measures).

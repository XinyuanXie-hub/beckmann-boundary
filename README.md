<!-- Verification narrative adapted from XinyuanXie-hub/Konig-constant, commit 165a31717d8084e6df9a7c8f745059af0e2ed40a, and XinyuanXie-hub/cyclic-lsi-new, commit 4b4ff9a506c0aac696119542b76276238c14cb9b, under Apache-2.0. Setup, verification script, workflow and Pages files derive from XinyuanXie-hub/lean-verification-template, commit a2b0336c176c884d3e7ea3b833b74673b0c2917d. -->

# Beckmann boundary comparison examples

This project uses Lean to verify two comparison examples, Proposition 5.2 and Theorem 5.5, from:

> Paata Ivanisvili, Xinyuan Xie and Haonan Zhang,
> *A Beckmann boundary form of Talagrand's conjecture on the discrete cube*,
> [arXiv:2606.31961v1](https://arxiv.org/abs/2606.31961v1).

## Mathematical statements

Let $`\Omega_n=\{-1,1\}^n`$ carry the uniform probability measure, and write $`\mathbb E g=2^{-n}\sum_{x\in\Omega_n}g(x)`$. Let $`x^{\oplus i}`$ denote the point obtained by flipping coordinate $`i`$ of $`x`$.

For a Boolean function $`f:\Omega_n\to\{-1,1\}`$, define

```math
Lf(x)=\sum_{i=1}^n\frac{f(x)-f(x^{\oplus i})}{2}.
```

For a vector field $`V:\Omega_n\to\mathbb R^n`$, its divergence and cost are

```math
\mathrm{div}\,V(x)=\sum_{i=1}^n\bigl(V_i(x)-V_i(x^{\oplus i})\bigr).
```

```math
\mathcal C(V)=\mathbb E\left(\sum_{i=1}^nV_i(x)^2\right)^{1/2}.
```

The **Beckmann boundary** is

```math
\mathsf B(f)=\inf\{\mathcal C(V):\mathrm{div}\,V=Lf\}.
```

The **positive one-sided boundary** is

```math
\mathsf H_+(f)=\mathbb E\sqrt{h_+(x)}.
```

```math
\begin{aligned}
h_+(x)=\#\{i:\;&f(x)=1,\\
&f(x^{\oplus i})=-1\}.
\end{aligned}
```

An **endpoint allocation** for $`f`$ is a family $`a_i(x)\geq0`$. On a nonsensitive edge, where $`f(x)=f(x^{\oplus i})`$, it satisfies

```math
a_i(x)=0.
```

On a sensitive edge, where $`f(x)\ne f(x^{\oplus i})`$, it satisfies

```math
a_i(x)+a_i(x^{\oplus i})=1.
```

Write $`\mathcal A(f)`$ for the set of such allocations, and let $`\mathcal A_{\mathrm{int}}(f)`$ consist of those satisfying $`a_i(x)\in\{0,1\}`$ for every $`x,i`$. Define the **optimized fractional** and **optimized integral colored boundaries** by

```math
\mathsf T_{\mathrm{frac}}(f)=\inf_{a\in\mathcal A(f)}\mathcal C(a).
```

```math
\mathsf T_{\mathrm{col}}(f)=
\inf_{a\in\mathcal A_{\mathrm{int}}(f)}\mathcal C(a).
```

Assigning every sensitive edge entirely to its positive endpoint gives $`\mathsf H_+(f)`$, the fixed all-red coloring. The two optimized boundaries instead minimize over all admissible allocations.

<a name="theorem-1"></a>

**Theorem 1 (fixed one-sided comparison).** For every integer $`n\geq1`$, let $`o=(-1,\ldots,-1)`$ and define $`f_n(o)=-1`$ and $`f_n(x)=1`$ for $`x\ne o`$. Then

```math
\mathsf B(f_n)=\frac{\sqrt n}{2^n}.
```

```math
\mathsf H_+(f_n)=\frac{n}{2^n}.
```

```math
\frac{\mathsf H_+(f_n)}{\mathsf B(f_n)}=\sqrt n.
```

<a name="theorem-2"></a>

**Theorem 2 (optimized coloring comparison).** For every integer $`k\geq1`$, set

```math
n_k=\frac{2^{k+2}(4^k-1)}{3}.
```

There exists a Boolean function $`f:\Omega_{n_k}\to\{-1,1\}`$ such that $`\mathsf B(f)>0`$ and

```math
\frac{\mathsf T_{\mathrm{frac}}(f)}{\mathsf B(f)}
\geq\frac{3}{4\sqrt6}\sqrt k.
```

```math
\frac{\mathsf T_{\mathrm{col}}(f)}{\mathsf B(f)}
\geq\frac{3}{4\sqrt6}\sqrt k.
```

The formal statement is this exact existence assertion. Since $`\log n_k\leq2k\log8`$ for $`k\geq1`$, its lower bounds give a $`\sqrt{\log n_k}`$ separation along these dimensions. This interpretation is not a separate formalized theorem or a claim of an optimal rate.

Lean encodes $`-1,+1`$ by `false,true`. The two theorem targets in [comparator.json](comparator.json) are `BeckmannExamples.proposition_5_2` and `BeckmannExamples.theorem_5_5`.

## Verification

To verify the correctness of the theorems in Lean, one only needs to check that the statements and definitions in [Challenge.lean](Challenge.lean) match [Theorem 1](#theorem-1) and [Theorem 2](#theorem-2) stated above, and confirm that `lake comparator` succeeds.

The results of `lake comparator` can be checked through the GitHub workflow provided by this project as follows:

1. Sign in to GitHub, open the “Actions” tab, then open the first workflow run listed there, or open it directly from [here](https://xinyuanxie-hub.github.io/beckmann-boundary/latest-run/).
2. Click “Verify the Challenge against Solution”, then expand “Run Comparator with Lean, NanoDa, and con-ron”.
3. Check that the log reports acceptance by con-ron, NanoDa, and Lean, followed by `Your solution is okay!`.

Note: Here, we use the [“gold standard”](https://lean-lang.org/doc/reference/latest/ValidatingProofs/#validating-comparator) for validating proofs in Lean, and we refer readers to [“Challenges and External Checkers”](https://lean-lang.org/doc/reference/latest/Build-Tools-and-Distribution/Lake/#lake-comparator) for details on how it works.

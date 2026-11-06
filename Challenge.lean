import Mathlib

/-!
Stage 1 only: arXiv:2606.31961v1, §§2.1–2.2, 5.2 and 5.4.
`false`/`true` encode -1/+1. Expectations are uniform on the cube.
Endpoint allocations encode an undirected fractional coloring without edge quotients:
on each sensitive edge the two nonnegative endpoint shares sum to one.
The integral restriction assigns the whole edge to exactly one endpoint.
-/
namespace BeckmannExamples

abbrev Cube (n : ℕ) := Fin n → Bool

def flip {n : ℕ} (x : Cube n) (i : Fin n) : Cube n :=
  Function.update x i (!x i)

noncomputable def avg {n : ℕ} (g : Cube n → ℝ) : ℝ :=
  (∑ x, g x) / (2 : ℝ) ^ n

def sign {n : ℕ} (f : Cube n → Bool) (x : Cube n) : ℝ :=
  if f x then 1 else -1

noncomputable def cost {n : ℕ} (V : Cube n → Fin n → ℝ) : ℝ :=
  avg fun x => Real.sqrt (∑ i, (V x i) ^ 2)

/-- §2.2, (8)–(9): unrestricted fields, with div V = Lf (no extra factor 2). -/
noncomputable def beckmann {n : ℕ} (f : Cube n → Bool) : ℝ :=
  sInf {t | ∃ V : Cube n → Fin n → ℝ, cost V = t ∧
    ∀ x, (∑ i, (V x i - V (flip x i) i)) =
      ∑ i, (sign f x - sign f (flip x i)) / 2}

/-- Fixed positive-side boundary: E sqrt(h_{f=1}), i.e. all-red coloring. -/
noncomputable def oneSided {n : ℕ} (f : Cube n → Bool) : ℝ :=
  avg fun x => Real.sqrt (∑ i : Fin n,
    if f x = true ∧ f (flip x i) = false then (1 : ℝ) else 0)

/-- Insensitive edges carry no mass; each sensitive edge has total share one. -/
def Allocation {n : ℕ} (f : Cube n → Bool) (a : Cube n → Fin n → ℝ) : Prop :=
  ∀ x i, 0 ≤ a x i ∧
    (if f x = f (flip x i) then a x i = 0
     else a x i + a (flip x i) i = 1)

/-- §2.1: optimized fractional coloring, with squared endpoint shares. -/
noncomputable def fractional {n : ℕ} (f : Cube n → Bool) : ℝ :=
  sInf {t | ∃ a, Allocation f a ∧ cost a = t}

/-- §2.1: optimized integral coloring, not a fixed one-sided boundary. -/
noncomputable def colored {n : ℕ} (f : Cube n → Bool) : ℝ :=
  sInf {t | ∃ a, Allocation f a ∧ (∀ x i, a x i = 0 ∨ a x i = 1) ∧ cost a = t}

/-- §5.2: negative only at o = (-1,...,-1). -/
def singletonComplement (n : ℕ) (x : Cube n) : Bool :=
  decide (∃ i, x i = true)

/-- Proposition 5.2: exact values and the fixed one-sided sqrt(n) ratio. -/
theorem proposition_5_2 (n : ℕ) (hn : 1 ≤ n) :
    beckmann (singletonComplement n) = Real.sqrt n / (2 : ℝ) ^ n ∧
    oneSided (singletonComplement n) = (n : ℝ) / (2 : ℝ) ^ n ∧
    oneSided (singletonComplement n) / beckmann (singletonComplement n) =
      Real.sqrt n := by
  sorry

/-- §5.4: the exact sequence of cube dimensions in Theorem 5.5. -/
def dimension (k : ℕ) : ℕ := 2 ^ (k + 2) * (4 ^ k - 1) / 3

/-- Theorem 5.5, (27) and its integral-coloring consequence.
The existential formulation is the statement in the paper; its explicit quotient
construction belongs to the proof. Positivity makes the displayed ratios meaningful.
Since log(n_k) ≤ 2k log(8) for k ≥ 1, these imply sqrt(log n_k) separation.
-/
theorem theorem_5_5 (k : ℕ) (hk : 1 ≤ k) :
    ∃ f : Cube (dimension k) → Bool,
      0 < beckmann f ∧
      (3 / (4 * Real.sqrt 6)) * Real.sqrt k ≤ fractional f / beckmann f ∧
      (3 / (4 * Real.sqrt 6)) * Real.sqrt k ≤ colored f / beckmann f := by
  sorry

end BeckmannExamples

import Mathlib

/-! Complete proofs of the two approved Beckmann comparison examples.
The challenge and comparator targets are unchanged. Supporting lemmas are
assembled below in dependency order; no Challenge import is used. -/


/- Supporting component: Defs -/
/-!
Definitions matching the approved challenge: arXiv:2606.31961v1, §§2.1–2.2, 5.2 and 5.4.
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

/-- §5.4: the exact sequence of cube dimensions in Theorem 5.5. -/
def dimension (k : ℕ) : ℕ := 2 ^ (k + 2) * (4 ^ k - 1) / 3


end BeckmannExamples


/- Supporting component: Singleton -/
namespace BeckmannExamples
open Finset

private abbrev Singleton_origin (n : ℕ) : Cube n := fun _ => false

private theorem Singleton_singleton_false {n : ℕ} (x : Cube n) :
    singletonComplement n x = false ↔ x = Singleton_origin n := by
  simp only [singletonComplement, decide_eq_false_iff_not, not_exists]
  constructor
  · intro h
    funext i
    simpa using h i
  · intro h i
    simp [h]

private theorem Singleton_singleton_sign {n : ℕ} (x : Cube n) :
    sign (singletonComplement n) x = if x = Singleton_origin n then -1 else 1 := by
  unfold sign
  by_cases h : x = Singleton_origin n
  · simp [h, singletonComplement, Singleton_origin]
  · have hf : singletonComplement n x = true := by
      cases hf : singletonComplement n x
      · exact False.elim (h ((Singleton_singleton_false x).mp hf))
      · rfl
    simp [h, hf]

private theorem Singleton_flip_flip {n : ℕ} (x : Cube n) (i : Fin n) :
    flip (flip x i) i = x := by
  ext j
  by_cases h : j = i
  · subst j; simp [flip]
  · simp [flip, h]

private theorem Singleton_flip_origin_ne {n : ℕ} (i : Fin n) :
    flip (Singleton_origin n) i ≠ Singleton_origin n := by
  intro h
  have := congrFun h i
  simp [flip, Singleton_origin] at this

private theorem Singleton_flip_eq_origin {n : ℕ} (x : Cube n) (i : Fin n) :
    flip x i = Singleton_origin n ↔ x = flip (Singleton_origin n) i := by
  constructor
  · intro h
    rw [← h, Singleton_flip_flip]
  · intro h
    rw [h, Singleton_flip_flip]

private theorem Singleton_flip_origin_injective {n : ℕ} :
    Function.Injective (fun i : Fin n => flip (Singleton_origin n) i) := by
  intro i j h
  by_contra hij
  have := congrFun h i
  simp [flip, Singleton_origin, hij] at this

private noncomputable def Singleton_singletonField (n : ℕ) : Cube n → Fin n → ℝ :=
  fun x _ => if x = Singleton_origin n then -1 else 0

private theorem Singleton_singletonField_div {n : ℕ} (x : Cube n) :
    (∑ i, (Singleton_singletonField n x i - Singleton_singletonField n (flip x i) i)) =
      ∑ i, (sign (singletonComplement n) x -
        sign (singletonComplement n) (flip x i)) / 2 := by
  apply Finset.sum_congr rfl
  intro i _
  simp only [Singleton_singletonField, Singleton_singleton_sign]
  split_ifs <;> norm_num

private theorem Singleton_singletonField_cost (n : ℕ) :
    cost (Singleton_singletonField n) = Real.sqrt n / (2 : ℝ)^n := by
  unfold cost avg
  congr 1
  have hp (x : Cube n) :
      Real.sqrt (∑ i, Singleton_singletonField n x i ^ 2) =
        if x = Singleton_origin n then Real.sqrt n else 0 := by
    by_cases h : x = Singleton_origin n <;> simp [Singleton_singletonField, h]
  simp_rw [hp]
  simp

private theorem Singleton_singleton_boundary (n : ℕ) :
    oneSided (singletonComplement n) = (n : ℝ) / (2 : ℝ)^n := by
  unfold oneSided avg
  congr 1
  have hi (x : Cube n) (i : Fin n) :
      (singletonComplement n x = true ∧ singletonComplement n (flip x i) = false) ↔
        x = flip (Singleton_origin n) i := by
    rw [Singleton_singleton_false, Singleton_flip_eq_origin]
    constructor
    · exact And.right
    · intro h
      refine ⟨?_, h⟩
      cases hf : singletonComplement n x
      · have he := (Singleton_singleton_false x).mp hf
        exact False.elim (Singleton_flip_origin_ne i (h.symm.trans he))
      · rfl
  simp_rw [hi]
  have hroot (x : Cube n) :
      Real.sqrt (∑ i : Fin n, if x = flip (Singleton_origin n) i then (1 : ℝ) else 0) =
        ∑ i : Fin n, if x = flip (Singleton_origin n) i then (1 : ℝ) else 0 := by
    by_cases h : ∃ i, x = flip (Singleton_origin n) i
    · obtain ⟨i, rfl⟩ := h
      have he (j : Fin n) : flip (Singleton_origin n) i = flip (Singleton_origin n) j ↔ j = i := by
        rw [Singleton_flip_origin_injective.eq_iff, eq_comm]
      simp only [he]
      simp
    · push Not at h
      simp [h]
  simp_rw [hroot]
  rw [Finset.sum_comm]
  simp

private noncomputable def Singleton_weight {n : ℕ} (x : Cube n) : ℝ :=
  ∑ i, if x i then 1 else 0

private theorem Singleton_weight_flip {n : ℕ} (x : Cube n) (i : Fin n) :
    Singleton_weight x - Singleton_weight (flip x i) = if x i then 1 else -1 := by
  unfold Singleton_weight
  rw [← Finset.sum_sub_distrib]
  calc
    _ = ∑ j : Fin n, if j = i then (if x i then (1 : ℝ) else -1) else 0 := by
      apply Finset.sum_congr rfl
      intro j _
      by_cases h : j = i
      · subst j; cases hx : x i <;> simp [flip, hx]
      · simp [flip, h]
    _ = _ := by simp

private theorem Singleton_summation_parts {n : ℕ} (φ : Cube n → ℝ)
    (V : Cube n → Fin n → ℝ) :
    (∑ x, φ x * ∑ i, (V x i - V (flip x i) i)) =
      ∑ x, ∑ i, (φ x - φ (flip x i)) * V x i := by
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm, Finset.sum_comm (f := fun x i => (φ x - φ (flip x i)) * V x i)]
  apply Finset.sum_congr rfl
  intro i _
  simp_rw [mul_sub, sub_mul, Finset.sum_sub_distrib]
  congr 1
  apply Fintype.sum_bijective (fun x : Cube n => flip x i)
    (Function.Involutive.bijective (fun x => Singleton_flip_flip x i))
  intro x
  simp [Singleton_flip_flip]

private theorem Singleton_singleton_charge (n : ℕ) :
    (∑ x : Cube n, Singleton_weight x * ∑ i,
      (sign (singletonComplement n) x - sign (singletonComplement n) (flip x i)) / 2) =
      (n : ℝ) := by
  simp_rw [← Singleton_singletonField_div]
  rw [Singleton_summation_parts]
  have hx (x : Cube n) :
      (∑ i, (Singleton_weight x - Singleton_weight (flip x i)) * Singleton_singletonField n x i) =
        if x = Singleton_origin n then (n : ℝ) else 0 := by
    by_cases h : x = Singleton_origin n
    · subst x
      simp [Singleton_weight_flip, Singleton_singletonField, Singleton_origin]
    · simp [Singleton_singletonField, h]
  simp_rw [hx]
  simp

private theorem Singleton_singleton_cost_lower {n : ℕ} (hn : 1 ≤ n)
    (V : Cube n → Fin n → ℝ)
    (hV : ∀ x, (∑ i, (V x i - V (flip x i) i)) =
      ∑ i, (sign (singletonComplement n) x - sign (singletonComplement n) (flip x i)) / 2) :
    Real.sqrt n / (2 : ℝ)^n ≤ cost V := by
  have hCS (x : Cube n) :
      (∑ i, (Singleton_weight x - Singleton_weight (flip x i)) * V x i) ≤
        Real.sqrt n * Real.sqrt (∑ i, V x i ^ 2) := by
    have h := Real.sum_mul_le_sqrt_mul_sqrt Finset.univ
      (fun i => Singleton_weight x - Singleton_weight (flip x i)) (V x)
    have he : (∑ i : Fin n, (Singleton_weight x - Singleton_weight (flip x i)) ^ 2) = (n : ℝ) := by
      simp_rw [Singleton_weight_flip]
      have hi (i : Fin n) : (if x i then (1 : ℝ) else -1)^2 = 1 := by
        cases x i <;> norm_num
      simp_rw [hi]
      simp
    simpa only [he] using h
  have hsum := Finset.sum_le_sum (fun x (_ : x ∈ (Finset.univ : Finset (Cube n))) => hCS x)
  rw [← Singleton_summation_parts] at hsum
  simp_rw [hV] at hsum
  rw [Singleton_singleton_charge, ← Finset.mul_sum] at hsum
  have hn0 : 0 < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
  have hs : 0 < Real.sqrt n := Real.sqrt_pos.2 hn0
  have hs2 := Real.sq_sqrt hn0.le
  have hsum' : Real.sqrt n ≤ ∑ x, Real.sqrt (∑ i, V x i ^ 2) := by
    nlinarith
  exact div_le_div_of_nonneg_right hsum' (by positivity)

private theorem Singleton_singleton_beckmann (n : ℕ) (hn : 1 ≤ n) :
    beckmann (singletonComplement n) = Real.sqrt n / (2 : ℝ)^n := by
  apply le_antisymm
  · apply csInf_le
    · refine ⟨0, ?_⟩
      rintro t ⟨V, rfl, _⟩
      unfold cost avg
      positivity
    · exact ⟨Singleton_singletonField n, Singleton_singletonField_cost n, Singleton_singletonField_div⟩
  · apply le_csInf
    · exact ⟨cost (Singleton_singletonField n), Singleton_singletonField n, rfl, Singleton_singletonField_div⟩
    · rintro t ⟨V, rfl, hV⟩
      exact Singleton_singleton_cost_lower hn V hV

theorem proposition_5_2 (n : ℕ) (hn : 1 ≤ n) :
    beckmann (singletonComplement n) = Real.sqrt n / (2 : ℝ) ^ n ∧
    oneSided (singletonComplement n) = (n : ℝ) / (2 : ℝ) ^ n ∧
    oneSided (singletonComplement n) / beckmann (singletonComplement n) =
      Real.sqrt n := by
  refine ⟨Singleton_singleton_beckmann n hn, Singleton_singleton_boundary n, ?_⟩
  rw [Singleton_singleton_beckmann n hn, Singleton_singleton_boundary n]
  have hn0 : 0 < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
  have hs : Real.sqrt n ≠ 0 := ne_of_gt (Real.sqrt_pos.2 hn0)
  have hp : (2 : ℝ)^n ≠ 0 := by positivity
  field_simp
  nlinarith [Real.sq_sqrt hn0.le]

end BeckmannExamples


/- Supporting component: Quotient -/
namespace BeckmannExamples
namespace Quotient

abbrev Group (k : ℕ) := Fin k → ZMod 2

/-- Linear quotient encoded on Boolean source coordinates. -/
def projection {n k : ℕ} (label : Fin n → Group k) (x : Cube n) : Group k :=
  ∑ i, if x i then label i else 0

lemma projection_flip {n k : ℕ} (label : Fin n → Group k) (x : Cube n)
    (i : Fin n) : projection label (flip x i) = projection label x + label i := by
  classical
  unfold projection
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i),
    ← Finset.add_sum_erase _ _ (Finset.mem_univ i)]
  have h : (∑ j ∈ Finset.univ.erase i, if flip x i j then label j else 0) =
      ∑ j ∈ Finset.univ.erase i, if x j then label j else 0 := by
    apply Finset.sum_congr rfl
    intro j hj
    have hji : j ≠ i := by simpa using (Finset.mem_erase.mp hj).1
    simp [flip, Function.update_of_ne hji]
  rw [h]
  simp only [flip, Function.update_self]
  cases hx : x i
  · simp only [Bool.not_false, Bool.false_eq_true, ↓reduceIte, zero_add]
    exact add_comm _ _
  · simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]
    ext j
    simp only [Pi.add_apply]
    have hz : label i j + label i j = 0 := by
      have hh : (2 : ZMod 2) = 0 := ZMod.natCast_self 2
      calc
        label i j + label i j = 2 * label i j := by ring
        _ = 0 := by rw [hh, zero_mul]
    simp only [Pi.zero_apply, zero_add]
    linear_combination -hz

/-- One-based first nonzero position, with k+1 at zero. -/
noncomputable def level {k : ℕ} (z : Group k) : ℕ :=
  if h : ∃ i, z i ≠ 0 then ((Finset.univ.filter (fun i => z i ≠ 0)).min' (by
    obtain ⟨i, hi⟩ := h
    exact ⟨i, by simp [hi]⟩)).val + 1 else k + 1

noncomputable def multiplicity {k : ℕ} (a : Group k) : ℕ := 8 ^ level a

noncomputable def alternating {k : ℕ} (z : Group k) : Bool :=
  decide (Even (level z))

abbrev Nonzero (k : ℕ) := {a : Group k // a ≠ 0}
noncomputable abbrev Coordinate (k : ℕ) := (a : Nonzero k) × Fin (multiplicity a.val)

/-- The coordinate label used by the paper's quotient-cube construction. -/
noncomputable def coordinateLabel {k : ℕ} (i : Coordinate k) : Group k := i.1.val

lemma level_zero (k : ℕ) : level (0 : Group k) = k + 1 := by
  simp [level]

noncomputable instance coordinateFintype (k : ℕ) : Fintype (Coordinate k) :=
  by
    classical
    exact inferInstanceAs (Fintype ((a : Nonzero k) × Fin (multiplicity a.val)))

noncomputable def canonicalLabel (k : ℕ) : Fin (Fintype.card (Coordinate k)) → Group k :=
  fun i => coordinateLabel ((Fintype.equivFin (Coordinate k)).symm i)

noncomputable def exampleFunction (k : ℕ) : Cube (Fintype.card (Coordinate k)) → Bool :=
  fun x => alternating (projection (canonicalLabel k) x)

lemma canonicalLabel_ne_zero (k : ℕ) (i : Fin (Fintype.card (Coordinate k))) :
    canonicalLabel k i ≠ 0 :=
  ((Fintype.equivFin (Coordinate k)).symm i).1.property

noncomputable def levelMass (k r : ℕ) : ℝ :=
  if r ≤ k then (2 : ℝ) ^ (k - r) else 1

noncomputable def packingLambda (k r : ℕ) : ℝ :=
  1 / Real.sqrt (3 * levelMass k (r + 1) * (8 : ℝ) ^ r)

lemma canonicalLabel_covers (k : ℕ) (a : Group k) (ha : a ≠ 0) :
    ∃ i, canonicalLabel k i = a := by
  let j : Coordinate k := ⟨⟨a, ha⟩, ⟨0, by unfold multiplicity; positivity⟩⟩
  refine ⟨Fintype.equivFin (Coordinate k) j, ?_⟩
  simp [canonicalLabel, coordinateLabel, j]

lemma sum_canonicalLabel (k : ℕ) (g : Group k → ℝ) :
    (∑ i, g (canonicalLabel k i)) =
      ∑ a : Nonzero k, (multiplicity a.val : ℝ) * g a.val := by
  classical
  have h := Equiv.sum_comp (Fintype.equivFin (Coordinate k)).symm
    (fun j : Coordinate k => g j.1.val)
  simp only [canonicalLabel, coordinateLabel]
  rw [h]
  change (∑ i : (a : Nonzero k) × Fin (multiplicity a.val), g i.1.val) = _
  rw [Fintype.sum_sigma]
  simp

/-- A symmetric packing weight, supported on adjacent quotient levels. -/
noncomputable def selectedWeight {k : ℕ} (z y : Group k) : ℝ :=
  let r := min (level z) (level y)
  if max (level z) (level y) = r + 1 then
    packingLambda k r
  else 0

lemma selectedWeight_symm {k : ℕ} (z y : Group k) :
    selectedWeight z y = selectedWeight y z := by
  simp only [selectedWeight, min_comm, max_comm]

lemma selectedWeight_nonneg {k : ℕ} (z y : Group k) :
    0 ≤ selectedWeight z y := by
  unfold selectedWeight
  dsimp only
  split
  · unfold packingLambda; positivity
  · positivity

end Quotient
end BeckmannExamples


/- Supporting component: Levels -/
namespace BeckmannExamples.Quotient

lemma level_eq_of_first {k : ℕ} (z : Group k) (r : Fin k)
    (hr : z r ≠ 0) (hprev : ∀ i : Fin k, i < r → z i = 0) :
    level z = r.val + 1 := by
  classical
  unfold level
  split
  · congr 1
    apply congrArg Fin.val
    apply le_antisymm
    · apply Finset.min'_le
      simp [hr]
    · apply le_of_not_gt
      intro h
      have hm := Finset.min'_mem (Finset.univ.filter fun i => z i ≠ 0) (by
        exact ⟨r, by simp [hr]⟩)
      have hn : z ((Finset.univ.filter fun i => z i ≠ 0).min' (by exact ⟨r, by simp [hr]⟩)) ≠ 0 := by
        simpa using hm
      exact hn (hprev _ h)
  · rename_i h
    exact False.elim (h ⟨r, hr⟩)

lemma level_eq_iff {k : ℕ} (z : Group k) (r : Fin k) :
    level z = r.val + 1 ↔ z r ≠ 0 ∧ ∀ i : Fin k, i < r → z i = 0 := by
  classical
  constructor
  · intro h
    unfold level at h
    split at h
    · rename_i hex
      let s := Finset.univ.filter fun i => z i ≠ 0
      have hs : s.Nonempty := by obtain ⟨i, hi⟩ := hex; exact ⟨i, by simp [s, hi]⟩
      have he : s.min' hs = r := Fin.ext (by simpa using h)
      constructor
      · have hm := Finset.min'_mem s hs
        rw [he] at hm
        simpa [s] using hm
      · intro i hi
        by_contra hne
        have hle : s.min' hs ≤ i := Finset.min'_le _ _ (by simp [s, hne])
        rw [he] at hle
        exact (not_le_of_gt hi) hle
    · omega
  · rintro ⟨hr, hp⟩
    exact level_eq_of_first z r hr hp

lemma level_eq_last_iff {k : ℕ} (z : Group k) : level z = k + 1 ↔ z = 0 := by
  classical
  constructor
  · intro h
    unfold level at h
    split at h
    · rename_i hex
      have hs : (Finset.univ.filter fun i => z i ≠ 0).Nonempty := by
        obtain ⟨i, hi⟩ := hex; exact ⟨i, by simp [hi]⟩
      have hm : ((Finset.univ.filter fun i => z i ≠ 0).min' hs).val < k := Fin.isLt _
      omega
    · rename_i hz
      ext i
      exact not_not.mp (fun hi => hz ⟨i, hi⟩)
  · rintro rfl
    exact level_zero k

lemma level_bounds {k : ℕ} (z : Group k) : 1 ≤ level z ∧ level z ≤ k + 1 := by
  classical
  unfold level
  split
  · rename_i hex
    have hs : (Finset.univ.filter fun i => z i ≠ 0).Nonempty := by
      obtain ⟨i, hi⟩ := hex; exact ⟨i, by simp [hi]⟩
    have hm : ((Finset.univ.filter fun i => z i ≠ 0).min' hs).val < k := Fin.isLt _
    omega
  · omega

lemma level_add_of_lt {k : ℕ} (y z : Group k) (h : level y < level z) :
    level (y + z) = level y := by
  classical
  have hy : y ≠ 0 := by intro he; rw [he, level_zero] at h; have := (level_bounds z).2; omega
  have hex : ∃ i, y i ≠ 0 := by by_contra he; apply hy; ext i; simpa using not_exists.mp he i
  let r : Fin k := (Finset.univ.filter fun i => y i ≠ 0).min' (by
    obtain ⟨i, hi⟩ := hex; exact ⟨i, by simp [hi]⟩)
  have hr : level y = r.val + 1 := by simp [level, hex, r]
  have hyr := (level_eq_iff y r).mp hr
  have hzpre : ∀ i : Fin k, i ≤ r → z i = 0 := by
    intro i hi
    by_contra hne
    have hz : level z ≤ i.val + 1 := by
      unfold level
      split
      · have hmin := Finset.min'_le (Finset.univ.filter fun j => z j ≠ 0) i (by simp [hne])
        exact Nat.add_le_add_right hmin 1
      · rename_i he
        exact False.elim (he ⟨i, hne⟩)
    have hh : i.val ≤ r.val := hi
    omega
  rw [hr]
  apply level_eq_of_first
  · simpa [hzpre r le_rfl] using hyr.1
  · intro i hi
    simp [hyr.2 i hi, hzpre i (le_of_lt hi)]

lemma zmod_two_ne_zero_iff (a : ZMod 2) : a ≠ 0 ↔ a = 1 := by
  constructor
  · intro h
    apply ZMod.val_injective 2
    have hz : a.val ≠ 0 := fun he => h ((ZMod.val_eq_zero a).mp he)
    have hv := ZMod.val_lt a
    norm_num [ZMod.val_one_eq_one_mod]
    omega
  · rintro rfl
    exact one_ne_zero

lemma card_level {k : ℕ} (r : Fin k) :
    (Finset.univ.filter fun z : Group k => level z = r.val + 1).card =
      2 ^ (k - r.val - 1) := by
  classical
  let t : Fin k → Finset (ZMod 2) := fun i =>
    if i < r then {0} else if i = r then {1} else Finset.univ
  have hset : (Finset.univ.filter fun z : Group k => level z = r.val + 1) =
      Fintype.piFinset t := by
    ext z
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Fintype.mem_piFinset]
    rw [level_eq_iff]
    constructor
    · rintro ⟨hr, hp⟩ i
      dsimp [t]
      split
      · simp [hp i ‹i < r›]
      · split
        · rename_i he; subst i
          simpa using (zmod_two_ne_zero_iff _).mp hr
        · simp
    · intro hz
      constructor
      · have hh := hz r
        simpa [t, zmod_two_ne_zero_iff] using hh
      · intro i hi
        have hh := hz i
        simpa [t, hi] using hh
  rw [hset, Fintype.card_piFinset]
  have ht : ∀ i : Fin k, (t i).card = if r < i then 2 else 1 := by
    intro i
    dsimp [t]
    split_ifs <;> simp_all [ZMod.card] <;> omega
  simp_rw [ht]
  rw [← Finset.prod_filter]
  have hf : (Finset.univ.filter fun i : Fin k => r < i) = Finset.Ioi r := by
    ext i; simp
  rw [hf]
  simp only [Finset.prod_const, Fin.card_Ioi]
  congr 1
  omega

lemma level_add_of_ne {k : ℕ} (y z : Group k) (h : level y ≠ level z) :
    level (y+z) = min (level y) (level z) := by
  rcases lt_or_gt_of_ne h with hlt | hgt
  · rw [level_add_of_lt y z hlt, min_eq_left (le_of_lt hlt)]
  · rw [add_comm, level_add_of_lt z y hgt, min_eq_right (le_of_lt hgt)]

lemma group_add_self {k : ℕ} (z : Group k) : z+z = 0 := by
  ext i
  change z i + z i = (0 : ZMod 2)
  have htwo : (2 : ZMod 2) = 0 := ZMod.natCast_self 2
  calc
    z i + z i = 2 * z i := by ring
    _ = 0 := by rw [htwo, zero_mul]

lemma level_label_of_distinct {k : ℕ} (z a : Group k)
    (h : level z ≠ level (z+a)) : level a = min (level z) (level (z+a)) := by
  have he : z+(z+a) = a := by rw [← add_assoc, group_add_self, zero_add]
  calc
    level a = level (z+(z+a)) := congrArg level he.symm
    _ = _ := level_add_of_ne z (z+a) h

end BeckmannExamples.Quotient


/- Supporting component: Positivity -/
namespace BeckmannExamples

lemma component_le_total {n : ℕ} (V : Cube n → Fin n → ℝ) (x : Cube n) (i : Fin n) :
    |V x i| ≤ ∑ y, Real.sqrt (∑ j, (V y j)^2) := by
  have h1 : (V x i)^2 ≤ ∑ j, (V x j)^2 :=
    Finset.single_le_sum (fun j _ => sq_nonneg (V x j)) (Finset.mem_univ i)
  have h2 : |V x i| ≤ Real.sqrt (∑ j, (V x j)^2) := by
    calc
      |V x i| = Real.sqrt ((V x i)^2) := (Real.sqrt_sq_eq_abs _).symm
      _ ≤ _ := Real.sqrt_le_sqrt h1
  exact h2.trans (Finset.single_le_sum (fun y _ => Real.sqrt_nonneg (∑ j, (V y j)^2)) (Finset.mem_univ x))

lemma charge_le_cost {n : ℕ} (V : Cube n → Fin n → ℝ) (x : Cube n) :
    |∑ i, (V x i - V (flip x i) i)| ≤ (2 * n * (2:ℝ)^n) * cost V := by
  have hp : (2:ℝ)^n ≠ 0 := by positivity
  have h : |∑ i, (V x i - V (flip x i) i)| ≤
      ∑ _i : Fin n, (2 * ∑ y, Real.sqrt (∑ j, (V y j)^2)) := by
    calc
      _ ≤ ∑ i, |V x i - V (flip x i) i| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ _ := Finset.sum_le_sum fun i _ => (abs_sub _ _).trans (by
        have h1 := component_le_total V x i
        have h2 := component_le_total V (flip x i) i
        linarith)
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at h
  unfold cost avg
  convert h using 1 <;> field_simp <;> ring

lemma sign_diff_nonneg {n : ℕ} (f : Cube n → Bool) (x : Cube n) (h : f x = true)
    (j : Fin n) : 0 ≤ (sign f x - sign f (flip x j)) / 2 := by
  simp only [sign, h, Bool.true_eq, ↓reduceIte]
  split <;> norm_num

lemma positive_charge {n : ℕ} (f : Cube n → Bool) (x : Cube n) (i : Fin n)
    (h : f x ≠ f (flip x i)) :
    1 ≤ |∑ j, (sign f x - sign f (flip x j)) / 2| := by
  cases hx : f x with
  | true =>
    have hi : f (flip x i) = false := by cases hy : f (flip x i) <;> simp_all
    have he : (sign f x - sign f (flip x i)) / 2 = 1 := by simp [sign, hx, hi]
    have hsum : 1 ≤ ∑ j, (sign f x - sign f (flip x j)) / 2 := by
      rw [← he]
      exact Finset.single_le_sum (fun j _ => sign_diff_nonneg f x hx j) (Finset.mem_univ i)
    exact hsum.trans (le_abs_self _)
  | false =>
    have hi : f (flip x i) = true := by cases hy : f (flip x i) <;> simp_all
    have he : (sign f (flip x i) - sign f x) / 2 = 1 := by simp [sign, hx, hi]
    have hsum : 1 ≤ ∑ j, (sign f (flip x j) - sign f x) / 2 := by
      rw [← he]
      apply Finset.single_le_sum _ (Finset.mem_univ i)
      intro j _
      simp only [sign, hx, Bool.false_eq_true, ↓reduceIte]
      split <;> norm_num
    have heq : (∑ j, (sign f (flip x j) - sign f x) / 2) =
        -(∑ j, (sign f x - sign f (flip x j)) / 2) := by
      rw [← Finset.sum_neg_distrib]
      apply Finset.sum_congr rfl
      intro j _
      ring
    rw [heq] at hsum
    exact hsum.trans (neg_le_abs _)

lemma beckmann_pos_of_sensitive {n : ℕ} (f : Cube n → Bool) (x : Cube n) (i : Fin n)
    (h : f x ≠ f (flip x i)) : 0 < beckmann f := by
  have hn : 0 < n := Nat.pos_of_ne_zero (by intro hn; subst n; exact Fin.elim0 i)
  have hc : (0:ℝ) < 2 * n * (2:ℝ)^n := by positivity
  have hnonempty : Set.Nonempty {t | ∃ V : Cube n → Fin n → ℝ, cost V = t ∧
      ∀ x, (∑ i, (V x i - V (flip x i) i)) =
      ∑ i, (sign f x - sign f (flip x i)) / 2} := by
    refine ⟨cost (fun x _ => sign f x / 2), (fun x _ => sign f x / 2), rfl, ?_⟩
    intro y
    apply Finset.sum_congr rfl
    intro j _
    ring
  have hlower : 1 / (2 * n * (2:ℝ)^n) ≤ beckmann f := by
    apply le_csInf hnonempty
    rintro t ⟨V, rfl, hV⟩
    apply (div_le_iff₀ hc).2
    have ha := charge_le_cost V x
    rw [hV x] at ha
    have hb := positive_charge f x i h
    nlinarith
  exact (div_pos zero_lt_one hc).trans_le hlower

end BeckmannExamples


/- Supporting component: ExamplePositive -/
namespace BeckmannExamples.Quotient

lemma exampleFunction_beckmann_pos (k : ℕ) (hk : 1 ≤ k) :
    0 < beckmann (exampleFunction k) := by
  classical
  let r : Fin k := ⟨k - 1, by omega⟩
  let a : Group k := fun j => if j = r then 1 else 0
  have har : a r ≠ 0 := by simp [a]
  have ha : a ≠ 0 := by
    intro he
    apply har
    exact congrFun he r
  have hlevel : level a = k := by
    have hfirst := level_eq_of_first a r har (by
      intro j hj
      have hne : j ≠ r := ne_of_lt hj
      simp [a, hne])
    simpa [r, Nat.sub_add_cancel hk] using hfirst
  obtain ⟨i, hi⟩ := canonicalLabel_covers k a ha
  apply beckmann_pos_of_sensitive (exampleFunction k) (fun _ => false) i
  have hz : projection (canonicalLabel k) (fun _ => false) = 0 := by
    simp [projection]
  simp only [exampleFunction, projection_flip, hz, zero_add, hi]
  simp only [alternating, level_zero, hlevel, Nat.even_add_one]
  cases h : decide (Even k) <;> simp_all

end BeckmannExamples.Quotient


/- Supporting component: LevelSums -/
namespace BeckmannExamples.Quotient

lemma level_le_dimension {k : ℕ} (a : Group k) (ha : a ≠ 0) : level a ≤ k := by
  have hb := (level_bounds a).2
  have hn : level a ≠ k + 1 := fun he => ha ((level_eq_last_iff a).mp he)
  omega

lemma weighted_layer_sum {k : ℕ} (F : ℕ → ℝ) :
    (∑ a : Group k, if a ≠ 0 then F (level a) else 0) =
      ∑ j : Fin k, (2:ℝ)^(k-j.val-1) * F (j.val+1) := by
  classical
  have hs : ∀ j : Fin k,
      (2:ℝ)^(k-j.val-1) * F (j.val+1) =
      ∑ a : Group k, if level a = j.val+1 then F (level a) else 0 := by
    intro j
    rw [← Finset.sum_filter]
    have he : (∑ a ∈ Finset.univ.filter (fun a : Group k => level a = j.val+1), F (level a)) =
        ∑ _a ∈ Finset.univ.filter (fun a : Group k => level a = j.val+1), F (j.val+1) := by
      apply Finset.sum_congr rfl
      intro a ha
      rw [(Finset.mem_filter.mp ha).2]
    rw [he, Finset.sum_const, card_level]
    simp
  simp_rw [hs]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  by_cases ha : a = 0
  · subst a
    simp only [ne_eq, not_true_eq_false, ↓reduceIte, level_zero]
    symm
    apply Finset.sum_eq_zero
    intro j _
    have hn : k+1 ≠ j.val+1 := by omega
    exact if_neg hn
  · rw [if_pos ha]
    have hpos := (level_bounds a).1
    have hle := level_le_dimension a ha
    let r : Fin k := ⟨level a-1, by omega⟩
    have hr : level a = r.val+1 := by dsimp [r]; omega
    rw [Finset.sum_eq_single r]
    · simp [hr]
    · intro j _ hj
      have hne : level a ≠ j.val+1 := by
        intro he
        apply hj
        apply Fin.ext
        dsimp [r]
        omega
      simp [hne]
    · simp

lemma truncated_weight_sum {k r : ℕ} (hr : r ≤ k) :
    (∑ a : Group k, if a ≠ 0 ∧ level a ≤ r then (multiplicity a : ℝ) else 0) =
      ∑ j ∈ Finset.range r, (2:ℝ)^(k-(j+1)) * 8^(j+1) := by
  classical
  have h := weighted_layer_sum (k:=k) (fun t => if t ≤ r then (8:ℝ)^t else 0)
  have hl : (∑ a : Group k, if a ≠ 0 ∧ level a ≤ r then (multiplicity a : ℝ) else 0) =
      ∑ a : Group k, if a ≠ 0 then (if level a ≤ r then (8:ℝ)^level a else 0) else 0 := by
    apply Finset.sum_congr rfl
    intro a _
    simp only [multiplicity, Nat.cast_pow, Nat.cast_ofNat]
    split_ifs <;> simp_all
  rw [hl, h]
  simp_rw [mul_ite, mul_zero]
  rw [Fin.sum_univ_eq_sum_range (fun j => if j+1 ≤ r then (2:ℝ)^(k-j-1)*8^(j+1) else 0)]
  have hs : Finset.range r ⊆ Finset.range k := Finset.range_mono hr
  calc
    (∑ j ∈ Finset.range k, if j+1 ≤ r then (2:ℝ)^(k-j-1)*8^(j+1) else 0) =
        ∑ j ∈ Finset.range r, if j+1 ≤ r then (2:ℝ)^(k-j-1)*8^(j+1) else 0 := by
      symm
      apply Finset.sum_subset hs
      intro j hj hnot
      have hjr : r ≤ j := by simpa using hnot
      simp [show ¬j+1 ≤ r by omega]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro j hj
      have hjr := Finset.mem_range.mp hj
      simp [show j+1 ≤ r by omega, Nat.sub_sub]

lemma weighted_mass_square_sum (k : ℕ) :
    (∑ a : Group k, if a ≠ 0 then (levelMass k (level a))^2 * (multiplicity a : ℝ) else 0) =
      (k : ℝ) * 2^(3*k) := by
  classical
  simp only [multiplicity, Nat.cast_pow, Nat.cast_ofNat]
  rw [weighted_layer_sum (fun r => (levelMass k r)^2 * (8:ℝ)^r)]
  have hterm : ∀ j : Fin k,
      (2:ℝ)^(k-j.val-1) * ((levelMass k (j.val+1))^2 * 8^(j.val+1)) = 2^(3*k) := by
    intro j
    have hj : j.val+1 ≤ k := by omega
    rw [levelMass, if_pos hj]
    rw [show k-j.val-1 = k-(j.val+1) by omega]
    simp only [show (8:ℝ) = 2^3 by norm_num, ← pow_mul, ← pow_add]
    congr 1
    omega
  simp_rw [hterm]
  simp

end BeckmannExamples.Quotient


/- Supporting component: Fibers -/
namespace BeckmannExamples.Quotient

private lemma Fibers_twice_eq_zero {k : ℕ} (z : Group k) : z + z = 0 := by
  ext i
  change z i + z i = 0
  calc
    z i + z i = 2 * z i := by ring
    _ = 0 := by rw [show (2 : ZMod 2) = 0 from ZMod.natCast_self 2, zero_mul]

lemma projection_xor {n k : ℕ} (label : Fin n → Group k) (x y : Cube n) :
    projection label (fun i => Bool.xor (x i) (y i)) = projection label x + projection label y := by
  unfold projection
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  cases hx : x i <;> cases hy : y i <;> simp [hx, hy, Fibers_twice_eq_zero]

noncomputable def xorEquiv {n : ℕ} (y : Cube n) : Cube n ≃ Cube n where
  toFun x := fun i => Bool.xor (x i) (y i)
  invFun x := fun i => Bool.xor (x i) (y i)
  left_inv x := by ext i; simp only; cases hx : x i <;> cases hy : y i <;> simp [hx, hy]
  right_inv x := by ext i; simp only; cases hx : x i <;> cases hy : y i <;> simp [hx, hy]

lemma projection_fiber_card_eq {n k : ℕ} (label : Fin n → Group k)
    (hsurj : Function.Surjective (projection label)) (z w : Group k) :
    (Finset.univ.filter (fun x => projection label x = z)).card =
      (Finset.univ.filter (fun x => projection label x = w)).card := by
  classical
  obtain ⟨y, hy⟩ := hsurj (z + w)
  apply Finset.card_equiv (xorEquiv y)
  intro x
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, xorEquiv, Equiv.coe_fn_mk,
    projection_xor, hy]
  constructor
  · intro hx
    rw [hx]
    simpa [add_assoc] using congrArg (fun a => a + w) (Fibers_twice_eq_zero z)
  · intro hx
    have hh := congrArg (fun a => a + (z + w)) hx
    have hzw : w + (z + w) = z := by
      calc
        w + (z + w) = z + (w + w) := by abel
        _ = z := by rw [Fibers_twice_eq_zero, add_zero]
    rw [add_assoc, Fibers_twice_eq_zero, add_zero, hzw] at hh
    exact hh

lemma sum_projection {n k : ℕ} (label : Fin n → Group k)
    (hsurj : Function.Surjective (projection label)) (g : Group k → ℝ) :
    (∑ x, g (projection label x)) =
      ((Finset.univ.filter (fun x => projection label x = 0)).card : ℝ) * ∑ z, g z := by
  classical
  rw [← Finset.sum_fiberwise Finset.univ (projection label) (fun x => g (projection label x))]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro z _
  calc
    (∑ x ∈ Finset.univ.filter (fun x => projection label x = z), g (projection label x)) =
        ∑ x ∈ Finset.univ.filter (fun x => projection label x = z), g z := by
      apply Finset.sum_congr rfl
      intro x hx
      rw [(Finset.mem_filter.mp hx).2]
    _ = ((Finset.univ.filter (fun x => projection label x = z)).card : ℝ) * g z := by simp
    _ = _ := by rw [projection_fiber_card_eq label hsurj z 0]

lemma avg_projection {n k : ℕ} (label : Fin n → Group k)
    (hsurj : Function.Surjective (projection label)) (g : Group k → ℝ) :
    avg (fun x => g (projection label x)) = (∑ z, g z) / (2:ℝ)^k := by
  classical
  have hc := sum_projection label hsurj (fun _ => (1:ℝ))
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one] at hc
  have hcQ : Fintype.card (Cube n) = 2^n := by simp [Cube]
  have hcG : Fintype.card (Group k) = 2^k := by simp [Group, ZMod.card]
  rw [hcQ, hcG] at hc
  push_cast at hc
  unfold avg
  rw [sum_projection label hsurj g]
  have h2n : (2:ℝ)^n ≠ 0 := by positivity
  have h2k : (2:ℝ)^k ≠ 0 := by positivity
  apply (div_eq_div_iff h2n h2k).2
  rw [hc]
  ring

lemma projection_single {n k : ℕ} (label : Fin n → Group k) (i : Fin n) :
    projection label (fun j => decide (j = i)) = label i := by
  classical
  simp [projection]

lemma projection_surjective_of_labels {n k : ℕ} (label : Fin n → Group k)
    (hlabel : ∀ z : Group k, z ≠ 0 → ∃ i, label i = z) :
    Function.Surjective (projection label) := by
  intro z
  by_cases hz : z = 0
  · refine ⟨fun _ => false, ?_⟩
    simp [projection, hz]
  · obtain ⟨i, hi⟩ := hlabel z hz
    exact ⟨fun j => decide (j = i), (projection_single label i).trans hi⟩

end BeckmannExamples.Quotient


/- Supporting component: PackingLevels -/
namespace BeckmannExamples.Quotient

lemma levelMass_pos (k r : ℕ) : 0 < levelMass k r := by
  unfold levelMass
  split <;> positivity

lemma levelMass_step (k r : ℕ) (hr : r < k) :
    levelMass k r = 2 * levelMass k (r+1) := by
  unfold levelMass
  rw [if_pos (by omega), if_pos (by omega)]
  rw [show k-r = (k-(r+1))+1 by omega, pow_succ]
  ring

lemma levelMass_step_le (k r : ℕ) (hr : r ≤ k) :
    levelMass k r ≤ 2 * levelMass k (r+1) := by
  rcases lt_or_eq_of_le hr with h | rfl
  · exact le_of_eq (levelMass_step k r h)
  · norm_num [levelMass]

lemma packingLambda_pos (k r : ℕ) : 0 < packingLambda k r := by
  unfold packingLambda
  exact one_div_pos.mpr (Real.sqrt_pos.mpr (by have := levelMass_pos k (r+1); positivity))

lemma packing_outgoing (k r : ℕ) :
    levelMass k (r+1) * (8:ℝ)^r * packingLambda k r ^ 2 = 1/3 := by
  have hp : 0 < 3 * levelMass k (r+1) * (8:ℝ)^r := by
    have := levelMass_pos k (r+1); positivity
  unfold packingLambda
  rw [div_pow, Real.sq_sqrt hp.le]
  field_simp [ne_of_gt (levelMass_pos k (r+1))]
  <;> ring

lemma packing_incoming (k r : ℕ) (hr : r ≤ k) :
    levelMass k r * (8:ℝ)^r * packingLambda k r ^ 2 ≤ 2/3 := by
  have h := levelMass_step_le k r hr
  calc
    _ ≤ (2 * levelMass k (r+1)) * (8:ℝ)^r * packingLambda k r ^ 2 := by
      gcongr
    _ = 2 * (levelMass k (r+1) * (8:ℝ)^r * packingLambda k r ^ 2) := by ring
    _ = 2/3 := by rw [packing_outgoing]; norm_num

lemma packing_vertex_norm (k r : ℕ) (hr : r ≤ k+1) :
    (if r ≤ k then levelMass k (r+1) * (8:ℝ)^r * packingLambda k r ^ 2 else 0) +
    (if 2 ≤ r then levelMass k (r-1) * (8:ℝ)^(r-1) * packingLambda k (r-1) ^ 2 else 0)
      ≤ 1 := by
  have hout : (if r ≤ k then levelMass k (r+1) * (8:ℝ)^r * packingLambda k r ^ 2 else 0) ≤ 1/3 := by
    split
    · rw [packing_outgoing]
    · norm_num
  have hin : (if 2 ≤ r then levelMass k (r-1) * (8:ℝ)^(r-1) * packingLambda k (r-1) ^ 2 else 0) ≤ 2/3 := by
    split
    · exact packing_incoming k (r-1) (by omega)
    · norm_num
  linarith

lemma levelMass_cube (k r : ℕ) (hr : r ≤ k) :
    levelMass k r ^ 3 * (8:ℝ)^r = ((2:ℝ)^k)^3 := by
  unfold levelMass
  rw [if_pos hr]
  rw [show (8:ℝ) = 2^3 by norm_num, ← pow_mul, ← pow_mul, ← pow_add]
  rw [← pow_mul]
  congr 1
  omega

lemma packing_term_lower_aux {M N W P : ℝ} (hM : 0 < M) (hN : 0 < N)
    (hW : 0 < W) (hP : 0 < P) (hbound : P^3 ≤ 2*M^2*N*W) :
    P * Real.sqrt P / Real.sqrt 6 ≤ M*N*W / Real.sqrt (3*N*W) := by
  have hd : 0 < Real.sqrt (3*N*W) := Real.sqrt_pos.mpr (by positivity)
  have h6 : 0 < Real.sqrt (6:ℝ) := Real.sqrt_pos.mpr (by norm_num)
  apply (div_le_div_iff₀ h6 hd).mpr
  apply (sq_le_sq₀ (by positivity) (by positivity)).mp
  calc
    (P * Real.sqrt P * Real.sqrt (3*N*W))^2 = 3*P^3*N*W := by
      simp only [mul_pow, Real.sq_sqrt hP.le, Real.sq_sqrt (show 0 ≤ 3*N*W by positivity)]
      ring
    _ ≤ (M*N*W*Real.sqrt 6)^2 := by
      rw [mul_pow, Real.sq_sqrt (show (0:ℝ) ≤ 6 by norm_num)]
      have hh := mul_le_mul_of_nonneg_right hbound (show 0 ≤ 3*N*W by positivity)
      nlinarith

lemma packing_level_lower (k r : ℕ) (hr : r ≤ k) :
    (2:ℝ)^k * Real.sqrt ((2:ℝ)^k) / Real.sqrt 6 ≤
      levelMass k r * levelMass k (r+1) * (8:ℝ)^r * packingLambda k r := by
  have hcube := levelMass_cube k r hr
  have hstep := levelMass_step_le k r hr
  have hbound : ((2:ℝ)^k)^3 ≤ 2 * levelMass k r ^ 2 * levelMass k (r+1) * (8:ℝ)^r := by
    have hh := mul_le_mul_of_nonneg_right hstep
      (show 0 ≤ levelMass k r ^ 2 * (8:ℝ)^r by positivity)
    nlinarith
  have hh := packing_term_lower_aux (levelMass_pos k r) (levelMass_pos k (r+1))
    (show 0 < (8:ℝ)^r by positivity) (show 0 < (2:ℝ)^k by positivity) hbound
  simpa only [packingLambda, mul_one_div] using hh

lemma packing_sum_lower (k : ℕ) :
    (k:ℝ) / Real.sqrt 6 * Real.sqrt ((2:ℝ)^k) ≤
      (∑ r ∈ Finset.range k,
        levelMass k (r+1) * levelMass k (r+2) * (8:ℝ)^(r+1) * packingLambda k (r+1)) /
        (2:ℝ)^k := by
  have hs : (k:ℝ) * ((2:ℝ)^k * Real.sqrt ((2:ℝ)^k) / Real.sqrt 6) ≤
      ∑ r ∈ Finset.range k,
        levelMass k (r+1) * levelMass k (r+2) * (8:ℝ)^(r+1) * packingLambda k (r+1) := by
    calc
      _ = ∑ _r ∈ Finset.range k, (2:ℝ)^k * Real.sqrt ((2:ℝ)^k) / Real.sqrt 6 := by simp
      _ ≤ _ := Finset.sum_le_sum fun r hr => packing_level_lower k (r+1) (by simpa using Finset.mem_range.mp hr)
  apply (le_div_iff₀ (show 0 < (2:ℝ)^k by positivity)).mpr
  convert hs using 1 <;> ring

end BeckmannExamples.Quotient


/- Supporting component: EdgeCounts -/
namespace BeckmannExamples.Quotient

lemma canonical_projection_surjective (k : ℕ) :
    Function.Surjective (projection (canonicalLabel k)) :=
  projection_surjective_of_labels (canonicalLabel k) (canonicalLabel_covers k)

lemma sum_canonicalLabel_all (k : ℕ) (g : Group k → ℝ) :
    (∑ i, g (canonicalLabel k i)) =
      ∑ a : Group k, if a = 0 then 0 else (multiplicity a : ℝ) * g a := by
  classical
  rw [sum_canonicalLabel]
  rw [← Finset.sum_subtype (Finset.univ.filter fun a : Group k => a ≠ 0)
    (by intro a; simp) (fun a => (multiplicity a : ℝ) * g a)]
  simp only [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro a _
  split_ifs <;> simp_all

lemma canonicalLabel_count (k : ℕ) (a : Group k) :
    (∑ i, if canonicalLabel k i = a then (1:ℝ) else 0) =
      if a = 0 then 0 else (multiplicity a : ℝ) := by
  classical
  rw [sum_canonicalLabel_all k (fun b => if b = a then (1:ℝ) else 0)]
  have hh (b : Group k) :
      (if b = 0 then (0:ℝ) else ↑(multiplicity b) * if b = a then 1 else 0) =
      if b = a then (if a = 0 then 0 else (multiplicity a : ℝ)) else 0 := by
    split_ifs <;> simp_all
  simp_rw [hh]
  simp

private lemma EdgeCounts_twice_zero {k : ℕ} (z : Group k) : z + z = 0 := by
  ext i
  change z i + z i = 0
  calc
    _ = 2 * z i := by ring
    _ = 0 := by rw [show (2:ZMod 2)=0 from ZMod.natCast_self 2, zero_mul]

lemma sum_level_indicator {k : ℕ} (s : ℕ) (hs : 1 ≤ s) (hs' : s ≤ k + 1) :
    (∑ y : Group k, if level y = s then (1:ℝ) else 0) = levelMass k s := by
  classical
  by_cases hk : s ≤ k
  · let r : Fin k := ⟨s-1, by omega⟩
    have hr : r.val + 1 = s := by dsimp [r]; omega
    have hc := card_level r
    rw [hr] at hc
    have he : k - r.val - 1 = k - s := by dsimp [r]; omega
    rw [he] at hc
    simp only [levelMass, hk, ↓reduceIte]
    rw [← Finset.sum_filter]
    simp only [Finset.sum_const, nsmul_eq_mul, mul_one]
    rw [hc]
    simp
  · have he : s = k+1 := by omega
    subst s
    simp only [level_eq_last_iff]
    simp [levelMass]

lemma directions_to_level {k : ℕ} (z : Group k) (s : ℕ)
    (hs : 1 ≤ s) (hs' : s ≤ k+1) (hne : level z ≠ s) :
    (∑ i, if level (z + canonicalLabel k i) = s then (1:ℝ) else 0) =
      levelMass k s * (8:ℝ) ^ min (level z) s := by
  classical
  rw [sum_canonicalLabel_all k (fun a => if level (z + a) = s then (1:ℝ) else 0)]
  rw [← Equiv.sum_comp (Equiv.addLeft z) (fun a : Group k =>
    if a = 0 then (0:ℝ) else (multiplicity a : ℝ) * if level (z+a)=s then 1 else 0)]
  have hterm (y : Group k) :
      (if (Equiv.addLeft z) y = 0 then (0:ℝ) else
        (multiplicity ((Equiv.addLeft z) y) : ℝ) *
        if level (z + (Equiv.addLeft z) y) = s then 1 else 0) =
      (if level y = s then (1:ℝ) else 0) * (8:ℝ) ^ min (level z) s := by
    change (if z+y=0 then (0:ℝ) else (multiplicity (z+y) : ℝ) *
      if level (z+(z+y))=s then 1 else 0) =
      (if level y=s then (1:ℝ) else 0) * (8:ℝ)^min (level z) s
    have hzz : z + (z + y) = y := by rw [← add_assoc, EdgeCounts_twice_zero, zero_add]
    simp only [hzz]
    by_cases hy : level y = s
    · have hdiff : level z ≠ level y := by simpa [hy] using hne
      have hzero : z + y ≠ 0 := by
        intro hh
        have hyz : y = z := by
          have := congrArg (fun t => z + t) hh
          simpa only [← add_assoc, EdgeCounts_twice_zero, zero_add, add_zero] using this
        exact hdiff (congrArg level hyz.symm)
      simp only [hzero, ↓reduceIte, hy, mul_one, one_mul]
      simp only [multiplicity, Nat.cast_pow, Nat.cast_ofNat, level_add_of_ne z y hdiff, hy]
    · simp [hy]
  simp_rw [hterm]
  rw [← Finset.sum_mul, sum_level_indicator s hs hs']

lemma selectedWeight_sq_decompose {k : ℕ} (z y : Group k) :
    selectedWeight z y ^ 2 =
      (if level y = level z + 1 then packingLambda k (level z) ^ 2 else 0) +
      (if level y = level z - 1 then packingLambda k (level z - 1) ^ 2 else 0) := by
  have hz := level_bounds z
  have hy := level_bounds y
  by_cases hnext : level y = level z + 1
  · have hmin : min (level z) (level y) = level z := by omega
    have hmax : max (level z) (level y) = level y := by omega
    have hprev : level y ≠ level z - 1 := by omega
    unfold selectedWeight
    dsimp only
    rw [hmin, hmax, if_pos hnext, if_neg hprev]
    simp [hnext]
  · by_cases hprev : level y = level z - 1
    · have hmin : min (level z) (level y) = level y := by omega
      have hmax : max (level z) (level y) = level z := by omega
      have hstep : level z = level y + 1 := by omega
      unfold selectedWeight
      dsimp only
      rw [hmin, hmax, if_pos hstep, if_neg hnext, if_pos hprev]
      rw [hprev]
      simp
    · have hno : max (level z) (level y) ≠ min (level z) (level y) + 1 := by omega
      simp [selectedWeight, hno, hnext, hprev]

lemma selectedWeight_sq_sum_eq {k : ℕ} (z : Group k) :
    (∑ i, selectedWeight z (z + canonicalLabel k i) ^ 2) =
      (if level z ≤ k then levelMass k (level z+1) * (8:ℝ)^(level z) *
        packingLambda k (level z)^2 else 0) +
      (if 2 ≤ level z then levelMass k (level z-1) * (8:ℝ)^(level z-1) *
        packingLambda k (level z-1)^2 else 0) := by
  classical
  simp_rw [selectedWeight_sq_decompose]
  rw [Finset.sum_add_distrib]
  congr 1
  · have hp : (∑ i, if level (z + canonicalLabel k i) = level z + 1 then
        packingLambda k (level z) ^ 2 else 0) =
      (∑ i, if level (z + canonicalLabel k i) = level z + 1 then (1:ℝ) else 0) *
        packingLambda k (level z)^2 := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro i _
      split_ifs <;> simp
    rw [hp]
    by_cases hz : level z ≤ k
    · rw [if_pos hz, directions_to_level z (level z+1) (by omega) (by omega) (by omega)]
      rw [min_eq_left (by omega)]
    · rw [if_neg hz]
      have hzero (i : Fin (Fintype.card (Coordinate k))) :
          level (z + canonicalLabel k i) ≠ level z + 1 := by
        have := (level_bounds (z + canonicalLabel k i)).2
        omega
      simp [hzero]
  · have hp : (∑ i, if level (z + canonicalLabel k i) = level z - 1 then
        packingLambda k (level z-1) ^ 2 else 0) =
      (∑ i, if level (z + canonicalLabel k i) = level z - 1 then (1:ℝ) else 0) *
        packingLambda k (level z-1)^2 := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro i _
      split_ifs <;> simp
    rw [hp]
    by_cases hz : 2 ≤ level z
    · rw [if_pos hz, directions_to_level z (level z-1) (by omega)
        (by have := (level_bounds z).2; omega) (by omega)]
      rw [min_eq_right (by omega)]
    · rw [if_neg hz]
      have hzero (i : Fin (Fintype.card (Coordinate k))) :
          level (z + canonicalLabel k i) ≠ level z - 1 := by
        have := (level_bounds (z + canonicalLabel k i)).1
        omega
      simp [hzero]

lemma selectedWeight_sq_sum_le {k : ℕ} (z : Group k) :
    (∑ i, selectedWeight z (z + canonicalLabel k i) ^ 2) ≤ 1 := by
  rw [selectedWeight_sq_sum_eq]
  exact packing_vertex_norm k (level z) (level_bounds z).2

end BeckmannExamples.Quotient


/- Supporting component: Estimates -/
namespace BeckmannExamples

/-- The numerical last step of Theorem 5.5, with a common positive scale. -/
theorem separation_ratio {k : ℕ} {B T s : ℝ}
    (hB : 0 < B)
    (hupper : B ≤ (4 / 3 : ℝ) * Real.sqrt k * s)
    (hlower : (k : ℝ) / Real.sqrt 6 * s ≤ T) :
    (3 / (4 * Real.sqrt 6)) * Real.sqrt k ≤ T / B := by
  have h6 : Real.sqrt 6 ≠ 0 := ne_of_gt (Real.sqrt_pos.2 (by norm_num))
  have hmul := mul_le_mul_of_nonneg_left hupper
    (show 0 ≤ (3 / (4 * Real.sqrt 6)) * Real.sqrt k by positivity)
  apply (le_div_iff₀ hB).2
  calc
    (3 / (4 * Real.sqrt 6) * Real.sqrt k) * B ≤
        (3 / (4 * Real.sqrt 6) * Real.sqrt k) *
          ((4 / 3 : ℝ) * Real.sqrt k * s) := hmul
    _ = (k : ℝ) / Real.sqrt 6 * s := by
      have hk := Real.sq_sqrt (show (0 : ℝ) ≤ k by positivity)
      field_simp
      rw [hk]
      ring
    _ ≤ T := hlower

/-- Multiplicity of level r+1, times its number of labels. -/
theorem weighted_level_term (k r : ℕ) (hr : r < k) :
    2 ^ (k - (r + 1)) * 8 ^ (r + 1) = 2 ^ (k + 2) * 4 ^ r := by
  rw [show (8 : ℕ) = 2 ^ 3 by norm_num, ← pow_mul, ← pow_add,
      show (4 : ℕ) = 2 ^ 2 by norm_num, ← pow_mul, ← pow_add]
  congr 1
  omega

/-- The dimension count (28), indexed by r=0,...,k-1. -/
theorem sum_weighted_levels (k : ℕ) :
    (∑ r ∈ Finset.range k, 2 ^ (k - (r + 1)) * 8 ^ (r + 1)) = dimension k := by
  calc
    (∑ r ∈ Finset.range k, 2 ^ (k - (r + 1)) * 8 ^ (r + 1)) =
        ∑ r ∈ Finset.range k, 2 ^ (k + 2) * 4 ^ r := by
      apply Finset.sum_congr rfl
      intro r hr
      exact weighted_level_term k r (Finset.mem_range.1 hr)
    _ = 2 ^ (k + 2) * (∑ r ∈ Finset.range k, 4 ^ r) := by rw [Finset.mul_sum]
    _ = dimension k := by
      have h := geom_sum_mul_of_one_le (show 1 ≤ (4 : ℕ) by norm_num) k
      norm_num at h
      unfold dimension
      rw [← h, ← Nat.mul_assoc, Nat.mul_div_cancel]
      norm_num

/-- The equal contributions used in the squared Beckmann cost. -/
theorem mass_cube_identity (k r : ℕ) (hr : r < k) :
    (2 ^ (k - (r + 1))) ^ 3 * 8 ^ (r + 1) = 2 ^ (3 * k) := by
  simp only [show (8 : ℕ) = 2 ^ 3 by norm_num, ← pow_mul, ← pow_add]
  congr 1
  omega

theorem sum_mass_cube (k : ℕ) :
    (∑ r ∈ Finset.range k, (2 ^ (k - (r + 1))) ^ 3 * 8 ^ (r + 1)) =
      k * 2 ^ (3 * k) := by
  calc
    _ = ∑ _r ∈ Finset.range k, 2 ^ (3 * k) := by
      apply Finset.sum_congr rfl
      intro r hr
      exact mass_cube_identity k r (Finset.mem_range.1 hr)
    _ = _ := by simp

/-- The last singleton level completes the geometric tail. -/
theorem level_tail_sum (d : ℕ) :
    (∑ s ∈ Finset.range d, 2 ^ s) + 1 = 2 ^ d := by
  simpa using geom_sum_mul_add (1 : ℕ) d

/-- Earlier levels have strictly less than one third of the current total weight. -/
theorem earlier_weight_identity (k r : ℕ) (hr : r < k) :
    3 * (∑ j ∈ Finset.range r, 2 ^ (k - (j + 1)) * 8 ^ (j + 1)) +
      2 ^ (k + 2) = 2 ^ (k - (r + 1)) * 8 ^ (r + 1) := by
  have hs : (∑ j ∈ Finset.range r, 2 ^ (k - (j + 1)) * 8 ^ (j + 1)) =
      2 ^ (k + 2) * (∑ j ∈ Finset.range r, 4 ^ j) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    exact weighted_level_term k j (lt_trans (Finset.mem_range.1 hj) hr)
  rw [hs, weighted_level_term k r hr]
  have hg := geom_sum_mul_add (3 : ℕ) r
  norm_num at hg
  calc
    _ = 2 ^ (k + 2) * ((∑ j ∈ Finset.range r, 4 ^ j) * 3 + 1) := by ring
    _ = _ := by rw [hg]

theorem earlier_weight_bound (k r : ℕ) (hr : r < k) :
    3 * (∑ j ∈ Finset.range r, 2 ^ (k - (j + 1)) * 8 ^ (j + 1)) ≤
      2 ^ (k - (r + 1)) * 8 ^ (r + 1) := by
  exact Nat.le.intro (earlier_weight_identity k r hr)

/-- Numeric estimate for a field supported on a fiber of mass 1/M. -/
theorem star_cost_bound {k : ℕ} (m w d : Fin k → ℝ) {M : ℝ}
    (hM : 0 < M) (hm : ∀ i, 0 ≤ m i) (hw : ∀ i, 0 < w i)
    (hd : ∀ i, 0 ≤ d i) (hdegree : ∀ i, d i ≤ (4 / 3 : ℝ) * m i * w i)
    (hmass : ∀ i, m i ^ 3 * w i = M ^ 3) :
    Real.sqrt (∑ i, m i * d i ^ 2 / w i) / M ≤
      (4 / 3 : ℝ) * Real.sqrt k * Real.sqrt M := by
  have hterm (i : Fin k) : m i * d i ^ 2 / w i ≤ (16 / 9 : ℝ) * M ^ 3 := by
    have hsq : d i ^ 2 ≤ ((4 / 3 : ℝ) * m i * w i) ^ 2 :=
      pow_le_pow_left₀ (hd i) (hdegree i) 2
    calc
      m i * d i ^ 2 / w i ≤ m i * ((4 / 3 : ℝ) * m i * w i) ^ 2 / w i :=
        div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hsq (hm i)) (le_of_lt (hw i))
      _ = (16 / 9 : ℝ) * (m i ^ 3 * w i) := by
        field_simp
        <;> ring
      _ = _ := by rw [hmass i]
  have hsum : (∑ i, m i * d i ^ 2 / w i) ≤ (16 / 9 : ℝ) * k * M ^ 3 := by
    calc
      _ ≤ ∑ _i : Fin k, (16 / 9 : ℝ) * M ^ 3 := Finset.sum_le_sum (fun i _ => hterm i)
      _ = _ := by simp; ring
  apply (div_le_iff₀ hM).2
  apply (Real.sqrt_le_iff).2
  refine ⟨by positivity, ?_⟩
  calc
    _ ≤ (16 / 9 : ℝ) * k * M ^ 3 := hsum
    _ = ((4 / 3 : ℝ) * Real.sqrt k * Real.sqrt M * M) ^ 2 := by
      rw [mul_pow, mul_pow, mul_pow, Real.sq_sqrt (by positivity),
        Real.sq_sqrt (le_of_lt hM)]
      ring

/-- Crude bound for all label weights through a given level, in naturals. -/
theorem partial_weight_bound_nat (k r : ℕ) (hr : r ≤ k) :
    3 * (∑ j ∈ Finset.range r, 2 ^ (k - (j + 1)) * 8 ^ (j + 1)) ≤
      4 * 2 ^ (k - r) * 8 ^ r := by
  have hs : (∑ j ∈ Finset.range r, 2 ^ (k - (j + 1)) * 8 ^ (j + 1)) =
      2 ^ (k + 2) * (∑ j ∈ Finset.range r, 4 ^ j) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    exact weighted_level_term k j (lt_of_lt_of_le (Finset.mem_range.1 hj) hr)
  have hp : 2 ^ (k + 2) * 4 ^ r = 4 * 2 ^ (k - r) * 8 ^ r := by
    simp only [show (8 : ℕ) = 2 ^ 3 by norm_num,
      show (4 : ℕ) = 2 ^ 2 by norm_num, ← pow_mul, ← pow_add]
    congr 1
    omega
  have hg : 3 * (∑ j ∈ Finset.range r, 4 ^ j) ≤ 4 ^ r := by
    have hg := geom_sum_mul_add (3 : ℕ) r
    norm_num at hg
    omega
  rw [hs, ← hp]
  calc
    _ = 2 ^ (k + 2) * (3 * (∑ j ∈ Finset.range r, 4 ^ j)) := by ring
    _ ≤ _ := Nat.mul_le_mul_left _ hg

/-- Crude degree bound (34), using all labels of level at most r. -/
theorem partial_weight_bound (k r : ℕ) (hr : r ≤ k) :
    (∑ j ∈ Finset.range r, (2 : ℝ) ^ (k - (j + 1)) * 8 ^ (j + 1)) ≤
      (4 / 3 : ℝ) * 2 ^ (k - r) * 8 ^ r := by
  have h : (3 : ℝ) * (∑ j ∈ Finset.range r,
      (2 : ℝ) ^ (k - (j + 1)) * 8 ^ (j + 1)) ≤ 4 * 2 ^ (k - r) * 8 ^ r := by
    exact_mod_cast partial_weight_bound_nat k r hr
  linarith

end BeckmannExamples


/- Supporting component: Dimensions -/
namespace BeckmannExamples.Quotient

lemma card_coordinate (k : ℕ) : Fintype.card (Coordinate k) = dimension k := by
  have hcard := sum_canonicalLabel_all k (fun _ => (1:ℝ))
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one] at hcard
  have hweight : (∑ a : Group k, if a = 0 then (0:ℝ) else (multiplicity a : ℝ)) =
      ∑ j : Fin k, (2:ℝ)^(k-j.val-1) * (8:ℝ)^(j.val+1) := by
    convert weighted_layer_sum (k:=k) (fun r => (8:ℝ)^r) using 1
    apply Finset.sum_congr rfl
    intro a _
    by_cases ha : a = 0 <;> simp [ha, multiplicity]
  rw [hweight] at hcard
  have hnat := sum_weighted_levels k
  have hreal : (∑ j : Fin k, (2:ℝ)^(k-j.val-1) * (8:ℝ)^(j.val+1)) =
      (dimension k : ℝ) := by
    rw [Fin.sum_univ_eq_sum_range (fun j => (2:ℝ)^(k-j-1) * (8:ℝ)^(j+1))]
    simp only [Nat.sub_sub]
    exact_mod_cast hnat
  exact_mod_cast hcard.trans hreal

end BeckmannExamples.Quotient


/- Supporting component: Charge -/
namespace BeckmannExamples.Quotient

noncomputable def quotientSign {k : ℕ} (z : Group k) : ℝ :=
  if alternating z then 1 else -1

noncomputable def charge {k : ℕ} (z : Group k) : ℝ :=
  (1 / 2 : ℝ) * ∑ a : Group k,
    if a = 0 then 0 else (multiplicity a : ℝ) * (quotientSign z - quotientSign (z + a))

lemma sum_charge {k : ℕ} : ∑ z : Group k, charge z = 0 := by
  classical
  unfold charge
  rw [← Finset.mul_sum, Finset.sum_comm]
  have h : ∀ a : Group k, (∑ z : Group k,
      if a = 0 then (0:ℝ) else (multiplicity a : ℝ) *
        (quotientSign z - quotientSign (z + a))) = 0 := by
    intro a
    by_cases ha : a = 0
    · simp [ha]
    · simp only [ha, ↓reduceIte]
      rw [← Finset.mul_sum, Finset.sum_sub_distrib]
      have heq : (∑ z : Group k, quotientSign (z + a)) = ∑ z : Group k, quotientSign z :=
        Equiv.sum_comp (Equiv.addRight a) quotientSign
      rw [heq, sub_self, mul_zero]
  simp [h]

lemma quotientSign_sub_abs_le {k : ℕ} (y z : Group k) :
    |quotientSign y - quotientSign z| ≤ 2 := by
  unfold quotientSign
  split <;> split <;> norm_num

lemma quotientSign_add_of_level_lt {k : ℕ} (z a : Group k)
    (h : level z < level a) : quotientSign (z + a) = quotientSign z := by
  simp [quotientSign, alternating, level_add_of_lt z a h]

lemma charge_abs_le {k : ℕ} (z : Group k) :
    |charge z| ≤ ∑ a : Group k,
      if a ≠ 0 ∧ level a ≤ level z then (multiplicity a : ℝ) else 0 := by
  classical
  unfold charge
  rw [abs_mul]
  norm_num only [abs_div, abs_one, abs_of_pos (show (0:ℝ) < 2 by norm_num)]
  calc
    (1 / 2 : ℝ) * |∑ a : Group k, if a = 0 then 0 else
        (multiplicity a : ℝ) * (quotientSign z - quotientSign (z + a))| ≤
      (1 / 2 : ℝ) * ∑ a : Group k, |if a = 0 then 0 else
        (multiplicity a : ℝ) * (quotientSign z - quotientSign (z + a))| :=
      mul_le_mul_of_nonneg_left (Finset.abs_sum_le_sum_abs _ _) (by norm_num)
    _ ≤ (1 / 2 : ℝ) * ∑ a : Group k,
        2 * (if a ≠ 0 ∧ level a ≤ level z then (multiplicity a : ℝ) else 0) := by
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      apply Finset.sum_le_sum
      intro a _
      by_cases ha : a = 0
      · simp [ha]
      · by_cases hl : level a ≤ level z
        · simp only [ite_eq_right ha, ite_eq_left (And.intro ha hl), abs_mul, Nat.abs_cast]
          have hb := quotientSign_sub_abs_le z (z + a)
          have hc := mul_le_mul_of_nonneg_left hb (show (0:ℝ) ≤ multiplicity a by positivity)
          nlinarith
        · have he := quotientSign_add_of_level_lt z a (lt_of_not_ge hl)
          simp [ha, hl, he]
    _ = _ := by rw [← Finset.mul_sum]; ring

lemma charge_degree_bound {k : ℕ} (z : Group k) (hz : z ≠ 0) :
    |charge z| ≤ (4 / 3 : ℝ) * levelMass k (level z) * (multiplicity z : ℝ) := by
  have hr : level z ≤ k := level_le_dimension z hz
  calc
    |charge z| ≤ _ := charge_abs_le z
    _ = _ := truncated_weight_sum hr
    _ ≤ (4 / 3 : ℝ) * (2:ℝ)^(k-level z) * 8^(level z) :=
      partial_weight_bound k (level z) hr
    _ = _ := by simp [levelMass, hr, multiplicity]

end BeckmannExamples.Quotient


/- Supporting component: Basics -/
namespace BeckmannExamples
open scoped BigOperators

@[simp] theorem flip_flip {n : ℕ} (x : Cube n) (i : Fin n) : flip (flip x i) i = x := by
  funext j
  by_cases h : j = i
  · subst j; simp [flip]
  · simp [flip, h]

theorem sum_flip {n : ℕ} (g : Cube n → ℝ) (i : Fin n) :
    ∑ x, g (flip x i) = ∑ x, g x := by
  exact Fintype.sum_equiv (⟨fun x => flip x i, fun x => flip x i,
    fun x => flip_flip x i, fun x => flip_flip x i⟩ : Cube n ≃ Cube n) _ _ (fun x => rfl)

theorem cost_nonneg {n : ℕ} (V : Cube n → Fin n → ℝ) : 0 ≤ cost V := by
  exact div_nonneg (Finset.sum_nonneg fun _ _ => Real.sqrt_nonneg _) (by positivity)

theorem beckmann_feasible {n : ℕ} (f : Cube n → Bool) :
    ∃ V : Cube n → Fin n → ℝ, ∀ x,
      (∑ i, (V x i - V (flip x i) i)) =
        ∑ i, (sign f x - sign f (flip x i)) / 2 := by
  refine ⟨fun x _ => sign f x / 2, fun x => ?_⟩
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem beckmann_bddBelow {n : ℕ} (f : Cube n → Bool) :
    BddBelow {t | ∃ V : Cube n → Fin n → ℝ, cost V = t ∧
    ∀ x, (∑ i, (V x i - V (flip x i) i)) =
      ∑ i, (sign f x - sign f (flip x i)) / 2} := by
  refine ⟨0, ?_⟩
  rintro t ⟨V, rfl, hV⟩
  exact cost_nonneg V

theorem beckmann_nonneg {n : ℕ} (f : Cube n → Bool) : 0 ≤ beckmann f := by
  obtain ⟨V, hV⟩ := beckmann_feasible f
  exact le_csInf ⟨cost V, V, rfl, hV⟩ (by rintro t ⟨W, rfl, hW⟩; exact cost_nonneg W)

noncomputable def redAllocation {n : ℕ} (f : Cube n → Bool) (x : Cube n) (i : Fin n) : ℝ :=
  if f x = true ∧ f (flip x i) = false then 1 else 0

theorem redAllocation_valid {n : ℕ} (f : Cube n → Bool) : Allocation f (redAllocation f) := by
  intro x i
  simp only [redAllocation, flip_flip]
  cases h : f x <;> cases h' : f (flip x i) <;> simp [h, h']

theorem redAllocation_integral {n : ℕ} (f : Cube n → Bool) :
    ∀ x i, redAllocation f x i = 0 ∨ redAllocation f x i = 1 := by
  intro x i
  unfold redAllocation
  split_ifs <;> simp

theorem fractional_bddBelow {n : ℕ} (f : Cube n → Bool) :
    BddBelow {t | ∃ a, Allocation f a ∧ cost a = t} := by
  refine ⟨0, ?_⟩
  rintro t ⟨a, ha, rfl⟩
  exact cost_nonneg a

theorem fractional_le_colored {n : ℕ} (f : Cube n → Bool) : fractional f ≤ colored f := by
  unfold fractional colored
  refine le_csInf ?_ ?_
  · exact ⟨cost (redAllocation f), redAllocation f,
      redAllocation_valid f, redAllocation_integral f, rfl⟩
  rintro t ⟨a, ha, hi, rfl⟩
  exact csInf_le (fractional_bddBelow f) ⟨a, ha, rfl⟩

theorem dot_le_norm {n : ℕ} (u v : Fin n → ℝ)
    (hu : ∑ i, (u i)^2 ≤ 1) :
    ∑ i, u i * v i ≤ Real.sqrt (∑ i, (v i)^2) := by
  calc
    _ ≤ Real.sqrt (∑ i, (u i)^2) * Real.sqrt (∑ i, (v i)^2) :=
      Real.sum_mul_le_sqrt_mul_sqrt _ _ _
    _ ≤ 1 * Real.sqrt (∑ i, (v i)^2) :=
      mul_le_mul_of_nonneg_right (by simpa using Real.sqrt_le_sqrt hu) (Real.sqrt_nonneg _)
    _ = _ := one_mul _

theorem integration_by_parts {n : ℕ} (φ : Cube n → ℝ) (V : Cube n → Fin n → ℝ) :
    (∑ x, φ x * (∑ i, (V x i - V (flip x i) i))) =
      ∑ x, ∑ i, (φ x - φ (flip x i)) * V x i := by
  simp_rw [Finset.mul_sum, mul_sub, sub_mul, Finset.sum_sub_distrib]
  congr 1
  rw [Finset.sum_comm, Finset.sum_comm (f := fun x i => φ (flip x i) * V x i)]
  apply Finset.sum_congr rfl
  intro i _
  simpa only [flip_flip] using (sum_flip (fun x => φ x * V (flip x i) i) i).symm

theorem weak_dual {n : ℕ} (f : Cube n → Bool) (φ : Cube n → ℝ)
    (hφ : ∀ x, ∑ i, (φ x - φ (flip x i)) ^ 2 ≤ 1) :
    avg (fun x => φ x * (∑ i, (sign f x - sign f (flip x i)) / 2)) ≤ beckmann f := by
  obtain ⟨V, hV⟩ := beckmann_feasible f
  unfold beckmann
  refine le_csInf ?_ ?_
  · exact ⟨cost V, V, rfl, hV⟩
  rintro t ⟨W, rfl, hW⟩
  unfold avg cost
  apply div_le_div_of_nonneg_right _ (by positivity)
  simp_rw [← hW]
  rw [integration_by_parts]
  exact Finset.sum_le_sum fun x _ => dot_le_norm _ _ (hφ x)

/-- Directed-edge version of fractional packing. Each undirected edge is counted twice. -/
theorem fractional_packing {n : ℕ} (f : Cube n → Bool)
    (w : Cube n → Fin n → ℝ)
    (hsym : ∀ x i, w (flip x i) i = w x i)
    (hzero : ∀ x i, f x = f (flip x i) → w x i = 0)
    (hnorm : ∀ x, ∑ i, (w x i)^2 ≤ 1) :
    avg (fun x => ∑ i, w x i) / 2 ≤ fractional f := by
  unfold fractional
  refine le_csInf ?_ ?_
  · exact ⟨cost (redAllocation f), redAllocation f, redAllocation_valid f, rfl⟩
  rintro t ⟨a, ha, rfl⟩
  have hmass : (∑ x, ∑ i, w x i) = 2 * (∑ x, ∑ i, w x i * a x i) := by
    calc
      _ = ∑ x, ∑ i, w x i * (a x i + a (flip x i) i) := by
        apply Finset.sum_congr rfl
        intro x _
        apply Finset.sum_congr rfl
        intro i _
        by_cases h : f x = f (flip x i)
        · simp [hzero x i h]
        · have hh := (ha x i).2
          rw [if_neg h] at hh
          rw [hh, mul_one]
      _ = (∑ x, ∑ i, w x i * a x i) + (∑ x, ∑ i, w x i * a (flip x i) i) := by
        simp_rw [mul_add, Finset.sum_add_distrib]
      _ = (∑ x, ∑ i, w x i * a x i) + (∑ x, ∑ i, w x i * a x i) := by
        congr 1
        rw [Finset.sum_comm, Finset.sum_comm (f := fun x i => w x i * a x i)]
        apply Finset.sum_congr rfl
        intro i _
        simpa only [hsym, flip_flip] using
          (sum_flip (fun x => w x i * a (flip x i) i) i).symm
      _ = _ := by ring
  calc
    _ = avg (fun x => ∑ i, w x i * a x i) := by
      unfold avg
      rw [hmass]
      ring
    _ ≤ cost a := by
      unfold avg cost
      apply div_le_div_of_nonneg_right _ (by positivity)
      exact Finset.sum_le_sum fun x _ => dot_le_norm _ _ (hnorm x)

end BeckmannExamples


/- Supporting component: StarField -/
namespace BeckmannExamples.Quotient
open Finset

private lemma StarField_add_self_zero {k : ℕ} (z : Group k) : z + z = 0 := by
  ext i
  change z i + z i = 0
  have hh : (2 : ZMod 2) = 0 := ZMod.natCast_self 2
  calc
    z i + z i = 2 * z i := by ring
    _ = 0 := by rw [hh, zero_mul]

private lemma StarField_add_eq_zero_iff_eq {k : ℕ} (z a : Group k) : z + a = 0 ↔ a = z := by
  constructor
  · intro h
    have hh := congrArg (fun t => z + t) h
    simpa only [← add_assoc, StarField_add_self_zero, zero_add, add_zero] using hh
  · rintro rfl
    exact StarField_add_self_zero _

lemma sum_by_label {n k : ℕ} (label : Fin n → Group k) (w : Group k → ℝ)
    (hcount : ∀ a, (∑ i : Fin n, if label i = a then (1 : ℝ) else 0) = w a)
    (g : Group k → ℝ) :
    (∑ i, g (label i)) = ∑ a, w a * g a := by
  classical
  calc
    _ = ∑ i : Fin n, ∑ a : Group k, if label i = a then g a else 0 := by
      apply Finset.sum_congr rfl
      intro i _
      simp
    _ = ∑ a : Group k, ∑ i : Fin n, if label i = a then g a else 0 := Finset.sum_comm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro a _
      rw [← hcount, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro i _
      split_ifs <;> simp

noncomputable def starField {n k : ℕ} (label : Fin n → Group k)
    (w q : Group k → ℝ) (x : Cube n) (i : Fin n) : ℝ :=
  if projection label x = 0 then -q (label i) / w (label i) else 0

lemma starField_div {n k : ℕ} (label : Fin n → Group k) (w q : Group k → ℝ)
    (hnonzero : ∀ i, label i ≠ 0)
    (hcount : ∀ a, (∑ i : Fin n, if label i = a then (1 : ℝ) else 0) = w a)
    (hw : ∀ a ≠ 0, w a ≠ 0) (hq : ∑ a, q a = 0) (x : Cube n) :
    (∑ i, (starField label w q x i - starField label w q (flip x i) i)) =
      q (projection label x) := by
  classical
  by_cases hx : projection label x = 0
  · have hf (i : Fin n) : projection label (flip x i) ≠ 0 := by
      simpa [projection_flip, hx] using hnonzero i
    simp only [starField, hx, ↓reduceIte, hf, sub_zero]
    rw [sum_by_label label w hcount (fun a => -q a / w a)]
    have hterm (a : Group k) : w a * (-q a / w a) = if a = 0 then 0 else -q a := by
      by_cases ha : a = 0
      · subst a
        have hw0 : w 0 = 0 := by
          rw [← hcount]
          simp [hnonzero]
        simp [hw0]
      · simp only [ha, ↓reduceIte]
        field_simp [hw a ha]
    simp_rw [hterm]
    have hsum : (∑ a : Group k, if a = 0 then (0 : ℝ) else -q a) = q 0 := by
      have hh : (∑ a : Group k, -q a) = 0 := by simp [hq]
      have hsplit : (∑ a : Group k, -q a) =
          -q 0 + ∑ a : Group k, if a = 0 then (0 : ℝ) else -q a := by
        rw [← Finset.sum_erase_add _ _ (Finset.mem_univ (0 : Group k))]
        simp [Finset.sum_ite, Finset.filter_ne', add_comm]
      linarith
    exact hsum
  · have hneighbor (i : Fin n) : projection label (flip x i) = 0 ↔
        label i = projection label x := by
      rw [projection_flip, StarField_add_eq_zero_iff_eq]
    simp only [starField, hx, ↓reduceIte, hneighbor, zero_sub]
    have hterm (i : Fin n) :
        -(if label i = projection label x then -q (label i) / w (label i) else 0) =
          (if label i = projection label x then (1 : ℝ) else 0) *
            (q (projection label x) / w (projection label x)) := by
      split_ifs with hi
      · simp only [hi, one_mul]; ring
      · simp
    simp_rw [hterm]
    rw [← Finset.sum_mul, hcount]
    field_simp [hw _ hx]

lemma starField_cost {n k : ℕ} (label : Fin n → Group k) (w q : Group k → ℝ)
    (hsurj : Function.Surjective (projection label)) :
    cost (starField label w q) =
      Real.sqrt (∑ i, (q (label i) / w (label i)) ^ 2) / (2 : ℝ) ^ k := by
  classical
  unfold cost
  have hp (x : Cube n) :
      Real.sqrt (∑ i, starField label w q x i ^ 2) =
        if projection label x = 0 then
          Real.sqrt (∑ i, (q (label i) / w (label i)) ^ 2) else 0 := by
    by_cases hx : projection label x = 0
    · simp only [starField, hx, ↓reduceIte]
      congr 1
      apply Finset.sum_congr rfl
      intro i _
      ring
    · simp [starField, hx]
  simp_rw [hp]
  rw [avg_projection label hsurj (fun z => if z = 0 then
    Real.sqrt (∑ i, (q (label i) / w (label i)) ^ 2) else 0)]
  simp

lemma starField_energy {n k : ℕ} (label : Fin n → Group k) (w q : Group k → ℝ)
    (hnonzero : ∀ i, label i ≠ 0)
    (hcount : ∀ a, (∑ i : Fin n, if label i = a then (1 : ℝ) else 0) = w a)
    (hw : ∀ a ≠ 0, w a ≠ 0) :
    (∑ i, (q (label i) / w (label i)) ^ 2) =
      ∑ a, if a = 0 then 0 else q a ^ 2 / w a := by
  classical
  rw [sum_by_label label w hcount (fun a => (q a / w a)^2)]
  apply Finset.sum_congr rfl
  intro a _
  by_cases ha : a = 0
  · subst a
    have hw0 : w 0 = 0 := by rw [← hcount]; simp [hnonzero]
    simp [hw0]
  · simp only [ha, ↓reduceIte]
    field_simp [hw a ha]

lemma beckmann_le_star {n k : ℕ} (label : Fin n → Group k) (w q : Group k → ℝ)
    (f : Cube n → Bool)
    (hnonzero : ∀ i, label i ≠ 0)
    (hcount : ∀ a, (∑ i : Fin n, if label i = a then (1 : ℝ) else 0) = w a)
    (hw : ∀ a ≠ 0, w a ≠ 0) (hq : ∑ a, q a = 0)
    (hsurj : Function.Surjective (projection label))
    (hcharge : ∀ x, (∑ i, (sign f x - sign f (flip x i)) / 2) =
      q (projection label x)) :
    beckmann f ≤
      Real.sqrt (∑ a, if a = 0 then 0 else q a ^ 2 / w a) / (2 : ℝ) ^ k := by
  have hfeas (x : Cube n) :
      (∑ i, (starField label w q x i - starField label w q (flip x i) i)) =
        ∑ i, (sign f x - sign f (flip x i)) / 2 := by
    rw [starField_div label w q hnonzero hcount hw hq, hcharge]
  have hupper : beckmann f ≤ cost (starField label w q) :=
    csInf_le (beckmann_bddBelow f) ⟨starField label w q, rfl, hfeas⟩
  rw [starField_cost label w q hsurj,
    starField_energy label w q hnonzero hcount hw] at hupper
  exact hupper

noncomputable def quotientCharge {k : ℕ} (w g : Group k → ℝ) (z : Group k) : ℝ :=
  ∑ a, w a * (g z - g (z + a)) / 2

lemma quotientCharge_sum {k : ℕ} (w g : Group k → ℝ) :
    ∑ z, quotientCharge w g z = 0 := by
  classical
  unfold quotientCharge
  rw [Finset.sum_comm]
  apply Finset.sum_eq_zero
  intro a _
  have htranslation : (∑ z, g (z + a)) = ∑ z, g z := by
    exact Fintype.sum_bijective (fun z : Group k => z + a)
      (Function.Involutive.bijective (fun z => by rw [add_assoc, StarField_add_self_zero, add_zero]))
      _ _ (fun _ => rfl)
  rw [← Finset.sum_div, ← Finset.mul_sum, Finset.sum_sub_distrib, htranslation]
  ring

lemma quotientCharge_laplacian {n k : ℕ} (label : Fin n → Group k)
    (w g : Group k → ℝ) (f : Cube n → Bool)
    (hcount : ∀ a, (∑ i : Fin n, if label i = a then (1 : ℝ) else 0) = w a)
    (hf : ∀ x, sign f x = g (projection label x)) (x : Cube n) :
    (∑ i, (sign f x - sign f (flip x i)) / 2) =
      quotientCharge w g (projection label x) := by
  simp_rw [hf, projection_flip]
  rw [sum_by_label label w hcount (fun a =>
    (g (projection label x) - g (projection label x + a)) / 2)]
  unfold quotientCharge
  apply Finset.sum_congr rfl
  intro a _
  ring

end BeckmannExamples.Quotient


/- Supporting component: StarEstimate -/
namespace BeckmannExamples.Quotient

lemma star_energy_bound {k : ℕ} (q : Group k → ℝ)
    (hq : ∀ a, a ≠ 0 → |q a| ≤ (4 / 3 : ℝ) * 2 ^ (k - level a) * 8 ^ level a) :
    (∑ a : Group k, if a ≠ 0 then q a ^ 2 / (multiplicity a : ℝ) else 0) ≤
      (16 / 9 : ℝ) * k * ((2 : ℝ) ^ k) ^ 3 := by
  classical
  calc
    _ ≤ ∑ a : Group k, if a ≠ 0 then
        (16 / 9 : ℝ) * (2 ^ (k - level a)) ^ 2 * 8 ^ level a else 0 := by
      apply Finset.sum_le_sum
      intro a _
      by_cases ha : a = 0
      · simp [ha]
      · rw [if_pos ha, if_pos ha]
        have hsq : q a ^ 2 ≤ ((4 / 3 : ℝ) * 2 ^ (k - level a) * 8 ^ level a) ^ 2 := by
          have hh := pow_le_pow_left₀ (abs_nonneg (q a)) (hq a ha) 2
          simpa using hh
        calc
          _ ≤ ((4 / 3 : ℝ) * 2 ^ (k - level a) * 8 ^ level a) ^ 2 /
              (multiplicity a : ℝ) := div_le_div_of_nonneg_right hsq (by positivity)
          _ = _ := by
            simp only [multiplicity, Nat.cast_pow, Nat.cast_ofNat]
            field_simp
            <;> ring
    _ = ∑ j : Fin k, (2:ℝ)^(k-j.val-1) *
        ((16 / 9 : ℝ) * (2 ^ (k - (j.val + 1))) ^ 2 * 8 ^ (j.val + 1)) :=
      weighted_layer_sum (k:=k) (fun r => (16 / 9 : ℝ) * (2 ^ (k-r)) ^ 2 * 8 ^ r)
    _ = ∑ _j : Fin k, (16 / 9 : ℝ) * ((2 : ℝ) ^ k) ^ 3 := by
      apply Finset.sum_congr rfl
      intro j _
      have hm : ((2:ℝ) ^ (k - (j.val+1))) ^ 3 * 8 ^ (j.val+1) =
          ((2:ℝ)^k)^3 := by
        have hn := mass_cube_identity k j.val j.isLt
        have hh : ((2:ℝ) ^ (k - (j.val+1))) ^ 3 * 8 ^ (j.val+1) =
            (2:ℝ)^(3*k) := by exact_mod_cast hn
        rw [hh]
        rw [← pow_mul]
        congr 1
        omega
      rw [Nat.sub_sub]
      calc
        _ = (16 / 9 : ℝ) * (((2:ℝ) ^ (k - (j.val+1))) ^ 3 * 8 ^ (j.val+1)) := by ring
        _ = _ := by rw [hm]
    _ = _ := by simp; ring

lemma star_cost_of_energy_bound {k : ℕ} {E : ℝ}
    (hE : E ≤ (16 / 9 : ℝ) * k * ((2:ℝ)^k)^3) :
    Real.sqrt E / (2:ℝ)^k ≤ (4 / 3 : ℝ) * Real.sqrt k * Real.sqrt ((2:ℝ)^k) := by
  apply (div_le_iff₀ (show 0 < (2:ℝ)^k by positivity)).2
  apply Real.sqrt_le_iff.mpr
  refine ⟨by positivity, ?_⟩
  calc
    E ≤ (16 / 9 : ℝ) * k * ((2:ℝ)^k)^3 := hE
    _ = ((4 / 3 : ℝ) * Real.sqrt k * Real.sqrt ((2:ℝ)^k) * (2:ℝ)^k)^2 := by
      rw [mul_pow, mul_pow, mul_pow, Real.sq_sqrt (by positivity), Real.sq_sqrt (by positivity)]
      ring

lemma star_cost_bound_of_charge_bound {k : ℕ} (q : Group k → ℝ)
    (hq : ∀ a, a ≠ 0 → |q a| ≤ (4 / 3 : ℝ) * 2 ^ (k - level a) * 8 ^ level a) :
    Real.sqrt (∑ a : Group k, if a ≠ 0 then q a ^ 2 / (multiplicity a : ℝ) else 0) /
      (2:ℝ)^k ≤ (4 / 3 : ℝ) * Real.sqrt k * Real.sqrt ((2:ℝ)^k) :=
  star_cost_of_energy_bound (star_energy_bound q hq)

end BeckmannExamples.Quotient


/- Supporting component: Upper -/
namespace BeckmannExamples.Quotient

noncomputable def canonicalWeight {k : ℕ} (a : Group k) : ℝ :=
  if a = 0 then 0 else (multiplicity a : ℝ)

lemma charge_eq_quotientCharge {k : ℕ} (z : Group k) :
    charge z = quotientCharge canonicalWeight quotientSign z := by
  classical
  unfold charge quotientCharge
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  by_cases ha : a = 0
  · simp [canonicalWeight, ha]
  · simp only [canonicalWeight, ha, ↓reduceIte]
    ring

lemma example_charge (k : ℕ) (x : Cube (Fintype.card (Coordinate k))) :
    (∑ i, (sign (exampleFunction k) x - sign (exampleFunction k) (flip x i)) / 2) =
      charge (projection (canonicalLabel k) x) := by
  rw [charge_eq_quotientCharge]
  exact quotientCharge_laplacian (canonicalLabel k) canonicalWeight quotientSign
    (exampleFunction k) (canonicalLabel_count k) (fun _ => rfl) x

lemma example_beckmann_le_energy (k : ℕ) :
    beckmann (exampleFunction k) ≤
      Real.sqrt (∑ a : Group k, if a = 0 then 0 else charge a ^ 2 / (multiplicity a : ℝ)) /
        (2 : ℝ)^k := by
  have hw : ∀ a : Group k, a ≠ 0 → canonicalWeight a ≠ 0 := by
    intro a ha
    simp only [canonicalWeight, ha, ↓reduceIte]
    unfold multiplicity
    positivity
  have hb := beckmann_le_star (canonicalLabel k) canonicalWeight charge (exampleFunction k)
    (canonicalLabel_ne_zero k) (canonicalLabel_count k) hw sum_charge
    (canonical_projection_surjective k) (example_charge k)
  convert hb using 1
  congr 2
  apply Finset.sum_congr rfl
  intro a _
  by_cases ha : a = 0 <;> simp [canonicalWeight, ha]

lemma example_beckmann_upper (k : ℕ) :
    beckmann (exampleFunction k) ≤
      (4 / 3 : ℝ) * Real.sqrt k * Real.sqrt ((2:ℝ)^k) := by
  have hq : ∀ a : Group k, a ≠ 0 →
      |charge a| ≤ (4 / 3 : ℝ) * 2 ^ (k - level a) * 8 ^ level a := by
    intro a ha
    simpa [levelMass, level_le_dimension a ha, multiplicity] using charge_degree_bound a ha
  have hb := star_cost_bound_of_charge_bound charge hq
  have he : (∑ a : Group k, if a = 0 then 0 else charge a ^ 2 / (multiplicity a : ℝ)) =
      ∑ a : Group k, if a ≠ 0 then charge a ^ 2 / (multiplicity a : ℝ) else 0 := by
    apply Finset.sum_congr rfl
    intro a _
    by_cases ha : a = 0 <;> simp [ha]
  have hc := example_beckmann_le_energy k
  rw [he] at hc
  exact hc.trans hb

end BeckmannExamples.Quotient


/- Supporting component: PackingSupport -/
namespace BeckmannExamples.Quotient

lemma selectedWeight_zero_of_alternating_eq {k : ℕ} (z y : Group k)
    (h : alternating z = alternating y) : selectedWeight z y = 0 := by
  unfold selectedWeight
  dsimp only
  split_ifs with hadj
  · have hp : Even (level z) ↔ Even (level y) := by
      simpa only [alternating, decide_eq_decide] using h
    have hlevels : level z + 1 = level y ∨ level y + 1 = level z := by omega
    rcases hlevels with hzy | hyz
    · rw [← hzy, Nat.even_add_one] at hp
      exact False.elim (not_iff_self hp.symm)
    · rw [← hyz, Nat.even_add_one] at hp
      exact False.elim (not_iff_self hp)
  · rfl

end BeckmannExamples.Quotient


/- Supporting component: Packing -/
namespace BeckmannExamples.Quotient

noncomputable def outgoing {k : ℕ} (z y : Group k) : ℝ :=
  if level y = level z + 1 then packingLambda k (level z) else 0

lemma selectedWeight_split {k : ℕ} (z y : Group k) :
    selectedWeight z y = outgoing z y + outgoing y z := by
  unfold selectedWeight outgoing
  dsimp only
  rcases le_total (level z) (level y) with h | h
  · rw [min_eq_left h, max_eq_right h]
    have hn : level z ≠ level y + 1 := by omega
    simp [hn]
  · rw [min_eq_right h, max_eq_left h]
    have hn : level y ≠ level z + 1 := by omega
    simp [hn]

lemma outgoing_sum {k : ℕ} (z : Group k) :
    (∑ i, outgoing z (z + canonicalLabel k i)) =
      if level z ≤ k then levelMass k (level z + 1) * (8 : ℝ)^level z *
        packingLambda k (level z) else 0 := by
  classical
  unfold outgoing
  by_cases h : level z ≤ k
  · rw [if_pos h]
    have he := directions_to_level z (level z+1) (by omega) (by omega) (by omega)
    calc
      _ = (∑ i, if level (z+canonicalLabel k i) = level z+1 then (1:ℝ) else 0) *
          packingLambda k (level z) := by rw [Finset.sum_mul]; congr 1; ext i; split_ifs <;> simp
      _ = _ := by rw [he, min_eq_left (by omega)]
  · rw [if_neg h]
    apply Finset.sum_eq_zero
    intro i _
    have hz := (level_bounds (z+canonicalLabel k i)).2
    simp [show level (z+canonicalLabel k i) ≠ level z+1 by omega]

lemma outgoing_total (k : ℕ) :
    (∑ z : Group k, ∑ i, outgoing z (z + canonicalLabel k i)) =
      ∑ r ∈ Finset.range k, levelMass k (r+1) * levelMass k (r+2) *
        (8:ℝ)^(r+1) * packingLambda k (r+1) := by
  classical
  simp_rw [outgoing_sum]
  have hh (z : Group k) :
      (if level z ≤ k then levelMass k (level z+1) * (8:ℝ)^level z * packingLambda k (level z) else 0) =
      if z ≠ 0 then levelMass k (level z+1) * (8:ℝ)^level z * packingLambda k (level z) else 0 := by
    by_cases hz : z=0
    · simp [hz, level_zero]
    · simp [hz, level_le_dimension z hz]
  simp_rw [hh]
  rw [weighted_layer_sum (fun t => levelMass k (t+1) * (8:ℝ)^t * packingLambda k t)]
  rw [Fin.sum_univ_eq_sum_range (fun j => (2:ℝ)^(k-j-1) * (levelMass k (j+1+1) * (8:ℝ)^(j+1) * packingLambda k (j+1)))]
  apply Finset.sum_congr rfl
  intro r hr
  have h : r < k := Finset.mem_range.mp hr
  have hm : levelMass k (r+1) = (2:ℝ)^(k-(r+1)) := by simp [levelMass, show r+1 ≤ k by omega]
  rw [hm]
  simp only [Nat.sub_sub, Nat.add_assoc]
  ring

lemma packing_average (k : ℕ) :
    avg (fun x => ∑ i, selectedWeight (projection (canonicalLabel k) x)
      (projection (canonicalLabel k) (flip x i))) / 2 =
    (∑ r ∈ Finset.range k, levelMass k (r+1) * levelMass k (r+2) *
      (8:ℝ)^(r+1) * packingLambda k (r+1)) / (2:ℝ)^k := by
  have hsurj := projection_surjective_of_labels (canonicalLabel k) (canonicalLabel_covers k)
  have hrev : (∑ x, ∑ i, outgoing (projection (canonicalLabel k) (flip x i))
      (projection (canonicalLabel k) x)) =
      ∑ x, ∑ i, outgoing (projection (canonicalLabel k) x)
      (projection (canonicalLabel k) (flip x i)) := by
    conv_lhs => rw [Finset.sum_comm]
    conv_rhs => rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    simpa only [flip_flip] using sum_flip (fun x =>
      outgoing (projection (canonicalLabel k) x) (projection (canonicalLabel k) (flip x i))) i
  have ha : avg (fun x => ∑ i, selectedWeight (projection (canonicalLabel k) x)
      (projection (canonicalLabel k) (flip x i))) / 2 =
      avg (fun x => ∑ i, outgoing (projection (canonicalLabel k) x)
        (projection (canonicalLabel k) (flip x i))) := by
    simp only [avg, selectedWeight_split, Finset.sum_add_distrib]
    rw [hrev]
    ring
  rw [ha]
  simp_rw [projection_flip]
  rw [avg_projection _ hsurj (fun z => ∑ i, outgoing z (z + canonicalLabel k i)), outgoing_total]

lemma example_fractional_lower (k : ℕ) :
    (k:ℝ) / Real.sqrt 6 * Real.sqrt ((2:ℝ)^k) ≤ fractional (exampleFunction k) := by
  let w := fun x i => selectedWeight (projection (canonicalLabel k) x)
      (projection (canonicalLabel k) (flip x i))
  have hp := fractional_packing (exampleFunction k) w
    (fun x i => by dsimp [w]; rw [flip_flip, selectedWeight_symm])
    (fun x i h => selectedWeight_zero_of_alternating_eq _ _ h)
    (fun x => by
      dsimp [w]
      simp_rw [projection_flip]
      exact selectedWeight_sq_sum_le _)
  have he := packing_average k
  change avg (fun x => ∑ i, w x i) / 2 = _ at he
  rw [he] at hp
  exact (packing_sum_lower k).trans hp

end BeckmannExamples.Quotient


namespace BeckmannExamples

/-- Theorem 5.5 with the approved dimension, constants and both optimized boundaries. -/
theorem theorem_5_5 (k : ℕ) (hk : 1 ≤ k) :
    ∃ f : Cube (dimension k) → Bool,
      0 < beckmann f ∧
      (3 / (4 * Real.sqrt 6)) * Real.sqrt k ≤ fractional f / beckmann f ∧
      (3 / (4 * Real.sqrt 6)) * Real.sqrt k ≤ colored f / beckmann f := by
  rw [← Quotient.card_coordinate k]
  have hB := Quotient.exampleFunction_beckmann_pos k hk
  have hupper := Quotient.example_beckmann_upper k
  have hlower := Quotient.example_fractional_lower k
  have hratio := separation_ratio hB hupper hlower
  refine ⟨Quotient.exampleFunction k, hB, hratio, ?_⟩
  exact hratio.trans (div_le_div_of_nonneg_right (fractional_le_colored _) hB.le)

end BeckmannExamples

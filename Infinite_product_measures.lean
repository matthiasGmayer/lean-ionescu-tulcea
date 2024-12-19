/- It is fine to import all of Mathlib in your project.
This might make the loading time of a file a bit longer. If you want a good chunk of Mathlib, but not everything, you can `import Mathlib.Tactic` and then add more imports as necessary. -/
import IonescuTulcea
import Mathlib
-- import Mathlib.MeasureTheory.Measure.ProbabilityMeasure

set_option autoImplicit true
/- open namespaces that you use to shorten names and enable notation. -/
open Function Set Classical

/- recommended whenever you define anything new. -/
noncomputable section


/- Now write definitions and theorems. -/

namespace ProductProbabilityMeasure
open MeasureTheory MeasurableSpace Measurable ProductLike



variable {I : Type*}
variable (Ω : ∀(i : I), Type*)
variable [∀i, MeasurableSpace (Ω i)]
variable (J : Set I)
variable (JF : Finset I)

instance : (i : JF) -> MeasurableSpace (JF.restrict Ω i) := by {
  intro i
  rw [show JF.restrict Ω i = Ω i by rfl]
  infer_instance
}
instance : ∀(i : J), MeasurableSpace (J.restrict Ω i) := by {
  intro i
  rw [show J.restrict Ω i = Ω i by rfl]
  infer_instance
}
-- ×_(i ∈ I) Ω_i
abbrev ProductSpace := (i: I) -> Ω i


-- def π (i : I) (ω : ProductSpace Ω) := ω i
def π (J : Set I) : ProductSpace Ω  -> ProductSpace (J.restrict Ω) :=
  fun ω => J.restrict ω

-- variable (i : I)
-- #check π Ω {i}

lemma pi_measurable (J : Set I) : Measurable (π Ω J) := by {
    exact measurable_restrict J
}

-- Ionescu-Tulcea
open ProbabilityMeasure

-- theorem finite_product {I : Type*} [Fintype I] (Ω : I -> Type*) [∀i, MeasurableSpace (Ω i)]
--   (P : (i : I) -> ProbabilityMeasure (Ω i)) :
--   ∃! ℙ : ProbabilityMeasure (ProductSpace Ω), ∀A : (i : I) -> Set (Ω i),
--   ℙ {a : a i ∈ A i} = Π (i : I), P i (A i) := sorry

open ProbabilityTheory
def measurable_equivalence_singleton_product {I : Type*} (α : I -> Type*) (i : I) [∀m, MeasurableSpace (α m)]
  : (∀(j : ({i} : Set I)), α j) ≃ᵐ α i
  := MeasurableEquiv.piUnique (δ' := ({i} : Set I)) (π := fun x => α ↑x)


/- There is no 1 in kernel composition, n=0 means choose first kernel -/
def FiniteCompKernelNat
  (n : ℕ)
  {α : ℕ -> Type*}
  [∀m, MeasurableSpace (α m)]
  (K : ∀m, Kernel (∀k: {k|k <= m}, α k) (α (m+1)))
  : Kernel (α 0) (∀k : {k|0 < k ∧ k <= n+1}, α k) :=
  if hn : n = 0 then
    by {
      let K' := K 0
      rw [show {k | k <= 0} = {0} by {
        ext; simp [hn]
      }] at K'
      simp at K'
      have h : {k | 0 < k ∧ k <= n + 1} = {1} := by ext; simp [hn]; omega
      rw [h]
      let K'' := change_right K' (measurable_equivalence_singleton_product α 1).symm
      exact change_left K'' (measurable_equivalence_singleton_product α 0)
      }
  else
    by {
    let n₀ := n - 1
    have hn₀ : n₀ + 1 = n := Nat.succ_pred_eq_of_ne_zero hn
    let K₀ := FiniteCompKernelNat n₀ K
    let K₁ := K n
    simp only [mem_setOf_eq] at K₀
    rw [hn₀] at K₀
    have h : {k | k <= n} = {0} ∪ {k | 0 < k ∧ k <= n} := by ext; simp; omega
    rw [h] at K₁
    have h₀ : Fact (0 ∉ {k : ℕ | 0 < k ∧ k <= n}) := ⟨by simp⟩
    have h₁ : Fact (n+1 ∉ {k : ℕ | 0 < k ∧ k <= n}) := ⟨by simp⟩
    let q : ProdLikeM ((k : ↑{k | 0 < k ∧ k ≤ n + 1}) → α ↑k) ((k : ↑{k | 0 < k ∧ k ≤ n}) → α ↑k) (α (n + 1)) := by {
      rw [show {k| 0 < k ∧ k <= n + 1} = {k | 0 < k ∧ k <= n} ∪ {n+1} by ext; simp; omega]
      infer_instance
    }
    exact compProd K₀ K₁
    }


def ProductProbabilityMeasure  {I : Type*} [Fintype I] {Ω : I -> Type*}
[∀i, MeasurableSpace (Ω i)] (P : (i : I) -> ProbabilityMeasure (Ω i)) :
  ProbabilityMeasure (ProductSpace Ω) := sorry


theorem existence_infinite_product_probability_measure :
∀(P : (i : I) -> ProbabilityMeasure (Ω i)),
  ∃! PP : ProbabilityMeasure (ProductSpace Ω), ∀(J : Finset I),
   ProbabilityMeasure.map ℙ (aemeasurable (measurable_restrict J))
    = ProductProbabilityMeasure (J.restrict P) := by {
      sorry
  }








  --  (show AEMeasurable (π Ω J) (μ := ↑ℙ)
  --  by {
  --   -- exact aemeasurable (pi_measurable Ω J)
  --   exact aemeasurable (measurable_restrict (J : Set I))
  --   }
    -- )

-/

import IonescuTulcea
import IonescuTulcea.Infinite_product_measures
-- import IonescuTulcea.finiteCompProd
-- import IonescuTulcea.finiteCompProdProps
-- import IonescuTulcea.strong_rec
import Mathlib
-- import Mathlib.MeasureTheory.Measure.ProbabilityMeasure

set_option autoImplicit true
/- open namespaces that you use to shorten names and enable notation. -/
open Function Set Classical ENNReal ProductProbabilityMeasure IndexedFamilies

/- recommended whenever you define anything new. -/
open Filter Topology
noncomputable section


/- Now write definitions and theorems. -/

open MeasureTheory MeasurableSpace Measurable ProductLike ProductProbabilityMeasure

-- Ionescu-Tulcea
open ProbabilityMeasure Measure ProductLike

open ProbabilityTheory ENNReal



-- Measures
#check MeasurableSpace
#check Measure
#check IsProbabilityMeasure

-- Kernels
#check Kernel
#check IsMarkovKernel

-- Compositional Product
#check Measure.compProd
#check Kernel.compProd

-- Defining properties
#check Measure.lintegral_compProd
#check Kernel.lintegral_compProd

section Definitions
variable {α₁ α₂ α₃ : Type*} [MeasurableSpace α₁] [MeasurableSpace α₂] [MeasurableSpace α₃]
variable (μ : Measure α₁) (K : Kernel α₁ α₂) (L : Kernel (α₁ × α₂) α₃)
#check μ ⊗ₘ K
#check K ⊗ₖ L

variable [IsProbabilityMeasure μ] [IsMarkovKernel K] [IsMarkovKernel L]
variable (f₁₂ : α₁ × α₂ → ℝ≥0∞) (hf₁₂ : Measurable f₁₂)
#check Measure.lintegral_compProd (κ := K) (μ := μ) (hf₁₂)

variable (a₁ : α₁) (f₂₃ : α₂ × α₃ → ℝ≥0∞) (hf₂₃ : Measurable f₂₃)
#check Kernel.lintegral_compProd K L a₁ hf₂₃

end Definitions

section Products


variable (α : ℕ -> Type*) [∀n, MeasurableSpace (α n)]
variable (n : ℕ)
-- ×_(k ∈ ℕ) α_k
#check ∀k : ℕ, α k
#check ∀k : {k // k <= n}, α k
-- We introduce an abreviation for ×_(k<=n) α_k
#check ⇑α {k|k<=n}
#check simp% (⇑α {k|k <= n})

variable (μ : Measure (α 0))
variable (K : (n : ℕ) -> Kernel (⇑α {k|k <= n}) (α (n+1)))
-- The Mathlib product is not general enough
#check μ ⊗ₘ (K 0)
#check K 0
#check α 0
#check simp% (⇑α {k|k<=0})

-- We can define types that behave like products
#check ProdLikeM
-- We can then define a general product
#check compProd'
-- We define a coercion between canonically equivalent types
#check convert_measure

-- We can now define a finite product
#check (convert_measure μ : Measure (⇑α {k|k<=0})) ⊗ₘ' (K 0)
#check (convert_measure μ : Measure (⇑α {k|k<=0})) ⊗ₘ' (K 0) ⊗ₘ' (K 1)
#check (convert_measure μ : Measure (⇑α {k|k<=0})) ⊗ₘ' (K 0) ⊗ₘ' (K 1) ⊗ₘ' (K 2)


#check FiniteCompMeasureKernelNat
#check FiniteCompKernelNat

-- For Ionescu-Tulcea, we need Carathedory's extension theorem
-- Mathlib has a specific version
#check OuterMeasure.toMeasure

-- We need a more specific version using a content
-- Mathlib does not define a content standardly,
-- only on compact sets in a topological space
#check Content

-- There is a weaker version, that is too general
-- since it doesn't require set algebra
#check AddContent

-- we can use hypothesis to ensure C is a set algebra and
-- get Caratheodorys extension theorem
#check AddContent.toMeasure


-- Now we only have to prove that cylinders are a setalgebra
#check cylinders
#check cylinders_SetAlgebra

-- We can now define a content on the cylinders
#check MeasureKernelSequenceContent

#check MeasureKernelSequenceContentSAdditive

-- We use a very strong recursion in the proof for sequences
#check strong_rec_on_nat

end Products

-- Notable difficulties when working with indexed families
section Difficulties
variable {α : ℕ -> Type*} [∀n, MeasurableSpace (α n)]

variable {n m: ℕ} (hnm : n = m)
variable (x : α n) (y : α m)
#check x = y
example : HEq x y := by {
  -- rw [hnm]
  subst hnm
  simp
}

def x_cast := by {
  rw [hnm] at x
  exact x
}
#check x_cast
#check x = x_cast hnm x

example : HEq x (x_cast hnm x) := by {
  unfold x_cast
  simp
  exact?
}
-- It is difficult to find lemmas

-- A lot of simple measurability proofs. measurability tactic does not find it and is very slow if it does.
#check assoc_compProd'_kernel_compProd'
-- This happens because rewrite lemmas use measurability assumptions that get turned into goals.


end Difficulties

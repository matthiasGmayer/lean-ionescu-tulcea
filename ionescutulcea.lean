import IonescuTulcea
import Mathlib
-- import Mathlib.MeasureTheory.Measure.ProbabilityMeasure

set_option autoImplicit true
/- open namespaces that you use to shorten names and enable notation. -/
open Function Set Classical ENNReal

/- recommended whenever you define anything new. -/
noncomputable section


/- Now write definitions and theorems. -/

namespace ProductProbabilityMeasure
open MeasureTheory MeasurableSpace Measurable ProductLike

-- Ionescu-Tulcea
open ProbabilityMeasure Measure ProductLike

open ProbabilityTheory
open Filter Topology

-- open IonescuTulcea
open ProductProbabilityMeasure


variable
  {α : ℕ -> Type*}
  [∀m, MeasurableSpace (α m)]
  [∀m, Inhabited (α m)]
  (μ : Measure (α 0))
  [hμ : IsProbabilityMeasure μ]
  (K : ∀m, Kernel (∀k: {k|k <= m}, α k) (α (m+1)))
  [hK : ∀n, IsMarkovKernel (K n)]
  (B : (n : ℕ) -> Set (∀k, α k))
  (hBcyl : ∀n, (B n) ∈ cylinder_n α n)
  (hBmono : ∀n, B n ⊇ B (n+1))
  (hBemp : ⋂n, B n = ∅)

def test := Tendsto (fun n => MeasureKernelSequenceContent μ K (B n)) atTop (𝓝 0)

      intro B hB hmono hempsect
      by_contra hcontra
      let A n := choose (hB n)
      have hAB n : {k|k<=n}.restrict ⁻¹' A n = B n := sorry
      have hABμ n: MeasureKernelSequenceContent μ K (B n)
        = FiniteCompMeasureKernelNat μ K n (A n) := sorry

      have hinf : ⨅ n, MeasureKernelSequenceContent μ K (B n) > 0 := sorry

      suffices ∃ω, ∀n, ({k|k<=n}.restrict ω) ∈ A (n) by {
        obtain ⟨ω,hω⟩ := this
        have inB : ω ∈ ⋂n, B n := by {
          simp
          intro n
          specialize hω n
          rw [<- hAB]
          simp
          assumption
        }
        rw [hempsect] at inB
        contradiction
      }

      -- let
      -- let Q n m ω' := sorry
      -- #check (Kernel.compProd' (K 2) (K 3) : Kernel _ {k | 1 <= k ∧ k <= 2})
      -- #check fun n m => FiniteCompKernelNat K n m
      -- #check fun n => shift K n
      let Q n m := FiniteCompKernelNat K n m
      #check Q
      #check kernel_slice
      let p n m : ProdLikeM _ _ _ := ⟨equiv_4 (α := α) n (n + m + 1) (by omega)⟩
      let f n m := kernel_slice (Q n (n + m)) (A (n + m + 1))
        (p := p n m)


      have hAmem n ω : ω ∈ A (n + 1) -> {k|k<=n}.restrict₂ (by simp; omega) ω ∈ A n := by {
        unfold A
        generalize_proofs h1 h2 h3
        intro h
        -- simp at h1 h2
        obtain ⟨h1m,h1s⟩ := choose_spec h1
        obtain ⟨h2m,h2s⟩ := choose_spec h2
        simp only at h1s h2s

        have hhh : ∃ω' , {k | k <= n + 1}.restrict ω' = ω := by exact Subtype.exists_pi_extension ω
        let ω' := choose hhh
        have hω' : ω' ∈ B (n + 1) := by {
          rw [<- h1s]
          simp
          rw [choose_spec hhh]
          exact h
        }
        specialize hmono n hω'
        rw [<- h2s] at hmono
        simp at hmono

        have hhhh : {k | k<=n}.restrict ω' = {k | k <= n}.restrict₂ (by simp;omega) ω := by {
          rw [<- choose_spec hhh]
          simp
          unfold ω'
          exact rfl
        }
        rw [<- hhhh]
        assumption
      }

      have hf n ω : f n 0 ω > 0 -> ω ∈ A n := by {
        unfold f
        simp
        intro h
        rw [show kernel_slice (Q n n) (A (n + 1)) (p := p n 0) ω = ((Q n n) ω)
          ((p n 0).slice (A (n + 1)) ω) from rfl] at h
        rw [show (p n 0).slice (A (n + 1)) ω = {b | (p n 0).equiv.symm (ω, b) ∈ A (n + 1)} from rfl] at h
        simp at h
        have h : {b | (p n 0).equiv.symm (ω, b) ∈ A (n + 1)} ≠ ∅ := by {
          by_contra hh
          simp only [Nat.add_zero, coe_setOf, mem_setOf_eq] at hh -- Why do i need this
          rw [hh] at h
          simp at h
        }
        let hnon : Nonempty {b | (p n 0).equiv.symm (ω,b) ∈ A (n+1)} := by exact nonempty_iff_ne_empty'.mpr h
        let ⟨b,hb⟩ := hnon.some
        let ω' := (p n 0).equiv.symm (ω, b)
        have hω' : ω' ∈ A (n+1) := by exact hb
        specialize hAmem n ω' hω'
        generalize_proofs hgg at hAmem
        rw [show restrict₂ hgg ω' = ω by unfold ω'; {
          ext i
          simp
          unfold ProdLikeM.equiv
          unfold p equiv_4
          let hi : (i : ℕ) <= n := i.2
          simp [hi]
          rfl
        }] at hAmem
        assumption
      }

      suffices ∃ω, ∀n, ⨅m, f n m ({k|k<=n}.restrict ω) > 0 by {
        obtain ⟨ω, hω⟩ := this
        use ω
        intro n
        specialize hω n
        have h : f n 0 (({k | k <= n}).restrict ω) > 0 := by {
          calc 0 < ⨅m, f n m ({k|k<=n}.restrict ω) := by apply hω
            _ <= f n 0 ({k|k<=n}.restrict ω) := by apply iInf_le
        }
        exact hf n ({k | k ≤ n}.restrict ω) h
      }




    · unfold MeasureKernelSequenceContent
      simp only [coe_setOf, mem_setOf_eq, AddContent.mk'_on_C, preimage_eq_univ_iff]
      have nothing : univ ∈ cylinder_n α 0 := by {
        unfold cylinder_n
        simp only [coe_setOf, mem_setOf_eq, mem_image, preimage_eq_univ_iff]
        use univ
        simp only [MeasurableSet.univ, subset_univ, and_self]
      }
      have h : ∃n, univ ∈ cylinder_n α n := by use 0
      simp only [h, ↓reduceDIte, gt_iff_lt]
      generalize_proofs g
      have hg : choose g = univ := by {
        have hg := (choose_spec g).2
        generalize hgg : choose g = gg
        have hr : range ({x | x <= Nat.find h}.restrict (π := α)) = univ := by {
          ext x
          simp
          exact Subtype.exists_pi_extension x
        }
        have hhgg : range {x | x ≤ Nat.find h}.restrict ⊆ gg := by {
          rw [<- hgg]
          assumption
        }
        rw [hr] at hhgg
        exact eq_univ_of_univ_subset hhgg
      }
      rw [hg]
      have h1 : (FiniteCompMeasureKernelNat μ K (Nat.find h))
        (@univ ((k : { x // x ≤ Nat.find h }) → α ↑k) :
          Set ((k : { x // x ≤ Nat.find h }) → α ↑k))
        = 1 := by {
        let t : IsProbabilityMeasure (FiniteCompMeasureKernelNat μ K (Nat.find h))
          := inferInstance
        exact isProbabilityMeasure_iff.mp t
      }
      have h2 : (FiniteCompMeasureKernelNat μ K (Nat.find h))
        (@univ ((k : { x // x ≤ Nat.find h }) → α ↑k) :
          Set ((k : { x // x ≤ Nat.find h }) → α ↑k))
        < ⊤ := by {
          rw [h1]
          simp
        }
      exact h2
  }

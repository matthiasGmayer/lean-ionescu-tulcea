import IonescuTulcea.prodLike
import IonescuTulcea.finiteCompProd
import Mathlib

set_option autoImplicit true
open Function Set Classical ENNReal

noncomputable section

/-!
This file contains some lemmas that are used in the proofs of the main results.
For example, we prove the associativity of the compProd' operator, so that we can
use measures and kernels. e.g. (μ ⊗ K₁ ... ⊗ Kn) ⊗ (.... Km) = μ ⊗ (K₁ ⊗ ... ⊗ Km)
This is done in generality by the lemma assoc_compProd'_kernel_compProd'
which deduces a prodlike structure from the given prodlikes.
To get the real associativity then you need to show that this inferred structure is the same
as the one in the statement of your lemma.
This is done in the lemma compProd'_measure_kernel_finite_comp
Furthermore there are a few lemmas that tell us how these products interact with integrals.
-/

namespace CompProdMeasures
open MeasureTheory MeasurableSpace Measurable ProductLike
open ProbabilityMeasure Measure ProductLike

open ProbabilityTheory
open IndexedFamilies
-- @[simp]
-- lemma kernel_comp_apply
--   {α : ℕ -> Type*}
--   [∀m, MeasurableSpace (α m)]
--   (K : ∀(m : ℕ), Kernel (∀k : {k|k <= m}, α k) (α (m+1)))
--   (n : ℕ) (m : ℕ)
--   ω
--   :
--   kernel_slice (FiniteCompKernelNat K n m) ω
--   = FiniteCompMeasureKernelNat (K n ω) K m := by {
--   }
lemma lintegral_convert_measure
  [MeasurableSpace α]
  [MeasurableSpace β]
  (e : EquivalentMeasurableSpace α β)
  (μ : Measure α)
  (f : β -> ℝ≥0∞)
  (hf : Measurable f)
  : ∫⁻ x, f x ∂(convert_measure μ) = ∫⁻ x, f (e.equiv x) ∂μ := by {
    unfold convert_measure
    rw [lintegral_map]
    exact hf
    exact MeasurableEquiv.measurable EquivalentMeasurableSpace.equiv
  }

lemma lintegral_convert_kernel
  [MeasurableSpace α]
  [MeasurableSpace β]
  [MeasurableSpace γ]
  [MeasurableSpace δ]
  (e : EquivalentMeasurableSpace α γ)
  (e' : EquivalentMeasurableSpace β δ)
  (K : Kernel α β)
  (f : δ -> ℝ≥0∞)
  (hf : Measurable f)
  (c : γ)
  : ∫⁻ x, f x ∂(convert_kernel K : Kernel γ δ) c
    = ∫⁻ (a : β), f (EquivalentMeasurableSpace.equiv a) ∂K (EquivalentMeasurableSpace.equiv.symm c):= by {
    unfold convert_kernel
    simp
    rw [Kernel.lintegral_map]
    exact MeasurableEquiv.measurable EquivalentMeasurableSpace.equiv
    exact hf
  }

lemma lintegral_compProd'
  [MeasurableSpace α]
  [MeasurableSpace β]
  [MeasurableSpace γ]
  [p : ProdLikeM γ α β]
  (μ : Measure α)
  (K : Kernel α β)
  [IsSFiniteKernel K]
  [SFinite μ]
  (f : γ -> ℝ≥0∞)
  (hf : Measurable f)
  : ∫⁻ ω, f ω ∂μ ⊗ₘ' K = ∫⁻ (a : α), ∫⁻ (b : β), f (p.equiv.symm (a, b)) ∂K a ∂μ := by {
    unfold compProd'
    rw [lintegral_map]
    rw [lintegral_compProd]
    all_goals simp [Measurable.comp', MeasurableEquiv.measurable, hf]
  }

lemma Kernel.lintegral_compProd'
  [MeasurableSpace α]
  [MeasurableSpace β]
  [MeasurableSpace γ]
  [MeasurableSpace δ]
  [MeasurableSpace ε]
  (p : ProdLikeM γ α β)
  (q : ProdLikeM ε β δ)
  (K : Kernel α β)
  (L : Kernel γ δ)
  [IsSFiniteKernel K]
  [IsSFiniteKernel L]
  (f : ε -> ℝ≥0∞)
  (hf : Measurable f)
  (a : α)
  : ∫⁻ ω, f ω ∂(K ⊗ₖ' L) a
    = ∫⁻ (b : β), ∫⁻ (c : δ),
      f (q.equiv.symm (b, c))
      ∂L (p.equiv.symm (a, b)) ∂K a := by {
    rw [Kernel.compProd'_def]
    unfold change_right change_left
    rw [Kernel.lintegral_map]
    rw [Kernel.lintegral_compProd]
    simp_rw [Kernel.lintegral_comap]
    simp only [Equiv.invFun_as_coe, MeasurableEquiv.coe_toEquiv_symm]
    all_goals simp [Measurable.comp', MeasurableEquiv.measurable, hf]
  }

lemma MeasurableEquivInSet
  [MeasurableSpace α]
  [MeasurableSpace β]
  (e : α ≃ᵐ β)
  (s : Set β)
  (a : α )
  : e a ∈ s <-> a ∈ e ⁻¹' s := by {
    simp
  }

@[simp]
lemma kernel_slice_integral
  [MeasurableSpace α]
  [MeasurableSpace β]
  [MeasurableSpace γ]
  [p : ProdLikeM γ α β]
  (μ : Measure α)
  (K : Kernel α β)
  [IsSFiniteKernel K]
  [SFinite μ]
  (A : Set γ)
  (hA : MeasurableSet A)
  : ∫⁻ ω : α, kernel_slice K A ω ∂μ = compProd' μ K A  := by {
    unfold kernel_slice ProdLikeM.slice compProd'
    rw [@MeasurableEquiv.map_apply]
    simp_rw [slice_preimage]
    rw [show p.equiv '' A = p.equiv.symm ⁻¹' A by {
      ext x
      simp
      constructor
      intro ⟨y,hy⟩
      rw [<- hy.2]
      simp [hy.1]
      intro h
      use p.equiv.symm x
      simp [h]
    }]
    generalize hAA' : p.equiv.symm ⁻¹' A = A'
    have hA' : MeasurableSet A' := by rw [<- hAA']; measurability;
    rw [<- setLIntegral_one, <- lintegral_indicator]
    -- simp_rw [ lintegral_indicator_one]
    rw [Measure.lintegral_compProd]
    have h : ∀ω, (K ω) {b | (ω,b) ∈ A'} = ∫⁻ b, {b|(ω,b) ∈ A'}.indicator 1 b ∂(K ω) := by {
      intro ω
      exact Eq.symm (lintegral_indicator_one (by
      subst hAA'
      simp_all only [MeasurableEquiv.measurableSet_preimage, mem_preimage, measurableSet_setOf]
      apply Measurable.comp'
      · simp_all only [measurable_mem]
      · apply Measurable.comp'
        · apply MeasurableEquiv.measurable
        · apply Measurable.prod
          · simp_all only [measurable_const]
          · simp_all only
            apply measurable_id'))
    }
    simp_rw [h]
    congr
    all_goals measurability
}

lemma preimage_indicator (f : α -> β) (A : Set β) : ((f ⁻¹' A).indicator 1 x : ℝ≥0∞) = A.indicator 1 (f x)  := by {
  exact rfl
}

@[simp]
lemma kernel_slice_fun_integral
  [MeasurableSpace α]
  [MeasurableSpace β]
  [MeasurableSpace γ]
  [MeasurableSpace δ]
  [p : ProdLikeM δ β γ]
  (μ : Measure α)
  (K : Kernel β γ)
  [IsSFiniteKernel K]
  [SFinite μ]
  (A : Set δ)
  (hA : MeasurableSet A)
  (f : α -> β)
  (hf : Measurable f)
  : ∫⁻ ω, kernel_slice K A (f ω) ∂μ = (μ ⊗ₘ (K.comap f hf)) (Prod.map f id ⁻¹' (p.1.symm ⁻¹' A)) := by {
    unfold kernel_slice ProdLikeM.slice
    simp_rw [slice_preimage]
    rw [show p.equiv '' A = p.equiv.symm ⁻¹' A by {
      ext x
      simp only [mem_image, mem_preimage]
      constructor
      intro ⟨y,hy⟩
      rw [<- hy.2]
      simp [hy.1]
      intro h
      use p.equiv.symm x
      simp only [h, MeasurableEquiv.apply_symm_apply, and_self]
    }]
    generalize hAA' : p.equiv.symm ⁻¹' A = A'
    have hA' : MeasurableSet A' := by rw [<- hAA']; measurability;
    have h : ∀ω, (K ω) {b | (ω,b) ∈ A'} = ∫⁻ b, {b|(ω,b) ∈ A'}.indicator 1 b ∂(K ω) := by {
      intro ω
      exact Eq.symm (lintegral_indicator_one (by
      subst hAA'
      simp_all only [MeasurableEquiv.measurableSet_preimage, mem_preimage, measurableSet_setOf]
      apply Measurable.comp'
      · simp_all only [measurable_mem]
      · apply Measurable.comp'
        · apply MeasurableEquiv.measurable
        · apply Measurable.prod
          · simp_all only [measurable_const]
          · simp_all only
            apply measurable_id'))
    }
    simp_rw [h]
    have hfid : Measurable (Prod.map f (@id γ)) := by {
      apply Measurable.prod <;> simp only [Prod.map_fst, Prod.map_snd]
      subst hAA'
      simp_all only [MeasurableEquiv.measurableSet_preimage, mem_preimage]
      apply Measurable.comp'
      · exact hf
      · apply measurable_fst
      subst hAA'
      simp_all only [MeasurableEquiv.measurableSet_preimage, mem_preimage, id_eq]
      apply measurable_snd
    }

    conv => rhs; tactic => {
      rw [<- setLIntegral_one, <- lintegral_indicator]
      apply MeasurableSet.preimage
      exact hA'
      exact hfid
    }
    rw [Measure.lintegral_compProd]
    congr
    apply Measurable.indicator
    exact measurable_const
    exact hfid hA'
}


@[simp]
lemma FiniteCompKernelNat_zero
  {α : ℕ -> Type*}
  [∀m, MeasurableSpace (α m)]
  (K : ∀(m : ℕ), Kernel (⇑α {k|k <= m}) (α (m+1)))
  : FiniteCompKernelNat K n 0 = convert_kernel (K n) := by rfl

@[simp]
lemma compProd'_measure_kernel_step
  {α : ℕ -> Type*}
  [∀m, MeasurableSpace (α m)]
  (μ : Measure (α 0))
  (K : ∀(m : ℕ), Kernel (⇑α {k|k <= m}) (α (m+1)))
  (n : ℕ)
  : compProd' (FiniteCompMeasureKernelNat μ K n) (K n)
    -- (p := ProdLikeM.insert_n_plus_1 n)
  = FiniteCompMeasureKernelNat μ K (n+1) := by rfl



@[simp]
lemma Kernel.compProd'_measure_kernel_step
  {α : ℕ -> Type*}
  [∀m, MeasurableSpace (α m)]
  (K : ∀(m : ℕ), Kernel (⇑α  {k|k <= m}) (α (m+1)))
  (n m : ℕ)
  : Kernel.compProd' (FiniteCompKernelNat K n m) (K (n+m+1))
    (p := ProdLikeM.insert_m n (m+1))
    = FiniteCompKernelNat K n (m+1) := by rfl

def Equiv.switch_equiv {α β γ : Type*} : α × β × γ ≃ (α × β) × γ where
  toFun := λ ⟨a,b,c⟩ => ((a,b),c)
  invFun := λ ⟨⟨a,b⟩,c⟩ => (a,b,c)
  left_inv := by {
    rintro ⟨a,b,c⟩
    simp
  }
  right_inv := by {
    rintro ⟨⟨a,b⟩,c⟩
    simp
  }

@[measurability]
lemma slice_measurable
  [MeasurableSpace α]
  [MeasurableSpace β]
  [MeasurableSpace γ]
  [p : ProdLikeM γ α β]
  (s : Set γ)
  (hs : MeasurableSet s)
  : MeasurableSet {b | p.equiv.symm (a, b) ∈ s} := by {
    simp only [mem_preimage, measurableSet_setOf]
    apply Measurable.comp'
    exact MeasurableSet.mem hs
    apply Measurable.comp'
    exact MeasurableEquiv.measurable ProdLikeM.equiv.symm
    exact measurable_prod_mk_left
  }

def MeasurableEquiv.switch_equiv
  {α β γ : Type*}
  [mα : MeasurableSpace α]
  [mβ : MeasurableSpace β]
  [mγ : MeasurableSpace γ]
  : α × β × γ ≃ᵐ (α × β) × γ where
  toEquiv := Equiv.switch_equiv
  measurable_toFun := prod_mk (prod_mk measurable_fst
        (Measurable.comp' measurable_fst measurable_snd))
        (Measurable.comp' measurable_snd measurable_snd)
  measurable_invFun := prod_mk (Measurable.comp' measurable_fst measurable_fst)
        (prod_mk (Measurable.comp' measurable_snd measurable_fst) measurable_snd)

instance
  [mα : MeasurableSpace α]
  [mβ : MeasurableSpace β]
  [mγ : MeasurableSpace γ]
  : EquivalentMeasurableSpace (α × β × γ) ((α × β) × γ) := ⟨MeasurableEquiv.switch_equiv⟩

def switch_ProdLikeM
  [MeasurableSpace α]
  [MeasurableSpace β]
  [MeasurableSpace γ]
  [MeasurableSpace δ]
  [MeasurableSpace ε]
  [MeasurableSpace E]
  [p : ProdLikeM γ α β] -- γ = α × β
  [q : ProdLikeM ε β δ] -- ε = β × δ
  [r : ProdLikeM E α ε] -- ε = β × δ
  : ProdLikeM E γ δ := ⟨by {
    let τ₁ : α × ε  ≃ᵐ α × β × δ := (MeasurableEquiv.refl α).prodCongr ProdLikeM.equiv
    let τ₂ : α × β × δ ≃ᵐ (α × β) × δ := MeasurableEquiv.switch_equiv
    let τ₃ : (α × β) × δ ≃ᵐ γ × δ := p.1.symm.prodCongr (MeasurableEquiv.refl δ)
    exact MeasurableEquiv.trans r.1 <|
          MeasurableEquiv.trans τ₁ <|
          MeasurableEquiv.trans τ₂ τ₃
  }⟩

@[simp]
lemma switch_ProdLikeM_fun
  [MeasurableSpace α]
  [MeasurableSpace β]
  [MeasurableSpace γ]
  [MeasurableSpace δ]
  [MeasurableSpace ε]
  [MeasurableSpace E]
  [p : ProdLikeM γ α β] -- γ = α × β
  [q : ProdLikeM ε β δ] -- ε = β × δ
  [r : ProdLikeM E α ε] -- ε = β × δ
  (e : E)
  : (switch_ProdLikeM (q:=q) (r:=r)).1  e =
    let ae : α × ε := r.1 e
    let bd : β × δ := q.1 ae.2
    let c : γ     := p.1.symm (ae.1, bd.1)
    (c, bd.2) := by rfl

@[simp]
lemma switch_ProdLikeM_invFun
  [MeasurableSpace α]
  [MeasurableSpace β]
  [MeasurableSpace γ]
  [MeasurableSpace δ]
  [MeasurableSpace ε]
  [MeasurableSpace E]
  [p : ProdLikeM γ α β] -- γ = α × β
  [q : ProdLikeM ε β δ] -- ε = β × δ
  [r : ProdLikeM E α ε] -- ε = β × δ
  (cd : γ × δ)
  : (switch_ProdLikeM (q:=q) (r:=r)).1.symm cd =
    let ab : α × β := p.1 cd.1
    let bd : β × δ := (ab.2, cd.2)
    r.1.symm (ab.1, q.1.symm bd) := by rfl

lemma switch_ProdLikeM_invFun'
  [MeasurableSpace α]
  [MeasurableSpace β]
  [MeasurableSpace γ]
  [MeasurableSpace δ]
  [MeasurableSpace ε]
  [MeasurableSpace E]
  [p : ProdLikeM γ α β] -- γ = α × β
  [q : ProdLikeM ε β δ] -- ε = β × δ
  [r : ProdLikeM E α ε] -- ε = β × δ
  : ⇑(switch_ProdLikeM (q:=q) (r:=r)).1.symm = fun (cd : γ × δ) =>
    let ab : α × β := p.1 cd.1
    let bd : β × δ := (ab.2, cd.2)
    r.1.symm (ab.1, q.1.symm bd) := by rfl

lemma compProd_kernel_apply
  [MeasurableSpace α]
  [MeasurableSpace β]
  [MeasurableSpace γ]
  (K : Kernel α β)
  (L : Kernel (α × β) γ)
  [IsMarkovKernel K]
  [IsMarkovKernel L]
  (a : α)
  : (K ⊗ₖ L) a = (K a) ⊗ₘ (L.comap (λ x => (a,x)) (by measurability)) := by {
    ext s hs
    rw [<- setLIntegral_one, <- lintegral_indicator]
    rw [<- setLIntegral_one, <- lintegral_indicator]
    rw [Measure.lintegral_compProd]
    rw [Kernel.lintegral_compProd]
    simp only [Kernel.coe_comap, comp_apply]
    exact (measurable_indicator_const_iff 1).mpr hs
    exact (measurable_indicator_const_iff 1).mpr hs
    exact hs
    exact hs
  }


lemma assoc_compProd'_kernel_compProd'
  [MeasurableSpace α]
  [MeasurableSpace β]
  [MeasurableSpace γ]
  [MeasurableSpace δ]
  [MeasurableSpace ε]
  [MeasurableSpace E]
  (μ : Measure α)
  (K : Kernel α β)
  (L : Kernel γ δ) -- L : Kernel (α × β) δ
  [hμ : IsProbabilityMeasure μ]
  [mK : IsMarkovKernel K]
  [mL : IsMarkovKernel L]
  [p : ProdLikeM γ α β] -- γ = α × β
  [q : ProdLikeM ε β δ] -- ε = β × δ
  [r : ProdLikeM E α ε] -- ε = β × δ
  : (compProd' μ (Kernel.compProd' K L))
    = (compProd' (p := switch_ProdLikeM (q:=q) (r:=r)) (compProd' μ K) L : Measure E) := by {
      ext s hs
      unfold compProd' Kernel.compProd' change_right change_left
      simp only [coe_setOf, mem_setOf_eq, Equiv.invFun_as_coe, MeasurableEquiv.coe_toEquiv_symm]
      rw [Measure.map_apply]
      rw [Measure.map_apply (hs := hs)]
      rw [<- setLIntegral_one, <-lintegral_indicator]
      rw [<- setLIntegral_one, <-lintegral_indicator]
      repeat rw [Measure.lintegral_compProd]
      conv => lhs; rhs; intro a; rhs; intro b; tactic => {
          exact show ((r.equiv.symm ⁻¹' s).indicator (fun x ↦ 1) (a,b) : ℝ≥0∞)
          = {b | (a,b) ∈ r.equiv.symm ⁻¹' s}.indicator 1 b by {
            rfl
          }
      }
      simp
      conv => lhs; rhs; intro a; tactic => {
        trans
        apply lintegral_indicator
        exact slice_measurable s hs
        apply setLIntegral_one
      }
      conv => lhs; rhs; intro a; tactic => {
        rw [Kernel.map_apply, Measure.map_apply]
        exact MeasurableEquiv.measurable ProdLikeM.equiv.symm
        exact slice_measurable s hs
        exact MeasurableEquiv.measurable ProdLikeM.equiv.symm
      }
      simp_rw [compProd_kernel_apply, <- setLIntegral_one]
      conv => lhs; rhs; intro a; tactic => {
        rewrite [<- lintegral_indicator]
        rewrite [Measure.lintegral_compProd]
        simp only [Kernel.coe_comap, comp_apply, preimage_setOf_eq]
        rfl
        simp only [preimage_setOf_eq]
        refine (measurable_indicator_const_iff 1).mpr ?_
        refine Measurable.setOf ?_
        apply Measurable.comp'
        exact MeasurableSet.mem hs
        apply Measurable.comp'
        exact MeasurableEquiv.measurable ProdLikeM.equiv.symm
        apply Measurable.comp'
        exact measurable_prod_mk_left
        exact MeasurableEquiv.measurable ProdLikeM.equiv.symm
        simp only [preimage_setOf_eq, measurableSet_setOf]
        apply Measurable.comp'
        exact MeasurableSet.mem hs
        apply Measurable.comp'
        exact MeasurableEquiv.measurable ProdLikeM.equiv.symm
        apply Measurable.comp'
        exact measurable_prod_mk_left
        exact MeasurableEquiv.measurable ProdLikeM.equiv.symm
      }

      rw [lintegral_map, Measure.lintegral_compProd]
      congr
      ext a
      congr
      ext b
      congr
      ext c
      repeat rw [indicator_apply]
      simp only [mem_setOf_eq, mem_preimage, switch_ProdLikeM_invFun,
        MeasurableEquiv.apply_symm_apply]

      all_goals let sp := switch_ProdLikeM (q:=q) (r:=r)
      · let f a b : ℝ≥0∞ := (sp.equiv.symm ⁻¹' s).indicator 1 (a, b)
        have heq : (fun a => ∫⁻ (b : δ), (sp.equiv.symm ⁻¹' s).indicator
            (fun x ↦ 1) (p.1.symm a, b) ∂L (p.equiv.symm a))
          = (fun a => ∫⁻ (b : δ), f a b ∂L a) ∘ p.1.symm := by rfl
        rw [heq]
        apply Measurable.comp ?_ (by
        simp_all only [MeasurableEquiv.apply_symm_apply, implies_true, f]
        apply MeasurableEquiv.measurable)
        apply Measurable.lintegral_kernel_prod_right
        simp_all only [MeasurableEquiv.apply_symm_apply, implies_true, f]
        apply Measurable.comp'
        · apply Measurable.indicator
          · apply measurable_one
          · simp_all only [MeasurableEquiv.measurableSet_preimage]
        · apply Measurable.prod
          apply measurable_fst
          apply measurable_snd
      · apply Measurable.lintegral_kernel_prod_right
        apply Measurable.indicator measurable_one
        exact (MeasurableEquiv.measurableSet_preimage ProdLikeM.equiv.symm).mpr hs
      · exact MeasurableEquiv.measurable ProdLikeM.equiv.symm
      · apply Measurable.indicator measurable_one
        exact (MeasurableEquiv.measurableSet_preimage ProdLikeM.equiv.symm).mpr hs
      · apply Measurable.indicator measurable_one
        exact (MeasurableEquiv.measurableSet_preimage ProdLikeM.equiv.symm).mpr hs
      · exact (MeasurableEquiv.measurableSet_preimage ProdLikeM.equiv.symm).mpr hs
      · exact (MeasurableEquiv.measurableSet_preimage ProdLikeM.equiv.symm).mpr hs
      · exact MeasurableEquiv.measurable ProdLikeM.equiv.symm
      · exact MeasurableEquiv.measurable ProdLikeM.equiv.symm
      . exact hs
}

lemma compProd_Kernelmap
  [MeasurableSpace α]
  [MeasurableSpace β]
  [MeasurableSpace γ]
  (μ : Measure α)
  [IsProbabilityMeasure μ]
  (K : Kernel α β)
  [IsMarkovKernel K]
  (f : β -> γ)
  (hf : Measurable f)
  : μ ⊗ₘ (K.map f) = (μ ⊗ₘ K).map λ (a, b) => (a,f b) := by {
    simp
    ext s hs
    induction s, hs using induction_on_inter with
    | h_eq => exact generateFrom_prod.symm
    | h_inter => exact isPiSystem_prod
    | empty => simp only [measure_empty]
    | basic s hs => {
      simp at hs
      obtain ⟨A,⟨hA,⟨B,⟨hB,h⟩⟩⟩⟩ := hs
      subst h
      rw [Measure.map_apply]
      rw [show ((fun x ↦ (x.1, f x.2)) ⁻¹' A ×ˢ B) = A ×ˢ (f ⁻¹' B)  by rfl]
      repeat rw [<- setLIntegral_one, Measure.setLIntegral_compProd]
      congr
      ext a
      repeat rw [setLIntegral_one]
      rw [Kernel.map_apply, Measure.map_apply]
      -- all_goals measurability
      simp_all only
      exact hB
      exact hf
      simp_all only [measurable_const]
      simp_all only
      apply measurableSet_preimage
      · exact hf
      · simp_all only
      simp_all only [measurable_const]
      exact hA
      exact hB
      apply Measurable.prod
      · simp_all only
        apply measurable_fst
      · simp_all only
        apply Measurable.comp'
        · exact hf
        · apply measurable_snd
      apply MeasurableSet.prod
      · simp_all only
      · simp_all only
    }
    | compl s hs h=> {
      have hk : IsMarkovKernel <| K.map f := by exact Kernel.IsMarkovKernel.map K hf
      have hμ' : IsProbabilityMeasure <|(Measure.map (fun x ↦ (x.1, f x.2)) (μ ⊗ₘ K)) := by {
        apply isProbabilityMeasure_map
        -- measurability
        apply AEMeasurable.prod_mk
        · apply Measurable.comp_aemeasurable'
          · apply measurable_fst
          · apply aemeasurable_id'
        · apply Measurable.comp_aemeasurable'
          · simp_all only
          · apply Measurable.comp_aemeasurable'
            · apply measurable_snd
            · apply aemeasurable_id'
      }
      repeat rw [prob_compl_eq_one_sub hs]
      simp [h]
    }
    | iUnion s pwd hs h => {
      -- #check Measure
      rw [show ∀A, (μ ⊗ₘ K.map f) A = (μ ⊗ₘ K.map f).toOuterMeasure A by exact fun A ↦
        rfl]
      rw [show ∀A, (Measure.map (fun x ↦ (x.1, f x.2)) (μ ⊗ₘ K)) A = (Measure.map (fun x ↦ (x.1, f x.2)) (μ ⊗ₘ K)).toOuterMeasure A by exact fun A ↦
        rfl]
      repeat rw [Measure.m_iUnion]
      simp
      congr
      ext i
      all_goals simp [*]
    }
  }


@[simp]
lemma compProd'_measure_kernel_convert
  {α : ℕ -> Type*}
  [∀m, MeasurableSpace (α m)]
  (μ : Measure (α 0))
  (K : ∀(m : ℕ), Kernel (⇑α {k|k <= m}) (α (m+1)))
  [mK : ∀m, IsMarkovKernel (K m)]
  [hμ : IsProbabilityMeasure μ]
  : compProd' (p := ProdLikeM.insert_m n (1))
      (FiniteCompMeasureKernelNat μ K n) (convert_kernel (K n))
    = compProd' (p := ProdLikeM.insert_n_plus_1 n)
      (FiniteCompMeasureKernelNat μ K n)
      (K n) := by {
      have hμ' : IsProbabilityMeasure (FiniteCompMeasureKernelNat μ K n) := by infer_instance
      repeat rw [compProd'_def]
      ext s hs
      repeat rw [MeasurableEquiv.map_apply]
      unfold
        convert_kernel
        EquivalentMeasurableSpace.refl
        MeasurableEquiv.refl
      simp only [coe_setOf, mem_setOf_eq, eq_mpr_eq_cast, MeasurableEquiv.symm_mk,
        MeasurableEquiv.coe_mk, Equiv.coe_fn_symm_mk, Equiv.refl_symm, Equiv.coe_refl,
        Kernel.comap_id]
      rw [compProd_Kernelmap, Measure.map_apply]
      congr

      all_goals simp_all only [
        Measurable.prod,
        measurable_fst,
        measurable_snd,
        Measurable.comp',
        MeasurableEquiv.measurable,
        MeasurableEquiv.measurableSet_preimage
      ]
    }


lemma equiv_symm_equal_is_equal
  (e f : α ≃ β) (h : e = f) : e.symm = f.symm := by rw [h]
lemma mequiv_symm_equal_is_equal
  [MeasurableSpace α]
  [MeasurableSpace β]
  (e f : α ≃ᵐ β) (h : e = f) : ⇑e.symm = ⇑f.symm := by rw [h]
lemma mequiv_symm_left
  [MeasurableSpace α]
  [MeasurableSpace β]
  (e : β ≃ᵐ α) (h' : a = e b) : e.symm a = b := by {
    apply_fun e
    simp
    exact h'
  }
@[simp]
lemma equivtofun
  : { toFun := f, invFun := f', left_inv := h, right_inv := g : Equiv α β}.1 = f := by rfl
@[simp]
lemma equivtofun'
  : { toFun := f, invFun := f', left_inv := h, right_inv := g : Equiv α β} x = f x := by rfl
@[simp]
lemma mequivtofun'
  [MeasurableSpace α]
  [MeasurableSpace β]
  {f : α -> β}
  {f' : β -> α}
  {h' : Measurable f}
  {g' : Measurable f'}
  {g : Function.RightInverse f' f}
  {h : LeftInverse f' f}
  (x : α)
  : { toFun := f, invFun := f', left_inv := h, right_inv := g, measurable_toFun := h', measurable_invFun := g' : MeasurableEquiv α β} x = f x := by rfl

@[simp]
lemma mequivtoinvfun
  [MeasurableSpace α]
  [MeasurableSpace β]
  {f : α -> β}
  {f' : β -> α}
  {h' : Measurable f}
  {g' : Measurable f'}
  {g : Function.RightInverse f' f}
  {h : LeftInverse f' f}
  : { toFun := f, invFun := f', left_inv := h, right_inv := g, measurable_toFun := h', measurable_invFun := g' : MeasurableEquiv α β}.symm.1
    = {toFun := f, invFun := f', left_inv := h, right_inv := g : Equiv α β}.symm := by rfl
@[simp]
lemma mequivtoinvfun'
  [MeasurableSpace α]
  [MeasurableSpace β]
  {f : α -> β}
  {f' : β -> α}
  {h' : Measurable f}
  {g' : Measurable f'}
  {g : Function.RightInverse f' f}
  {h : LeftInverse f' f}
  (x : β)
  : { toFun := f, invFun := f', left_inv := h, right_inv := g, measurable_toFun := h', measurable_invFun := g' : MeasurableEquiv α β}.symm x = f' x := by rfl

@[simp]
lemma mequivtoinvfun''
  [MeasurableSpace α]
  [MeasurableSpace β]
  {f : α -> β}
  {f' : β -> α}
  {h' : Measurable f}
  {g' : Measurable f'}
  {g : Function.RightInverse f' f}
  {h : LeftInverse f' f}
  (x : β)
  : { toFun := f, invFun := f', left_inv := h, right_inv := g, measurable_toFun := h', measurable_invFun := g' : MeasurableEquiv α β}.symm.toEquiv x = f' x := by rfl

lemma compProd'_measure_kernel_finite_comp
  {α : ℕ -> Type*}
  [∀m, MeasurableSpace (α m)]
  (μ : Measure (α 0))
  (K : ∀(m : ℕ), Kernel (∀k : {k|k <= m}, α k) (α (m+1)))
  [mK: ∀m, IsMarkovKernel (K m)]
  [hμ : IsProbabilityMeasure μ]
  (n m : ℕ)
  : compProd' (FiniteCompMeasureKernelNat μ K n) (FiniteCompKernelNat K n m)
    (p := ProdLikeM.insert_m n (m+1))
    = FiniteCompMeasureKernelNat μ K (n+m+1) := by {
      induction m with
      | zero => {
        rw [FiniteCompKernelNat_zero]
        rw [compProd'_measure_kernel_convert]
        -- Why does simp not take lemma?
        rfl
      }
      | succ m hm => {
        let _ : IsProbabilityMeasure <| FiniteCompMeasureKernelNat μ K n := by infer_instance
        let _ : ∀n m, IsMarkovKernel (FiniteCompKernelNat K n m) := by intros; infer_instance
        simp only [coe_setOf, mem_setOf_eq]
        rw [<- Kernel.compProd'_measure_kernel_step]
        rw [<- compProd'_measure_kernel_step]
        rw [assoc_compProd'_kernel_compProd']
        rw [hm]
        ext s hs
        unfold compProd'
        rw [MeasurableEquiv.map_apply]
        conv => rhs; apply MeasurableEquiv.map_apply
        repeat rw [<- setLIntegral_one, <- lintegral_indicator]
        repeat rw [Measure.lintegral_compProd]
        congr
        ext a
        congr
        ext b
        congr
        apply (show ∀f g s, f = g -> f⁻¹'s = g⁻¹'s by intro f g s h; rw [h])
        apply mequiv_symm_equal_is_equal
        ext x : 2
        simp only [mem_setOf_eq, coe_setOf, switch_ProdLikeM_fun]
        unfold ProdLikeM.equiv
        conv => rhs; apply ProdLikeM.insert_n_plus_1_apply
        congr
        conv => lhs; rhs; rhs; rhs; rhs; rhs; apply ProdLikeM.insert_m_apply
        conv => lhs; rhs; rhs; rhs; apply ProdLikeM.ge_n_insert_m_plus_1_apply
        conv => lhs; rhs; lhs; arg 1; apply ProdLikeM.insert_m_apply
        conv => lhs; apply ProdLikeM.insert_m_apply_inv
        simp only [coe_setOf, mem_setOf_eq, restrict₂, id_eq, Int.reduceNeg, eq_mpr_eq_cast,
          cast_eq, eq_mp_eq_cast, Int.Nat.cast_ofNat_Int]
        ext j
        by_cases hj : (j : ℕ) ≤ n <;> simp [hj]

        repeat {
          try apply Measurable.indicator
          exact measurable_const
          rw [MeasurableEquiv.measurableSet_preimage]
          exact hs
        }
        repeat rw [MeasurableEquiv.measurableSet_preimage]; exact hs
      }
    }

@[simp]
lemma compapp_null_action
  {α : I -> Type*}
  [∀n, Inhabited (α n)]
  (ω : ⇑α J)
  {L : Set I}
  {b : ⇑α K}
  {i : L}
  : compapp ω (compose' b ω i) = ω := by {
    unfold compapp compose compose' blowup
    simp
    ext j
    simp only [mem_singleton_iff, Set.restrict_apply, eq_mpr_eq_cast, Subtype.coe_prop, ↓reduceDIte]
  }

@[simp]
lemma compapp_reduce
  {α : I -> Type*}
  [∀n, Inhabited (α n)]
  (ω : ⇑α J)
  {L : Set I}
  {b : ⇑α K}
  {i : L}
  (hi : (i : I) ∈ K)
  : compapp ω (compose' b ω i)
    = compapp (L:=L) ω (b ⟨(i : I),hi⟩ ) := by {
    unfold compapp compose compose' blowup
    simp
    ext j
    simp only [mem_singleton_iff, Set.restrict_apply, eq_mpr_eq_cast, Subtype.coe_prop, ↓reduceDIte]
    by_cases h : (j : I) ∈ J <;> simp [h]
    by_cases h : (j : I) = i <;> simp [h]
    unfold compose
    simp [hi]
  }

lemma mem_congr {a b : α} (s : Set α) (h : a = b) : a ∈ s <-> b ∈ s := by rw [h]

lemma kernel_measurability
  [MeasurableSpace α]
  [MeasurableSpace β]
  [MeasurableSpace γ]
  (K : Kernel α β)
  [IsSFiniteKernel K]
  (f : γ -> α)
  (g : γ -> β -> ℝ≥0∞)
  (hf : Measurable f)
  (hg : Measurable <| uncurry g)
  : Measurable fun x => ∫⁻ c : β, g x c ∂K (f x) := by {
    simp_rw [show ∀x, K (f x) = K.comap f hf x by {
      intro x
      exact rfl
    } ]
    apply lintegral_kernel_prod_left
    exact measurable_swap_iff.mp hg
  }

lemma kernel_slice_integral''
  {α : ℕ -> Type*}
  [∀n, MeasurableSpace (α n)]
  [∀n, Inhabited (α n)]
  (K : ∀n, Kernel (⇑α {k|k ≤ n}) (α (n+1)))
  [∀n, IsMarkovKernel (K n)]
  (n m : ℕ)
  (ω : ⇑α {k | k ≤ n})
  (f : ⇑α {k | k <= n + (m+1) + 1} -> ℝ≥0∞)
  (hf : Measurable f)
  : ∫⁻ (a : ⇑α {k | n < k ∧ k ≤ n + (m + 1) + 1}),
      f (compose' a ω)
    ∂(FiniteCompKernelNat K n (m + 1)) ω =
    ∫⁻ (ω' : α (n + 1)),
    ∫⁻ (a : ⇑α {k | n + 1 < k ∧ k ≤ n + 1 + m + 1}),
      f (compapp₃ a ω ω')
    ∂(FiniteCompKernelNat K (n + 1) m) (compapp ω ω') ∂(K n) ω
    := by {
      induction m with
      | zero => {
        unfold FiniteCompKernelNat
        simp only [Nat.reduceAdd, coe_setOf, mem_setOf_eq, Nat.add_zero, FiniteCompKernelNat_zero]
        rw [Kernel.lintegral_compProd']
        rw [lintegral_convert_kernel]
        congr; ext a
        rw [lintegral_convert_kernel]
        congr 1
        ·
          apply congrArg
          simp only [ProdLikeM.insert_m_apply_inv, coe_setOf, mem_setOf_eq,
          eq_mp_eq_cast, id_eq, eq_mpr_eq_cast, EquivalentMeasurableSpace.refl_equiv,
          MeasurableEquiv.symm_refl, MeasurableEquiv.refl_apply]
          ext i
          split_ifs <;> simp [compapp, compose, blowup, *]
          split_ifs
          rfl
          exfalso; omega
        · ext c; apply congrArg
          ext i
          unfold compose' compapp₃ compose
          simp only [mem_setOf_eq, ProdLikeM.ge_n_insert_m_plus_1_apply_inv, Set.restrict_apply]
          split_ifs <;> try {exfalso; omega} <;> try rfl
        · apply Measurable.comp' hf
          exact measurable_compapp₃_fst ω a
        ·
          apply kernel_measurability
          apply Measurable.comp'
          apply MeasurableEquiv.measurable
          exact measurable_prod_mk_left
          unfold uncurry
          simp only [Prod.mk.eta, ProdLikeM.ge_n_insert_m_plus_1_apply_inv, coe_setOf, mem_setOf_eq]
          apply Measurable.comp' hf
          apply Measurable.comp' (measurable_compose'_fst ω)
          refine measurable_pi_iff.mpr ?_
          intro i
          split_ifs
          apply Measurable.eval
          exact measurable_fst
          generalize_proofs h
          have hi : (i : ℕ) = n+1+1 := by omega
          obtain ⟨i,h'⟩ := i
          simp at hi
          subst hi
          simp
          exact measurable_snd
        · apply Measurable.comp' hf
          exact measurable_compose'_fst ω
      }
      | succ m hm => {
        let g := (fun (x : ⇑α {k | k <= n + (m + 1) + 1}) =>
              let a : α (n+1) := x ⟨n+1, by simp⟩
              let b : ⇑α {k | n + 1 < k ∧ k ≤ n + 1 + m + 1} :=
                {k | n + 1 < k ∧ k ≤ n + 1 + m + 1}.restrict₂ (by simp;intros;omega) x
              ∫⁻ (c : α (n + 1 + m + 1 + 1)), f (compose' (ProdLikeM.equiv.symm (b, c))
              (compapp (L:={k | k <= n + 1}) ω a)) ∂(K (n + 1 + m + 1)) ((ProdLikeM.insert_m_plus_1 (n + 1) m).equiv.symm (compapp ω a, b))
            )
        conv => rhs; rhs; intro ω'; tactic => {
          unfold FiniteCompKernelNat
          rw [Kernel.lintegral_compProd']
          apply Measurable.comp'
          exact hf
          apply measurable_compapp₃_fst
        }
        conv => rhs; rhs; intro a; rhs; intro b; tactic => {
          have h : ∫⁻ (c : α (n + 1 + m + 1 + 1)),
            f (compapp₃ (ProdLikeM.equiv.symm (b, c)) ω a)
            ∂(K (n + 1 + m + 1))
              ((ProdLikeM.insert_m_plus_1 (n + 1) m).equiv.symm (compapp ω a, b))
            = g (compapp₃ b ω a) := by {
              unfold g
              simp only [coe_setOf, mem_setOf_eq]
              congr
              · ext ⟨val, prop⟩
                unfold compapp compapp₃ compose blowup
                simp only [mem_setOf_eq, mem_singleton_iff, eq_mpr_eq_cast, Set.restrict_apply,
                  lt_self_iff_false, add_le_add_iff_right, false_and, ↓reduceDIte,
                  add_le_iff_nonpos_right, nonpos_iff_eq_zero, one_ne_zero, cast_eq]
              · ext ⟨val, prop⟩
                unfold compapp₃
                simp only [mem_setOf_eq] at prop
                simp only [mem_setOf_eq, restrict₂, Set.restrict_apply, and_self, ↓reduceDIte, prop]
              · ext c
                congr
                generalize_proofs h1 h2
                rw [show (compapp₃ b ω a ⟨n + 1, h2⟩) = a by {
                  unfold compapp₃
                  simp only [mem_setOf_eq, Set.restrict_apply, lt_self_iff_false,
                    add_le_add_iff_right, false_and, ↓reduceDIte, add_le_iff_nonpos_right,
                    nonpos_iff_eq_zero, one_ne_zero, cast_eq]
                }]
                let p := (ProdLikeM.ge_n_insert_m_plus_1_plus_1 (α:=α) (n + 1) m)
                have h : p.equiv.symm (b, c) = p.equiv.symm
                  (restrict₂ h1 (compapp₃ b ω a), c) := by {
                    congr
                    unfold compapp₃
                    ext ⟨val,prop⟩
                    simp only [mem_setOf_eq] at prop
                    simp only [mem_setOf_eq, restrict₂, Set.restrict_apply, and_self, ↓reduceDIte,
                      prop]
                  }
                conv => rhs; arg 1; apply h.symm
                generalize p.1.symm (b, c) = d
                unfold compapp₃ compapp compose' compose blowup
                ext ⟨val,prop⟩
                simp only [mem_setOf_eq] at prop
                simp only [mem_setOf_eq, Set.restrict_apply, mem_singleton_iff, eq_mpr_eq_cast]
                simp only [show val <= n + 1 + (m + 1) + 1 by omega, and_true, Int.reduceNeg, id_eq,
                  Int.Nat.cast_ofNat_Int]
                by_cases hn : n+1 < val
                simp only [hn, ↓reduceDIte, Int.reduceNeg, show ¬val <= n by omega]
                simp only [hn, ↓reduceDIte, Int.reduceNeg, show val <= n +1 by omega]
              }
          rw [h]
          }
        rw [<- hm g]

        conv => lhs; tactic => {
          unfold FiniteCompKernelNat
          rw [Kernel.lintegral_compProd']
          apply Measurable.comp'
          exact hf
          unfold compose'
          apply Measurable.comp'
          exact measurable_restrict {k | k ≤ n + (m + 1 + 1) + 1}
          unfold compose
          apply measurable_pi_lambda
          intro a
          split_ifs
          apply measurable_pi_apply
          apply measurable_const
          apply measurable_const
        }
        congr
        ext b
        unfold g
        simp only
        have hnn : (n + (m + 1) + 1) = (n + 1 + m + 1) := by omega
        congr 1 <;> try rw [hnn]
        conv => lhs; arg 2; apply ProdLikeM.insert_m_apply_inv
        conv => rhs; arg 2; apply ProdLikeM.insert_m_apply_inv
        simp only [coe_setOf, mem_setOf_eq, eq_mp_eq_cast, id_eq, eq_mpr_eq_cast, restrict₂]
        congr 1 <;> try rw [hnn]
        ·
          refine hfunext ?_ ?_
          rw [show n+ (m+1+1) = n+1+(m+1) by ring]
          intro a a' haa'
          obtain ⟨val, property⟩ := a
          obtain ⟨val', property'⟩ := a'
          have h: val=val' := by {
            refine (Subtype.heq_iff_coe_eq ?_).mp haa'
            intro x; ring_nf
          }
          simp [compapp, compose', compose, blowup]
          subst h
          by_cases h : val <= n
          · simp [h, show val <= n+1 by omega]
          · by_cases h' : val = n+1
            · subst h'
              simp only [add_le_iff_nonpos_right, nonpos_iff_eq_zero, one_ne_zero, ↓reduceDIte,
                le_refl, cast_eq, heq_eq_eq]
            · simp [h, h', show ¬val <= n+1 by omega,
                show val <= n+ (m+1) + 1 by omega,
                show n < val by omega,
                ]
        ·
          {
          refine hfunext ?_ ?_
          · rw [show n+ (m+1) + 1 + 1 = n+1+m+1+1 by omega]
          · intro a a' haa'
            simp only [coe_setOf, mem_setOf_eq, heq_eq_eq]
            congr
            conv => lhs; lhs; apply ProdLikeM.ge_n_insert_m_plus_1_apply_inv
            conv => rhs; lhs; apply ProdLikeM.ge_n_insert_m_plus_1_apply_inv
            ext ⟨val,prop⟩
            simp only [mem_setOf_eq] at prop
            simp only [mem_setOf_eq, compose', coe_setOf, Set.restrict_apply, compose, restrict₂,
              compapp, lt_add_iff_pos_right, zero_lt_one, add_le_add_iff_right,
              le_add_iff_nonneg_right, zero_le, and_self, ↓reduceDIte, mem_singleton_iff, blowup,
              eq_mpr_eq_cast]
            have h2 : val <= n + 1 + (m + 1) + 1 := by omega
            simp only [prop, and_true, h2]
            by_cases h : val <= n
            · simp only [Nat.not_lt.mpr h, ↓reduceDIte, h, false_and,
                dite_eq_ite]
              by_cases h' : val <= n+1
              · simp only [Nat.not_lt.mpr h', ↓reduceDIte, h', ↓reduceIte]
              · exfalso; omega
            · simp only [show n < val by exact Nat.gt_of_not_le h, ↓reduceDIte, true_and, h]
              by_cases h' : val <= n+(m+1+1) <;> by_cases h'' : val <= n+1
              · have h''' : val = n + 1 := by omega
                subst h'''
                simp only [add_le_add_iff_left, le_add_iff_nonneg_left, zero_le, ↓reduceDIte,
                  lt_self_iff_false, le_refl, cast_eq]
              · simp only [h', ↓reduceDIte, Nat.gt_of_not_le h'',
                  show val <= n + 1 + (m + 1) by omega, and_self,
                  show val <= n + (m + 1) + 1 by omega, Int.reduceNeg, id_eq, Int.Nat.cast_ofNat_Int]
              · exfalso; omega
              · have h''' : val = (n+(m+1+1)+1) := by omega
                subst h'''
                simp only [add_le_iff_nonpos_right, nonpos_iff_eq_zero, one_ne_zero, ↓reduceDIte,
                  cast_eq, add_lt_add_iff_right, lt_add_iff_pos_right, add_pos_iff, zero_lt_one,
                  or_true, or_self, show ¬(n + (m + 1 + 1) + 1) <= n + 1 + (m + 1) by omega,
                  and_false]
                symm
                rw [cast_eq_iff_heq]
                exact haa'.symm
          }
        · {
          unfold g
          simp only [coe_setOf, mem_setOf_eq]
          apply kernel_measurability
          · apply measurable_pi_lambda
            intro j
            apply Measurable.eval
            apply Measurable.comp'
            apply MeasurableEquiv.measurable
            apply Measurable.prod <;> simp only
            · apply Measurable.comp'
              apply measurable_compapp_snd ω
              apply measurable_pi_apply
            · apply measurable_restrict₂
          · unfold uncurry
            simp only
            apply Measurable.comp' hf
            refine measurable_pi_iff.mpr ?_
            intro i
            unfold compose' compose
            simp only [mem_setOf_eq, eq_mpr_eq_cast, Set.restrict_apply, dite_eq_ite]
            split_ifs
            apply Measurable.eval
            apply Measurable.comp'
            apply MeasurableEquiv.measurable
            apply Measurable.prod <;> simp only
            apply Measurable.comp'
            apply measurable_restrict₂
            exact measurable_fst
            exact measurable_snd
            apply Measurable.eval
            apply Measurable.comp'
            apply measurable_compapp_snd ω
            apply Measurable.eval
            exact measurable_fst
            exact measurable_const
          }
      }
    }

lemma mem_congr_heq
  (A : Set α)
  (B : Set β)
  (x : α)
  (y : β)
  (h : α = β)
  (hxy : HEq x y)
  (hAB: HEq A B)
  : x ∈ A <-> y ∈ B := by {
    subst h
    simp_all only [heq_eq_eq]
  }

@[simp]
lemma kernel_slice_integral'
  {α : ℕ -> Type*}
  [∀n, MeasurableSpace (α n)]
  [∀n, Inhabited (α n)]
  (K : ∀n, Kernel (⇑α {k|k ≤ n}) (α (n+1)))
  [∀n, IsMarkovKernel (K n)]
  (A : ∀n, Set (⇑α {k|k ≤ n}))
  (hA : ∀n, MeasurableSet (A n))
  (n m : ℕ)
  (ω : ⇑α {k | k ≤ n})
  :
  kernel_slice (FiniteCompKernelNat K n (m + 1)) (A (n + m + 2)) ω =
    ∫⁻ (ω' : α (n + 1)), kernel_slice (FiniteCompKernelNat K (n + 1) m)
      (A (n + 1 + m + 1)) (compapp ω ω') ∂(K n) ω
      := by {
        unfold kernel_slice
        rw [<- setLIntegral_one, <- lintegral_indicator]
        simp only [coe_setOf, mem_setOf_eq]
        simp_rw [<- setLIntegral_one]
        conv => rhs; rhs; intro a; tactic => {
          rw [<- lintegral_indicator]
          apply ProdLikeM.slice_measurable
          apply hA
        }
        let f : _ -> ℝ≥0∞ := (A (n + (m + 1) + 1)).indicator 1
        have hf : Measurable f := by {
          unfold f
          apply Measurable.indicator
          exact measurable_one
          apply hA
        }
        conv => rhs; rhs; intro a; rhs; intro b; tactic => {
          suffices  _ = f (compapp₃ b ω a) from this
          simp only [indicator_apply, coe_setOf, mem_setOf_eq, Pi.one_apply, f]
          congr 1
          unfold ProdLikeM.slice
          simp only [mem_setOf_eq, eq_iff_iff]
          conv => lhs; rhs; apply ProdLikeM.insert_m_apply_inv
          simp only [coe_setOf, mem_setOf_eq, eq_mp_eq_cast, id_eq, eq_mpr_eq_cast]
          -- generalize_proofs h h'
          -- let x : (j : { x // x ≤ n + 1 + (m + 1) }) → α ↑j
          --   := fun j ↦ if h_1 : ↑j ≤ n + 1 then compapp ω a ⟨↑j, h j h_1⟩ else b ⟨↑j, h' j h_1⟩
          have hn : n+1+m+1 = n+(m+1)+1 := by omega
          apply mem_congr_heq <;> try rw [hn]
          apply hfunext
          rw [show n+1+(m+1) = n+(m+1)+1 by omega]; rfl
          intro i j hij
          have h : (i : ℕ) = j := by {
            refine (Subtype.heq_iff_coe_eq ?_).mp hij
            intro a; simp only [mem_setOf_eq]; omega
          }
          obtain ⟨i,hi⟩ := i
          obtain ⟨j,hj⟩ := j
          simp only at h
          subst h
          simp only [mem_setOf_eq, heq_eq_eq]
          unfold compapp
          simp only [Set.restrict_apply, mem_setOf_eq]
          unfold compose blowup compapp₃
          simp only [mem_setOf_eq, mem_singleton_iff, eq_mpr_eq_cast, Set.restrict_apply]
          split_ifs <;> try rfl
          all_goals try {rename_i h; obtain ⟨x,y⟩ := h; exfalso; omega}
          rename_i h1 h2 h3
          simp at h2
          exfalso
          apply h2
          constructor
          omega
          omega
          rename_i h1 h2 h3
          exfalso
          apply h1
          constructor
          omega
          omega
        }
        conv => lhs; rhs; intro b; tactic => {
          suffices _ = f (compose' b ω) by exact this
          simp only [indicator_apply, coe_setOf, mem_setOf_eq, Pi.one_apply, f]
          congr 1
          unfold ProdLikeM.slice
          simp only [mem_setOf_eq, eq_iff_iff]
          conv => lhs; rhs; apply ProdLikeM.insert_m_apply_inv
          simp only [coe_setOf, mem_setOf_eq, eq_mp_eq_cast, id_eq, eq_mpr_eq_cast]
          -- generalize_proofs h h'
          -- let x : (j : { x // x ≤ n + 1 + (m + 1) }) → α ↑j
          --   := fun j ↦ if h_1 : ↑j ≤ n + 1 then compapp ω a ⟨↑j, h j h_1⟩ else b ⟨↑j, h' j h_1⟩
          have hn : n+m+2 = n+(m+1)+1 := by omega
          apply mem_congr_heq <;> try rw [hn]
          apply hfunext
          rw [show n+(m+1+1) = n+(m+1)+1 by omega]; rfl
          intro i j hij
          have h : (i : ℕ) = j := by {
            refine (Subtype.heq_iff_coe_eq ?_).mp hij
            intro a; simp only [mem_setOf_eq]; omega
          }
          obtain ⟨i,hi⟩ := i
          obtain ⟨j,hj⟩ := j
          simp only at h
          subst h
          simp only [mem_setOf_eq, heq_eq_eq]
          unfold compose' compose
          simp only [mem_setOf_eq, Set.restrict_apply]
          split_ifs <;> try rfl
          all_goals exfalso
          rename_i h1
          obtain ⟨x,y⟩ := h1
          omega
          rename_i h1
          apply h1
          constructor
          omega
          omega
        }
        apply kernel_slice_integral''
        exact hf
        apply ProdLikeM.slice_measurable
        apply hA
      }

/- It is fine to import all of Mathlib in your project.
This might make the loading time of a file a bit longer. If you want a good chunk of Mathlib, but not everything, you can `import Mathlib.Tactic` and then add more imports as necessary. -/
import IonescuTulcea.prodLike
import IonescuTulcea.finiteCompProd
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

@[simp]
lemma FiniteCompKernelNat_zero
  {α : ℕ -> Type*}
  [∀m, MeasurableSpace (α m)]
  (K : ∀(m : ℕ), Kernel (∀k : {k|k <= m}, α k) (α (m+1)))
  : FiniteCompKernelNat K n 0 = convert_kernel (K n) := by rfl

@[simp]
lemma compProd'_measure_kernel_step
  {α : ℕ -> Type*}
  [∀m, MeasurableSpace (α m)]
  (μ : Measure (α 0))
  (K : ∀(m : ℕ), Kernel (∀k : {k|k <= m}, α k) (α (m+1)))
  (n : ℕ)
  : compProd' (FiniteCompMeasureKernelNat μ K n) (K n) = FiniteCompMeasureKernelNat μ K (n+1) := by rfl



@[simp]
lemma Kernel.compProd'_measure_kernel_step
  {α : ℕ -> Type*}
  [∀m, MeasurableSpace (α m)]
  (K : ∀(m : ℕ), Kernel (∀k : {k|k <= m}, α k) (α (m+1)))
  (n m : ℕ)
  : Kernel.compProd' (FiniteCompKernelNat K n m) (K (n+m+1)) (p := prod_equiv_6 n (m+1))
    = FiniteCompKernelNat K n (m+1) := by rfl

-- lemma assoc_Kernel.compProd'
--   [MeasurableSpace α₁]
--   [MeasurableSpace α₂]
--   [MeasurableSpace α₃]
--   [MeasurableSpace β₁]
--   [MeasurableSpace β₂]
--   [MeasurableSpace β₃]
--   [MeasurableSpace γ]
--   (K₁ : Kernel α₁ β₁)
--   -- [p₁ : ProdLikeM α₂ α₁ β₁]
--   (K₂ : Kernel α₂ β₂)
--   -- α₁ × β₁ = α₂
--   -- α₁ × β₁ = α₂
--   (K₃ : Kernel α₃ β₃)
--   [p₁ : ProdLikeM α₂ α₁ β₁]
--   [q₁ : ProdLikeM γ β₁ β₂]
--   [p₂ : ProdLikeM α₃ α₂ β₂]
--   [q₂ : ProdLikeM γ β₂ β₃]
--   -- [q₁ : ProdLikeM α₃ α₂ β₂]
--   : Kernel.compProd' (Kernel.compProd' K₁ K₂) K₃
--     = Kernel.compProd' K₁ (Kernel.compProd' K₂ K₃) := by {
--   }

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
  : switch_ProdLikeM.1 e =
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
  : switch_ProdLikeM.1.symm cd =
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
  : (compProd' μ (Kernel.compProd' K L : Kernel α ε) : Measure E)
    = (compProd' (p := switch_ProdLikeM) (compProd' μ K) L : Measure E) := by {
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

      all_goals let sp := switch_ProdLikeM (δ:=δ) (α := α) (γ := γ) (E := E)
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
      · let f a b : ℝ≥0∞ := (sp.equiv.symm ⁻¹' s).indicator 1 (a, b)
        have heq : (fun a ↦ ∫⁻ (b : δ), (sp.1.symm ⁻¹' s).indicator (fun x => 1) (a, b) ∂L a)
          = (fun a => ∫⁻ (b : δ), f a b ∂L a) := by rfl
        rw [heq]

      -- apply Measurable.lintegral_kernel (κ := L)
        -- (β := δ) (κ := L) (s := (switch_ProdLikeM.equiv.symm.1.1 ⁻¹' s))
      -- conv => rhs; intro a; si


      -- apply_fun r.1
      -- conv => lhs; unfold ProdLikeM.equiv; simp
      -- unfold switch_ProdLikeM MeasurableEquiv.switch_equiv
      --   Equiv.switch_equiv MeasurableEquiv.refl MeasurableEquiv.prodCongr


      -- simp [MeasurableEquiv.refl, MeasurableEquiv.prodCongr,
      --   MeasurableEquiv.switch_equiv, Equiv.switch_equiv]


      -- conv => rhs; rhs; intro a; tactic => {
      --   trans
      --   apply lintegral_indicator
      --   apply Measurable.comp'
      --   apply MeasurableEquiv.measurable
      --   exact measurable_prod_mk_left
      --   exact hs
      --   rw [setLIntegral_one]
      -- }

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


-- @[simp]
lemma compProd'_measure_kernel_convert
  {α : ℕ -> Type*}
  [∀m, MeasurableSpace (α m)]
  (μ : Measure (α 0))
  (K : ∀(m : ℕ), Kernel (∀k : {k|k <= m}, α k) (α (m+1)))
  [mK : ∀m, IsMarkovKernel (K m)]
  [hμ : IsProbabilityMeasure μ]
  : compProd' (p := prod_equiv_6 n 1) (FiniteCompMeasureKernelNat μ K n) (convert_kernel (K n))
    = compProd' (FiniteCompMeasureKernelNat μ K n) (K n) := by {
      have hμ' : IsProbabilityMeasure (FiniteCompMeasureKernelNat μ K n) := by infer_instance
      repeat rw [compProd'_def]
      ext s hs
      repeat rw [MeasurableEquiv.map_apply]
      unfold
        convert_kernel
        instEquivalentMeasurableSpace
        MeasurableEquiv.refl
      simp only [coe_setOf, mem_setOf_eq, eq_mpr_eq_cast, MeasurableEquiv.symm_mk,
        MeasurableEquiv.coe_mk, Equiv.coe_fn_symm_mk, Equiv.refl_symm, Equiv.coe_refl,
        Kernel.comap_id]
      rw [compProd_Kernelmap, Measure.map_apply]
      rfl
      all_goals simp_all only [
        Measurable.prod,
        measurable_fst,
        measurable_snd,
        Measurable.comp',
        MeasurableEquiv.measurable,
        MeasurableEquiv.measurableSet_preimage
      ]
    }


lemma compProd'_measure_kernel_finite_comp
  {α : ℕ -> Type*}
  [∀m, MeasurableSpace (α m)]
  (μ : Measure (α 0))
  (K : ∀(m : ℕ), Kernel (∀k : {k|k <= m}, α k) (α (m+1)))
  [mK: ∀m, IsMarkovKernel (K m)]
  [hμ : IsProbabilityMeasure μ]
  (n m : ℕ)
  : compProd' (FiniteCompMeasureKernelNat μ K n) (FiniteCompKernelNat K n m)
    (p := prod_equiv_6 n (m+1))
    = FiniteCompMeasureKernelNat μ K (n+m+1) := by {
      induction m with
      | zero => {
        rw [FiniteCompKernelNat_zero, compProd'_measure_kernel_convert]
        -- Why does simp not take lemma?
        rfl
      }
      | succ m hm => {
        let _ : IsProbabilityMeasure <| FiniteCompMeasureKernelNat μ K n := by infer_instance
        let _ : IsProbabilityMeasure <| (FiniteCompMeasureKernelNat μ K (n + (m + 1)) ⊗ₘ K (n + (m + 1))) := by infer_instance
        let _ : IsProbabilityMeasure ((Measure.map ((instProdLikeMForallValNatMemSetSetOfLeHAddOfNatForall (n + (m + 1))).equiv.symm)
            (FiniteCompMeasureKernelNat μ K (n + (m + 1)) ⊗ₘ K (n + (m + 1))))) := by {
              apply isProbabilityMeasure_map ?_
              simp_all only [coe_setOf, mem_setOf_eq]
              apply Measurable.aemeasurable
              apply MeasurableEquiv.measurable
            }
        let _ : IsProbabilityMeasure <| FiniteCompMeasureKernelNat μ K (n + (m + 1)) := by infer_instance
        let _ : IsProbabilityMeasure <|
          (compProd' (FiniteCompMeasureKernelNat μ K (n + (m + 1))) (K (n + (m + 1)))
            : Measure ((k : ↑{k | k ≤ n + (m + 1) + 1}) → α ↑k)) := by infer_instance
        let p := (prod_equiv_6 (α := α) n ((m+1)+1))
        simp only [coe_setOf, mem_setOf_eq]
        rw [<- Kernel.compProd'_measure_kernel_step]
        rw [<- compProd'_measure_kernel_step]
        rw [assoc_compProd'_kernel_compProd']

        -- congrm compProd' (FiniteCompMeasureKernelNat μ K ?_) (K (n + (m + 1)))
        ext s hs
        unfold compProd' Kernel.compProd' change_right change_left
        simp only [coe_setOf, mem_setOf_eq, Equiv.invFun_as_coe, MeasurableEquiv.coe_toEquiv_symm]
        rw [Measure.map_apply]
        rw [Measure.map_apply (hs := hs)]
        rw [<-setLIntegral_one, <-lintegral_indicator]
        rw [<- setLIntegral_one, <-lintegral_indicator]
        repeat rw [Measure.lintegral_compProd]
        conv => lhs; rhs; intro a; rhs; intro b; tactic => {
            exact show ((p.equiv.symm ⁻¹' s).indicator (fun x ↦ 1) (a,b) : ℝ≥0∞)
            = {b | (a,b) ∈ p.equiv.symm ⁻¹' s}.indicator 1 b by {
              rfl
            }
        }
        conv => lhs; rhs; intro a; tactic => {
          trans
          apply lintegral_indicator
            (show MeasurableSet {b | (a, b) ∈ p.equiv.symm ⁻¹' s} by {
              simp only [mem_preimage, measurableSet_setOf]
              apply Measurable.comp'
              exact MeasurableSet.mem hs
              apply Measurable.comp'
              exact MeasurableEquiv.measurable ProdLikeM.equiv.symm
              exact measurable_prod_mk_left
            })
          apply setLIntegral_one
        }






        -- simp only [coe_setOf, mem_setOf_eq]
        -- rw [<-setLIntegral_one s, <-lintegral_indicator]

        unfold compProd' Kernel.compProd' change_right change_left
        simp only [coe_setOf, mem_setOf_eq, Equiv.invFun_as_coe, MeasurableEquiv.coe_toEquiv_symm]
        rw [Measure.map_apply]

        rw [<- setLIntegral_one]
        rw [Measure.setLIntegral_compProd]

        -- rw [<- setLIntegral_one]

        -- apply_fun cast (show ((k : ↑{k | k ≤ n + (m + 1)}) → α ↑k) = ((k : ↑{k | k ≤ n + m + 1}) → α ↑k) from rfl)
        -- convert HEq _ _
        -- rw [assoc_compProd'_kernel_compProd']

        -- #check assoc_compProd'_kernel_compProd' (FiniteCompMeasureKernelNat μ K n) (FiniteCompKernelNat K n m)
        -- rw [<- assoc_compProd'_kernel_compProd' (p := prod_equiv_6 n (m+1))]
        -- rw [compProd'_measure_kernel_step μ K (n + (m+1)), hm]
      }
    }

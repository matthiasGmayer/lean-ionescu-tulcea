/- It is fine to import all of Mathlib in your project.
This might make the loading time of a file a bit longer. If you want a good chunk of Mathlib, but not everything, you can `import Mathlib.Tactic` and then add more imports as necessary. -/
import Mathlib
-- import Mathlib.MeasureTheory.Measure.ProbabilityMeasure

set_option autoImplicit true
/- open namespaces that you use to shorten names and enable notation. -/
open Function Set Classical

/- recommended whenever you define anything new. -/
noncomputable section


/- Now write definitions and theorems. -/

namespace ProductLike
open MeasureTheory MeasurableSpace Measurable ProbabilityTheory MeasurableEquiv

section ProductLike

variable
  [MeasurableSpace F]
  [MeasurableSpace α]
  [MeasurableSpace β]
  [MeasurableSpace F']
  [MeasurableSpace γ]

class ProdLikeM
(F : Type*) (α β : outParam (Type*))
[MeasurableSpace F] [MeasurableSpace α] [MeasurableSpace β] where
  equiv : F ≃ᵐ α × β


instance : CoeSort (ProdLikeM F α β) (Type u) := ⟨fun _ => F⟩

instance : ProdLikeM (α × β) α β := ⟨MeasurableEquiv.refl (α × β)⟩

def ProdLikeM.symm (p : ProdLikeM F α β) : ProdLikeM F β α := ⟨trans p.equiv prodComm⟩

def ProdLikeM.fst_type (P : ProdLikeM F α β) := α
def ProdLikeM.snd_type (P : ProdLikeM F α β) := β

def ProdLikeM.fst (P : ProdLikeM F α β) (x : P) : α := (P.equiv x).fst
def ProdLikeM.snd (P : ProdLikeM F α β) (x : P) : β := (P.equiv x).snd


def change_left [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ]
  (K : Kernel α β) (τ : α ≃ᵐ γ) : Kernel γ β := K.comap τ.invFun τ.measurable_invFun

def change_right [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ]
  (K : Kernel α β) (τ : β ≃ᵐ γ) : Kernel α γ := K.map τ

def Kernel.compProd'
  (K : Kernel α β)
  (p : ProdLikeM F α β)
  (L : Kernel p γ)
  (q : ProdLikeM F' β γ)
  : Kernel α q :=
  change_right (K ⊗ₖ (change_left L p.equiv)) q.equiv.symm



-- infixl:100 " ⊗ₖ' " => Kernel.compProd'
-- infixl:100 " ⊗ₖ'[" p "]" => Kernel.compProd' p


#check Measure.compProd
def compProd' (μ : Measure α) (K : Kernel α β) [p: ProdLikeM γ α β]
  : MeasureTheory.Measure γ := (μ.compProd K).map p.equiv.symm

-- infixl:100 (priority := high) " ⊗ₘ' " => Measure.compProd'

lemma compProd'_def (μ : Measure α) (K : Kernel α β) (p: ProdLikeM γ α β)
  : compProd' μ K (p := p) = (μ.compProd K).map p.equiv.symm := rfl

lemma compProd'_apply (μ : Measure α) (K : Kernel α β) [p: ProdLikeM γ α β]
  (s : Set (α × β)) (hs : MeasurableSet s)
  : compProd' μ K (p := p) (p.equiv ⁻¹' s) = (μ ⊗ₘ K) s := by {
    rw [compProd'_def]
    rw [Measure.map_apply]
    simp
    exact MeasurableEquiv.measurable ProdLikeM.equiv.symm
    apply MeasurableSet.preimage hs (MeasurableEquiv.measurable p.equiv)
  }

-- @[simp]
-- theorem compProd'_is_Kernel_compProd (K : Kernel α β) (L : Kernel (α × β) γ)
-- : compProd' K ⊗ₖ' L = K ⊗ₖ L := by {
--   rw [show K ⊗ₖ' L = change_right (K ⊗ₖ change_left L ProdLikeM.equiv) ProdLikeM.equiv.symm from rfl]
--   unfold change_right change_left
--   generalize_proofs ms1 ms2
--   rw [show L.comap ProdLikeM.equiv.invFun ms1 = L by {
--     exact rfl
--   }]
--   rw [show ⇑ProdLikeM.equiv.symm = id by {
--     rfl
--   }]
--   exact Kernel.map_id (K ⊗ₖ L)
-- }




section IndexedFamilies

variable {I : Type*} {J K : Set I} [hJK : Fact (Disjoint J K)]
  (α : I -> Type*)
  [∀i, MeasurableSpace (α i)]
  (i : I)
  [hi : Fact (i ∉ J)]

def prod_equiv : (∀i : J, α i) × (∀i: K, α i) ≃ᵐ ∀i : ↑(J ∪ K), α i where
  toFun := fun (x,y) => fun i => if hJ : i.val ∈ J then x ⟨i,hJ⟩ else
  have hK : ↑i ∈ K := by {
    have h : (j : I) -> j ∈ J ∪ K -> j ∉ J -> j ∈ K := by {
      intro j hjk hj
      simp [hj] at hjk
      assumption
    }
    exact h ↑i i.property hJ
  }
  y ⟨i,hK⟩
  invFun z :=
  have hJ : J ⊆ J ∪ K := by exact subset_union_left
  have hK : K ⊆ J ∪ K := by exact subset_union_right
  (J.restrict₂ hJ z, K.restrict₂ hK z)
  left_inv := by {
    unfold LeftInverse
    intro ⟨a,b⟩
    simp
    constructor
    · ext x
      simp
    · ext x
      rw [← @subset_compl_iff_disjoint_left] at hJK
      generalize hJK.1 = hJK
      specialize hJK x.property
      simp at hJK
      simp [hJK, x.property]
  }
  right_inv := by {
    unfold Function.RightInverse LeftInverse
    intro c
    simp
    ext x
    by_cases h : ↑x ∈ J <;> simp [h]
  }
  measurable_toFun := by {
    simp
    apply measurable_pi_lambda
    intro i
    by_cases h : i.val ∈ J <;> simp [h]
    · let f := (fun c : (∀i:J,α i) × (∀i:K,α i) => (c.1 ⟨↑i,h⟩))
      let p1 := fun c : (∀i:J,α i) × (∀i:K,α i) ↦ (c.1 : (∀i:J,α i))
      let eval_i := (fun a : (∀i:J,α i) => a ⟨↑i,h⟩)
      have h : f = eval_i ∘ p1 := by unfold f eval_i p1; ext; simp
      unfold f at h
      rw [h]
      apply Measurable.comp
      apply measurable_pi_apply
      exact measurable_fst
    · generalize_proofs hK
      let f := (fun c : (∀i:J,α i) × (∀i:K,α i) => (c.2 ⟨↑i,hK⟩))
      let p1 := fun c : (∀i:J,α i) × (∀i:K,α i) ↦ (c.2 : (∀i:K,α i))
      let eval_i := (fun a : (∀i:K,α i) => a ⟨↑i,hK⟩)
      have h : f = eval_i ∘ p1 := by unfold f eval_i p1; ext; simp
      unfold f at h
      rw [h]
      apply Measurable.comp
      apply measurable_pi_apply
      exact measurable_snd
    }
  measurable_invFun := by {
    simp
    apply Measurable.prod <;> simp
    exact measurable_restrict₂ subset_union_left
    exact measurable_restrict₂ subset_union_right
  }

instance : ProdLikeM (∀i : ↑(J ∪ K), α i) (∀i : J, α i) (∀i: K, α i) := ⟨(prod_equiv α).symm⟩

instance : ProdLikeM (∀i : ↑(J ∪ {i}), α i) (∀i : J, α i) (α i) :=
  let K : Set I := {i}
  let hJK : Fact (Disjoint J K) := by {
    rw [disjoint_singleton_right]
    assumption
  }
  let p : ProdLikeM (∀i : ↑(J ∪ K), α i) (∀i : J, α i) (∀i: K, α i) := by infer_instance
  let hK : Unique ↑K := uniqueSingleton i
  let τ : (∀i: K, α i) ≃ᵐ α i := piUnique (δ' := K) fun i ↦ α ↑i
  let τ' : (∀i : J, α i) × (∀i: K, α i) ≃ᵐ (∀i : J, α i) × (α i) :=
    (MeasurableEquiv.refl ((i : ↑J) → α ↑i)).prodCongr τ
  ⟨MeasurableEquiv.trans p.equiv τ'⟩

instance : ProdLikeM (∀i : ↑({i} ∪ J), α i) (α i) (∀i : J, α i) :=
  let p : ProdLikeM (∀i : ↑(J ∪ {i}), α i) (∀i : J, α i) (α i) := by infer_instance
  by {
    rw [union_comm]
    exact p.symm
  }

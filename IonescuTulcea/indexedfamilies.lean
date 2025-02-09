/- It is fine to import all of Mathlib in your project.
This might make the loading time of a file a bit longer. If you want a good chunk of Mathlib, but not everything, you can `import Mathlib.Tactic` and then add more imports as necessary. -/
import Mathlib

namespace IndexedFamilies
-- import Mathlib.MeasureTheory.Measure.ProbabilityMeasure

set_option autoImplicit true
/- open namespaces that you use to shorten names and enable notation. -/
open Function Set Classical ENNReal

/- recommended whenever you define anything new. -/
noncomputable section

lemma mem_congr {a b : α} (s t: Set α) (h : a = b) (h' : s = t) : a ∈ s <-> b ∈ t := by rw [h,h']
variable {I : Type*} {α : I -> Type*}

instance project_coerce {I : Type*} : CoeFun (I -> Type _) (fun _ => Set I -> Type _) where
  coe α J := ∀k : J, α k

def hmul {I : Type*} {α : I -> Type*} {J K : Set I} (a : ⇑α J) (b : ⇑α K)
  : ⇑α (J ∪ K) :=
  fun i => if hJ : (i : I) ∈ J then a ⟨i, hJ⟩ else b ⟨i, by aesop⟩

instance : HMul (⇑α J) (⇑α K) (⇑α (J ∪ K)) where
  hMul a b := hmul a b
instance : Coe (α i) (⇑α {i}) where
  coe x := fun j => cast (by aesop) x
instance : HMul (⇑α J) (α i) (⇑α (J ∪ {i})) where
  hMul a b := a * (b : ⇑α {i})

lemma hmul_assoc
  (a : ⇑α J) (b : ⇑α K)
  -- (c : ⇑α L)
  (c : α i)
  : HEq (a * b * c) (a * (b * c)) := by {
    apply hfunext
    simp_all only [union_singleton, union_insert]
    intro n m h
    have h' : (n : I) = m := by {
      refine (Subtype.heq_iff_coe_eq ?_).mp h
      intro x
      simp_all only [union_singleton, mem_insert_iff, mem_union, union_insert]
    }
    obtain ⟨n,hn⟩ := n
    obtain ⟨m,hm⟩ := m
    simp at h'
    subst h'
    suffices HEq (hmul (hmul a b) c ⟨n, hn⟩) (hmul a (hmul b c) ⟨n, hm⟩) by {
      exact this
    }
    unfold hmul
    simp
  }



@[ext]
structure Subfamily (α : I -> Type*) where
  val : ∀k, Option (α k)

instance : CoeFun (Subfamily α) (fun _ => ∀k, Option (α k)) where
  coe s := s.val
instance : CoeDep (Subfamily α) s (∀k, Option (α k)) where
  coe := s.val
instance : CoeDep (∀k, Option (α k)) val (Subfamily α) where
  coe := ⟨val⟩

@[coe]
def DependSubfamily_to_Subfamily (J : Set I) (x : ⇑α J) : Subfamily α
:= ⟨fun j => if h : j ∈ J then some (x ⟨j,h⟩) else none⟩

instance instDependantSubfamily_to_Subfamily {J : Set I} (x : ⇑α J) : CoeDep (⇑α J) x (Subfamily α) where
  coe := DependSubfamily_to_Subfamily J x

@[coe]
def Single_to_Subfamily (i : I) (x : α i) : Subfamily α
:= ⟨fun j => if h : j = i then some (cast (by rw [h]) x) else none⟩

instance instSingle_to_Subfamily {i : I} (x : α i) : CoeDep (α i) x (Subfamily α) where
  coe := Single_to_Subfamily i x
-- instance instSingle_to_Subfamily : CoeDep (α i) x (Subfamily α) where
--   coe := Single_to_Subfamily i x

-- lemma DependantSubfamily_to_Subfamily_bijective :
--   Bijective ((DependantSubfamily_to_Subfamily (α := α)).coe) := by {
--   }

def Subfamily.idx (s : Subfamily α) : Set I := {i | s.val i ≠ none}
lemma Subfamily.mem_idx (s : Subfamily α) (i : I) {x : α i}
  (h : s i = some x) : i ∈ s.idx := by {
    simp [idx]
    simp_all only [reduceCtorEq, not_false_eq_true]
}

@[simp]
lemma Subfamily.coe_idx (J : Set I) (x : ⇑α J) : (x : Subfamily α).idx = J := by {

  simp [*]
}

def Subfamily.get (s : Subfamily α) {i : I} (hi : i ∈ s.idx) : α i :=
  match h : s.val i with
  | some x => x
  | none => by simp [idx, h] at hi

@[simp]
lemma Subfamily.coe_get (J : Set I) (x : ⇑α J) (i : J) : (x : Subfamily α).get (by aesop) = x i := by {
  obtain ⟨i, hi⟩ := i
  simp [get, hi]
  split
  rename_i a b
  simp [hi] at b
  exact b.symm
  rename_i a
  exfalso
  simp [hi] at a
}


def Subfamily.dependant (s : Subfamily α) (J : Set I := s.idx) (hJ : J = s.idx := by rfl) (i : J)
  : α i :=
    have hi : (i : I) ∈ s.idx := by aesop
    s.get hi

-- @[irreducible]
-- instance Subfamily_to_DependantSubfamily_idx : CoeDep (Subfamily α) s (⇑α s.idx) where
--   coe i := s.dependant _ rfl i

instance Subfamily_to_DependantSubfamily [∀k, Inhabited (α k)]
  : CoeDep (Subfamily α) s (⇑α J) where
  coe i := (s i).getD default

def Subfamily.mul {α : I -> Type*} (s t : Subfamily α) : Subfamily α where
  val i := match (s.val i), (t.val i) with
    | some x, _ => some x
    | _     , y => y
lemma Subfamily.mul_idx (s t : Subfamily α) : (Subfamily.mul s t).idx = s.idx ∪ t.idx := by {
  unfold idx mul
  ext i
  rcases hs : s.val i <;> rcases ht : t.val i <;> simp [hs, ht]
}

def Subfamily.one : Subfamily α where
  val _ := none

lemma Subfamily.mul_comm (s t : Subfamily α) (h : Disjoint s.idx t.idx)
  : s.mul t = t.mul s := by {
    unfold mul
    simp only [mk.injEq]
    ext i : 1
    rcases hs : s.val i <;> rcases ht : t.val i <;> simp
    apply mem_idx at hs
    apply mem_idx at ht
    exfalso
    rw [disjoint_iff_inter_eq_empty] at h
    have hu : i ∈ s.idx ∩ t.idx := by {
      simp
      exact ⟨hs, ht⟩
    }
    rw [h] at hu
    contradiction
  }

instance : Monoid (Subfamily α) where
  mul := Subfamily.mul
  mul_assoc := by {
    intro s t r
    let mul := Subfamily.mul (α := α)
    suffices (mul (mul s t) r) = (mul s (mul t r)) by exact this
    ext i : 2
    unfold mul Subfamily.mul
    simp only
    rcases hs : s.val i <;> rcases ht : t.val i <;> rcases hr : r.val i <;> simp
  }
  one := Subfamily.one
  one_mul := by {
    intro s
    suffices Subfamily.one.mul s = s by exact this
    ext i : 2
    unfold Subfamily.mul
    simp only [Subfamily.one]
  }
  mul_one := by {
    intro s
    suffices s.mul Subfamily.one = s by exact this
    ext i : 2
    unfold Subfamily.mul
    simp only [Subfamily.one]
    rcases hs : s.val i <;> simp
  }

def Subfamily.restrict (s : Subfamily α) (J : Set I) : Subfamily α where
  val i := if i ∈ J then s.val i else none

@[simp]
lemma Subfamily.restrict_apply (s : Subfamily α) (J : Set I) (i : I)
: (s.restrict J) i = if i ∈ J then s.val i else none := rfl

lemma Subfamily.restrict_idx (s : Subfamily α) (J : Set I)
  : (s.restrict J).idx = s.idx ∩ J := by {
    unfold idx restrict
    ext x
    simp
    rcases hs : s.val x <;> simp
}

lemma DependantSubfamily_apply_eq_Subfamily_apply
  {J : Set I}
  (x : ⇑α J)
  (j : J)
  : x j = (x : Subfamily α).get (by aesop) := by {
    simp
  }

lemma DependantSubfamily_eq_if_Subfamily_eq
  {J K : Set I}
  (x : ⇑α J)
  (y : ⇑α K)
  (h : (x : Subfamily α) = y)
  : HEq x y := by {
    have hx : (x : Subfamily α).idx = J := by simp
    have hy : (y : Subfamily α).idx = K := by simp
    have hxy : J = K := by {
      rw [←hx, ←hy]
      rw [h]
    }
    subst hxy
    apply hfunext
    rfl
    intro a a' haa'
    simp at haa'
    subst haa'
    simp
    rw [DependantSubfamily_apply_eq_Subfamily_apply x]
    rw [DependantSubfamily_apply_eq_Subfamily_apply y]
    obtain ⟨j,hj⟩ := a
    unfold Subfamily.get
    simp
    apply_fun (· j) at h
    simp at h
    split
    split
    rename_i x g y g'
    rw [h] at g
    simp_all only [Subfamily.coe_idx, ↓reduceDIte, Option.some.injEq]
    exfalso; simp_all only [Subfamily.coe_idx, ↓reduceDIte, Option.some.injEq, reduceCtorEq]
    exfalso; simp_all only [Subfamily.coe_idx, ↓reduceDIte, Option.some.injEq, reduceCtorEq]
  }




-- -- instance : Coe Subfamily I α (α ) := ⟨fun s => ⟨s.index_set, s.family⟩⟩


-- /- Now write definitions and theorems. -/
-- def compose
--   {α : I -> Type*} {J K : Set I}
--   [∀i, Inhabited (α i)]
--   (ω₁ : (∀i:J, α i))
--   (ω₂ : (∀i:K, α i)) (i : I) : α i :=
--     if h : i ∈ J then
--       ω₁ ⟨i,h⟩
--     else if h: i ∈ K then
--       ω₂ ⟨i,h⟩
--     else default

-- def compose'
--   {α : I -> Type*} {J K L : Set I}
--   [∀i, Inhabited (α i)]
--   (ω₁ : (∀i:J, α i))
--   (ω₂ : (∀i:K, α i)) := L.restrict (compose ω₁ ω₂)

-- def blowup
--   {α : I -> Type*}
--   {i : I}
--   (a : α i)
--   : (∀j : ({i} : Set I), α j) := by {
--     intro j
--     rw [j.2]
--     exact a
--   }
-- @[measurability]
-- lemma measurable_blowup
--   {α : I -> Type*}
--   [mα : ∀i, MeasurableSpace (α i)]
--   {i : I}
--   : Measurable (blowup (α := α) (i:=i)) := by {
--     unfold blowup
--     simp
--     generalize_proofs h
--     have h' : ∀j : ({i} : Set I), HEq (mα i) (mα j) := by aesop
--     have h: ∀a, ∀j, cast (h j) a = MeasurableEquiv.cast (h j) (h' j) a := by {
--       intro a j
--       rfl
--     }
--     simp_rw [h]
--     apply measurable_pi_lambda
--     intro a
--     generalize_proofs h1 h2
--     exact MeasurableEquiv.measurable (MeasurableEquiv.cast h1 h2)
--   }

-- def compapp
--   {α : I -> Type*} {J L : Set I}
--   {i : I}
--   [∀i, Inhabited (α i)]
--   (ω₁ : (∀i:J, α i))
--   (ω₂ : (α i))
--   := L.restrict (compose ω₁ <| blowup ω₂)

-- lemma compapp_apply
--   {α : I -> Type*} {J L : Set I}
--   {i j : I}
--   [∀i, Inhabited (α i)]
--   (ω₁ : (∀i:J, α i))
--   (ω₂ : (α i))
--   (h : j ∈ J)
--   (h2 : j ∈ L)
--   : compapp (L := L) ω₁ ω₂ ⟨j, h2⟩ = ω₁ ⟨j, h⟩ := by {
--     simp [compapp, compose, blowup, *]
--   }

-- @[measurability]
-- theorem measurable_compose
--   {α : I -> Type*} {J K : Set I}
--   [∀i, Inhabited (α i)]
--   [∀n, MeasurableSpace (α n)]
--   (ω₁ : (∀i:J, α i))
--   : Measurable (compose (α := α) (K := K) ω₁) := by {
--     unfold compose
--     apply measurable_pi_lambda
--     intro i
--     by_cases hJ : i ∈ J
--     simp [hJ]
--     by_cases hK : i ∈ K
--     simp [hJ, hK]
--     apply measurable_pi_apply
--     simp [hJ, hK]
--   }

-- @[measurability]
-- lemma measurable_compapp
--   {α : I -> Type*} {J L : Set I}
--   [∀i, Inhabited (α i)]
--   [∀n, MeasurableSpace (α n)]
--   (ω₁ : (∀i:J, α i))
--   (i : I)
--   : Measurable (compapp (L:=L) (i:=i) ω₁) := by {
--     unfold compapp
--     apply Measurable.comp'
--     exact measurable_restrict L
--     apply Measurable.comp'
--     exact measurable_compose ω₁
--     apply measurable_blowup
--   }

-- def compose₃
--   {α : I -> Type*} {J K L M : Set I}
--   [∀i, Inhabited (α i)]
--   (ω₁ : (∀i:J, α i))
--   (ω₂ : (∀i:K, α i))
--   (ω₃ : (∀i:L, α i))
--   := M.restrict fun j =>
--     if h : j ∈ J then
--       ω₁ ⟨j,h⟩
--     else if h: j ∈ K then
--       ω₂ ⟨j,h⟩
--     else if h: j ∈ L then
--       ω₃ ⟨j,h⟩
--     else
--       default

-- def compapp₃
--   {α : I -> Type*} {J K M : Set I}
--   [∀i, Inhabited (α i)]
--   (ω₁ : (∀i:J, α i))
--   (ω₂ : (∀i:K, α i))
--   {i : I}
--   (ω₃ : α i)
--   := M.restrict fun j =>
--     if h : j ∈ J then
--       ω₁ ⟨j,h⟩
--     else if h: j ∈ K then
--       ω₂ ⟨j,h⟩
--     else if h: j = i then
--       cast (by aesop) ω₃
--     else
--       default

-- def restrict' {α : I -> Type*}
--   [∀i, Inhabited (α i)]
--   {J : Set I} (ω : (∀i:J, α i))
--   (K : Set I)
--   (k : K)
--   : α k
--   := if h : (k : I) ∈ J then
--     ω ⟨k,h⟩
--   else default

-- -- @[simp]
-- lemma compose₃_heq
--   {α : I -> Type*}
--   {J K L M : Set I}
--   {J' K' L' M' : Set I}
--   [∀i, Inhabited (α i)]
--   (hJ : J=J')
--   (hK : K=K')
--   (hL : L=L')
--   (hM : M=M')
--   : HEq
--     (compose₃ (α := α) (J:=J) (K:=K) (L:=L) (M:=M))
--     (compose₃ (α := α) (J:=J') (K:=K') (L:=L') (M:=M')) := by {
--       subst hJ hK hL hM
--       rfl
--     }

-- lemma compapp₃_heq
--   {α : I -> Type*}
--   {J K M : Set I}
--   {J' K' M' : Set I}
--   (i i' : I)
--   [∀i, Inhabited (α i)]
--   (hJ : J=J')
--   (hK : K=K')
--   (hM : M=M')
--   (hi : i = i')
--   : HEq
--     (compapp₃ (α := α) (J:=J) (K:=K) (M:=M) (i:=i))
--     (compapp₃ (α := α) (J:=J') (K:=K') (M:=M') (i:=i')) := by {
--       subst hJ hK hM hi
--       rfl
--     }

-- lemma compose'_compapp_compapp₃
--   {α : I -> Type*}
--   {J K L M : Set I}
--   (hL : J ∪ K ⊆ L)
--   [∀i, Inhabited (α i)]
--   (ω₁ : (∀i:J, α i))
--   (ω₂ : (∀i:K, α i))
--   {i : I}
--   (hi : i ∈ L)
--   (ω₃ : α i)
--   : compose' ω₁ (compapp (L:=L) ω₂ ω₃) = compapp₃ (M:=M) ω₁ ω₂ ω₃ := by {
--     have hJ : J ⊆ L := by aesop
--     have hK : K ⊆ L := by aesop
--     ext x
--     simp [compose', compapp₃, compose, compapp]
--     by_cases h : (x : I) ∈ J
--     <;> by_cases h' : (x : I) ∈ K
--     <;> by_cases h'' : (x : I) = i
--     <;> simp [h,h']
--     -- aesop
--     intro g; exfalso; apply g; exact hK h'
--     intro g; exfalso; apply g; exact hK h'
--     have g : (x : I) ∈ L := by aesop
--     simp [g, h'', hi]
--     rfl
--     simp only [↓reduceDIte, ite_self, h'']
--   }

-- @[measurability]
-- lemma measurable_compapp₃_fst
--   {α : I -> Type*}
--   {J K M : Set I}
--   [∀i, Inhabited (α i)]
--   [∀n, MeasurableSpace (α n)]
--   (ω₂ : (∀i:K, α i))
--   {i : I}
--   (ω₃ : α i)
--   : Measurable fun ω₁ => (compapp₃ (M:=M) (J:=J) (α := α) ω₁ ω₂ ω₃) := by {
--     unfold compapp₃
--     apply Measurable.comp'
--     exact measurable_restrict M
--     apply measurable_pi_lambda
--     intro j
--     by_cases hJ: j ∈ J
--     · simp only [hJ, ↓reduceDIte]
--       apply measurable_pi_apply
--     · by_cases hK: j ∈ K
--       · simp only [hJ, ↓reduceDIte, hK, measurable_const]
--       · by_cases hi: j = i
--         · simp only [hJ, ↓reduceDIte, hK, measurable_const]
--         · simp only [hJ, ↓reduceDIte, hK, hi, measurable_const]
--   }

-- @[ext]
-- structure Subfamily where
--   idx : Set I
--   val : ⇑α idx

-- def Subfamily.option

-- @[ext]
-- lemma Subfamily.ext (s t : Subfamily α) (h : s.idx = t.idx)
--   (∀i, s.val i = t.val ⟨i, by aesop⟩)
--   : s = t := by {
--   cases s; cases t
--   simp_all only [h, h']
-- }

-- instance : CoeFun (Subfamily α) (fun s => ⇑α s.idx) where
--   coe s := s.val
-- instance : CoeDep (Subfamily α) s (⇑α s.idx) where
--   coe := s.val
-- instance : CoeDep (⇑α J) val (Subfamily α) where
--   coe := ⟨J, val⟩

-- def Subfamily.mul (s t : Subfamily α) : Subfamily α :=
--   ⟨s.idx ∪ t.idx, fun i => if h : ↑i ∈ s.idx then s ⟨i,h⟩
--     else t ⟨i, by aesop⟩⟩

-- lemma Subfamily.mul_idx (s t : Subfamily α) : (Subfamily.mul α s t).idx
--   = s.idx ∪ t.idx := rfl
-- lemma Subfamily.mul_val (s t : Subfamily α) : (Subfamily.mul α s t).val
--   = fun (i : ↑(s.idx ∪ t.idx)) => if h : ↑i ∈ s.idx then s ⟨i,h⟩
--     else t ⟨i, by aesop⟩ := rfl
-- lemma Subfamily.mul_comm (s t : Subfamily α) (h : Disjoint s.idx t.idx)
--   : Subfamily.mul α s t = Subfamily.mul α t s := by {
--     ext i
--     rw [mul_idx]
--     rw [mul_idx]
--     simp_all only [mem_union]
--     apply Iff.intro
--     · intro a
--       cases a with
--       | inl h_1 => simp_all only [or_true]
--       | inr h_2 => simp_all only [true_or]
--     · intro a
--       cases a with
--       | inl h_1 => simp_all only [or_true]
--       | inr h_2 => simp_all only [true_or]
--     apply hfunext

--   }

-- instance : Monoid (Subfamily α) where
--   mul := Subfamily.mul α
--   mul_assoc := by {
--     intro s t r
--     let mul := Subfamily.mul α
--     suffices (mul (mul s t) r) = (mul s (mul t r)) by exact this
--     have h : (mul (mul s t) r).idx = (mul s (mul t r)).idx := by {
--       rw [Subfamily.mul_idx α]
--       rw [Subfamily.mul_idx]
--       rw [Subfamily.mul_idx]
--       rw [Subfamily.mul_idx]
--       rw [union_assoc]
--     }
--     ext i
--     · rw [h]
--     · apply hfunext
--       rw [h]
--       intro a a' haa'
--       have hval : (a : I) = a' := by {
--         refine (Subtype.heq_iff_coe_eq ?_).mp haa'
--         intro x
--         rw [h]
--       }
--       obtain ⟨val, prop⟩ := a
--       obtain ⟨val', prop'⟩ := a'
--       simp at hval
--       subst hval
--       unfold mul Subfamily.mul
--       simp only [mem_union, heq_eq_eq]
--       by_cases h : val ∈ s.idx <;> simp only [h, true_or, ↓reduceDIte, false_or]
--   }
--   one := ⟨∅, fun i => by aesop⟩
--   one_mul := by {
--     intro s;
--     suffices Subfamily.mul α ⟨∅, by aesop⟩ s = s by exact this
--     unfold Subfamily.mul
--     ext i <;> simp
--     apply hfunext
--     · simp
--     · intro a a' haa'
--       have h : ∅ ∪ s.idx = s.idx := by simp
--       have hval : (a : I) = a' := by {
--         refine (Subtype.heq_iff_coe_eq ?_).mp haa'
--         intro x
--         rw [h]
--       }
--       obtain ⟨val, prop⟩ := a
--       obtain ⟨val', prop'⟩ := a'
--       subst hval
--       simp only [heq_eq_eq]
--   }
--   mul_one := sorry


-- -- instance : Coe Subfamily I α (α ) := ⟨fun s => ⟨s.index_set, s.family⟩⟩


-- /- Now write definitions and theorems. -/
-- def compose
--   {α : I -> Type*} {J K : Set I}
--   [∀i, Inhabited (α i)]
--   (ω₁ : (∀i:J, α i))
--   (ω₂ : (∀i:K, α i)) (i : I) : α i :=
--     if h : i ∈ J then
--       ω₁ ⟨i,h⟩
--     else if h: i ∈ K then
--       ω₂ ⟨i,h⟩
--     else default

-- def compose'
--   {α : I -> Type*} {J K L : Set I}
--   [∀i, Inhabited (α i)]
--   (ω₁ : (∀i:J, α i))
--   (ω₂ : (∀i:K, α i)) := L.restrict (compose ω₁ ω₂)

-- def blowup
--   {α : I -> Type*}
--   {i : I}
--   (a : α i)
--   : (∀j : ({i} : Set I), α j) := by {
--     intro j
--     rw [j.2]
--     exact a
--   }
-- @[measurability]
-- lemma measurable_blowup
--   {α : I -> Type*}
--   [mα : ∀i, MeasurableSpace (α i)]
--   {i : I}
--   : Measurable (blowup (α := α) (i:=i)) := by {
--     unfold blowup
--     simp
--     generalize_proofs h
--     have h' : ∀j : ({i} : Set I), HEq (mα i) (mα j) := by aesop
--     have h: ∀a, ∀j, cast (h j) a = MeasurableEquiv.cast (h j) (h' j) a := by {
--       intro a j
--       rfl
--     }
--     simp_rw [h]
--     apply measurable_pi_lambda
--     intro a
--     generalize_proofs h1 h2
--     exact MeasurableEquiv.measurable (MeasurableEquiv.cast h1 h2)
--   }

-- def compapp
--   {α : I -> Type*} {J L : Set I}
--   {i : I}
--   [∀i, Inhabited (α i)]
--   (ω₁ : (∀i:J, α i))
--   (ω₂ : (α i))
--   := L.restrict (compose ω₁ <| blowup ω₂)

-- lemma compapp_apply
--   {α : I -> Type*} {J L : Set I}
--   {i j : I}
--   [∀i, Inhabited (α i)]
--   (ω₁ : (∀i:J, α i))
--   (ω₂ : (α i))
--   (h : j ∈ J)
--   (h2 : j ∈ L)
--   : compapp (L := L) ω₁ ω₂ ⟨j, h2⟩ = ω₁ ⟨j, h⟩ := by {
--     simp [compapp, compose, blowup, *]
--   }

-- @[measurability]
-- theorem measurable_compose
--   {α : I -> Type*} {J K : Set I}
--   [∀i, Inhabited (α i)]
--   [∀n, MeasurableSpace (α n)]
--   (ω₁ : (∀i:J, α i))
--   : Measurable (compose (α := α) (K := K) ω₁) := by {
--     unfold compose
--     apply measurable_pi_lambda
--     intro i
--     by_cases hJ : i ∈ J
--     simp [hJ]
--     by_cases hK : i ∈ K
--     simp [hJ, hK]
--     apply measurable_pi_apply
--     simp [hJ, hK]
--   }

-- @[measurability]
-- lemma measurable_compapp
--   {α : I -> Type*} {J L : Set I}
--   [∀i, Inhabited (α i)]
--   [∀n, MeasurableSpace (α n)]
--   (ω₁ : (∀i:J, α i))
--   (i : I)
--   : Measurable (compapp (L:=L) (i:=i) ω₁) := by {
--     unfold compapp
--     apply Measurable.comp'
--     exact measurable_restrict L
--     apply Measurable.comp'
--     exact measurable_compose ω₁
--     apply measurable_blowup
--   }

-- def compose₃
--   {α : I -> Type*} {J K L M : Set I}
--   [∀i, Inhabited (α i)]
--   (ω₁ : (∀i:J, α i))
--   (ω₂ : (∀i:K, α i))
--   (ω₃ : (∀i:L, α i))
--   := M.restrict fun j =>
--     if h : j ∈ J then
--       ω₁ ⟨j,h⟩
--     else if h: j ∈ K then
--       ω₂ ⟨j,h⟩
--     else if h: j ∈ L then
--       ω₃ ⟨j,h⟩
--     else
--       default

-- def compapp₃
--   {α : I -> Type*} {J K M : Set I}
--   [∀i, Inhabited (α i)]
--   (ω₁ : (∀i:J, α i))
--   (ω₂ : (∀i:K, α i))
--   {i : I}
--   (ω₃ : α i)
--   := M.restrict fun j =>
--     if h : j ∈ J then
--       ω₁ ⟨j,h⟩
--     else if h: j ∈ K then
--       ω₂ ⟨j,h⟩
--     else if h: j = i then
--       cast (by aesop) ω₃
--     else
--       default

-- def restrict' {α : I -> Type*}
--   [∀i, Inhabited (α i)]
--   {J : Set I} (ω : (∀i:J, α i))
--   (K : Set I)
--   (k : K)
--   : α k
--   := if h : (k : I) ∈ J then
--     ω ⟨k,h⟩
--   else default

-- -- @[simp]
-- lemma compose₃_heq
--   {α : I -> Type*}
--   {J K L M : Set I}
--   {J' K' L' M' : Set I}
--   [∀i, Inhabited (α i)]
--   (hJ : J=J')
--   (hK : K=K')
--   (hL : L=L')
--   (hM : M=M')
--   : HEq
--     (compose₃ (α := α) (J:=J) (K:=K) (L:=L) (M:=M))
--     (compose₃ (α := α) (J:=J') (K:=K') (L:=L') (M:=M')) := by {
--       subst hJ hK hL hM
--       rfl
--     }

-- lemma compapp₃_heq
--   {α : I -> Type*}
--   {J K M : Set I}
--   {J' K' M' : Set I}
--   (i i' : I)
--   [∀i, Inhabited (α i)]
--   (hJ : J=J')
--   (hK : K=K')
--   (hM : M=M')
--   (hi : i = i')
--   : HEq
--     (compapp₃ (α := α) (J:=J) (K:=K) (M:=M) (i:=i))
--     (compapp₃ (α := α) (J:=J') (K:=K') (M:=M') (i:=i')) := by {
--       subst hJ hK hM hi
--       rfl
--     }

-- lemma compose'_compapp_compapp₃
--   {α : I -> Type*}
--   {J K L M : Set I}
--   (hL : J ∪ K ⊆ L)
--   [∀i, Inhabited (α i)]
--   (ω₁ : (∀i:J, α i))
--   (ω₂ : (∀i:K, α i))
--   {i : I}
--   (hi : i ∈ L)
--   (ω₃ : α i)
--   : compose' ω₁ (compapp (L:=L) ω₂ ω₃) = compapp₃ (M:=M) ω₁ ω₂ ω₃ := by {
--     have hJ : J ⊆ L := by aesop
--     have hK : K ⊆ L := by aesop
--     ext x
--     simp [compose', compapp₃, compose, compapp]
--     by_cases h : (x : I) ∈ J
--     <;> by_cases h' : (x : I) ∈ K
--     <;> by_cases h'' : (x : I) = i
--     <;> simp [h,h']
--     -- aesop
--     intro g; exfalso; apply g; exact hK h'
--     intro g; exfalso; apply g; exact hK h'
--     have g : (x : I) ∈ L := by aesop
--     simp [g, h'', hi]
--     rfl
--     simp only [↓reduceDIte, ite_self, h'']
--   }

-- @[measurability]
-- lemma measurable_compapp₃_fst
--   {α : I -> Type*}
--   {J K M : Set I}
--   [∀i, Inhabited (α i)]
--   [∀n, MeasurableSpace (α n)]
--   (ω₂ : (∀i:K, α i))
--   {i : I}
--   (ω₃ : α i)
--   : Measurable fun ω₁ => (compapp₃ (M:=M) (J:=J) (α := α) ω₁ ω₂ ω₃) := by {
--     unfold compapp₃
--     apply Measurable.comp'
--     exact measurable_restrict M
--     apply measurable_pi_lambda
--     intro j
--     by_cases hJ: j ∈ J
--     · simp only [hJ, ↓reduceDIte]
--       apply measurable_pi_apply
--     · by_cases hK: j ∈ K
--       · simp only [hJ, ↓reduceDIte, hK, measurable_const]
--       · by_cases hi: j = i
--         · simp only [hJ, ↓reduceDIte, hK, measurable_const]
--         · simp only [hJ, ↓reduceDIte, hK, hi, measurable_const]
--   }

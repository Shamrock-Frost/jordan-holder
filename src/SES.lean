import group_theory.subgroup
import group_theory.quotient_group
import group_theory.category
open category_theory

structure SES (A B C : Group) :=
(f : A ⟶ B) (g : B ⟶ C)
(f_inj : function.injective f)
(g_surj : function.surjective g)
(im_f_eq_ker_g : set.range f = is_group_hom.ker g)

def SES.normal_quotient {G : Group} (H : set G) [normal_subgroup H]
  : SES (Group.of H) G (Group.of (quotient_group.quotient H)) := {
    f := ⟨subtype.val, subtype_val.is_group_hom⟩,
    g := ⟨quotient_group.mk, quotient_group.is_group_hom _⟩,
    f_inj := subtype.val_injective,
    g_surj := @quotient.exists_rep _ (quotient_group.left_rel _),
    im_f_eq_ker_g := by {
      unfold_coes, rw [quotient_group.ker_mk, subtype.val_range], refl
    } }

def is_group_hom.coim {G H : Group} (φ : G → H) [is_group_hom φ]
  := quotient_group.quotient (is_group_hom.ker φ)

instance coim_is_group {G H : Group}
  {φ : G → H} [is_group_hom φ] : group (is_group_hom.coim φ) :=
  quotient_group.group (is_group_hom.ker φ)

def SES.ker_coim {G H : Group} (φ : G → H) [is_group_hom φ]
  : SES (Group.of (is_group_hom.ker φ)) G (Group.of (is_group_hom.coim φ)) :=
  SES.normal_quotient (is_group_hom.ker φ)

instance is_group_hom.range_factorization {G H : Group} (φ : G → H) [is_group_hom φ]
  : is_group_hom (set.range_factorization φ) := is_group_hom.mk' $ by {
    intros x y, apply subtype.eq,
    rw subtype_val.is_group_hom.map_mul,
    transitivity φ (x * y), refl,
    transitivity φ x * φ y,
    apply is_mul_hom.map_mul, refl
  }

def SES.ker_im {G H : Group} (φ : G → H) [is_group_hom φ]
  : SES (Group.of (is_group_hom.ker φ)) G (Group.of (set.range φ)) := {
    f := ⟨subtype.val, subtype_val.is_group_hom⟩,
    g := ⟨set.range_factorization φ, by apply_instance⟩,
    f_inj := subtype.val_injective,
    g_surj := set.surjective_onto_range,
    im_f_eq_ker_g := by {
      unfold_coes,
      transitivity is_group_hom.ker φ,
      rw subtype.range_val, funext, refl,
      funext, simp [set.range_factorization],
      transitivity φ x = 1,
      rw ← is_group_hom.mem_ker φ, refl,
      rw ← @set.mem_def _ _ (is_group_hom.ker _),
      rw is_group_hom.mem_ker, rw subtype.ext, refl } }

lemma SES.left_normal {A B C : Group} (S : SES A B C)
  : normal_subgroup (set.range S.f) := 
  by rw SES.im_f_eq_ker_g; apply is_group_hom.normal_subgroup_ker

noncomputable
def SES.f_rev {A B C : Group} (S : SES A B C) : set.range S.f → A :=
λ y, classical.some y.property

lemma SES.f_rev_spec_r {A B C : Group} (S : SES A B C)
  : ∀ y, S.f (S.f_rev y) = y := λ y, classical.some_spec y.property

lemma SES.f_rev_spec_l {A B C : Group} (S : SES A B C)
  : ∀ x, S.f_rev ⟨S.f x, x, rfl⟩ = x :=
  λ x, S.f_inj (S.f_rev_spec_r ⟨S.f x, x, rfl⟩)

instance SES.f_rev_hom {A B C} {S : SES A B C}
  : is_group_hom (SES.f_rev S) :=
  @is_group_hom.mk _ _ _ _ (SES.f_rev S) $ by {
    constructor, intros,
    cases x with x hx, cases y with y hy,
    cases hx with a ha, cases hy with b hb,
    subst ha, subst hb,
    transitivity SES.f_rev S ⟨S.f (a * b), a*b, rfl⟩,
    congr, apply subtype.eq, simp,
    rw (is_group_hom.to_is_monoid_hom S.f).map_mul,
    apply subtype_val.is_monoid_hom.map_mul,
    repeat { rw SES.f_rev_spec_l } }


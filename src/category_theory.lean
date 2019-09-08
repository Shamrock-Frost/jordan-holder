import category_theory.isomorphism
import category_theory.category
import group_theory.category

open category_theory

universes v u

def subtype_val.group_hom {G : Group} {s : set G} [is_subgroup s]
  : Group.of s ⟶ G := ⟨subtype.val, subtype_val.is_group_hom⟩

instance is_group_hom.range_factorization {G H : Group} (φ : G → H) [is_group_hom φ]
  : is_group_hom (set.range_factorization φ) := is_group_hom.mk' $ by {
    intros x y, apply subtype.eq,
    rw subtype_val.is_group_hom.map_mul,
    transitivity φ (x * y), refl,
    transitivity φ x * φ y,
    apply is_mul_hom.map_mul, refl
  }

noncomputable
def Group.inj_im_iso {G H : Group} (φ : G ⟶ H) (h : function.injective φ)
  : G ≅ Group.of (set.range φ) := {
    hom := ⟨set.range_factorization φ, by apply_instance⟩,
    inv := ⟨λ x : Group.of (set.range φ), @function.inv_fun _ ⟨1⟩ _ φ x.val,
            is_group_hom.mk' $ λ x y, by {
              cases x with x hx, cases hx with a ha, subst ha,
              cases y with y hy, cases hy with b hb, subst hb,
              rw is_monoid_hom.map_mul subtype.val,
              simp, rw ← is_monoid_hom.map_mul φ,
              repeat { rw function.left_inverse_inv_fun },
              any_goals { assumption }, exact subtype_val.is_monoid_hom }⟩,
   hom_inv_id' := by intros; ext; apply @function.left_inverse_inv_fun; exact h,
   inv_hom_id' := by { intros, ext, unfold_coes, simp,
                       dsimp [set.range_factorization], apply subtype.eq, simp,
                       apply function.inv_fun_eq, exact x.property } }

def Group.surj_im_iso {G H : Group} (φ : G ⟶ H) (h : function.surjective φ)
  : Group.of (set.range φ) ≅ H := {
    hom := subtype_val.group_hom,
    inv := ⟨λ x, ⟨x, h x⟩, is_group_hom.mk' $ λ x y, subtype.eq $
                           by rw is_monoid_hom.map_mul subtype.val;
                              exact subtype_val.is_monoid_hom⟩ }

noncomputable
def Group.iso_of_bijective {G H : Group} (φ :  G ⟶ H) (h : function.bijective φ)
  := iso.trans (Group.inj_im_iso φ h.left) (Group.surj_im_iso φ h.right)

def Group.iso_left_inverse {G H : Group} (φ : G ≅ H)
  : function.left_inverse φ.inv φ.hom :=
  λ x, by { transitivity (φ.inv ∘ φ.hom) x, refl,
            transitivity id x, apply congr_fun,
            exact subtype.mk.inj φ.hom_inv_id, refl }

lemma Group.iso_inj {G H : Group} (φ : G ≅ H) : function.injective φ.hom :=
  function.injective_of_left_inverse (Group.iso_left_inverse φ)

def Group.iso_right_inverse {G H : Group} (φ : G ≅ H)
  : function.right_inverse φ.inv φ.hom :=
  Group.iso_left_inverse φ.symm

lemma Group.iso_surj {G H : Group} (φ : G ≅ H) : function.surjective φ.hom :=
  function.surjective_of_has_right_inverse ⟨_, Group.iso_right_inverse φ⟩

lemma Group.iso_bij  {G H : Group} (φ : G ≅ H) : function.bijective φ.hom :=
  ⟨Group.iso_inj φ, Group.iso_surj φ⟩

def Group.ker_of_inj_comp {G H H' : Group} (φ : G ⟶ H) (ψ : H ⟶ H')
  (h : function.injective ψ)
  : is_group_hom.ker (φ ≫ ψ) = is_group_hom.ker φ :=
begin
  unfold_coes, simp, dsimp [is_group_hom.ker],
  rw set.preimage_comp, congr,
  rw is_group_hom.inj_iff_trivial_ker ψ at h,
  assumption
end

def Group.ker_of_comp_inj {G H K : Group}
  (φ : G ⟶ K) (ψ : H ⟶ G) (h : function.injective ψ)
  : is_group_hom.ker (ψ ≫ φ) = ψ ⁻¹' is_group_hom.ker φ :=
  by apply set.preimage_comp

def Group.subsingleton_iso (G H : Group) [subsingleton G] [subsingleton H] : G ≅ H := {
  hom := ⟨λ x, 1, is_group_hom.mk' (λ x y, subsingleton.elim _ _)⟩,
  inv := ⟨λ x, 1, is_group_hom.mk' (λ x y, subsingleton.elim _ _)⟩
}

def pullback {A B C : Type _} (f : A → C) (g : B → C)
  := { p : A × B | f p.fst = g p.snd }

def pullback_of_inj_to_inter {A B C : Type _} {f : A → C} {g : B → C}
  (hf : function.injective f) (hg : function.injective g)
  : pullback f g → set.inter (set.range f) (set.range g) :=
  λ x, subtype.mk (f x.val.fst) $
      by { constructor, apply set.mem_range_self, 
           rw (_ : f x.val.fst = g x.val.snd), apply set.mem_range_self,
           exact x.property }

lemma pullback_of_inj_to_inter_is_bijective {A B C : Type _} {f : A → C} {g : B → C}
  (hf : function.injective f) (hg : function.injective g)
  : function.bijective (pullback_of_inj_to_inter hf hg) :=
begin
  constructor,
  { intros x y hxy,
    cases x with x hx, cases x with x₁ x₂,
    cases y with y hy, cases y with y₁ y₂,
    simp, simp [pullback_of_inj_to_inter] at hxy,
    apply and.intro (hf hxy),
    apply hg, transitivity f x₁, exact hx.symm,
    rw hxy, exact hy },
  { intro y, cases y with y hy, cases hy with hy₁ hy₂,
    cases hy₁ with a ha, cases hy₂ with b hb,
    subst hb, use ⟨(a, b), ha⟩, exact subtype.eq ha }
end

noncomputable
def pullback_inj_fin {A B C : Type _} {f : A → C} {g : B → C}
  (hf : function.injective f) (hg : function.injective g) [fintype C]
  : fintype (pullback f g) :=
  fintype.of_injective (subtype.val ∘ pullback_of_inj_to_inter hf hg)
                       (function.injective_comp subtype.val_injective
                        $ and.left $ pullback_of_inj_to_inter_is_bijective hf hg)

local attribute [instance] classical.prop_decidable
lemma pullback_card_lt_of_conflict {A B C : Type _} {f : A → C} {g : B → C}
  (hf : function.injective f) (hg : function.injective g) [fintype C]
  (a : A) (hx : ∀ b : B, f a ≠ g b)
  : @fintype.card (pullback f g) (pullback_inj_fin hf hg) < fintype.card C := by {
    apply @nat.lt_of_le_of_lt _ (fintype.card (set.inter (set.range f) (set.range g))),
    apply fintype.card_le_of_injective,
    apply and.left (pullback_of_inj_to_inter_is_bijective hf hg),
    unfold_coes, rw fintype.subtype_card,
    apply finset.card_lt_card, rw finset.ssubset_iff,
    existsi f a, constructor,
    { rw finset.mem_filter, intro h, cases h,
      cases h_right, apply hx, symmetry, assumption },
    { intros x h, apply finset.mem_univ } 
  }

instance {A B} [group A] [group B] : group (A × B) := {
  mul := λ p q, ⟨p.fst * q.fst, p.snd * q.snd⟩,
  one := ⟨1, 1⟩,
  inv := λ p, ⟨p.fst⁻¹, p.snd⁻¹⟩,
  mul_assoc := by { intros, simp, constructor; apply mul_assoc },
  one_mul := by intros p; apply prod.ext; apply one_mul,
  mul_one := by intros p; apply prod.ext; apply mul_one,
  mul_left_inv := by intros p; apply prod.ext; apply mul_left_inv
}

instance prod_fst.is_group_hom {α β} [group α] [group β]
  : is_group_hom (@prod.fst α β) := is_group_hom.mk' $ λ _ _, rfl
instance prod_snd.is_group_hom {α β} [group α] [group β]
  : is_group_hom (@prod.snd α β) := is_group_hom.mk' $ λ _ _, rfl

def Group.fst {A B : Group.{u}} : Group.of (A × B) ⟶ A :=
  ⟨prod.fst, by apply_instance⟩

def Group.snd {A B : Group.{u}} : Group.of (A × B) ⟶ B :=
  ⟨prod.snd, by apply_instance⟩

instance {A B C : Group} {f : A ⟶ C} {g : B ⟶ C}
   : is_subgroup (pullback f g) := {
   inv_mem := by { intros p h, cases p with x y, refine (_ : f x⁻¹ = g y⁻¹),
                   rw [is_group_hom.map_inv f, is_group_hom.map_inv g],
                   rw (_ : f x = g y), assumption },
   to_is_submonoid := {
     one_mem := eq.trans (is_monoid_hom.map_one f) $ eq.symm $ is_monoid_hom.map_one g,
     mul_mem := by { intros p q hp hq, cases p with p₁ p₂, cases q with q₁ q₂,
                     refine (_ : f (p₁ * q₁) = g (p₂ * q₂)),
                     rw [is_monoid_hom.map_mul f, is_monoid_hom.map_mul g],
                     congr; assumption } } }

def Group.pullback_of_isos_is_iso {G G' H H': Group} (iso : H ≅ H')
  (f : G ⟶ H) (f' : G' ⟶ H')
  : Group.of (pullback (f ≫ iso.hom) f') ≅ Group.of (pullback (f' ≫ iso.inv) f) := {
    hom := ⟨λ p, ⟨p.val.swap, show iso.inv (f' p.val.snd) = f (p.val.fst),
                              from eq.trans (eq.symm $ congr_arg iso.inv p.property)
                                            (Group.iso_left_inverse iso (f p.val.fst))⟩,
            is_group_hom.mk' $ λ x y, subtype.eq $ by cases x; cases x_val; cases y; cases y_val; refl⟩,
    inv := ⟨λ p, ⟨p.val.swap, show iso.hom (f p.val.snd) = f' (p.val.fst),
                              from eq.trans (eq.symm $ congr_arg iso.hom p.property)
                                            (Group.iso_left_inverse iso.symm (f' p.val.fst))⟩,
            is_group_hom.mk' $ λ x y, subtype.eq $ by cases x; cases x_val; cases y; cases y_val; refl⟩,
  }

lemma surj_im_normal {G H : Group}
  (φ : G ⟶ H) (h : function.surjective φ)
  (N : set G) [normal_subgroup N]
  : normal_subgroup (φ '' N) := normal_subgroup.mk $ by {
    intros n hn x, cases hn with y hn, cases hn with ha ha,
    subst ha, cases h x with b hb, subst hb,
    rw [← is_group_hom.map_inv φ, ← is_monoid_hom.map_mul φ, ← is_monoid_hom.map_mul φ],
    existsi b * y * b⁻¹, refine and.intro _ rfl,
    apply normal_subgroup.normal, assumption
  }

instance Group.inhabited {G} [group G] : inhabited G := ⟨1⟩

def Group.iso_restrict {G G' : Group} (iso : G ≅ G')
  (H : set G) [is_subgroup H] : Group.of H ≅ Group.of (iso.hom '' H) := {
    hom := ⟨λ x, ⟨iso.hom x.val, x.val, x.property, rfl⟩,
            is_group_hom.mk' $ by {
              intros x y, unfold_coes, apply subtype.eq, simp,
              rw [is_monoid_hom.map_mul subtype.val, is_monoid_hom.map_mul iso.hom.val],
              congr, exact subtype_val.is_monoid_hom
            }⟩,
    inv := ⟨λ x, ⟨iso.inv x.val,
                  by { cases x, cases x_property with a ha,
                       cases ha with ha ha, subst ha, simp,
                       rw Group.iso_left_inverse, assumption }⟩,
                  is_group_hom.mk' $ by {
                    intros x y, unfold_coes, apply subtype.eq, simp,
                    rw [is_monoid_hom.map_mul subtype.val, is_monoid_hom.map_mul iso.inv.val],
                    congr, exact subtype_val.is_monoid_hom
                  }⟩,
    hom_inv_id' := by {
      unfold_coes, simp, ext,
      apply subtype.eq, refine congr_fun _ x,
      funext, apply congr_fun (subtype.mk.inj iso.hom_inv_id)
    },
    inv_hom_id' := by {
      unfold_coes, simp, ext,
      apply subtype.eq, refine congr_fun _ x,
      funext, apply congr_fun (subtype.mk.inj iso.inv_hom_id)
    }
  }

lemma Group.eq_of_im_eq_and_contain_ker
  {G K : Group} (φ : G ⟶ K) {s : set G} [is_subgroup s]
  (h1 : φ '' s = set.univ) (h2 : is_group_hom.ker φ ⊆ s)
  : s = set.univ := by {
    apply set.eq_univ_of_univ_subset, intros x h, clear h,
    have : φ x ∈ set.univ := set.mem_univ _, rw ← h1 at this,
    cases this with y h,
    have := is_group_hom.inv_ker_one' _ h.right,
    rw ← is_group_hom.mem_ker φ at this, have := h2 this,
    rw (_ : x = y * (y⁻¹ * x)),
    apply is_submonoid.mul_mem, exact h.left, assumption,
    symmetry, apply mul_inv_cancel_left
  }

def Group.subroup_eq_of_eq {G : Group} {s t : set G}
  [is_subgroup s] [is_subgroup t] (h : s = t)
  : Group.of s = Group.of t := by {
    tactic.unfreeze_local_instances, subst h,
  }

lemma weird {H G : Group} {s t : set G} [is_subgroup s] [is_subgroup t]
  (h : s = t)
  (iso : Group.of t ≅ H)
  (x : s)
  : iso.hom.val (@eq.rec _ _ subtype x _ h)
  = (@eq.rec _ _ (λ K : Group, K ≅ H)
             iso _ (Group.subroup_eq_of_eq h)
    .symm).hom.val x :=
begin
  admit
end

inductive Group.list_equiv : list Group → list Group → Prop
| nil : Group.list_equiv [] []
| skip : ∀ G G' {xs ys}, (G ≅ G') → Group.list_equiv xs ys → Group.list_equiv (G::xs) (G'::ys)
| swap : ∀ G G' {xs}, Group.list_equiv (G::G'::xs) (G'::G::xs)
| trans : ∀ {xs ys zs}, 
  Group.list_equiv xs ys
  → Group.list_equiv ys zs
  → Group.list_equiv xs zs
import group_theory.subgroup
import group_theory.quotient_group
import group_theory.category
import .category_theory
open category_theory

universe u
structure SES (A B C : Group.{u}) :=
(f : A ⟶ B) (g : B ⟶ C)
(f_inj : function.injective f)
(g_surj : function.surjective g)
(im_f_eq_ker_g : set.range f = is_group_hom.ker g)

lemma SES.is_cc {A B C : Group} (S : SES A B C)
  : ∀ x : A, S.g (S.f x) = 1 :=
  by { intro x, apply iff.mp (is_group_hom.mem_ker S.g), 
       rw ← SES.im_f_eq_ker_g, existsi x, refl }

lemma is_group_hom.im_trivial {G H : Group} (φ : G → H) [is_group_hom φ]
  : φ '' is_subgroup.trivial G = is_subgroup.trivial H :=
begin
  simp [set.image, set_of], rw is_group_hom.map_one φ, 
  simp [is_subgroup.trivial], funext, apply propext,
  constructor; intro h,
  { rw h, apply or.inl, refl },
  { symmetry, apply or.resolve_right h, exact not_false }
end

lemma SES.inj_of_left_triv {A B C : Group} [subsingleton A] (S : SES A B C)
  : function.injective S.g :=
begin
  apply iff.mpr (is_group_hom.inj_iff_trivial_ker S.g),
  rw ← S.im_f_eq_ker_g, 
  transitivity S.f '' is_subgroup.trivial A,
  rw ← set.image_univ, congr, ext, simp, apply subsingleton.elim,
  apply is_group_hom.im_trivial
end

noncomputable
def SES.iso_of_left_triv {A B C : Group} [subsingleton A] (S : SES A B C) : B ≅ C :=
  Group.iso_of_bijective S.g ⟨S.inj_of_left_triv, S.g_surj⟩

lemma SES.surj_of_right_triv {A B C : Group} [subsingleton C] (S : SES A B C)
  : function.surjective S.f :=
begin
  rw [← set.range_iff_surjective, S.im_f_eq_ker_g],
  ext, rw is_group_hom.mem_ker, simp,
  apply subsingleton.elim,
end

noncomputable
def SES.iso_of_right_triv {A B C : Group} [subsingleton C] (S : SES A B C) : A ≅ B :=
  Group.iso_of_bijective S.f ⟨S.f_inj, S.surj_of_right_triv⟩

def SES.transport_iso_mid {A B B' C : Group}
  (S : SES A B C) (iso : B ≅ B') : SES A B' C :=
  { f := S.f ≫ iso.hom, g := iso.inv ≫ S.g,
    f_inj := function.injective_comp (Group.iso_inj iso) S.f_inj,
    g_surj := function.surjective_comp S.g_surj (Group.iso_surj iso.symm),
    im_f_eq_ker_g := by {
      unfold_coes, simp, 
      rw set.range_comp,
      have := Group.ker_of_comp_inj S.g iso.inv (Group.iso_inj iso.symm),
      unfold_coes at this, simp at this, rw this,
      have := S.im_f_eq_ker_g, unfold_coes at this, rw this,
      apply congr_fun, apply set.image_eq_preimage_of_inverse,
      apply Group.iso_left_inverse, apply Group.iso_right_inverse } }

def SES.transport_iso_right {A B C C' : Group}
  (S : SES A B C) (iso : C ≅ C') : SES A B C' :=
  { f := S.f, g := S.g ≫ iso.hom, f_inj := S.f_inj,
    g_surj := function.surjective_comp
                (Group.iso_surj iso)
                S.g_surj,
    im_f_eq_ker_g := by {
      unfold_coes, simp,
      transitivity is_group_hom.ker S.g,
      exact S.im_f_eq_ker_g,
      transitivity is_group_hom.ker (@category_struct.comp Group _ _ _ _ S.g iso.hom),
      symmetry, apply Group.ker_of_inj_comp,
      apply Group.iso_inj, refl } }

def SES.self_right (G : Group) : SES 1 G G :=
  { f := ⟨λ x, 1, is_group_hom.mk' (λ x y, eq.symm $ mul_one 1)⟩,
    g := 𝟙 G,
    f_inj := by { intros x y _, apply subsingleton.elim },
    g_surj := λ x, ⟨x, rfl⟩,
    im_f_eq_ker_g := by {
      transitivity is_subgroup.trivial G,
      ext, unfold_coes, simp, constructor; intro h; exact h.symm,
      symmetry, apply iff.mpr (is_group_hom.trivial_ker_iff_eq_one _),
      intros x hx, exact hx } }

def SES.normal_quotient {G : Group} (H : set G) [normal_subgroup H]
  : SES (Group.of H) G (Group.of (quotient_group.quotient H)) := {
    f := subtype_val.group_hom,
    g := ⟨quotient_group.mk, quotient_group.is_group_hom _⟩,
    f_inj := subtype.val_injective,
    g_surj := @quotient.exists_rep _ (quotient_group.left_rel _),
    im_f_eq_ker_g := by {
      unfold_coes, transitivity set.range subtype.val, refl,
      rw [quotient_group.ker_mk, subtype.val_range], refl } }

def is_group_hom.coim {G H : Group} (φ : G → H) [is_group_hom φ]
  := quotient_group.quotient (is_group_hom.ker φ)

instance coim_is_group {G H : Group}
  {φ : G → H} [is_group_hom φ] : group (is_group_hom.coim φ) :=
  quotient_group.group (is_group_hom.ker φ)

def SES.ker_coim {G H : Group} (φ : G → H) [is_group_hom φ]
  : SES (Group.of (is_group_hom.ker φ)) G (Group.of (is_group_hom.coim φ)) :=
  SES.normal_quotient (is_group_hom.ker φ)

def SES.ker_im {G H : Group} (φ : G → H) [is_group_hom φ]
  : SES (Group.of (is_group_hom.ker φ)) G (Group.of (set.range φ)) := {
    f := subtype_val.group_hom,
    g := ⟨set.range_factorization φ, by apply_instance⟩,
    f_inj := subtype.val_injective,
    g_surj := set.surjective_onto_range,
    im_f_eq_ker_g := by {
      unfold_coes,
      transitivity set.range subtype.val, refl,
      transitivity is_group_hom.ker φ,
      rw subtype.range_val, funext,
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

noncomputable
def SES.left_iso_range {A B C : Group} (S : SES A B C) : A ≅ Group.of (set.range S.f) := {
  hom := ⟨λ x, ⟨S.f x, set.mem_range_self x⟩,
          is_group_hom.mk' $ λ x y, by {
            apply subtype.eq, rw is_monoid_hom.map_mul subtype.val,
            apply is_monoid_hom.map_mul S.f, exact subtype_val.is_monoid_hom
          }⟩,
  inv := ⟨S.f_rev, by apply_instance⟩,
  hom_inv_id' := subtype.eq (funext S.f_rev_spec_l),
  inv_hom_id' := subtype.eq (funext $ λ x, subtype.eq $ S.f_rev_spec_r x)
}

noncomputable
def SES.pullback {H G K A B : Group} (S : SES H G K) (S' : SES A K B)
  : SES H (Group.of ((S.g) ⁻¹' set.range (S'.f))) A := 
  { f := ⟨λ x, subtype.mk (S.f x)
            $ by { rw set.mem_preimage, 
                    have : S.f x ∈ is_group_hom.ker S.g,
                    { rw ← SES.im_f_eq_ker_g, existsi x, refl },
                    rw this.resolve_right not_false,
                    have : is_subgroup (set.range S'.f) := is_group_hom.range_subgroup S'.f,
                    apply is_submonoid.one_mem },
          @is_group_hom.mk _ _ _ _ _ $ by {
      constructor, intros, apply subtype.eq,
      unfold_coes, simp, transitivity S.f x * S.f y,
      apply is_monoid_hom.map_mul, refl }⟩,
    f_inj := by { intros x y h, apply S.f_inj, 
                  unfold_coes at h, simp at h, exact h },
    g := ⟨λ x, S'.f_rev ⟨S.g x.val, x.property⟩,
          @is_group_hom.mk _ _ _ _ _ $ by {
            constructor, intros, 
            rw ← is_monoid_hom.map_mul S'.f_rev, congr, 
            rw is_monoid_hom.map_mul subtype.val,
            unfold_coes, simp,
            apply is_monoid_hom.map_mul,
            apply is_group_hom.to_is_monoid_hom, }⟩,
    g_surj := λ y, by { unfold_coes, simp,
                        cases S.g_surj (S'.f y) with x hx, 
                        refine exists.intro (subtype.mk x _) _,
                        apply set.mem_preimage.mpr, existsi y, exact hx.symm,
                        simp, transitivity S'.f_rev ⟨S'.f y, y, rfl⟩,
                        congr, assumption, apply SES.f_rev_spec_l },
    im_f_eq_ker_g := by {
      ext, cases x with x hx,
      transitivity x ∈ set.range S.f,
      { constructor; intro h; cases h with a ha,
        { existsi a, unfold_coes at ha, simp at ha, assumption },
        { have h := hx, rw ← ha at h,
          rw (_ : subtype.mk x hx = subtype.mk (S.f a) h),
          existsi a, refl, apply subtype.eq, exact ha.symm, } },
      rw [SES.im_f_eq_ker_g, is_group_hom.mem_ker, is_group_hom.mem_ker],
      unfold_coes, simp,
      constructor; intro h,
      { transitivity S'.f_rev ⟨1, is_submonoid.one_mem _⟩,
        congr, assumption, apply is_group_hom.map_one S'.f_rev, },
      { have := congr_arg S'.f h,
        rw SES.f_rev_spec_r at this,
        unfold_coes at this, simp at this, rw this,
        apply is_group_hom.map_one, } } }.

lemma ker_comp {A B C : Group} (f : A ⟶ B) (g : B ⟶ C)
  : is_group_hom.ker (g ∘ f) = f⁻¹' (is_group_hom.ker g) :=
by ext; rw [is_group_hom.mem_ker, set.mem_preimage, is_group_hom.mem_ker]

def third_iso {H G K A B : Group}
  (S : SES H G K) (S' : SES A K B)
  : SES (Group.of (S.g ⁻¹' set.range S'.f)) G B := {
    f := subtype_val.group_hom,
    g := S.g ≫ S'.g,
    f_inj := λ _ _ h, subtype.eq h,
    g_surj := function.surjective_comp S'.g_surj S.g_surj,
    im_f_eq_ker_g := by {
      unfold_coes, transitivity is_group_hom.ker (S'.g ∘ S.g),
      rw ker_comp, rw ← S'.im_f_eq_ker_g, 
      transitivity set.range subtype.val, refl,
      simp, refl, refl } }

local attribute [instance] classical.prop_decidable
lemma SES.simple {G : Group}
  : simple_group G ↔ (∀ {H K : Group}, nonempty (SES H G K) → subsingleton H ∨ subsingleton K) := 
begin
  constructor; intro h,
  { intros H K S, cases S with S,
    cases h, cases h (is_group_hom.ker S.g) with h h,
    { apply or.inl,
      rw [← S.im_f_eq_ker_g, is_subgroup.eq_trivial_iff] at h,
      constructor, intros, apply S.f_inj, 
      transitivity (1 : G), apply h, existsi a, refl,
      symmetry, apply h, existsi b, refl },
    { apply or.inr, constructor, intros,
      cases (S.g_surj a) with a ha, subst ha,
      cases (S.g_surj b) with b hb, subst hb,
      have ha : a ∈ set.univ := set.mem_univ _,
      have hb : b ∈ set.univ := set.mem_univ _,
      rw [← h, is_group_hom.mem_ker] at ha hb,
      transitivity (1 : K), assumption, symmetry, assumption } },
  { constructor, intros,
    cases h ⟨@SES.normal_quotient G N _inst_1⟩ with h h,
    { apply or.inl,
      rw @is_subgroup.eq_trivial_iff _ _ N _inst_1.to_is_subgroup,
      intros, apply @subtype.mk.inj _ N, apply @subsingleton.elim _ h,
      assumption, apply @is_submonoid.one_mem _ _ _ _inst_1.to_is_submonoid },
    { apply or.inr, apply set.eq_univ_of_forall,
      suffices : ∀ x : G, 1⁻¹ * x ∈ N,
      { intro, specialize this x, rw [one_inv, one_mul] at this, exact this },
      cases h with h, intro x,
      specialize h (@quotient_group.mk _ _ N _inst_1.to_is_subgroup 1),
      specialize h (@quotient_group.mk _ _ N _inst_1.to_is_subgroup x),
      dsimp [quotient_group.mk] at h,
      rw quotient.eq' at h_1, assumption, } }
end

def partial_second_iso {H H' G G' K K' : Group.{u}}
  (iso : G ≅ G') (hK' : simple_group K')
  (S : SES H G K) (S' : SES H' G' K')
  (x : H) (x_not_in_H' : ¬ (S'.g (iso.hom (S.f x)) = 1))
  : SES (Group.of $ pullback (S.f ≫ iso.hom) S'.f) H K' := {
    f := @subtype_val.group_hom (Group.of $ H × H') _ _ ≫ @Group.fst H H',
    g := S.f ≫ iso.hom ≫ S'.g,
    f_inj := by { intros x y h,
                  cases x with x hx, cases x with x₁ x₂,
                  cases y with y hy, cases y with y₁ y₂,
                  replace h : x₁ = y₁ := h, apply subtype.eq,
                  simp, apply and.intro h, apply S'.f_inj,
                  exact eq.trans (eq.symm hx) (eq.trans (congr_arg _ h) hy) },
    g_surj := by { intro y, cases S'.g_surj y with a ha,
                   destruct hK', intro hK',
                   replace hK' := λ inst, @hK' (S'.g '' (iso.hom '' set.range S.f)) inst,
                   suffices : normal_subgroup (S'.g '' (iso.hom '' set.range S.f)),
                   have : S'.g '' (iso.hom '' set.range S.f) = set.univ,
                   { apply or.resolve_left (hK' this), intro h,
                     apply x_not_in_H',
                     rw [← is_subgroup.mem_trivial, ← h],
                     apply set.mem_image_of_mem,
                     apply set.mem_image_of_mem,
                     apply set.mem_range_self },
                   rw set.eq_univ_iff_forall at this,
                   simp, cases this y with a ha,
                   cases ha with ha' ha, cases ha' with a ha, cases ha with ha' ha,
                   subst ha, subst ha, cases ha' with a ha', existsi a, rw ha',
                   rw SES.im_f_eq_ker_g, rw ← set.image_comp,
                   apply @surj_im_normal G K' (iso.hom ≫ S'.g),
                   apply function.surjective_comp, exact S'.g_surj, apply Group.iso_surj },
    im_f_eq_ker_g := by {
      unfold_coes, simp,
      transitivity is_group_hom.ker (@category_struct.comp Group _ _ _ _ S.f
                                      (@category_struct.comp Group _ _ _ _ iso.hom S'.g)),
      rw Group.ker_of_comp_inj _ _ S.f_inj,
      dsimp [subtype_val.group_hom, Group.fst],
      rw [set.range_comp, subtype.range_val],
      rw [Group.ker_of_comp_inj _ _ (Group.iso_inj iso), ← S'.im_f_eq_ker_g],
      ext x, rw set.mem_preimage,
      constructor; intro h; cases h with k hk,
      { existsi k.snd, symmetry, rw ← hk.right, exact hk.left },
      { existsi (x, k), constructor, exact hk.symm, refl },
      refl
    }
  }

structure SES.equiv {H H' G G' K K' : Group}
  (iso : G ≅ G') (S : SES H G K) (S' : SES H' G' K') :=
(α : H ≅ H') (β : K ≅ K')
(l_comm : S.f ≫ iso.hom = α.hom ≫ S'.f)
(r_comm : S.g ≫ β.hom = iso.hom ≫ S'.g)

def SES.equiv_symm {H H' G G' K K' : Group}
  (iso : G ≅ G') (S : SES H G K) (S' : SES H' G' K')
  (eqv : SES.equiv iso S S') : SES.equiv iso.symm S' S := {
    α := eqv.α.symm, β := eqv.β.symm,
    l_comm := by {
      refine (_ : @category_struct.comp Group _ _ _ _ S'.f iso.inv 
                = @category_struct.comp Group _ _ _ _ eqv.α.inv S.f),
      rw [iso.comp_inv_eq, category.assoc, eqv.l_comm, ← category.assoc,
          eqv.α.inv_hom_id, category.id_comp] },
    r_comm := by {
      refine (_ : @category_struct.comp Group _ _ _ _ S'.g eqv.β.inv 
                = @category_struct.comp Group _ _ _ _ iso.inv S.g),
      symmetry,
      rw [iso.inv_comp_eq, ← category.assoc, ← eqv.r_comm, category.assoc,
          eqv.β.hom_inv_id, category.comp_id] }
  }

noncomputable
def SES.map_out_right {H G G' K : Group} (S : SES H G K)
  (φ : G ⟶ G') (hker : ∀ x : H, φ (S.f x) = 1) : K ⟶ G' := {
    val := λ k, φ (function.inv_fun S.g k),
    property := is_group_hom.mk' $ by {
      intros,
      rw [← is_monoid_hom.map_mul φ, is_group_hom.one_iff_ker_inv φ],
      suffices : function.inv_fun S.g (x * y)
               * (function.inv_fun S.g x * function.inv_fun ⇑(S.g) y)⁻¹
               ∈ set.range S.f,
      { cases this with a ha, rw ← ha, apply_assumption },
      rw [SES.im_f_eq_ker_g, is_group_hom.mem_ker, ← is_group_hom.one_iff_ker_inv],
      rw is_monoid_hom.map_mul S.g,
      repeat { rw @function.inv_fun_eq _ _ _ S.g _ (S.g_surj _) }
    }
  }

lemma SES.map_out_right_comm {H G G' K : Group} (S : SES H G K)
  (φ : G ⟶ G') (hker : ∀ x : H, φ (S.f x) = 1)
  : ∀ x : G, SES.map_out_right S φ hker (S.g x) = φ x :=
begin
  intros,
  apply iff.mpr (is_group_hom.one_iff_ker_inv φ (function.inv_fun S.g $ S.g x) x),
  suffices : function.inv_fun S.g (S.g x) * x⁻¹ ∈ set.range S.f,
  { cases this with a ha, rw ← ha, apply_assumption },
  rw [SES.im_f_eq_ker_g, is_group_hom.mem_ker, ← is_group_hom.one_iff_ker_inv],
  apply function.right_inverse_inv_fun, exact S.g_surj
end

noncomputable
def SES.equiv_of_left {H H' G G' K K' : Group}
  (iso : G ≅ G') (S : SES H G K) (S' : SES H' G' K')
  (α : H ≅ H') (l_comm : S.f ≫ iso.hom = α.hom ≫ S'.f)
  : SES.equiv iso S S' := 
  have h1 : ∀ x, (iso.hom ≫ S'.g) (S.f x) = 1,
  by { intro, rw ← iso.eq_comp_inv at l_comm, rw l_comm,
       suffices : S'.g ((iso.hom.val ∘ iso.inv.val) (S'.f (α.hom x))) = 1,
       exact this, have := iso.inv_hom_id,
       simp [(≫), category_struct.id] at this,
       rw this, simp, apply S'.is_cc },
  have h2 : ∀ x, (iso.inv ≫ S.g) (S'.f x) = 1,
  by by { intro, replace l_comm := l_comm.symm,
          rw ← α.eq_inv_comp at l_comm, rw l_comm,
          suffices : S.g ((iso.inv.val ∘ iso.hom.val) (S.f (α.inv x))) = 1,
          exact this, have := iso.hom_inv_id,
          simp [(≫), category_struct.id] at this,
          rw this, simp, apply S.is_cc },
  { α := α, l_comm := l_comm,
    β := {
      hom := SES.map_out_right S (iso.hom ≫ S'.g) h1,
      inv := SES.map_out_right S' (iso.inv ≫ S.g) h2,
      hom_inv_id' := by {
        ext, cases S.g_surj x with x h, subst h, unfold_coes, simp,
        have := SES.map_out_right_comm S (iso.hom ≫ S'.g) h1 x,
        unfold_coes at this, simp [(≫)] at this, rw this, clear this,
        have := SES.map_out_right_comm S' (iso.inv ≫ S.g) h2 (iso.hom.val x),
        unfold_coes at this, simp [(≫)] at this, rw this, clear this,
        congr, transitivity (iso.inv.val ∘ iso.hom.val) x, refl,
        transitivity id x, apply congr_fun, exact subtype.mk.inj iso.hom_inv_id, refl,
      },
      inv_hom_id' := by {
        ext, cases S'.g_surj x with x h, subst h, unfold_coes, simp,
        have := SES.map_out_right_comm S' (iso.inv ≫ S.g) h2 x,
        unfold_coes at this, simp [(≫)] at this, rw this, clear this,
        have := SES.map_out_right_comm S (iso.hom ≫ S'.g) h1 (iso.inv.val x),
        unfold_coes at this, simp [(≫)] at this, rw this, clear this,
        congr, transitivity (iso.hom.val ∘ iso.inv.val) x, refl,
        transitivity id x, apply congr_fun, exact subtype.mk.inj iso.inv_hom_id, refl,
      }
    },
    r_comm := by {
      unfold_coes, simp,
      ext, transitivity SES.map_out_right S (iso.hom ≫ S'.g) h1 (S.g x),
      refl, apply SES.map_out_right_comm,
    }
  }.

noncomputable
def SES.equiv_of_ker_im_match {H H' G G' K K' : Group}
  (iso : G ≅ G') (S : SES H G K) (S' : SES H' G' K')
  (h_l : ∀ x : H, S'.g (iso.hom (S.f x)) = 1)
  (h_r : ∀ x : H', S.g (iso.inv (S'.f x)) = 1)
  : SES.equiv iso S S' :=
    have h1 : iso.hom '' set.range S.f ⊆ is_group_hom.ker S'.g
            ∧ iso.inv '' set.range S'.f ⊆ is_group_hom.ker S.g,
    from by { constructor; intros x hx;
              cases hx with x hx; cases hx with hx hx;
              subst hx; cases hx with x hx; subst hx;
              rw is_group_hom.mem_ker; apply_assumption },
    have h2 : iso.hom '' set.range S.f = set.range S'.f,
    by { rw [← S.im_f_eq_ker_g, ← S'.im_f_eq_ker_g] at h1,
         cases h1 with h h', rw set.image_subset_iff at h',
         rw ← set.image_eq_preimage_of_inverse at h',
         exact funext (λ x, propext ⟨@h x, @h' x⟩),
         apply Group.iso_left_inverse, apply Group.iso_right_inverse },
    have h3  : Group.of ↥(⇑(iso.hom) '' set.range ⇑(S.f)) = Group.of ↥(set.range ⇑(S'.f)),
    by { rw Group.subgroup_eq_of_eq h2, },
    have h4 : ∀ {A B : Group} (h : A = B) (t : A),
          t == (eq.rec (category_theory.iso.refl A) h : A ≅ B).hom.val t,
    by { intros, cases h, refl },
    begin
      refine SES.equiv_of_left iso S S' _ _,  
      transitivity,
      exact (S.left_iso_range ≪≫ Group.iso_restrict iso _),
      transitivity, tactic.swap, apply S'.left_iso_range.symm,
      exact eq.rec (category_theory.iso.refl (Group.of ↥(⇑(iso.hom) '' set.range ⇑(S.f)))) h3,
      rw category_theory.iso.trans_assoc,
      ext, 
      dsimp [(≪≫)], 
      dsimp [SES.left_iso_range],
      dsimp [Group.iso_restrict],
      unfold_coes,
      dsimp [subtype.val],
      rw (_ : S'.f.val = ⇑(S'.f)), tactic.swap, refl,
      rw S'.f_rev_spec_r,
      unfold_coes, 
      clear h1, clear h_l, clear h_r, 
      generalize h : subtype.mk ((iso.hom).val ((S.f).val x)) _ = t,
      transitivity t.val, { subst h },
      congr, ext, rw h2, apply h4 h3
    end

lemma Group.normal_subgroup_card_lt_of_nontriv_quot
  {H G K : Group} [fintype G] (S : SES H G K) (hK : ¬ subsingleton K)
  : @fintype.card H (fintype.of_injective S.f S.f_inj) < fintype.card G :=
begin
  have : ∃ k : K, k ≠ 1,
  { by_contradiction h, rw not_exists_not at h,
    apply hK, constructor, intros,
    transitivity (1 : K), apply h, symmetry, apply h },
  cases this with k hk, cases S.g_surj k with x hx, subst hx,
  replace hk := mt (iff.mp (is_group_hom.mem_ker S.g)) hk,
  rw [← S.im_f_eq_ker_g] at hk,
  apply @nat.lt_of_le_of_lt _ (@finset.card _ (finset.erase finset.univ x)),
  have h1 : ∀ (y : G), y ∈ finset.erase finset.univ x ↔ y ≠ x,
  { intro, rw [finset.mem_erase, (_ : y ∈ finset.univ ↔ true)],
    apply and_true, rw iff_true, apply finset.mem_univ },
  have h2 : fintype { y : G // y ≠ x } := fintype.subtype _ h1,
  rw ← @fintype.subtype_card _ (λ y, y ≠ x) _ h1,
  apply @nat.le_trans _ (@fintype.card { y : G // y ≠ x } h2),
  apply @fintype.card_le_of_injective H _ (fintype.of_injective S.f S.f_inj) h2
          (λ y, ⟨S.f y, λ h, hk ⟨y, h⟩⟩)
          (λ _ _ hab, S.f_inj (subtype.mk.inj hab)),
  apply nat.le_of_eq, congr, 
  rw finset.card_erase_of_mem, dsimp [fintype.card],
  apply nat.pred_lt, refine (_ : ¬ (fintype.card G = 0)),
  rw fintype.card_eq_zero_iff, exact λ h, h 1, apply finset.mem_univ
end

def SES.not_contains_of_simple_quot_and_proper {H H' G G' K K' : Group} (iso : G ≅ G')
  (S : SES H G K) (S' : SES H' G' K')
  (hK : simple_group K) (hK' : ¬ subsingleton K')
  (hnoteqv : SES.equiv iso S S' → false)
  : ∃ x, S'.g (iso.hom (S.f x)) ≠ 1 :=
begin
  have h1 : ¬ ((∀ x, S'.g (iso.hom (S.f x)) = 1)
          ∧ (∀ x, S.g (iso.inv (S'.f x)) = 1)),
  { intro h, apply hnoteqv, cases h,
    apply SES.equiv_of_ker_im_match; assumption },
  rw classical.not_and_distrib at h1, cases h1, 
  rw ← classical.not_forall, assumption,
  rw ← classical.not_forall, intro h2, apply h1,
  suffices : iso.inv '' set.range S'.f ⊆ is_group_hom.ker S.g,
  { intro, rw ← is_group_hom.mem_ker S.g,
    exact this ⟨S'.f x, set.mem_range_self x, rfl⟩ },
  destruct hK, intro,
  have : iso.hom '' set.range S.f ⊆ is_group_hom.ker S'.g,
  { intros x hx, cases hx with x' hx,
    rw ← hx.right, cases hx.left with x hx, rw ← hx,
    rw is_group_hom.mem_ker, apply h2 },
  cases @simple (S.g '' (iso.inv '' is_group_hom.ker S'.g))
                (@surj_im_normal _ _ S.g S.g_surj _
                  (surj_im_normal iso.inv (Group.iso_surj iso.symm) _)),
  rw [set.image_subset_iff,
    ← set.image_eq_preimage_of_inverse
      (Group.iso_right_inverse _) (Group.iso_left_inverse _)] at this,
  transitivity S.g ⁻¹' (S.g '' (iso.inv '' is_group_hom.ker S'.g)),
  rw S'.im_f_eq_ker_g, apply set.subset_preimage_image S.g,
  rw h, refl, exfalso, apply hK',
  have : ∀ x : K', x = 1,
  { have h3 := Group.eq_of_im_eq_and_contain_ker _ h _,
    intro x, cases S'.g_surj x with x hx, subst hx,
    rw ← is_group_hom.mem_ker S'.g,
    have h4 : iso.inv x ∈ set.univ := set.mem_univ _,
    rw [← h3, set.mem_image_iff_of_inverse
              (Group.iso_right_inverse _) (Group.iso_left_inverse _),
        Group.iso_right_inverse _] at h4, 
    assumption,
    rw [← S.im_f_eq_ker_g,
        set.image_eq_preimage_of_inverse
          (Group.iso_right_inverse _) (Group.iso_left_inverse _)],
    rw ← set.image_subset_iff, assumption },
  constructor, intros, transitivity (1 : K'),
  apply_assumption, symmetry, apply_assumption, 
end

noncomputable
def SES.partial_second_iso' {H H' G G' K K' : Group} (iso : G ≅ G')
  (S : SES H G K) (S' : SES H' G' K')
  (hK₁ : simple_group K) (hK₂ : ¬ subsingleton K)
  (hK'₁ : simple_group K') (hK'₂ : ¬ subsingleton K')
  (hnoteqv : SES.equiv iso S S' → false)
  : SES (Group.of (pullback (S.f ≫ iso.hom) S'.f)) H K' :=
begin
  cases classical.subtype_of_exists (SES.not_contains_of_simple_quot_and_proper iso S S' hK₁ hK'₂ hnoteqv),
  apply @partial_second_iso H H' G G' K K' iso hK'₁ S S', assumption,
end
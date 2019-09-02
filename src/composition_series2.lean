import group_theory.subgroup
import group_theory.quotient_group
import data.fintype
import .SES

universes u v w

section 

open is_subgroup

inductive normal_series (T : Group.{u}): Group.{u} → Type (u+1)
| initial : ∀ {G K : Group.{u}},
  SES T G K → normal_series G
| step : ∀ {H G K : Group.{u}},
       SES H G K
       → ¬ (subsingleton H)
       → ¬ (subsingleton K)
       → normal_series H 
       → normal_series G

inductive is_composition_series : ∀ {G : Group.{u}}, normal_series 1 G → Type (u+2)
| initial : ∀ {G K} (S : SES 1 G K), is_composition_series (normal_series.initial S)
| step : ∀ {H G K : Group.{u}} (S : SES H G K)
           (H_nontriv : ¬ (subsingleton H))
           (K_nontriv : ¬ (subsingleton K))
           (σ : normal_series 1 H),
           simple_group K →
           is_composition_series (normal_series.step S H_nontriv K_nontriv σ)

def length {T} : ∀ {G : Group}, normal_series T G → nat
| _ (normal_series.initial _) := 1
| _ (normal_series.step _ _ _ σ) := 1 + length σ

def ℓ := @length

def factors' {T : Group} : ∀ {G : Group}, normal_series T G → list Group
| _ (@normal_series.initial _ _ K _) := [K]
| _ (@normal_series.step _ _ _ K _ _ _ σ) := K :: factors' σ

lemma is_group_hom.im_trivial {G H : Group} (φ : G → H) [is_group_hom φ]
  : φ '' is_subgroup.trivial G = is_subgroup.trivial H :=
begin
  simp [set.image, set_of], rw is_group_hom.map_one φ, 
  simp [is_subgroup.trivial], funext, apply propext,
  constructor; intro h,
  { rw h, apply or.inl, refl },
  { symmetry, apply or.resolve_right h, exact not_false }
end

def normal_series.pullback : ∀ {H G K : Group} (S : SES H G K), normal_series 1 K → normal_series H G
| _ _ _ S (@normal_series.initial _ _ C0 S') := normal_series.initial S
| H G K S (@normal_series.step _ Kn _ Cn S' _ _ σ) := 
  let S'' : SES H (Group.of (S.g ⁻¹' (set.range S'.f))) Kn
    := {
      f := ⟨λ x, subtype.mk (S.f x)
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
              unfold_coes, 
              
              apply subtype.eq,
              transitivity S.f x * S.f y,
              apply @is_monoid_hom.map_mul _ _ _ _ _
                (@is_group_hom.to_is_monoid_hom _ _ _ _ _ S.f_hom),
              refl, }⟩,
      g_surj := λ y, by { simp, cases S.g_surj (S'.f y) with x hx, 
                          refine exists.intro (subtype.mk x _) _,
                          apply set.mem_preimage.mpr, existsi y, exact hx.symm,
                          simp, transitivity S'.f_rev ⟨S'.f y, y, rfl⟩,
                          congr, assumption, apply SES.f_rev_spec_l },
      im_f_eq_ker_g := sorry }
  in by { refine normal_series.step _ _ _ (normal_series.pullback _ σ),
        }
  -- let rec := normal_series.pullback _ σ
  -- in 

-- def merge {G H : Group}
--   (H_nontriv : ¬ (subsingleton H))
--   (σ : normal_series H)
--   : ∀ {K}, SES H G K
--          → ¬ (subsingleton K)
--          → normal_series K
--          → normal_series G
-- | K S K_nontriv normal_series.empty
--   := normal_series.step S H_nontriv K_nontriv σ
-- | K S K_nontriv
--   (normal_series.step S' A_nontriv B_nontriv σ')
--   := 

end
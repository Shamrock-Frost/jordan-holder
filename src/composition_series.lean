import group_theory.subgroup
import group_theory.quotient_group
import data.fintype
import data.multiset
import .SES .induction .category_theory .list_equiv

universes u v w

open is_subgroup

inductive normal_series (T : Group.{u}): Group.{u} → Type (u+1)
| initial {} : ∀ {T'}, (T' ≅ T) → normal_series T'
| step : ∀ {H G K : Group.{u}},
       SES H G K
       → normal_series H 
       → normal_series G

def length {T} : ∀ {G : Group}, normal_series T G → nat
| _ (normal_series.initial _) := 0
| _ (normal_series.step _ σ) := 1 + length σ

def ℓ := @length

def factors {T : Group} : ∀ {G : Group}, normal_series T G → list Group
| _ (normal_series.initial _) := []
| _ (@normal_series.step _ _ _ K _ σ) := K :: factors σ

def is_composition_series
  {G : Group} (σ : normal_series 1 G)
  := list.foldr (∧) true
     $ list.map (λ K : Group, simple_group K ∧ ¬ subsingleton K)
     $ factors σ

lemma is_composition_series.initial {T : Group} {h : T ≅ 1}
  : is_composition_series (normal_series.initial h) := trivial

lemma is_composition_series.step
  {H G K : Group} (S : SES H G K) (σ : normal_series 1 H)
  : is_composition_series (normal_series.step S σ)
  ↔ is_composition_series σ ∧ simple_group K ∧ ¬ subsingleton K :=
  and_comm _ _

noncomputable
def normal_series.pullback : ∀ {H G K : Group} (S : SES H G K),
  normal_series 1 K → normal_series H G
| H G K S (normal_series.initial h) := 
  normal_series.initial (category_theory.iso.symm
                        $ @SES.iso_of_right_triv _ _ _
                              ⟨λ x y : K, Group.iso_inj h (subsingleton.elim _ _)⟩
                              S)
| H G K S (@normal_series.step _ _ Kn Cn S' σ) :=
  normal_series.step (third_iso S S')
  $ normal_series.pullback (SES.pullback S S') σ

lemma normal_series.pullback_factors {H G K : Group.{u}} (S : SES H G K)
  (σ : normal_series 1 K) 
  : factors (σ.pullback S) = factors σ :=
begin
  revert S G H, induction σ; intros H G S,
  { constructor },
  { dsimp [normal_series.pullback, factors],
    apply congr_arg, apply_assumption }
end

def normal_series.transport {T G H : Group} (iso : G ≅ H) 
  : normal_series T G → normal_series T H
| (normal_series.initial iso') := normal_series.initial (iso.symm ≪≫ iso')
| (normal_series.step S σ) := normal_series.step (S.transport_iso_mid iso) σ

lemma normal_series.transport_factors {T G H : Group} (iso : G ≅ H)
  (σ : normal_series T G) : factors (σ.transport iso) = factors σ
  := by cases σ; refl

def normal_series.merge {H : Group} (σ : normal_series 1 H)
  : ∀ {G : Group}, normal_series H G → normal_series 1 G
| G (normal_series.initial iso) := normal_series.transport iso.symm σ
| G (@normal_series.step _ H' _ K S σ') :=
  normal_series.step S (normal_series.merge σ')

lemma normal_series.merge_factors {H : Group} (σ : normal_series 1 H)
  {G : Group} (σ' : normal_series H G) 
  : factors (normal_series.merge σ σ') = factors σ' ++ factors σ :=
begin
  induction σ',
  { dsimp [normal_series.merge], rw normal_series.transport_factors, refl },
  { dsimp [factors, normal_series.merge], apply congr_arg, assumption }
end

noncomputable
def normal_series.of_SES {H G K : Group} (S : SES H G K)
  (σ : normal_series 1 H) (σ' : normal_series 1 K)
  := normal_series.merge σ $ normal_series.pullback S σ'

lemma list.foldr_append_assoc {α} (f : α → α → α) (a : α) (xs ys : list α)
  (hid : ∀ x : α, f a x = x)
  (hassoc : ∀ x y z, f x (f y z) = f (f x y) z)
: list.foldr f a (xs ++ ys) = f (list.foldr f a xs) (list.foldr f a ys) :=
begin
  induction xs with x xs ih,
  { symmetry, apply hid },
  { dsimp [list.foldr], rw ih, apply hassoc }
end

lemma is_composition_series.of_SES {H G K : Group} (S : SES H G K)
  (σ : normal_series 1 H) (σ' : normal_series 1 K)
  : is_composition_series σ
  → is_composition_series σ'
  → is_composition_series (normal_series.of_SES S σ σ') :=
begin
  dsimp [is_composition_series], intros h h',
  dsimp [normal_series.of_SES],
  rw [normal_series.merge_factors, normal_series.pullback_factors],
  rw [list.map_append, list.foldr_append_assoc],
  constructor; assumption,
  { intro P, exact propext (true_and P) },
  { intros, exact propext (and_assoc _ _).symm }
end

local attribute [instance] classical.prop_decidable
lemma composition_series_of
  : ∀ {G : Group} (is_fin : fintype G),
    ∃ σ : normal_series 1 G, is_composition_series σ :=
  finite_group.induction_subquot (λ (G : Group) _, ∃ σ : normal_series 1 G, is_composition_series σ)
  (λ G is_fin hsub hquot,
   if h : simple_group G
   then if h' : subsingleton G
        then ⟨normal_series.initial $ @Group.subsingleton_iso _ _ h' _,
              is_composition_series.initial⟩
        else exists.intro (normal_series.step (SES.self_right G)
                          $ normal_series.initial $ by refl)
                      $ iff.mpr (is_composition_series.step (SES.self_right G)
                                 $ normal_series.initial $ by refl)
                      $ ⟨@is_composition_series.initial _ $ by refl, h, h'⟩
   else by { have ex_n : ∃ (N : set G), normal_subgroup N ∧ N ≠ is_subgroup.trivial G ∧ N ≠ set.univ,
             { by_contradiction h', apply h, constructor, intros,
               by_contradiction h'', apply h',
               existsi N, existsi _inst_1, constructor; intro; apply h'',
               apply or.inl, assumption, apply or.inr, assumption },
             cases classical.subtype_of_exists ex_n with H h,
             cases @hsub H h.left.to_is_subgroup h.right.right with σ σ_comp,
             cases @hquot H h.left h.right.left with σ' σ'_comp,
             existsi normal_series.of_SES _ σ σ',
             apply is_composition_series.of_SES; assumption,
             apply SES.normal_quotient })

lemma jordan_holder :
  ∀ {G : Group} (is_fin : fintype G) {G' : Group} (iso : G ≅ G')
  (σ : normal_series 1 G) (σ' : normal_series 1 G'),
  is_composition_series σ → is_composition_series σ' →
  equiv_group_lists (factors σ) (factors σ') :=
  finite_group.induction_ord
    (λ (G : Group) _, ∀ {G' : Group} (iso : G ≅ G')
                        (σ : normal_series 1 G) (σ' : normal_series 1 G'),
                      is_composition_series σ → is_composition_series σ'→
                      equiv_group_lists (factors σ) (factors σ'))
  $ by { intros G is_fin ih G' iso σ σ' hσ hσ',
         cases σ with _ _ H _ K S σ; cases σ' with _ _ H' _ K' S' σ',
         { apply and.intro rfl, existsi list.nil, constructor; trivial },
         { exfalso, rw is_composition_series.step at hσ',
           apply hσ'.right.right, constructor, intros x y,
           cases S'.g_surj x, subst h, cases S'.g_surj y, subst h,
           apply congr_arg, apply Group.iso_inj (iso.symm ≪≫ σ_a),
            apply subsingleton.elim },
         { exfalso, rw is_composition_series.step at hσ,
           apply hσ.right.right, constructor, intros x y,
           cases S.g_surj x, subst h, cases S.g_surj y, subst h,
           apply congr_arg, apply Group.iso_inj (iso ≪≫ σ'_a), apply subsingleton.elim },
         cases classical.type_decidable (SES.equiv iso S S') with heqv,
         { rw is_composition_series.step at hσ hσ',
           cases @ih _ _
              (@Group.normal_subgroup_card_lt_of_nontriv_quot _ _ _ is_fin S hσ.right.right)
              H' heqv.α σ σ' hσ.left hσ'.left with hlen h, cases h with L hL,
           apply and.intro (congr_arg nat.succ hlen),
           existsi list.cons K L,
           exact ⟨list.perm.skip _ hL.left, ⟨heqv.β⟩, hL.right⟩ },
         rw is_composition_series.step at hσ hσ',
         cases SES.not_contains_of_simple_quot_and_proper iso S S' hσ.right.left hσ'.right.right val with x hx,
         cases SES.not_contains_of_simple_quot_and_proper iso.symm S' S hσ'.right.left hσ.right.right _ with x' hx',
         tactic.swap,
         { intro eqv, apply val, rw ← iso.symm_symm_eq, apply SES.equiv_symm, assumption },
         have H_S : SES (Group.of (pullback (S.f ≫ iso.hom) S'.f)) H K'
         := @partial_second_iso H H' G G' K K' iso hσ'.right.left S S' x hx,
         have H'_S : SES (Group.of (pullback (S'.f ≫ iso.inv) S.f)) H' K
         := @partial_second_iso H' H G' G K' K iso.symm hσ.right.left S' S x' hx',
         let is_fin' := @fintype.of_bijective _ _ is_fin iso.hom (Group.iso_bij iso),
         have card_G_eq_card_G' : @fintype.card _ is_fin = @fintype.card _ is_fin',
         { rw fintype.card_eq, constructor, constructor,
           apply Group.iso_left_inverse iso, apply Group.iso_right_inverse iso },
         let is_fin_H : fintype H := @fintype.of_injective _ _ is_fin S.f S.f_inj,
         let H_card_lt : @fintype.card H is_fin_H < @fintype.card G is_fin
         := @Group.normal_subgroup_card_lt_of_nontriv_quot _ _ _ is_fin S hσ.right.right,
         let is_fin_H' : fintype H' := @fintype.of_injective _ _ is_fin' S'.f S'.f_inj,
         have H'_card_lt : @fintype.card H' is_fin_H' < @fintype.card G is_fin,
         { rw card_G_eq_card_G',
           exact @Group.normal_subgroup_card_lt_of_nontriv_quot _ _ _ is_fin' S' hσ'.right.right },
         let pullback₁_fin : fintype (Group.of $ pullback (S.f ≫ iso.hom) S'.f)
         := @pullback_inj_fin _ _ _ (S.f ≫ iso.hom) S'.f
                              (function.injective_comp (Group.iso_inj iso) S.f_inj)
                              S'.f_inj is_fin',
         have pullback₁_card_lt : @fintype.card _ pullback₁_fin < @fintype.card G is_fin,
         { apply @nat.lt_of_le_of_lt _ (@fintype.card _ (@pullback_inj_fin _ _ _ (S.f ≫ iso.hom) S'.f
                                                          (function.injective_comp (Group.iso_inj iso) S.f_inj)
                                                          S'.f_inj is_fin')),
           apply nat.le_of_eq, refl, rw card_G_eq_card_G',
           apply pullback_card_lt_of_conflict _ _ x,
           intro b, intro h, apply hx,
           transitivity S'.g (S'.f b), rw ← h, refl, apply S'.is_cc },
         let pullback₂_fin : fintype (Group.of $ pullback (S'.f ≫ iso.inv) S.f)
         := @pullback_inj_fin _ _ _ (S'.f ≫ iso.inv) S.f
                             (function.injective_comp (Group.iso_inj iso.symm) S'.f_inj)
                              S.f_inj is_fin,
         cases @composition_series_of (Group.of (pullback (S.f ≫ iso.hom) S'.f))
                                     pullback₁_fin with pullback₁_σ pullback₁_σ_comp,
         cases @composition_series_of (Group.of (pullback (S'.f ≫ iso.inv) S.f))
                                     pullback₂_fin with pullback₂_σ pullback₂_σ_comp,
         have heqv_pullback₁₂ :=
            ih _ pullback₁_fin pullback₁_card_lt
               (Group.pullback_of_isos_is_iso iso _ _)
               pullback₁_σ pullback₂_σ pullback₁_σ_comp pullback₂_σ_comp,
         let H_σ := normal_series.step H_S pullback₁_σ,
         have H_σ_comp : is_composition_series H_σ := ⟨hσ'.right, pullback₁_σ_comp⟩,
         have heqv_H :=
            ih _ is_fin_H H_card_lt (category_theory.iso.refl H)
               σ H_σ hσ.left H_σ_comp,
         let H'_σ := normal_series.step H'_S pullback₂_σ,
         have H'_σ_comp : is_composition_series H'_σ := ⟨hσ.right, pullback₂_σ_comp⟩,
         have heqvH' :=
            ih _ is_fin_H' H'_card_lt (category_theory.iso.refl H')
               H'_σ σ' H'_σ_comp hσ'.left,
         dsimp [factors], 
         transitivity list.cons K (factors H_σ),
         apply equiv_group_lists.skip, assumption,
         transitivity list.cons K' (factors H'_σ),
         apply equiv_group_lists.swap', assumption,
         apply equiv_group_lists.skip, assumption }
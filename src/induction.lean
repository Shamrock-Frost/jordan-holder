import group_theory.subgroup
import group_theory.quotient_group
import group_theory.category
open category_theory

local attribute [instance] classical.prop_decidable

lemma fintype.card_of_removed {α} [fintype α] (a : α)
  : fintype.card { x : α // x ≠ a } = nat.pred (fintype.card α) :=
begin
  transitivity finset.card (finset.erase finset.univ a),
  apply fintype.card_of_subtype, intros,
  rw [finset.mem_erase, eq_true_intro (finset.mem_univ x), and_true],
  apply finset.card_erase_of_mem, apply finset.mem_univ
end

noncomputable
def quotient.out_avoid {α} (s : setoid α) (a b : α)
  (hdist : a ≠ b) : quotient s → { x : α // x ≠ b } :=
  λ x, if h : quotient.out x = b
       then ⟨a, hdist⟩
       else ⟨quotient.out x, h⟩

lemma quotient.out_avoid_inj {α : Type*} (s : setoid α) (a b : α)
  (hdist : a ≠ b) (hrel : setoid.r a b)
  : function.injective (quotient.out_avoid s a b hdist) :=
  λ x y hxy,
  if hx : quotient.out x = b
  then if hy : quotient.out y = b
       then calc x   = quotient.mk b : by { rw ← hx, rw quotient.out_eq }
                 ... = y : by { symmetry, rw ← hy, rw quotient.out_eq }
       else by { simp [quotient.out_avoid] at hxy,
                 rw [dif_pos hx, dif_neg hy] at hxy,
                 transitivity quotient.mk b,
                 rw ← hx, rw quotient.out_eq,
                 transitivity quotient.mk a,
                 exact quot.eqv_gen_sound (eqv_gen.symm _ _ (eqv_gen.rel _ _ hrel)),
                 rw subtype.ext at hxy, simp at hxy,
                 rw hxy, rw quotient.out_eq }
  else if hy : quotient.out y = b
       then by { simp [quotient.out_avoid] at hxy,
                 rw [dif_neg hx, dif_pos hy] at hxy,
                 transitivity quotient.mk a,
                 rw subtype.ext at hxy, simp at hxy,
                 rw ← hxy, rw quotient.out_eq,
                 transitivity quotient.mk b,
                 exact quot.eqv_gen_sound (eqv_gen.rel _ _ hrel),
                 rw ← hy, rw quotient.out_eq }
        else by { simp [quotient.out_avoid] at hxy,
                  rw [dif_neg hx, dif_neg hy] at hxy,
                  rw subtype.ext at hxy, simp at hxy,
                  rw [← quotient.out_eq x, ← quotient.out_eq y, hxy] }

lemma quotient.card_lt {α : Type*} [fintype α] (s : setoid α)
  (a b : α) (hdist : a ≠ b) (hrel : setoid.r a b)
  : fintype.card (quotient s) < fintype.card α :=
  by { apply @nat.lt_of_le_of_lt _ (fintype.card { x : α // x ≠ b }) _,
       apply fintype.card_le_of_injective (quotient.out_avoid s a b hdist),
       apply quotient.out_avoid_inj, assumption,
       rw fintype.card_of_removed, apply nat.pred_lt,
       intro h, rw fintype.card_eq_zero_iff at h, exact h a }

lemma finite_group.induction_ord (P : Π (G : Group), fintype G → Sort _)
  : (∀ (G : Group) (h : fintype G),
      (∀ (H : Group) (h' : fintype H),
       @fintype.card H h' < @fintype.card G h → P H h')
    → P G h)
  → ∀ (G : Group) (h : fintype G), P G h :=
begin
  intro inductive_step,
  suffices : ∀ n (G : Group) (h : fintype G), @fintype.card G h = n → P G h,
  { intros, apply this (@fintype.card G h), refl },
  intro n, apply @nat.strong_rec_on (λ n, ∀ (G : Group) (h : fintype G), @fintype.card G h = n → P G h) n,
  clear n, intros n ih G h card_eq,
  apply inductive_step, 
  intros H h' hlt,
  apply ih (@fintype.card H h') (card_eq ▸ hlt),
  refl
end

noncomputable
lemma finite_group.induction_subquot (P : Π (G : Group), fintype G → Sort _)
  : (∀ (G : Group) (h : fintype G),
      (∀ (H : set G) [inst : is_subgroup H], H ≠ set.univ →
       P (@Group.of H (@subtype.group _ _ _ inst))
                      (@subtype.fintype _ h _ _))
      → (∀ (N : set G) [inst : normal_subgroup N], N ≠ is_subgroup.trivial G →
          P (@Group.of (@quotient_group.quotient _ _ N inst.to_is_subgroup)
                       (@quotient_group.group _ _ N inst))
            (@quotient.fintype _ h _ _))
      → P G h)
  → ∀ (G : Group) (h : fintype G), P G h :=
begin
  intro inductive_step,
  apply finite_group.induction_ord,
  intros G h ih,
  apply inductive_step,
  { intros H inst h', apply ih,
    apply @nat.lt_of_le_of_lt _ (@fintype.card (subtype H) (@subtype.fintype _ h _ _)),
    refl,
    rw fintype.card_of_subtype (@set.to_finset _ H (@subtype.fintype _ h _ _)),
    dsimp [fintype.card], apply finset.card_lt_card,
    refine (_ : @set.to_finset _ H (@subtype.fintype _ h _ _) < @finset.univ _ h),
    apply lt_of_le_of_ne,
    apply finset.subset_univ,
    intro h'', apply h', ext,
    transitivity true, rw iff_true,
    have : x ∈ @set.to_finset _ H (@subtype.fintype _ h _ _), rw h'', apply finset.mem_univ,
    rw set.mem_to_finset at this, assumption,
    rw true_iff, apply set.mem_univ,
    intro, rw set.mem_to_finset, refl },
  { intros N inst hproper,
    apply ih,
    apply @nat.lt_of_le_of_lt _ (@fintype.card (@quotient_group.quotient _ _ N inst.to_is_subgroup) (@quotient.fintype _ h _ _)),
    refl, dsimp [quotient_group.quotient],
    have : ∃ x : G, x ∈ N ∧ x ≠ 1,
    { by_contra h, apply hproper,
      rw @is_subgroup.eq_trivial_iff _ _ _ inst.to_is_subgroup,
      intros, by_contra, apply h, 
      existsi x, constructor; assumption },
    cases this with x hx, cases hx with hN hdist,
    apply quotient.card_lt _, exact hdist.symm,
    refine (_ : 1⁻¹ * x ∈ N),
    rw [one_inv, one_mul], assumption }
end
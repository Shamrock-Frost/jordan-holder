import group_theory.subgroup
import group_theory.quotient_group
import data.fintype

universes u v w

section 

variables {G : Type u} [group G]

open is_subgroup

def fixed_by (N : set G) (H : set G) : Prop :=
  ∀ n, n ∈ N → ∀ h, h ∈ H → h * n * h⁻¹ ∈ N

def subset_inter_subset_right (N H : set G) : set H :=
  λ h, ↑ h ∈ N

instance subset_inter_subgroup {N H : set G} [is_subgroup N] [is_subgroup H]
  : @is_subgroup H subtype.group (subset_inter_subset_right N H) := {
    inv_mem := by { intros n helem, refine (_ : (↑ n) ⁻¹ ∈ N),
                    apply inv_mem, assumption },
    mul_mem := by { intros n n' h h', refine (_ : (↑ n) * (↑ n') ∈ N),
                    apply is_submonoid.mul_mem, assumption' },
    one_mem := by { refine (_ : ↑ 1 ∈ N), apply is_submonoid.one_mem }
  }

lemma fixed_by_to_normal (N : set G) [is_subgroup N] (H : set G) [is_subgroup H]
  (h : fixed_by N H) : @normal_subgroup H subtype.group (subset_inter_subset_right N H) :=
begin
  apply @normal_subgroup.mk H subtype.group (subset_inter_subset_right N H),
  intros, refine (_ : (↑ g) * (↑ n) * (↑ g⁻¹) ∈ N),
  apply h, assumption, apply g.property
end

def subquotient (H : set G) [is_subgroup H] (N : set G) [is_subgroup N]
  : Type u := quotient_group.quotient (subset_inter_subset_right N H)

def subquotient_group {H : set G} [is_subgroup H] {N : set G} [is_subgroup N] (hfix : fixed_by N H)
  : group (subquotient H N) := @quotient_group.group _ _ _ (fixed_by_to_normal N H hfix)

inductive normal_series' : set G → Type (u+1)
| empty : normal_series' (trivial G)
| step : ∀ (N : set G) [is_subgroup N] (H : set G) [is_subgroup H],
           N ⊂ H → fixed_by N H → normal_series' N → normal_series' H

def normal_series (G : Type u) [group G] := normal_series' (@set.univ G)

inductive is_composition_series : ∀ {H : set G}, normal_series' H → Prop
| empty : is_composition_series normal_series'.empty
| step : ∀ (N : set G) [inst_N : is_subgroup N] (H : set G) [inst_H : is_subgroup H]
           (hsub : N ⊂ H) (hfix : fixed_by N H)
           (S : normal_series' N),
           @simple_group (subquotient H N) (@subquotient_group _ _ H inst_H N inst_N hfix) →
           is_composition_series (@normal_series'.step _ _ N inst_N H inst_H hsub hfix S)

structure some_group :=
{G : Type u} (group_structure : group G)

def factors' (G : Type u) [group G]
  (S : normal_series G) : list some_group :=
  @normal_series'.rec_on _ _ (λ _ _, list some_group) 
                         _ S [] 
                         (λ N inst_N H inst_H hsub hfix _ l,
                            ⟨@subquotient_group _ _ H inst_H N inst_N hfix⟩ :: l)

-- noncomputable def composition_series_of_fin_group (is_fin : fintype G)
--   : normal_series G :=
--   if h : simple_group G
--   then normal_series'.step G 
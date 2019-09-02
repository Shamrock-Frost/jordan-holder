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

lemma quot_simple_iff_maximal (N : set G) [is_subgroup N]
  (is_max : lattice) := sorry

-- lemma subquot_simple_iff (N : set G) [inst_N : is_subgroup N] (H : set G) [inst_H : is_subgroup H]
--            (hfix : fixed_by N H) :
--            @simple_group (subquotient H N) (@subquotient_group _ _ H inst_H N inst_N hfix)
--            ↔ (∀ (K : set G) [is_subgroup K], K ⊆ H ∧ ∃ (n ∈ N) (k ∈ K), k * n * k⁻¹ ∉ N) :=
-- begin 
--   transitivity (∀ (K : set G) [is_subgroup K], K ⊆ H → ¬ fixed_by N K),
--   admit,
--   { constructor; intros h K inst_K,
--     specialize @h K inst_K,
--     dsimp [fixed_by] at h, }
-- end
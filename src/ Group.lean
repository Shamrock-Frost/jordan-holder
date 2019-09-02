import group_theory.subgroup
import group_theory.quotient_group
import group_theory.category
open category_theory

def Group.range {G H : Group} (φ : G ⟶ H) :=
  Group.of (set.range φ)


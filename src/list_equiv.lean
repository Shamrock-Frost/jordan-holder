import .category_theory .SES

universe u

def equiv_group_lists (L₁ L₂ : list Group) :=
  list.length L₁ = list.length L₂ ∧
  ∃ L, list.perm L L₁
     ∧ (list.foldr (∧) true
       $ list.zip_with (λ K K' : Group, nonempty (K ≅ K')) L L₂)

def termwise_iso_symm 
  : ∀ {xs ys : list Group},
  list.length xs = list.length ys
  → list.foldr (∧) true (list.zip_with (λ K K' : Group, nonempty (K ≅ K')) xs ys)
  → list.foldr (∧) true (list.zip_with (λ K K' : Group, nonempty (K ≅ K')) ys xs)
| [] [] hlen h := trivial
| [] (_::_) hlen h := by cases hlen
| (_::_) [] hlen h := by cases hlen
| (x::xs) (y::ys) hlen h :=
  match h.left with
  | ⟨iso⟩ := ⟨⟨iso.symm⟩, termwise_iso_symm (nat.succ.inj hlen) h.right⟩
  end

@[symm]
def equiv_group_lists.symm {xs ys : list Group}
  (heqv : equiv_group_lists xs ys) : equiv_group_lists ys xs :=
begin
  cases heqv with hlen heqv, cases heqv with L hL,
  cases hL with hperm hL, revert ys, induction hperm; intros ys hlen heqv,
  { simp at hlen, have := iff.mp list.length_eq_zero hlen.symm,
    rw this, obviously },
  case list.perm.skip : x xs L hperm ih
  { constructor, exact hlen.symm, cases ys with y ys, cases hlen, 
    cases ih (nat.succ_inj hlen) heqv.right with _ h,
    cases h with L' h, existsi list.cons y L',
    constructor, apply list.perm.skip, exact h.left,
    constructor, cases heqv.left, constructor, exact val.symm,
    exact h.right, },
  case list.perm.swap : x x' xs ys
  { constructor, exact hlen.symm,
    cases ys with y ys, cases hlen, cases ys with y' ys, cases hlen, 
    existsi list.cons y' (list.cons y ys), constructor,
    apply list.perm.swap, dsimp [list.zip_with] at heqv,
    cases heqv.left with h, cases heqv.right.left with h',
    exact ⟨⟨h'.symm⟩, ⟨h.symm⟩, termwise_iso_symm (nat.succ.inj $ nat.succ.inj hlen) heqv.right.right⟩ },
  case list.perm.trans : xs zs ws hxz hzw ih ih'
  { have : list.length ys = list.length zs,
    symmetry, transitivity list.length ws, apply list.perm_length, assumption', 
    cases ih this.symm heqv with _ h,
    cases h with L h, cases @ih' L _ _,
    tactic.swap, transitivity list.length ys, assumption,
    apply list.perm_length h.left.symm, tactic.swap,
    apply termwise_iso_symm, transitivity list.length ys,
    apply list.perm_length h.left, assumption,
    exact h.right,
    cases right with L' h', apply and.intro hlen.symm,
    existsi L', refine and.intro _ h'.right, transitivity L,
    exact h'.left, exact h.left }
end

inductive list.perm_seq {α : Type u} : list α → list α → Type (u+1)
| nil   : list.perm_seq [] []
| skip  : Π (x : α) {l₁ l₂ : list α}, list.perm_seq l₁ l₂ → list.perm_seq (x::l₁) (x::l₂)
| swap  : Π (x y : α) (l : list α), list.perm_seq (y::x::l) (x::y::l)
| trans : Π {l₁ l₂ l₃ : list α}, list.perm_seq l₁ l₂ → list.perm_seq l₂ l₃ → list.perm_seq l₁ l₃

lemma list.perm_iff_perm_seq {α} {xs ys : list α} : xs ~ ys ↔ nonempty (list.perm_seq xs ys) :=
begin
  constructor; intro hperm,
  { induction hperm,
    { constructor, constructor },
    { cases hperm_ih, constructor, constructor, assumption },
    { constructor, constructor },
    { cases hperm_ih_a, cases hperm_ih_a_1, constructor, constructor; assumption } },
  { cases hperm, induction hperm,
    { constructor },
    { constructor, assumption },
    { constructor },
    { constructor; assumption } }
end

lemma list.perm_seq_length {α} {xs xs' : list α}
  : list.perm_seq xs xs' → list.length xs = list.length xs'
  := by { intro h, replace h := nonempty.intro h,
          rw ← list.perm_iff_perm_seq at h, apply list.perm_length h }

def apply_perm {α β} : ∀ {ys ys' : list α},
  list.perm_seq ys ys'
  → ∀ (xs : list β), xs.length = ys.length → Σ (xs' : list β), list.perm_seq xs xs'
| [] [] list.perm_seq.nil := λ xs,
  match xs with
  | [] := λ _, ⟨[], list.perm_seq.nil⟩
  | _::_ := λ hlen, false.elim (nat.succ_ne_zero _ hlen)
  end
| (._::ys) (._::ys') (list.perm_seq.skip y hperm) := λ xs,
  match xs with
  | [] := λ hlen, false.elim $ nat.succ_ne_zero _ hlen.symm
  | (x::xs) := λ hlen,
    let ⟨xs', h⟩ := apply_perm hperm xs (nat.succ.inj hlen)
    in ⟨x::xs', list.perm_seq.skip x h⟩
  end
| ._ ._ (list.perm_seq.swap a b ys) := λ xs,
  match xs with
  | [] := λ hlen, false.elim $ nat.succ_ne_zero _ hlen.symm
  | [_] := λ hlen, false.elim $ nat.succ_ne_zero _ (nat.succ.inj hlen.symm)
  | (x::x'::xs) := 
      λ _, ⟨x' :: x :: xs, list.perm_seq.swap x' x xs⟩
  end
| ys ys'' (@list.perm_seq.trans _ _ ys' _ hperm hperm') := λ xs hlen,
  let ⟨xs', h⟩ := apply_perm hperm xs hlen,
      ⟨xs'', h'⟩ := apply_perm hperm' xs'
        $ calc list.length xs' = list.length xs : eq.symm (list.perm_seq_length h)
               ...             = list.length ys : hlen
               ...             = list.length ys' : list.perm_seq_length hperm
  in ⟨xs'', list.perm_seq.trans h h'⟩

lemma apply_perm_spec {α α' β γ} {f : α → α' → β} (c : β → γ → γ) (n : γ)
  (f_comm : left_commutative c)
  {xs : list α} {ys L : list α'}
  (hlen : list.length xs = list.length ys)
  (hperm : list.perm_seq ys L)
  : list.foldr c n (list.zip_with f xs ys)
  = list.foldr c n (list.zip_with f (apply_perm hperm xs hlen).fst L) :=
begin
  revert xs, induction hperm; intros,
  { dsimp at hlen, rw list.length_eq_zero at hlen, subst hlen, refl },
  case list.perm_seq.skip : y ys ys' hperm ih {
    cases xs with x xs, { exfalso, exact nat.succ_ne_zero _ (eq.symm hlen), },
    dsimp [apply_perm], destruct (apply_perm hperm xs (nat.succ_inj hlen)), 
    intros, rw a, dsimp [apply_perm._match_3, list.zip_with, list.foldr],
    apply congr_arg, rw (_ : fst = (apply_perm hperm xs (nat.succ_inj hlen)).fst),
    apply ih, rw a,
  },
  case list.perm_seq.swap : y' y ys xs hlen ih {
    cases xs with x xs, contradiction,
    cases xs with x' xs, have := nat.succ_inj hlen, contradiction,
    apply f_comm,
  },
  case list.perm_seq.trans : ys ys' ys'' hperm hperm' ih ih' {
    dsimp [apply_perm], destruct apply_perm hperm xs hlen, intros,
    rw a, dsimp [apply_perm._match_6],
    have hlen' : list.length fst = list.length ys',
    { transitivity list.length xs, symmetry, apply list.perm_seq_length, assumption,
      transitivity list.length ys, assumption, apply list.perm_seq_length, assumption, },
    destruct apply_perm hperm' fst hlen', intros,
    rw a_1, dsimp [apply_perm._match_5],
    rw (_ : fst_1 = (apply_perm hperm' fst hlen').fst),
    rw ← ih', rw (_ : fst = (apply_perm hperm xs hlen).fst),
    apply ih, rw a, rw a_1,
  }
end

@[trans]
lemma equiv_group_lists.trans {xs ys zs : list Group}
  (hxy : equiv_group_lists xs ys) (hyz : equiv_group_lists ys zs)
  : equiv_group_lists xs zs :=
begin
  cases hxy with hlen hxy, cases hxy with L h, cases h with hperm h,
  replace hyz := equiv_group_lists.symm hyz,
  cases hyz with hlen' hyz, cases hyz with L' h', cases h' with hperm' h',
  constructor, exact eq.trans hlen hlen'.symm,
  have : list.foldr and true (list.zip_with (λ (K K' : Group), nonempty (K ≅ K')) L L'),
  { replace hlen := eq.trans (list.perm_length hperm) hlen,
    replace hlen' := eq.trans (list.perm_length hperm') hlen',
    clear hperm, clear hperm', clear xs, clear zs,
    revert L L', induction ys with y ys ih; intros xs zs h h' hlen hlen';
    cases xs with x xs; cases zs with z zs; try { contradiction },
    case list.nil { constructor },
    case list.cons {
      constructor,
      { cases h.left, cases h'.left, constructor,
        transitivity y, assumption, symmetry, assumption },
      { apply ih, exact h.right, exact h'.right,
        exact nat.succ.inj hlen, exact nat.succ.inj hlen' } } },
  replace hlen := eq.trans hlen (eq.symm hlen'),
  clear h, clear h', clear hlen', clear ys,  
  rw list.perm_iff_perm_seq at hperm hperm',
  cases hperm, cases hperm',
  have hlen' : list.length L = list.length L'
    := calc list.length L = list.length xs : list.perm_seq_length hperm
            ...           = list.length zs : hlen
            ...           = list.length L' : eq.symm (list.perm_seq_length hperm'),
  existsi (apply_perm hperm' L hlen').fst, constructor,
  { have hperm := iff.mpr list.perm_iff_perm_seq ⟨hperm⟩,
    have hperm'' := iff.mpr list.perm_iff_perm_seq ⟨(apply_perm hperm' L hlen').snd⟩,
    transitivity L, symmetry, assumption, assumption },
  rw ← apply_perm_spec, assumption,
  { intros p q r, rw [← and_assoc p q, and_comm p q, and_assoc q p], }
end

lemma equiv_group_lists.skip {xs ys : list Group} (x : Group)
  (heqv : equiv_group_lists xs ys) : equiv_group_lists (x::xs) (x::ys) :=
begin
  cases heqv with hlen heqv, apply and.intro (congr_arg nat.succ hlen),
  cases heqv with L h, cases h with hperm h, existsi (list.cons x L),
  constructor, apply list.perm.skip, assumption, refine ⟨_, h⟩, constructor, refl
end

lemma equiv_group_lists.swap' {xs ys : list Group} (a b : Group)
  (heqv : equiv_group_lists xs ys) : equiv_group_lists (a::b::xs) (b::a::ys) :=
begin
  cases heqv with hlen heqv, apply and.intro (congr_arg nat.succ (congr_arg nat.succ hlen)),
  cases heqv with L h, cases h with hperm h, existsi (list.cons b (list.cons a L)),
  constructor, apply list.perm.swap', assumption, refine ⟨_, _, h⟩; constructor; refl
end
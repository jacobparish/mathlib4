import Mathlib.Tactic
import Mathlib.Data.Finite.Defs
import Mathlib.Data.Finset.Card

namespace Combinatorics

open Set Finset

variable {α β : Type*}
variable {n : ℕ}

abbrev NSet (α : Type*) (n : ℕ) := { s : Finset α // s.card = n }

notation α "⟦^" n "⟧" => NSet α n

namespace NSet

@[simp]
lemma card_eq (s : α⟦^n⟧) : s.val.card = n := s.prop

open Classical in
noncomputable def insert_notMem (s : α⟦^n⟧) (a : α) (h : a ∉ (s : Finset α)) : α⟦^n+1⟧ :=
  ⟨insert a s, by simp [card_insert_of_notMem h]⟩

open Classical in
noncomputable def erase_mem (s : α⟦^n + 1⟧) (a : α) (h : a ∈ (s : Finset α)) : α⟦^n⟧ :=
  ⟨erase s a, by simp [card_erase_of_mem h]⟩

open Classical in
@[simp]
lemma coe_insert_notMem (s : α⟦^n⟧) (a : α) (h : a ∉ (s : Finset α))
    : s.insert_notMem a h = insert a (s : Finset α)
  := rfl

open Classical in
@[simp]
lemma coe_erase_mem (s : α⟦^n + 1⟧) (a : α) (h : a ∈ (s : Finset α))
    : s.erase_mem a h = erase (s : Finset α) a
  := rfl

lemma mem_insert_notMem {s : α⟦^n⟧} {a : α} (h : a ∉ (s : Finset α))
    : a ∈ (s.insert_notMem a h : Finset α) := by
  simp [insert_notMem]

lemma notMem_erase_mem {s : α⟦^n + 1⟧} {a : α} (h : a ∈ (s : Finset α))
    : a ∉ (s.erase_mem a h : Finset α) := by
  simp [erase_mem]

@[simp]
lemma erase_insert_notMem {s : α⟦^n⟧} {a : α} (h : a ∉ (s : Finset α))
    : (s.insert_notMem a h).erase_mem a (mem_insert_notMem h) = s := by
  simp [insert_notMem, erase_mem, h]

@[simp]
lemma insert_erase_mem {s : α⟦^n + 1⟧} {a : α} (h : a ∈ (s : Finset α))
    : (s.erase_mem a h).insert_notMem a (notMem_erase_mem h) = s := by
  simp [insert_notMem, erase_mem, h]

open Classical in
noncomputable def preimage (s : β⟦^n⟧) (f : α → β) (hf : InjOn f (f ⁻¹' s)) (hs : ↑s ⊆ range f)
    : α⟦^n⟧ :=
  ⟨s.val.preimage f hf, by
    rw [card_preimage]
    convert s.card_eq
    grind
  ⟩

open Classical in
noncomputable def image (s : α⟦^n⟧) (f : α → β) (hf : InjOn f s) : β⟦^n⟧ :=
  ⟨s.val.image f, by rw [card_image_of_injOn hf, s.card_eq]⟩

@[simp]
lemma coe_preimage (s : β⟦^n⟧) {f : α → β} (hf : InjOn f (f ⁻¹' s)) (hs : ↑s ⊆ range f)
  : (s.preimage f hf hs).val = s.val.preimage f hf := rfl

open Classical in
@[simp]
lemma coe_image (s : α⟦^n⟧) {f : α → β} (hf : InjOn f s) : (s.image f hf).val = s.val.image f := rfl

open Classical in
@[simp]
lemma image_preimage (s : β⟦^n⟧) {f : α → β} (hf : InjOn f (f ⁻¹' s)) (hs : ↑s ⊆ range f)
    : (s.preimage f hf hs).image f (by simpa) = s := by
  ext
  grind [coe_image, coe_preimage, Finset.image_preimage]

noncomputable instance {x : Set α} : CoeOut (x⟦^n⟧) (α⟦^n⟧) where
  coe s := s.image (↑) injOn_subtype_val

noncomputable instance {t : Finset α} : CoeOut (t⟦^n⟧) (α⟦^n⟧) where
  coe s := s.image (↑) injOn_subtype_val

lemma val_nonempty (s : α⟦^n + 1⟧) : s.val.Nonempty := by
  simp [← card_ne_zero, s.card_eq]

end NSet

namespace Ramsey

open NSet Filter Ultrafilter

open Classical in
/--
Given, for every finite subset `t` of `α`, some `a` satisfying `p t a`, we can build a sequence
`f : ℕ → α` such that `p (f {0,...,k-1}) (f k)` holds for every `k`.
-/
private noncomputable def ramseySeq {p : Finset α → α → Prop} (h : ∀ t, ∃ a, p t a) (k : ℕ) : α :=
  (h <| univ.image fun l : Fin k => ramseySeq h l).choose

open Classical in
/--
When `p` implies `a ∉ t`, then the sequence is injective.
-/
private lemma ramseySeq_inj {p : Finset α → α → Prop} (hp : ∀ t a, p t a → a ∉ t)
    (h : ∀ t, ∃ a, p t a) : (ramseySeq h).Injective := by
  apply Function.Injective.of_lt_imp_ne
  intro k₁ k₂ hk
  let t : Finset α := univ.image fun l : Fin k₂ => ramseySeq h l
  have : ramseySeq h k₁ ∈ t := by
    rw [mem_image_univ_iff_mem_range]
    use ⟨k₁, hk⟩
  grind [ramseySeq]

variable {α : Type*} [Infinite α]
variable {ι : Type*} [Finite ι]

/--
Given a coloring `c` of the `(n+1)`-sets of `α`, the set `ramseySet c s i` consists of all elements
`a : α` that extend the `n`-set `s` to an `(n+1)`-set of color `i`.
-/
private def ramseySet (c : α⟦^n + 1⟧ → ι) (s : α⟦^n⟧) (i : ι) :=
  { a | ∃ h : a ∉ s.val, c (s.insert_notMem a h) = i }

/--
For each `n`-set `s` of `α`, since `c` partitions the complement of `s` into finitely many pieces,
one of them must lie in the hyperfilter on `α`.
-/
private lemma exists_color_ramseySet_mem_hyperfilter (c : α⟦^n + 1⟧ → ι) (s : α⟦^n⟧)
    : ∃ i, ramseySet c s i ∈ hyperfilter α := by
  apply finite_iUnion_mem_iff.mp
  apply mem_hyperfilter_of_finite_compl
  convert s.val.finite_toSet
  ext
  simp [ramseySet]

/--
A coloring `c` on `(n+1)`-sets induces a coloring on `n`-sets by sending an `n`-set `s` to some
color `i` such that `ramseySet c s i` is in the hyperfilter on `α`.
-/
private noncomputable def inducedColoring (c : α⟦^n + 1⟧ → ι) (s : α⟦^n⟧) : ι :=
  (exists_color_ramseySet_mem_hyperfilter c s).choose

/--
The key property of the induced coloring `c'`: for every finite subset `t` of `α`, there is some
`a ∉ t` such that `c' s = c (s ∪ {a})` for every `n`-set `s ⊆ t`.
-/
private lemma exists_notMem_inducedColoring_eq (c : α⟦^n + 1⟧ → ι) (t : Finset α)
    : ∃ (a : α) (ha : a ∉ t), ∀ (s : α⟦^n⟧) (hs : ↑s ⊆ t),
    inducedColoring c s = c (s.insert_notMem a (by tauto)) := by
  have ⟨a, ha, ha'⟩ : ((↑t)ᶜ ∩ (⋂ s : t⟦^n⟧, ramseySet c s (inducedColoring c s))).Nonempty
      := by
    apply (hyperfilter α).nonempty_of_mem
    apply (hyperfilter α).inter_mem
    · exact compl_mem_hyperfilter_of_finite t.finite_toSet
    · exact iInter_mem.mpr fun s => (exists_color_ramseySet_mem_hyperfilter c s).choose_spec
  use a, ha
  intro s hs
  have ⟨_, hcs⟩ := mem_iInter.mp ha' <| s.preimage (↑) injOn_subtype_val (by simp [hs])
  simp_all

open Classical in
/--
The infinite Ramsey theorem. If `α` is an infinite type, and if `c` is a coloring of the `n`-sets of
`α` by a finite type `ι`, then there is an infinite subset `x` of `α` for which all `n`-sets of `x`
are the same color.
-/
theorem exists_infinite_monochromatic_subset (n : ℕ) (c : α⟦^n⟧ → ι) : ∃ x : Set α, x.Infinite ∧
    ∀ s₁ s₂ : α⟦^n⟧, ↑s₁ ⊆ x → ↑s₂ ⊆ x → c s₁ = c s₂ := by
  induction n generalizing α with
  | zero =>
    use univ, infinite_univ_iff.mpr inferInstance
    intro ⟨s, hs⟩ ⟨t, ht⟩
    simp [hs, ht, card_eq_zero.mp]
  | succ n IH =>
    -- `c'` is the coloring to which we will apply the induction hypothesis.
    set c' := inducedColoring c with c'_def
    have hc' := exists_notMem_inducedColoring_eq c
    let f := ramseySeq hc'
    have f_inj := ramseySeq_inj (by tauto) hc'
    let y := range f
    have y_inf := infinite_coe_iff.mpr (infinite_range_of_injective f_inj)
    -- The key claim: for every `(n+1)`-set `s ⊆ y`, there is some `a ∈ s` such that
    -- `c' s = c (s \ {a})`, namely the last value enumerated by `f`.
    have hy (s : α⟦^n+1⟧) (hs : ↑s ⊆ y) : ∃ (a : α) (ha : a ∈ s.val), c s = c' (s.erase_mem a ha)
        := by
      let s_pre := s.preimage f f_inj.injOn hs
      let k := s_pre.val.max' s_pre.val_nonempty
      have hk : k ∈ s_pre.val := s_pre.val.max'_mem s_pre.val_nonempty
      have hfk : f k ∈ s.val := by simp_all [s_pre]
      use f k, hfk
      let t : Finset α := univ.image fun l : Fin k => f l
      let s' := s.erase_mem (f k) hfk
      have hs' : (s' : Set α) ⊆ t := by
        intro b hb
        rw [Finset.coe_image, coe_univ, image_univ]
        have : b ∈ s.val := by simp_all [s']
        obtain ⟨l, rfl⟩ := hs this
        refine ⟨⟨l, ?_⟩, rfl⟩
        apply s_pre.val.lt_max'_of_mem_erase_max'
        rw [mem_erase]
        simp only [coe_erase_mem, coe_erase, mem_diff, SetLike.mem_coe, mem_singleton_iff, s'] at hb
        use hb.2 ∘ congrArg f
        simpa [s_pre]
      rw [c'_def, (hc' t).choose_spec.2 s' hs']
      congr
      ext
      grind [ramseySeq, coe_insert_notMem, coe_erase_mem]
    -- Since `y` is infinite, we can apply the induction hypothesis to `c'` restricted to `y`.
    let ⟨x, x_inf, hx⟩ := IH fun s : y⟦^n⟧ => c' s
    use x, x_inf.image injOn_subtype_val
    -- A version of the key claim to streamline the conclusion.
    have hy' (s : α⟦^n+1⟧) (hs : (s : Set α) ⊆ x)
        : ∃ (s' : y⟦^n⟧) (hs' : (s' : Set y) ⊆ x), c s = c' s' := by
      have hsy := hs.trans (Subtype.coe_image_subset y x)
      let ⟨a, ha, ha'⟩ := hy s hsy
      use (s.erase_mem a ha).preimage (↑) injOn_subtype_val (by simp [erase_mem]; tauto)
      simp [ha']
      grind
    intros
    grind

end Ramsey

end Combinatorics

import Mathlib.Algebra.Order.ZeroLEOne
import Mathlib.Data.Fin.Basic
import Mathlib.Data.List.Chain
import Mathlib.Data.List.Interleave

namespace List

variable {α : Type*} {r : α → α → Prop}

lemma isChain_append_pair (l : List α) (a b : α) :
    IsChain r (l ++ [a, b]) ↔ IsChain r (l ++ [a]) ∧ r a b := by
  simp

lemma interleave_append (l₁ l₂ l₃ l₄ : List α) (h : l₁.length = l₂.length) :
    (l₁ ++ l₃).interleave (l₂ ++ l₄) = l₁.interleave l₂ ++ l₃.interleave l₄ := by
  induction l₁ generalizing l₂ with rcases l₂ with _ | ⟨b, l₂⟩ <;> simp_all

lemma interleave_append_left (l₁ l₂ l₃ l₄ : List α) (h : l₁.length + 1 = l₂.length) :
    (l₁ ++ l₃).interleave (l₂ ++ l₄) = l₁.interleave l₂ ++ l₄.interleave l₃ := by
  rcases l₂ with _ | ⟨_, l₂⟩
  · simp_all
  · simp only [length_cons] at h
    simp [cons_append, interleave_cons, interleave_append l₂ l₁ l₄ l₃ (by lia)]

lemma interleave_append_singleton (l₁ l₂ : List α) (a b : α) (h : l₁.length = l₂.length) :
    (l₁ ++ [a]).interleave (l₂ ++ [b]) = (l₁.interleave l₂) ++ [b, a] := by
  simp [interleave_append l₁ l₂ _ _ h]

lemma interleave_append_singleton_left (l₁ l₂ : List α) (a b : α)
    (h : l₁.length + 1 = l₂.length) :
    (l₁ ++ [a]).interleave (l₂ ++ [b]) = (l₁.interleave l₂) ++ [a, b] := by
  simp [interleave_append_left l₁ l₂ _ _ h]

lemma interleave_append_singleton_right (l₁ l₂ : List α) (a : α) (h : l₁.length = l₂.length) :
    l₁.interleave (l₂ ++ [a]) = (l₁.interleave l₂) ++ [a] := by
  rw [← append_nil l₁, interleave_append l₁ l₂ [] [a] h]
  simp

lemma interleaves_cons_reverse {l₁ l₂ : List α} {a b : α}
    (h : l₁.length = l₂.length) :
    Interleaves r (a :: l₁).reverse (b :: l₂).reverse ↔
      r b a ∧ Interleaves r l₁.reverse (b :: l₂).reverse := by
  rw [interleaves_iff_length_isChain_interleave,
      interleaves_iff_length_isChain_interleave]
  simp only [reverse_cons, length_reverse, length_cons, length_append]
  rw [interleave_append_singleton _ _ _ _ (by simp [h]),
      interleave_append_singleton_right _ _ _ (by simp [h]),
      isChain_append_pair]
  simp [h, and_comm]

lemma interleaves_cons_reverse_left {l₁ l₂ : List α} {a b c : α}
    (h : l₁.length + 1 = (c :: l₂).length) :
    Interleaves r (a :: l₁).reverse (b :: c :: l₂).reverse ↔
      r a b ∧ r c a ∧ Interleaves r l₁.reverse (c :: l₂).reverse := by
  have h_eq : l₁.length = l₂.length := by simp_all
  rw [interleaves_iff_length_isChain_interleave,
      interleaves_iff_length_isChain_interleave]
  simp only [reverse_cons, length_reverse, length_cons, length_append]
  rw [interleave_append_singleton_left _ _ _ _ (by simp [h_eq]),
      interleave_append_singleton_right _ _ _ (by simp [h_eq]),
      isChain_append_pair, append_assoc, cons_append,
      nil_append, isChain_append_pair]
  simp [h_eq, and_comm]

lemma interleaves_reverse_of_interlaced_left
    {l₁ l₂ : List α} (h : l₁.length + 1 = l₂.length)
    (hint : ∀ (i : Fin l₁.length) (j : Fin l₂.length),
      i.val + 1 = j.val → r l₂[j.val] l₁[i.val])
    (hint' : ∀ (i : Fin l₂.length) (j : Fin l₁.length),
      i.val < j.val + 1 → r l₁[j.val] l₂[i.val]) :
    Interleaves r l₁.reverse l₂.reverse := by
  induction l₁ generalizing l₂ with
  | nil =>
    rcases l₂ with _ | ⟨_, _ | ⟨_, _⟩⟩
    · simp
    · simp
    · simp only [length] at h
      lia
  | cons a l₁ ih =>
    rcases l₂ with _ | ⟨b, _ | ⟨c, l₂⟩⟩
    · simp only [length] at h
      lia
    · simp only [length] at h
      lia
    · have : l₁.length + 1 = (c :: l₂).length := by
        simp only [length_cons] at h ⊢
        lia
      rw [interleaves_cons_reverse_left this]
      exact ⟨hint' ⟨0, by simp⟩ ⟨0, by simp⟩ (by simp),
              hint ⟨0, by simp⟩ ⟨1, by simp⟩ (by simp),
              ih this
                (fun i j h_eq ↦
                  hint ⟨i.val + 1, Nat.succ_lt_succ i.isLt⟩
                    ⟨j.val + 1, Nat.succ_lt_succ j.isLt⟩ (by lia))
                (fun i j h_lt ↦
                  hint' ⟨i.val + 1, Nat.succ_lt_succ i.isLt⟩
                    ⟨j.val + 1, Nat.succ_lt_succ j.isLt⟩ (by lia))⟩

lemma interleaves_reverse_of_interlaced
    {l₁ l₂ : List α} (h : l₁.length = l₂.length)
    (hint : ∀ (k : Fin l₁.length), r l₂[k.val] l₁[k.val])
    (hint' : ∀ (i j : Fin l₁.length), i.val < j.val → r l₁[j.val] l₂[i.val]) :
    Interleaves r l₁.reverse l₂.reverse := by
  induction l₁ generalizing l₂ with
  | nil =>
    rcases l₂ with _ | ⟨_, l₂⟩
    · simp
    · simp only [length] at h
      lia
  | cons a l₁ _ =>
    rcases l₂ with _ | ⟨b, l₂⟩
    · simp only [length] at h
      lia
    · have h_len : l₁.length = l₂.length := by
        simp only [length_cons] at h ⊢
        lia
      rw [interleaves_cons_reverse h_len]
      refine ⟨hint ⟨0, Nat.succ_pos _⟩,
              interleaves_reverse_of_interlaced_left (congrArg (· + 1) h_len)
                (fun i j hij ↦ ?_)
                (fun i j hij ↦ hint' ⟨i.val,
                  show i.val < l₁.length + 1 from h_len.symm ▸ i.isLt⟩
                  ⟨j.val + 1, Nat.succ_lt_succ j.isLt⟩ hij)⟩
      · rcases i with ⟨i_val, hi⟩
        rcases j with ⟨_ | j_val, hj⟩
        · lia
        · obtain rfl : i_val = j_val := by lia
          exact hint ⟨i_val + 1, h.symm ▸ hj⟩

lemma Interleaves.ofFn [Preorder α] {n : ℕ}
    (f g : Fin n → α)
    (hint : ∀ k : Fin n, f k < g k)
    (hint' : ∀ (i j : Fin n), i < j → g i < f j) :
    Interleaves (· > ·) (ofFn f).reverse (ofFn g).reverse := by
  refine interleaves_reverse_of_interlaced (by simp) ?_ ?_ <;> simp_all

end List

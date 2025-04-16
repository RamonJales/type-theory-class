-- γ ⨯ (α + β) ≅ (γ ⨯ α) + (γ ⨯ β)
def f_distributive : (γ × (α ⊕ β)) → (γ × α) ⊕ (γ × β)
| (w, Sum.inl a) => Sum.inl (w, a)
| (w, Sum.inr b) => Sum.inr (w, b)

def f'_distributive : (γ × α) ⊕ (γ × β) → (γ × (α ⊕ β))
| Sum.inl (w, a) => (w, Sum.inl a)
| Sum.inr (w, b) => (w, Sum.inr b)

theorem types_distributive {γ α β : Type} :
  (∀ (x : γ × (α ⊕ β)), (f'_distributive ∘ f_distributive) x = x) ∧
  (∀ (y : (γ × α) ⊕ (γ × β)), (f_distributive ∘ f'_distributive) y = y) :=
by
    constructor
    -- And left case:
    intro x
    cases x
    rename_i w s
    cases s
    rename_i a
    calc
        (f'_distributive ∘ f_distributive) (w, Sum.inl a)
          = f'_distributive (f_distributive ((w, Sum.inl a))) := by rfl
        _ = f'_distributive (Sum.inl (w, a))                  := by rfl
        _ = (w, Sum.inl a)                                    := by rfl
    rename_i b
    calc
        (f'_distributive ∘ f_distributive) (w, Sum.inr b)
          = f'_distributive (f_distributive (w, Sum.inr b)) := by rfl
        _ = f'_distributive (Sum.inr (w, b))                := by rfl
        _ = (w, Sum.inr b)                                  := by rfl
    -- And right case:
    intro y
    cases y
    rename_i p
    cases p
    rename_i w a
    calc
        (f_distributive ∘ f'_distributive) (Sum.inl (w, a))
            = f_distributive (f'_distributive ((Sum.inl (w, a)))) := by rfl
          _ = f_distributive (w, Sum.inl a)                       := by rfl
          _ = Sum.inl (w, a)                                      := by rfl
    rename_i p
    cases p
    rename_i w b
    calc
        (f_distributive ∘ f'_distributive) (Sum.inr (w, b))
            = f_distributive (f'_distributive ((Sum.inr (w, b))))   := by rfl
          _ = f_distributive (w, Sum.inr b)                         := by rfl
          _ = Sum.inr (w, b)                                        := by rfl

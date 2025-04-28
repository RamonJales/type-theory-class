open Sum

instance : Add Type where
  add := Sum

def inv (f : α → β) (f' : β → α) := f ∘ f' = id ∧ id = f'∘ f
def iso (f : α → β) := ∃f': β → α, inv f f'
def type_isomorphism (α β : Type) := ∃f : α → β, iso f

-- γ ⨯ (α + β) ≅ (γ ⨯ α) + (γ ⨯ β)
def f_distributive : (γ × (α ⊕ β)) → (γ × α) ⊕ (γ × β)
| (w, inl a) => inl (w, a)
| (w, inr b) => inr (w, b)

def f'_distributive : (γ × α) ⊕ (γ × β) → (γ × (α ⊕ β))
| inl (w, a) => (w, inl a)
| inr (w, b) => (w, inr b)

-- (α + β) + γ ≅ α + (β + γ)
def f_add_ass : ((α + β) + γ) → (α + (β + γ))
  | inl (inl a) => inl a
  | inl (inr b) => inr (inl b)
  | inr c => inr (inr c)

def f'_add_ass : (α + (β + γ)) → ((α + β) + γ)
  | inl a => inl (inl a)
  | inr (inl b) => inl (inr b)
  | inr (inr c) => inr c

-- 0 + α ≅ α
def f_add_id : (Empty + α) → α
  | inl epty => epty.elim
  | inr a => a

def f'_add_id : α → (Empty + α)
  | a => inr a

-- 1 × α ≅ α
def f_prod_id : Unit × α → α
  | (_, a) => a

def f'_prod_id : α → Unit × α
  | a => ((), a) --or (Unit.unit, a)

-- (α ⨯ β) ⨯ γ ≅ α ⨯ (β ⨯ γ)
def f_prod_ass : ((α × β) × γ) → (α × (β × γ))
  | ((a, b), c) => (a, (b, c))

def f'_prod_ass : (α × (β × γ)) → ((α × β) × γ)
  | (a, (b, c)) => ((a, b), c)

-- δ^α+β ≅ δ^α ⨯ δ^β
def f_exp_distributive {α : Type u} {β : Type v} {δ : Type w} :
  ((α ⊕ β) → δ) → ((α → δ) × (β → δ))
| f => (fun a => f (inl a), fun b => f (inr b))


def f'_exp_distributive {α : Type u} {β : Type v} {δ : Type w} :
  (((α → δ) × (β → δ) → (α ⊕ β) → δ))
  | (f, f') => fun w => match w with
                    | inl a => f a
                    | inr b => f' b
-- note que w não é usado, logo podemos definir assim:
  -- | (f, f') => λ
  --               | inl a => f a
  --               | inr b => f' b


-- (γ^β)^α ≅ γ^{β ⨯ α}
def f_exp_curry : (α → β → δ) → ((α × β) → δ)
  | f => fun (a,b) => f a b

def f'_exp_curry : ((α × β) → δ) → (α → β → δ)
  | f => fun a => fun b => f (a,b)


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
        (f'_distributive ∘ f_distributive) (w, inl a)
          = f'_distributive (f_distributive ((w, inl a))) := by rfl
        _ = f'_distributive (inl (w, a))                  := by rfl
        _ = (w, inl a)                                    := by rfl
    rename_i b
    calc
        (f'_distributive ∘ f_distributive) (w, inr b)
          = f'_distributive (f_distributive (w, inr b)) := by rfl
        _ = f'_distributive (inr (w, b))                := by rfl
        _ = (w, inr b)                                  := by rfl
    -- And right case:
    intro y
    cases y
    rename_i p
    cases p
    rename_i w a
    calc
        (f_distributive ∘ f'_distributive) (inl (w, a))
            = f_distributive (f'_distributive ((inl (w, a)))) := by rfl
          _ = f_distributive (w, inl a)                       := by rfl
          _ = inl (w, a)                                      := by rfl
    rename_i p
    cases p
    rename_i w b
    calc
        (f_distributive ∘ f'_distributive) (inr (w, b))
            = f_distributive (f'_distributive ((inr (w, b))))   := by rfl
          _ = f_distributive (w, inr b)                         := by rfl
          _ = inr (w, b)                                        := by rfl

theorem type_add_ass {γ α β : Type} : type_isomorphism ((α + β) + γ) (α + (β + γ)) := by
  sorry

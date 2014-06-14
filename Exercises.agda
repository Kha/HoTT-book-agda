{-# OPTIONS --without-K #-}

open import HoTT

-- 1.2

rec× : {A B C : Type₀} → (A → B → C) → (A × B → C)
rec× f x = f (fst x) (snd x)

rec×-pair : {A B C : Type₀} → (f : A → B → C) → (x : A) → (y : B) → rec× f (x , y) == f x y
rec×-pair f x y = idp

recΣ : {A C : Type₀} {B : A → Type₀} → ((a : A) → B a → C) → (x : Σ A B) → C
recΣ f x = f (fst x) (snd x)

-- ...

-- 1.3

ind× : {A B : Type₀} → (C : A × B → Type₀) → ((a : A) → (b : B) → C (a , b)) → ((x : A × B) → C x)
ind× C f x = f (fst x) (snd x)
-- no uppt needed since _×_ posseses judgemental uniqueness

ind×-pair : {A B : Type₀} → (C : A × B → Type₀) → (f : (a : A) → (b : B) → C (a , b)) → (a : A) → (b : B) → ind× C f (a , b) == f a b
ind×-pair C f a b = idp

indΣ : {A : Type₀} {B : A → Type₀} (C : Σ A B → Type₀) → ((a : A) → (b : B a) → C (a , b)) → (x : Σ A B) → C x
indΣ C f x = f (fst x) (snd x)

-- ...

-- 1.4

iterℕ : ∀ {i} → {C : Type i} → C → (C → C) → ℕ → C
iterℕ c₀ cₛ 0 = c₀
iterℕ c₀ cₛ (S n) = cₛ $ iterℕ c₀ cₛ n

module _ {i} {C : Type i} (c₀ : C) (cₛ : ℕ → C → C) where
  private
    recℕ-aux : ℕ → ℕ × C
    recℕ-aux n  = iterℕ (0 , c₀) cₛ' n where
      cₛ' : ℕ × C → ℕ × C
      cₛ' (n , c) = (S n , cₛ n c)

  recℕ : ℕ → C
  recℕ = snd ∘ recℕ-aux

  recℕ-0 : recℕ 0 == c₀
  recℕ-0 = idp
  
  recℕ-S : (n : ℕ) → recℕ (S n) == cₛ n (recℕ n)
  recℕ-S n = ap (λ x → cₛ x (recℕ n)) (recℕ-aux-fst-id n)
    where
      recℕ-aux-fst-id : (n : ℕ) → fst (recℕ-aux n) == n
      recℕ-aux-fst-id O = idp
      recℕ-aux-fst-id (S n) = ap S (recℕ-aux-fst-id n)

-- 1.5

_+'_ : ∀ {i} (A : Type i) (B : Type i) → Type i
A +' B = Σ Bool (λ b → if b then A else B)

module _ {i} (A : Type i) (B : Type i) where
  inl' : A → A +' B
  inl' a = (true , a)

  inr' : B → A +' B
  inr' b = (false , b)

  module _ {j} (C : A +' B → Type j) (f : (a : A) → C (inl' a)) (g : (b : B) → C (inr' b)) where 
    ind+' : (x : A +' B) → C x
    ind+' (true , a) = f a
    ind+' (false , b) = g b

    ind+'-inl' : (a : A) → ind+' (inl' a) == f a
    ind+'-inl' a = idp

-- 1.6

_×'_ : ∀ {i} (A : Type i) (B : Type i) → Type i
A ×' B = (b : Bool) → (if b then A else B)

module _ {i} (A : Type i) (B : Type i) where
  pair' : A → B → A ×' B
  pair' a b true = a
  pair' a b false = b

  fst' : A ×' B → A
  fst' x = x true

  snd' : A ×' B → B
  snd' x = x false

  private
    uppt'-aux : (x : A ×' B) (b : Bool) → pair' (fst' x) (snd' x) b == x b
    uppt'-aux x true = idp
    uppt'-aux x false = idp

  uppt' : (x : A ×' B) → pair' (fst' x) (snd' x) == x
  uppt' = λ= ∘ uppt'-aux

  uppt'-pair' : (a : A) (b : B) → uppt' (pair' a b) == idp
  uppt'-pair' a b = uppt' (pair' a b) =⟨ λ= uppt'-aux-pair |in-ctx λ= ⟩
                    λ= (λ x → idp) =⟨ ! (λ=-η idp) ⟩
                    idp ∎
                    where
    uppt'-aux-pair : (x : Bool) → uppt'-aux (pair' a b) x == idp
    uppt'-aux-pair true = idp
    uppt'-aux-pair false = idp

  module _ {j} (C : A ×' B → Type j) (f : (a : A) → (b : B) → C (pair' a b)) where 
    ind×' : (x : A ×' B) → C x
    ind×' x = transport C (uppt' x) (f (fst' x) (snd' x))

    ind×'-correct : (a : A) (b : B) → ind×' (pair' a b) == f a b
    ind×'-correct a b = ind×' x =⟨ idp ⟩
                        transport C (uppt' x) (f a b) =⟨ uppt'-pair' a b |in-ctx (λ x₁ → transport C x₁ (f a b)) ⟩
                        transport C idp (f a b) =⟨ idp ⟩
                        f a b ∎
                        where
                          x = pair' a b

-- Theorem 2.1.6

-- a somewhat more book-oriented version of [conc^2-comm]
eckmann-hilton : ∀ {i} {X : Ptd i} (α β : Ω^ 2 X) → α ∙ β == β ∙ α
eckmann-hilton α β = α ∙ β   =⟨ ! (∙-unit-r α) ∙ᵣ β ⟩
                     α ⋆2 β  =⟨ ⋆2=⋆'2 α β ⟩
                     α ⋆'2 β =⟨ β ∙ₗ (∙-unit-r α) ⟩
                     β ∙ α   ∎

-- Corollary 2.4.4

_∼_ : ∀ {i j} {A : Type i} {P : A → Type j} (f g : (x : A) → P x) → Type (lmax i j)
_∼_ {A = A} f g = (x : A) → f x == g x

module _ {i j} {A : Type i} {B : Type j} where
  ∼-refl : (f : A → B) → f ∼ f
  ∼-refl f x = idp

  ∼-symm : (f g : A → B) → f ∼ g → g ∼ f
  ∼-symm f g H x = ! (H x)

  ∼-trans : {f g h : A → B} → f ∼ g → g ∼ h → f ∼ h
  ∼-trans H H' x = H x ∙ H' x

  ∼-ap-comm : {f g : A → B} (H : f ∼ g) {x y : A} (p : x == y) → H x ∙ ap g p == ap f p ∙ H y
  ∼-ap-comm H {x = x} idp = ∙-unit-r (H x)

r-complete-! : ∀ {i} {A : Type i} {x y z : A} (p : x == y) (q : y == z) → (p ∙ q) ∙ ! q == p
r-complete-! p q = ∙-assoc p q (! q) ∙ p ∙ₗ !-inv-r q ∙ ∙-unit-r p

∼-comm : ∀ {i} {A : Type i} (f : A → A) (H : f ∼ idf A) (x : A) → H (f x) == ap f (H x)
∼-comm {A = A} f H x = H (f x)                     =⟨ ! (r-complete-! (H (f x)) (H x)) ⟩
                      (H (f x) ∙ H x) ∙ ! (H x)    =⟨ α ∙ᵣ ! (H x) ⟩
                      (ap f (H x) ∙ H x) ∙ ! (H x) =⟨ r-complete-! (ap f (H x)) (H x) ⟩
                      ap f (H x) ∎
                      where
                        α : H (f x) ∙ H x == ap f (H x) ∙ H x
                        α = H (f x) ∙ H x              =⟨ H (f x) ∙ₗ ! (ap-idf (H x)) ⟩
                            H (f x) ∙ ap (idf A) (H x) =⟨ ∼-ap-comm H (H x) ⟩
                            ap f (H x) ∙ H x ∎

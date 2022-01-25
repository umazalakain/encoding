open import Relation.Binary.PropositionalEquality using (_≡_; refl; trans)
open import Function using (_∘_; _$_)
open import Data.Unit using (⊤; tt)
open import Data.List.Base using (List; []; _∷_)
open import Data.Nat.Base using (ℕ; zero; suc)
open import Data.Product using (Σ; Σ-syntax; _×_; _,_; proj₁; proj₂)

module LinearPi where


data Usage : Set₁ where
  0∙ 1∙ ω∙ : Usage

mutual
  data Type : Set₁ where
    pure : Set → Type
    prod : (T : Type) → (⟦ T ⟧ₜ → Type) → Type
    chan : Usage → Usage → Type → Type

  ⟦_⟧ₜ : Type → Set
  ⟦ pure V ⟧ₜ = V
  ⟦ prod A B ⟧ₜ = Σ ⟦ A ⟧ₜ (⟦_⟧ₜ ∘ B)
  ⟦ chan _ _ _ ⟧ₜ = ⊤


TypedValue : Set₁
TypedValue = Σ Type ⟦_⟧ₜ


Ctx : Set₁
Ctx = List TypedValue



data Univ : Set where
  usage type ctx : Univ

⟦_⟧ᵤ : Univ → Set₁
⟦ usage ⟧ᵤ = Usage
⟦ type ⟧ᵤ = TypedValue
⟦ ctx ⟧ᵤ = Ctx


infixr 5 _∷_

data _≔_+_ : ∀ {u} → ⟦ u ⟧ᵤ → ⟦ u ⟧ᵤ → ⟦ u ⟧ᵤ → Set where
  -- linear
  0∙ : 0∙ ≔ 0∙ + 0∙
  1∙-left : 1∙ ≔ 1∙ + 0∙
  1∙-right : 1∙ ≔ 0∙ + 1∙
  prod-left : ∀ {A B a b} → (prod A B , (a , b)) ≔ (prod A B , (a , b)) + (pure ⊤ , tt)
  prod-right : ∀ {A B a b} → (prod A B , (a , b)) ≔ (pure ⊤ , tt) + (prod A B , (a , b))

  -- shared
  ω∙ : ω∙ ≔ ω∙ + ω∙
  pure : ∀ {A a} → (pure A , a) ≔ (pure A , a) + (pure A , a)
  [] : _≔_+_ {ctx} [] [] []

  -- recursive
  chan : ∀ {ix iy iz ox oy oz T}
       → ix ≔ iy + iz
       → ox ≔ oy + oz
       → (chan ix ox T , tt) ≔ (chan iy oy T , tt) + (chan iz oz T , tt)
  _∷_ : ∀ {a b c as bs cs}
      → _≔_+_ {type} a b c
      → _≔_+_ {ctx} as bs cs
      → _≔_+_ {ctx} (a ∷ as) (b ∷ bs) (c ∷ cs)


data _⊆_ : ∀ {u} → ⟦ u ⟧ᵤ → ⟦ u ⟧ᵤ → Set₁ where
  -- linear
  0∙ : _⊆_ {usage} 0∙ 0∙
  1∙ : _⊆_ {usage} 1∙ 1∙
  prod : ∀ {A a B b} → (prod A B , (a , b)) ⊆ (prod A B , (a , b))

  --shared
  ω∙ : ∀ {m} → _⊆_ {usage} m ω∙
  pure : ∀ {A a} → (pure A , a) ⊆ (pure A , a)
  [] : _⊆_ {ctx} [] []

  -- recursive
  chan : ∀ {il ol ir or : Usage} {s t}
       → il ⊆ ir
       → ol ⊆ or
       → s ≡ t
       → (chan il ol s , tt) ⊆ (chan ir or t , tt)
  _∷_ : ∀ {l r ls rs}
      → _⊆_ {type} l r
      → _⊆_ {ctx} ls rs
      → _⊆_ {ctx} (l ∷ ls) (r ∷ rs)


data Null : ∀ {u} → ⟦ u ⟧ᵤ → Set₁ where
  0∙ : Null {u = usage} 0∙
  ω∙ : Null {u = usage} ω∙
  pure : ∀ {A a} → Null (pure A , a)
  chan : ∀ {i o : Usage} {t : Type}
       → Null i
       → Null o
       → Null (chan i o t , tt)
  prod : ∀ {A B a b}
       → Null (A , a)
       → Null (B a , b)
       → Null (prod A B , (a , b))
  [] : Null {u = ctx} []
  _∷_ : ∀ {x xs}
      → Null {u = type} x
      → Null {u = ctx} xs
      → Null {u = ctx} (x ∷ xs)


data _∋_ : Ctx → TypedValue → Set₁ where
  here : ∀ {x x' xs}
       → Null xs
       → x ⊆ x'
       → (x' ∷ xs) ∋ x
  there : ∀ {x x' xs}
        → Null x'
        → xs ∋ x
        → (x' ∷ xs) ∋ x


data Term : Ctx → TypedValue → Set₁ where
  var : ∀ {xs x} → xs ∋ x → Term xs x
  pure : ∀ {xs A} a → Null xs → Term xs (pure A , a)
  pair : ∀ {xs ys zs X Y x y}
       → xs ≔ ys + zs
       → Term ys (X , x)
       → Term zs (Y x , y)
       → Term xs (prod X Y , (x , y))


data Process : Ctx → Set₁ where
  end : ∀ {xs}
      → Null xs → Process xs
  par : ∀ {xs ys zs}
      → xs ≔ ys + zs
      → Process ys
      → Process zs
      → Process xs
  new : ∀ {xs} i o t
      → Process ((chan i o t , tt) ∷ xs)
      → Process xs
  rep : ∀ {xs}
      → Null xs
      → Process xs
      → Process xs
  send : ∀ {xs ys zs vs ws T t}
       → xs ≔ ys + zs
       → Term ys (T , t)
       → zs ≔ vs + ws
       → Term vs (chan 0∙ 1∙ T , tt)
       → Process ws
       → Process xs
  recv : ∀ {xs ys zs T}
       → xs ≔ ys + zs
       → Term ys (chan 1∙ 0∙ T , tt)
       → (∀ (t : ⟦ T ⟧ₜ ) → Process ((T , t) ∷ zs))
       → Process xs
  letprod : ∀ {xs ys zs A B a b}
          → xs ≔ ys + zs
          → Term ys (prod A B , (a , b))
          → Process ((A , a) ∷ (B a , b) ∷ zs)
          → Process xs


data _[_↦_]≔_ {a} {A : Set a} : List A → ℕ → A → List A → Set where
  here : ∀ {x xs t} → (x ∷ xs) [ zero ↦ t ]≔ (t ∷ xs)
  there : ∀ {xs i t ys x}
        → xs [ i ↦ t ]≔ ys
        → (x ∷ xs) [ suc i ↦ t ]≔ (x ∷ ys)

repl : Type → ℕ → Type
repl A zero = pure ⊤
repl A (suc n) = chan 1∙ 0∙ (prod A λ _ → repl A n)

+-comm : ∀ {u} {x y z : ⟦ u ⟧ᵤ} → x ≔ y + z → x ≔ z + y
+-comm {usage} 0∙ = 0∙
+-comm {usage} 1∙-left = 1∙-right
+-comm {usage} 1∙-right = 1∙-left
+-comm {usage} ω∙ = ω∙
+-comm {type} prod-left = prod-right
+-comm {type} prod-right = prod-left
+-comm {type} pure = pure
+-comm {type} (chan sp sp₁) = chan (+-comm sp) (+-comm sp₁)
+-comm {ctx} [] = []
+-comm {ctx} (sp ∷ sp₁) = +-comm sp ∷ +-comm sp₁

+-idˡ : ∀ {u} (x : ⟦ u ⟧ᵤ) → Σ[ n ∈ ⟦ u ⟧ᵤ ] x ≔ n + x × Null n
+-idˡ {usage} 0∙ = 0∙ , 0∙ , 0∙
+-idˡ {usage} 1∙ = 0∙ , 1∙-right , 0∙
+-idˡ {usage} ω∙ = ω∙ , ω∙ , ω∙
+-idˡ {type} (prod A B , (a , b)) = (pure ⊤ , tt) , prod-right , pure
+-idˡ {type} (pure A , a) = (pure A , a) , pure , pure
+-idˡ {type} (chan i o t , tt)
  with x , spx , nx ← +-idˡ i
  with y , spy , ny ← +-idˡ o
  = (chan x y t , tt) , chan spx spy , chan nx ny
+-idˡ {ctx} [] = [] , [] , []
+-idˡ {ctx} (x ∷ xs)
  with ix , spx , nx ← +-idˡ x
  with ixs , spxs , nxs ← +-idˡ xs
  = ix ∷ ixs , spx ∷ spxs , nx ∷ nxs

+-idʳ : ∀ {u} (x : ⟦ u ⟧ᵤ) → Σ[ n ∈ ⟦ u ⟧ᵤ ] x ≔ x + n × Null n
+-idʳ x = let a , b , c = +-idˡ x in a , +-comm b , c

⊆-refl : ∀ {u} (x : ⟦ u ⟧ᵤ) → x ⊆ x
⊆-refl {usage} 0∙ = 0∙
⊆-refl {usage} 1∙ = 1∙
⊆-refl {usage} ω∙ = ω∙
⊆-refl {type} (pure x , w) = pure
⊆-refl {type} (prod x y , w) = prod
⊆-refl {type} (chan i o t , w) = chan (⊆-refl i) (⊆-refl o) refl
⊆-refl {ctx} [] = []
⊆-refl {ctx} (x ∷ xs) = ⊆-refl x ∷ ⊆-refl xs

⊆-trans : ∀ {u} {x y z : ⟦ u ⟧ᵤ} → x ⊆ y → y ⊆ z → x ⊆ z
⊆-trans 0∙ b = b
⊆-trans 1∙ b = b
⊆-trans prod b = b
⊆-trans ω∙ ω∙ = ω∙
⊆-trans pure b = b
⊆-trans [] b = b
⊆-trans (chan ia oa eq) (chan ib ob qe) = chan (⊆-trans ia ib) (⊆-trans oa ob) (trans eq qe)
⊆-trans (a ∷ as) (b ∷ bs) = ⊆-trans a b ∷ ⊆-trans as bs

⊆-repl : ∀ {A} n {t} → (repl A n , t) ⊆ (repl A n , t)
⊆-repl zero = pure
⊆-repl (suc n) = chan 1∙ 0∙ refl

Null-+ : ∀ {u} {xs ys zs : ⟦ u ⟧ᵤ} → xs ≔ ys + zs → Null ys → Null zs → Null xs
Null-+ 0∙ nys nzs = nzs
Null-+ prod-left nys nzs = nys
Null-+ prod-right nys nzs = nzs
Null-+ ω∙ nys nzs = nzs
Null-+ pure nys nzs = nzs
Null-+ [] nys nzs = nzs
Null-+ (chan sp sp₁) (chan nys nys₁) (chan nzs nzs₁) = chan (Null-+ sp nys nzs) (Null-+ sp₁ nys₁ nzs₁)
Null-+ (sp ∷ sp₁) (nys ∷ nys₁) (nzs ∷ nzs₁) = Null-+ sp nys nzs ∷ Null-+ sp₁ nys₁ nzs₁

Null-⊆ : ∀ {u} {x y : ⟦ u ⟧ᵤ} → Null x → x ⊆ y → Null y
Null-⊆ {usage} n 0∙ = n
Null-⊆ {usage} n ω∙ = ω∙
Null-⊆ {type} n prod = n
Null-⊆ {type} n pure = n
Null-⊆ {type} (chan n n₁) (chan sub sub₁ eq) = chan (Null-⊆ n sub) (Null-⊆ n₁ sub₁)
Null-⊆ {ctx} n [] = n
Null-⊆ {ctx} (n ∷ n₁) (sub ∷ sub₁) = Null-⊆ n sub ∷ Null-⊆ n₁ sub₁

Null-∋ : ∀ {t xs} → Null t → xs ∋ t → Null xs
Null-∋ n (here n' x) = Null-⊆ n x ∷ n'
Null-∋ n (there n' x) = n' ∷ Null-∋ n x

Null-Term : ∀ {t xs} → Null t → Term xs t → Null xs
Null-Term n (var x) = Null-∋ n x
Null-Term n (pure _ x) = x
Null-Term (prod n n₁) (pair x t t₁) = Null-+ x (Null-Term n t) (Null-Term n₁ t₁)

replrecv : ∀ {xs ys zs} → xs ≔ zs + ys → Null ys → (n : ℕ) → (t : ⟦ repl (pure ⊤) n ⟧ₜ) → Term zs (prod (pure ℕ) (repl (pure ⊤)) , (n , t)) → Process xs
replrecv sp null zero t term = end (Null-+ (+-comm sp) null (Null-Term (prod pure pure) term))
replrecv {_} {ys} sp null (suc n) t term =
  let (i , sp' , ni) = +-idˡ ys in
  let (i' , spi , nii) = +-idˡ i in
  letprod sp term
  (recv (pure ∷ chan 1∙-left 0∙ ∷ sp') (var (there pure (here ni (chan 1∙ 0∙ refl)))) λ where
    (tt , t') →
      let (_ , sp'' , ni') = +-idʳ (repl (pure ⊤) n , t') in
      let (_ , sp''' , ni'') = +-idˡ (repl (pure ⊤) n , t') in
      letprod (prod-left ∷ pure ∷ chan 0∙ 0∙ ∷ sp') (var (here (pure ∷ chan 0∙ 0∙ ∷ ni) prod))
      (replrecv (pure ∷ sp'' ∷ pure ∷ pure ∷ chan 0∙ 0∙ ∷ sp') (pure ∷ ni'' ∷ pure ∷ pure ∷ chan 0∙ 0∙ ∷ null) n t' (pair (pure ∷ sp''' ∷ pure ∷ pure ∷ chan 0∙ 0∙ ∷ spi) (pure n (pure ∷ ni'' ∷ pure ∷ pure ∷ chan 0∙ 0∙ ∷ nii)) (var (there pure (here (pure ∷ pure ∷ chan 0∙ 0∙ ∷ ni) (⊆-repl _)))))))

_ : Process ((chan 1∙ 1∙ (prod (pure ℕ) (repl (pure ⊤))) , tt) ∷ [])
_ = par (chan 1∙-left 1∙-right ∷ [])
  (recv
    (chan 1∙-left 0∙ ∷ [])
    (var (here [] (chan 1∙ 0∙ refl)))
    λ (n , c) → replrecv
      (prod-left ∷ chan 0∙ 0∙ ∷ [])
      (pure ∷ (chan 0∙ 0∙ ∷ []))
      n
      c
      (var (here (chan 0∙ 0∙ ∷ []) prod)))
  (new 1∙ 1∙ (prod (pure ⊤) (λ _ → pure ⊤)) $
    send
      (chan 1∙-left 1∙-right ∷ chan 0∙ 1∙-right ∷ [])
      (pair (chan 1∙-right 0∙ ∷ chan 0∙ 0∙ ∷ []) (pure 1 (chan 0∙ 0∙ ∷ (chan 0∙ 0∙ ∷ []))) (var (here (chan 0∙ 0∙ ∷ []) (chan 1∙ 0∙ refl))))
      (chan 0∙ 1∙-right ∷ (chan 0∙ 1∙-left ∷ []))
      (var (there (chan 0∙ 0∙ ) (here [] (chan 0∙ 1∙ refl)))) $
      send
        (chan 0∙ 1∙-right ∷ chan 0∙ 0∙ ∷ [])
        (pair (chan 0∙ 0∙ ∷ (chan 0∙ 0∙ ∷ [])) (pure tt (chan 0∙ 0∙ ∷ (chan 0∙ 0∙ ∷ []))) (pure tt (chan 0∙ 0∙ ∷ (chan 0∙ 0∙ ∷ []))))
        (chan 0∙ 1∙-left ∷ (chan 0∙ 0∙ ∷ []))
        (var (here (chan 0∙ 0∙ ∷ []) (chan 0∙ 1∙ refl)))
        (end (chan 0∙ 0∙ ∷ (chan 0∙ 0∙ ∷ []))))


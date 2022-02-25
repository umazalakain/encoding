{-# OPTIONS --allow-unsolved-metas #-}
open import Relation.Binary.PropositionalEquality using (_≡_; refl; trans; cong; cong₂)
open import Function using (_∘_; _$_)
open import Data.Unit using (⊤; tt)
open import Data.List.Base using (List; []; _∷_)
open import Data.Nat.Base using (ℕ; zero; suc)
open import Data.Product as Product using (Σ; Σ-syntax; _×_; _,_; proj₁; proj₂)

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

+-cancel : ∀ {u} {a b c : ⟦ u ⟧ᵤ} → a ≔ b + c → Null c → a ≡ b
+-cancel 0∙ null = refl
+-cancel 1∙-left null = refl
+-cancel prod-left null = refl
+-cancel ω∙ null = refl
+-cancel pure null = refl
+-cancel [] null = refl
+-cancel (chan i o) (chan inull onull) rewrite +-cancel i inull | +-cancel o onull = refl
+-cancel (spl ∷ spls) (null ∷ nulls) = cong₂ _∷_ (+-cancel spl null) (+-cancel spls nulls)

null-unrestr : ∀ {u} {xs : ⟦ u ⟧ᵤ} → Null xs → xs ≔ xs + xs
null-unrestr {xs = xs} null
  with _ , fill , fillnull ← +-idˡ xs
  with refl ← +-cancel fill null
  = fill

Null-⊆ : ∀ {u} {x y : ⟦ u ⟧ᵤ} → Null x → x ⊆ y → Null y
Null-⊆ {usage} n 0∙ = n
Null-⊆ {usage} n ω∙ = ω∙
Null-⊆ {type} n prod = n
Null-⊆ {type} n pure = n
Null-⊆ {type} (chan n n₁) (chan sub sub₁ eq) = chan (Null-⊆ n sub) (Null-⊆ n₁ sub₁)
Null-⊆ {ctx} n [] = n
Null-⊆ {ctx} (n ∷ n₁) (sub ∷ sub₁) = Null-⊆ n sub ∷ Null-⊆ n₁ sub₁

Null-0∙⊆ : {x : Usage} → Null x → 0∙ ⊆ x
Null-0∙⊆ 0∙ = 0∙
Null-0∙⊆ ω∙ = ω∙

Null-∋ : ∀ {t xs} → Null t → xs ∋ t → Null xs
Null-∋ n (here n' x) = Null-⊆ n x ∷ n'
Null-∋ n (there n' x) = n' ∷ Null-∋ n x

Null-Term : ∀ {t xs} → Null t → Term xs t → Null xs
Null-Term n (var x) = Null-∋ n x
Null-Term n (pure _ x) = x

data InsertAt : ℕ → TypedValue → Ctx → Ctx → Set₁ where
  here : ∀ {x xs} → InsertAt zero x xs (x ∷ xs)
  there : ∀ {n x xs ys x'} → InsertAt n x xs ys → InsertAt (suc n) x (x' ∷ xs) (x' ∷ ys)


null-insert : ∀ {n x xs ys} → InsertAt n x xs ys → Null x → Null xs → Null ys
null-insert here nx nxs = nx ∷ nxs
null-insert (there ins) nx (nx' ∷ nxs) = nx' ∷ null-insert ins nx nxs

insert-null : ∀ {n t xs ys} → InsertAt n t xs ys → Null ys → Null t × Null xs
insert-null here (t-null ∷ xs-null) = t-null , xs-null
insert-null (there ins) (x-null ∷ xs-null) = Product.map₂ (x-null ∷_) (insert-null ins xs-null)

extract : ∀ {n t zs ms ls rs} → InsertAt n t zs ms → ms ≔ ls + rs → Σ[ (x , y , xs , ys) ∈ (TypedValue × TypedValue × Ctx × Ctx) ] t ≔ x + y × zs ≔ xs + ys × InsertAt n x xs ls × InsertAt n y ys rs
extract here (spl ∷ spls) = _ , spl , spls , here , here
extract (there ins) (spl ∷ spls) =
  let _ , spl' , spls' , insl , insr = extract ins spls in
  _ , spl' , spl ∷ spls' , there insl , there insr

imtract : ∀ {xs ys zs x y z n ms} → xs ≔ ys + zs → x ≔ y + z → InsertAt n x xs ms → Σ[ (ls , rs) ∈ Ctx × Ctx ] ms ≔ ls + rs × InsertAt n y ys ls × InsertAt n z zs rs
imtract spl spl1 here = _ , spl1 ∷ spl , here , here
imtract (spl ∷ spls) spl1 (there ins) =
  let _ , spl2 , insl , insr = imtract spls spl1 ins in
  _ , spl ∷ spl2 , there insl , there insr

Var-null-insert : ∀ {x n xs ys t} → Null x → InsertAt n x xs ys → xs ∋ t → ys ∋ t
Var-null-insert null here vr = there null vr
Var-null-insert null (there ins) (here null' sub) = here (null-insert ins null null') sub
Var-null-insert null (there ins) (there null' vr) = there null' (Var-null-insert null ins vr)

Term-null-insert : ∀ {x n xs ys t} → Null x → InsertAt n x xs ys → Term xs t → Term ys t
Term-null-insert null ins (var x) = var (Var-null-insert null ins x)
Term-null-insert null ins (pure a x) = pure a (null-insert ins null x)
Term-null-insert {x} null ins (pair spl l r)
  with _ , fill , fillnull ← +-idˡ x
  with _ , spl1 , insl , insr ← imtract spl fill ins
  = pair spl1 (Term-null-insert fillnull insl l) (Term-null-insert null insr r)

Process-null-insert : ∀ {x n xs ys} → Null x → InsertAt n x xs ys → Process xs → Process ys
Process-null-insert null ins (end x) = end (null-insert ins null x)
Process-null-insert {x} null ins (par spl p q)
  with _ , fill , fillnull ← +-idˡ x
  with _ , spl1 , insl , insr ← imtract spl fill ins
  = par spl1 (Process-null-insert fillnull insl p) (Process-null-insert null insr q)
Process-null-insert null ins (new i o t proc) = new i o t (Process-null-insert null (there ins) proc)
Process-null-insert null ins (rep x proc) = rep (null-insert ins null x) (Process-null-insert null ins proc)
Process-null-insert {x} null ins (send spl-payload payload spl-channel channel proc)
  with _ , fill , fillnull ← +-idˡ x
  with _ , spl1 , insl , insr ← imtract spl-payload fill ins
  with _ , spl2 , insrl , insrr ← imtract spl-channel fill insr
  = send
    spl1 (Term-null-insert fillnull insl payload)
    spl2 (Term-null-insert fillnull insrl channel)
    (Process-null-insert null insrr proc)
Process-null-insert {x} null ins (recv spl-channel channel cont)
  with _ , fill , fillnull ← +-idˡ x
  with _ , spl1 , insl , insr ← imtract spl-channel fill ins
  = recv spl1 (Term-null-insert fillnull insl channel) (Process-null-insert null (there insr) ∘ cont)
Process-null-insert {x} null ins (letprod spl-prd prd proc)
  with _ , fill , fillnull ← +-idˡ x
  with _ , spl1 , insl , insr ← imtract spl-prd fill ins
  = letprod spl1 (Term-null-insert fillnull insl prd) (Process-null-insert null (there (there insr)) proc)


Term-lift : ∀ {x xs t} → Null x → Term xs t → Term (x ∷ xs) t
Term-lift null = Term-null-insert null here

Process-lift : ∀ {x xs} → Null x → Process xs → Process (x ∷ xs)
Process-lift null = Process-null-insert null here


⊆-var : ∀ {s t xs} → s ⊆ t → xs ∋ t → xs ∋ s
⊆-var sub (here x x₁) = here x (⊆-trans sub x₁)
⊆-var sub (there x vr) = there x (⊆-var sub vr)

⊆-term : ∀ {s t xs} → s ⊆ t → Term xs t → Term xs s
⊆-term sub (var x) = var (⊆-var sub x)
⊆-term pure (pure a x) = pure a x
⊆-term prod (pair spl l r) = pair spl (⊆-term (⊆-refl _) l) (⊆-term (⊆-refl _) r)

reorient : ∀ {u} {xs ys zs as bs ps qs : ⟦ u ⟧ᵤ} → xs ≔ ys + zs → ys ≔ ps + qs → zs ≔ as + bs → Σ[ (ys' , zs') ∈ ⟦ u ⟧ᵤ × ⟦ u ⟧ᵤ ] xs ≔ ys' + zs' × ys' ≔ ps + as × zs' ≔ qs + bs
reorient {usage} 0∙ 0∙ 0∙ = _ , 0∙ , 0∙ , 0∙
reorient {usage} 1∙-left 1∙-left 0∙ = _ , 1∙-left , 1∙-left , 0∙
reorient {usage} 1∙-left 1∙-right 0∙ = _ , 1∙-right , 0∙ , 1∙-left
reorient {usage} 1∙-right 0∙ 1∙-left = _ , 1∙-left , 1∙-right , 0∙
reorient {usage} 1∙-right 0∙ 1∙-right = _ , 1∙-right , 0∙ , 1∙-right
reorient {usage} ω∙ ω∙ ω∙ = _ , ω∙ , ω∙ , ω∙
reorient {type} prod-left prod-left pure = _ , prod-left , prod-left , pure
reorient {type} prod-left prod-right pure = _ , prod-right , pure , prod-left
reorient {type} prod-right pure prod-left = _ , prod-left , prod-right , pure
reorient {type} prod-right pure prod-right = _ , prod-right , pure , prod-right
reorient {type} pure pure pure = _ , pure , pure , pure
reorient {type} (chan imid omid) (chan ileft oleft) (chan iright oright)
  with _ , imid' , ileft' , iright' ← reorient imid ileft iright
  with _ , omid' , oleft' , oright' ← reorient omid oleft oright
  = _ , chan imid' omid' , chan ileft' oleft' , chan iright' oright'
reorient {ctx} [] [] [] = _ , [] , [] , []
reorient {ctx} (x ∷ mid) (y ∷ left) (z ∷ right)
  with _ , x' , y' , z' ← reorient x y z
  with _ , mid' , left' , right' ← reorient mid left right
  = _ , x' ∷ mid' , y' ∷ left' , z' ∷ right'

subst-var : ∀ {xs ys zs t n ws s}
           → xs ≔ ys + zs
           → Term ys t
           → InsertAt n t zs ws
           → ws ∋ s
           → xs ∋ s
-- FIXME: index ∋ by natural number, disallow the index being eliminated (n) being the index of ws ∋ s
subst-var spl term here (here null sub) = {!h!} -- rewrite +-cancel spl null = {!here!}
subst-var (spl ∷ spls) term (there ins) (here null sub) = {!here!}
subst-var spl term ins (there x ni) = {!!}

subst-term : ∀ {xs ys zs t n ws s}
           → xs ≔ ys + zs
           → Term ys t
           → InsertAt n t zs ws
           → Term ws s
           → Term xs s
subst-term spl term ins (var x) = var (subst-var spl term ins x)
subst-term spl term ins (pure a x) = {!!}
subst-term spl term ins (pair spl' l r) = pair {!!} (subst-term {!!} {!!} {!!} {!!}) (subst-term {!!} {!!} {!!} {!!})

⊆-split : ∀ {u} {x y z x' : ⟦ u ⟧ᵤ} → x ≔ y + z → x ⊆ x' → Σ[ (y' , z') ∈ ⟦ u ⟧ᵤ × ⟦ u ⟧ᵤ ] x' ≔ y' + z' × y ⊆ y' × z ⊆ z'
⊆-split {x' = x'} 0∙ sub = let _ , fill , fillnull = +-idʳ x' in _ , fill , sub , Null-0∙⊆ fillnull
⊆-split {x' = x'} 1∙-left sub = let _ , fill , fillnull = +-idʳ x' in _ , fill , sub , Null-0∙⊆ fillnull
⊆-split {x' = x'} 1∙-right sub = let _ , fill , fillnull = +-idˡ x' in _ , fill , Null-0∙⊆ fillnull , sub
⊆-split prod-left prod = _ , prod-left , ⊆-refl _ , ⊆-refl _
⊆-split prod-right prod = _ , prod-right , ⊆-refl _ , ⊆-refl _
⊆-split ω∙ ω∙ = _ , ω∙ , ω∙ , ω∙
⊆-split pure pure = _ , pure , pure , pure
⊆-split [] [] = _ , [] , [] , []
⊆-split (chan i o) (chan isub osub eq) =
  let _ , ispl , isubl , isubr = ⊆-split i isub in
  let _ , ospl , osubl , osubr = ⊆-split o osub in
  _ , chan ispl ospl , chan isubl osubl eq , chan isubr osubr eq
⊆-split (spl ∷ spls) (sub ∷ subs) =
  let _ , spl' , subl' , subr' = ⊆-split spl sub in
  let _ , spls' , subls' , subrs' = ⊆-split spls subs in
  _ , spl' ∷ spls' , subl' ∷ subls' , subr' ∷ subrs'

var-split : ∀ {xs x y z} → xs ∋ x → x ≔ y + z → Σ[ (ys , zs) ∈ Ctx × Ctx ] xs ≔ ys + zs × ys ∋ y × zs ∋ z
var-split {_ ∷ xs} (here null lt) spl
  with _ , fill , fillnull ← +-idʳ xs
  with _ , spl1 , subl , subr ← ⊆-split spl lt
  = _ , spl1 ∷ fill , here null subl , here fillnull subr
var-split {xs = x ∷ _} (there n vr) spl
  with _ , fill , fillnull ← +-idʳ x
  with _ , spl' , inl , inr ← var-split vr spl
  = _ , fill ∷ spl' , there n inl , there fillnull inr

term-split : ∀ {xs x y z} → Term xs x → x ≔ y + z → Σ[ (ys , zs) ∈ Ctx × Ctx ] xs ≔ ys + zs × Term ys y × Term zs z
term-split (var x) spl
  with _ , spl1 , lvr , rvr ← var-split x spl
  = _ , spl1 , var lvr , var rvr
term-split {xs} (pure a x) pure
  with _ , fill , fillnull ← +-idʳ xs
  = _ , null-unrestr x , pure a x , pure a x
term-split {xs} (pair spl1 lterm rterm) prod-left
  with _ , fill , fillnull ← +-idʳ xs
  = _ , fill , pair spl1 lterm rterm , pure tt fillnull
term-split {xs} (pair spl1 lterm rterm) prod-right
  with _ , fill , fillnull ← +-idˡ xs
  = _ , fill , pure tt fillnull , pair spl1 lterm rterm

subst-proc : ∀ {xs ys zs t n ws}
           → xs ≔ ys + zs
           → Term ys t
           → InsertAt n t zs ws
           → Process ws
           → Process xs
subst-proc spl term ins (end ws-null)
  with t-null , zs-null ← insert-null ins ws-null
  rewrite +-cancel spl zs-null
  = end (Null-Term t-null term)
subst-proc spl term ins (par spl1 p q)
  with (a , b , as , bs) , tspl , cspl , insl , insr ← extract ins spl1
  with _ , spl2 , lterm , rterm ← term-split term tspl
  with _ , spl' , lspl' , rspl' ← reorient spl spl2 cspl
  = par spl' (subst-proc lspl' lterm insl p) (subst-proc rspl' rterm insr q)
subst-proc spl term ins (new i o t p)
  with _ , ispl , inull ← +-idˡ i
  with _ , ospl , onull ← +-idˡ o
  = new i o t (subst-proc (chan ispl ospl ∷ spl) (Term-lift (chan inull onull) term) (there ins) p)
subst-proc spl term ins (rep ws-null p)
  with t-null , zs-null ← insert-null ins ws-null
  with refl ← +-cancel spl zs-null
  = rep (Null-Term t-null term) (subst-proc spl term ins p)
subst-proc spl term ins (send {ms} {ls} {rs} spl-payload payload spl-channel channel p)
  with (a , b , as , bs) , tspl , cspl , insl , insr ← extract ins spl-payload
  with (q , k , qs , ks) , foo , bar , asd , das ← extract {!!} {!!}
  with _ , spl2 , lterm , rterm ← term-split term tspl
  = send
  {!!}
  (subst-term {!!} {!!} insl payload)
  {!!}
  (subst-term {!!} {!!} {!!} channel)
  (subst-proc {!!} {!!} {!!} p)
subst-proc spl term ins (recv {ms} {ls} {rs} {T} spl-channel channel cont)
  with (a , b , as , bs) , tspl , cspl , insl , insr ← extract ins spl-channel
  with _ , spl2 , lterm , rterm ← term-split term tspl
  with _ , spl' , lspl' , rspl' ← reorient spl spl2 cspl
  = recv spl' (subst-term lspl' lterm insl channel) λ t →
    let _ , tright , tfill = +-idˡ (T , t)
    in subst-proc (tright ∷ rspl') (Term-lift tfill rterm) (there insr) (cont t)
subst-proc spl term ins (letprod spl-prod prd p)
  = letprod
  {!!}
  (subst-term {!!} {!!} {!!} {!!})
  (subst-proc ({!!} ∷ {!!} ∷ {!!}) {!!} {!!} {!!})

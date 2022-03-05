
open import Relation.Binary.PropositionalEquality using (_≡_; refl; trans; cong; cong₂)
open import Function using (_∘_; _$_)
open import Data.Unit using (⊤; tt)
open import Data.List.Base using (List; []; _∷_)
open import Data.Nat.Base using (ℕ; zero; suc)
open import Data.Product as Product using (Σ; Σ-syntax; _×_; _,_; proj₁; proj₂)

open import LinearPi.TypeSystem

module LinearPi.Weakening where


repl : Type → ℕ → Type
repl A zero = pure ⊤
repl A (suc n) = chan #1 #0 (prod A λ _ → repl A n)

+-comm : ∀ {u} {x y z : ⟦ u ⟧ᵤ} → x ≔ y + z → x ≔ z + y
+-comm {usage} #0 = #0
+-comm {usage} #1-left = #1-right
+-comm {usage} #1-right = #1-left
+-comm {usage} #ω = #ω
+-comm {type} prod-left = prod-right
+-comm {type} prod-right = prod-left
+-comm {type} pure = pure
+-comm {type} (chan sp sp₁) = chan (+-comm sp) (+-comm sp₁)
+-comm {ctx} [] = []
+-comm {ctx} (sp ∷ sp₁) = +-comm sp ∷ +-comm sp₁

+-idˡ : ∀ {u} (x : ⟦ u ⟧ᵤ) → Σ[ n ∈ ⟦ u ⟧ᵤ ] x ≔ n + x × Null n
+-idˡ {usage} #0 = #0 , #0 , #0
+-idˡ {usage} #1 = #0 , #1-right , #0
+-idˡ {usage} #ω = #ω , #ω , #ω
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
⊆-refl {usage} #0 = #0
⊆-refl {usage} #1 = #1
⊆-refl {usage} #ω = #ω
⊆-refl {type} (pure x , w) = pure
⊆-refl {type} (prod x y , w) = prod
⊆-refl {type} (chan i o t , w) = chan (⊆-refl i) (⊆-refl o) refl
⊆-refl {ctx} [] = []
⊆-refl {ctx} (x ∷ xs) = ⊆-refl x ∷ ⊆-refl xs

⊆-trans : ∀ {u} {x y z : ⟦ u ⟧ᵤ} → x ⊆ y → y ⊆ z → x ⊆ z
⊆-trans #0 b = b
⊆-trans #1 b = b
⊆-trans prod b = b
⊆-trans #ω #ω = #ω
⊆-trans pure b = b
⊆-trans [] b = b
⊆-trans (chan ia oa eq) (chan ib ob qe) = chan (⊆-trans ia ib) (⊆-trans oa ob) (trans eq qe)
⊆-trans (a ∷ as) (b ∷ bs) = ⊆-trans a b ∷ ⊆-trans as bs

⊆-repl : ∀ {A} n {t} → (repl A n , t) ⊆ (repl A n , t)
⊆-repl zero = pure
⊆-repl (suc n) = chan #1 #0 refl

+-cancel : ∀ {u} {a b c : ⟦ u ⟧ᵤ} → a ≔ b + c → Null c → a ≡ b
+-cancel #0 null = refl
+-cancel #1-left null = refl
+-cancel prod-left null = refl
+-cancel #ω null = refl
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
Null-⊆ {usage} n #0 = n
Null-⊆ {usage} n #ω = #ω
Null-⊆ {type} n prod = n
Null-⊆ {type} n pure = n
Null-⊆ {type} (chan n n₁) (chan sub sub₁ eq) = chan (Null-⊆ n sub) (Null-⊆ n₁ sub₁)
Null-⊆ {ctx} n [] = n
Null-⊆ {ctx} (n ∷ n₁) (sub ∷ sub₁) = Null-⊆ n sub ∷ Null-⊆ n₁ sub₁

Null-#0⊆ : {x : Usage} → Null x → #0 ⊆ x
Null-#0⊆ #0 = #0
Null-#0⊆ #ω = #ω

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

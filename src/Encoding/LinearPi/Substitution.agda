{-# OPTIONS --allow-unsolved-metas #-}

open import Relation.Binary.PropositionalEquality using (_≡_; refl; trans; cong; cong₂)
open import Function using (_∘_; _$_)
open import Data.Unit using (⊤; tt)
open import Data.List.Base using (List; []; _∷_)
open import Data.Nat.Base using (ℕ; zero; suc)
open import Data.Product as Product using (Σ; Σ-syntax; _×_; _,_; proj₁; proj₂)

open import LinearPi.TypeSystem
open import LinearPi.Weakening

module LinearPi.Substitution where




reorient : ∀ {u} {xs ys zs as bs ps qs : ⟦ u ⟧ᵤ} → xs ≔ ys + zs → ys ≔ ps + qs → zs ≔ as + bs → Σ[ (ys' , zs') ∈ ⟦ u ⟧ᵤ × ⟦ u ⟧ᵤ ] xs ≔ ys' + zs' × ys' ≔ ps + as × zs' ≔ qs + bs
reorient {chan} ℓ∅ ℓ∅ ℓ∅ = _ , ℓ∅ , ℓ∅ , ℓ∅
reorient {chan} # # # = _ , # , # , #
reorient {chan} ℓᵢ-left ℓᵢ-left ℓ∅ = _ , ℓᵢ-left , ℓᵢ-left , ℓ∅
reorient {chan} ℓᵢ-left ℓᵢ-right ℓ∅ = _ , ℓᵢ-right , ℓ∅ , ℓᵢ-left
reorient {chan} ℓᵢ-right ℓ∅ ℓᵢ-left = _ , ℓᵢ-left , ℓᵢ-right , ℓ∅
reorient {chan} ℓᵢ-right ℓ∅ ℓᵢ-right = _ , ℓᵢ-right , ℓ∅ , ℓᵢ-right
reorient {chan} ℓₒ-left ℓₒ-left ℓ∅ = _ , ℓₒ-left , ℓₒ-left , ℓ∅
reorient {chan} ℓₒ-left ℓₒ-right ℓ∅ = _ , ℓₒ-right , ℓ∅ , ℓₒ-left
reorient {chan} ℓₒ-right ℓ∅ ℓₒ-left = _ , ℓₒ-left , ℓₒ-right , ℓ∅
reorient {chan} ℓₒ-right ℓ∅ ℓₒ-right = _ , ℓₒ-right , ℓ∅ , ℓₒ-right
reorient {chan} ℓᵢₒ-left ℓᵢₒ-left ℓ∅ = _ , ℓᵢₒ-left , ℓᵢₒ-left , ℓ∅ 
reorient {chan} ℓᵢₒ-left ℓᵢₒ-right ℓ∅ = _ , ℓᵢₒ-right , ℓ∅ , ℓᵢₒ-left
reorient {chan} ℓᵢₒ-left ℓᵢₒ ℓ∅ = _ , ℓᵢₒ , ℓᵢ-left , ℓₒ-left
reorient {chan} ℓᵢₒ-left ℓₒᵢ ℓ∅ = _ , ℓₒᵢ , ℓₒ-left , ℓᵢ-left
reorient {chan} ℓᵢₒ-right ℓ∅ ℓᵢₒ-left = _ , ℓᵢₒ-left , ℓᵢₒ-right , ℓ∅
reorient {chan} ℓᵢₒ-right ℓ∅ ℓᵢₒ-right = _ , ℓᵢₒ-right , ℓ∅ , ℓᵢₒ-right
reorient {chan} ℓᵢₒ-right ℓ∅ ℓᵢₒ = _ , ℓᵢₒ , ℓᵢ-right , ℓₒ-right
reorient {chan} ℓᵢₒ-right ℓ∅ ℓₒᵢ = _ , ℓₒᵢ , ℓₒ-right , ℓᵢ-right
reorient {chan} ℓᵢₒ ℓᵢ-left ℓₒ-left = _ , ℓᵢₒ-left , ℓᵢₒ , ℓ∅
reorient {chan} ℓᵢₒ ℓᵢ-left ℓₒ-right = _ , ℓᵢₒ , ℓᵢ-left , ℓₒ-right
reorient {chan} ℓᵢₒ ℓᵢ-right ℓₒ-left = _ , ℓₒᵢ , ℓₒ-right , ℓᵢ-left
reorient {chan} ℓᵢₒ ℓᵢ-right ℓₒ-right = _ , ℓᵢₒ-right , ℓ∅ , ℓᵢₒ
reorient {chan} ℓₒᵢ ℓₒ-left ℓᵢ-left = _ , ℓᵢₒ-left , ℓₒᵢ , ℓ∅
reorient {chan} ℓₒᵢ ℓₒ-left ℓᵢ-right = _ , ℓₒᵢ , ℓₒ-left , ℓᵢ-right
reorient {chan} ℓₒᵢ ℓₒ-right ℓᵢ-left = _ , ℓᵢₒ , ℓᵢ-right , ℓₒ-left
reorient {chan} ℓₒᵢ ℓₒ-right ℓᵢ-right = _ , ℓᵢₒ-right , ℓ∅ , ℓₒᵢ
reorient {type} prod-left prod-left pure = _ , prod-left , prod-left , pure
reorient {type} prod-left prod-right pure = _ , prod-right , pure , prod-left
reorient {type} prod-right pure prod-left = _ , prod-left , prod-right , pure
reorient {type} prod-right pure prod-right = _ , prod-right , pure , prod-right
reorient {type} pure pure pure = _ , pure , pure , pure
reorient {type} (chan mid) (chan left) (chan right)
  with _ , mid' , left' , right' ← reorient mid left right
  = _ , chan mid' , chan left' , chan right'
reorient {ctx} [] [] [] = _ , [] , [] , []
reorient {ctx} (x ∷ mid) (y ∷ left) (z ∷ right)
  with _ , x' , y' , z' ← reorient x y z
  with _ , mid' , left' , right' ← reorient mid left right
  = _ , x' ∷ mid' , y' ∷ left' , z' ∷ right'


+-⊇ : ∀ {u} {xs' xs ys zs : ⟦ u ⟧ᵤ} → xs' ⊇ xs → xs ≔ ys + zs → Σ[ (ys' , zs') ∈ ⟦ u ⟧ᵤ × ⟦ u ⟧ᵤ ] xs' ≔ ys' + zs' × ys' ⊇ ys × zs' ⊇ zs
+-⊇ {chan} ## # = _ , # , ## , ##
+-⊇ {chan} #∅ ℓ∅ = _ , # , #∅ , #∅
+-⊇ {chan} #ᵢ ℓᵢ-left = _ , # , #ᵢ , #∅
+-⊇ {chan} #ᵢ ℓᵢ-right = _ , # , #∅ , #ᵢ
+-⊇ {chan} #ₒ ℓₒ-left = _ , # , #ₒ , #∅
+-⊇ {chan} #ₒ ℓₒ-right = _ , # , #∅ , #ₒ
+-⊇ {chan} ∅ ℓ∅ = _ , ℓ∅ , ∅ , ∅
+-⊇ {chan} ᵢ ℓᵢ-left = _ , ℓᵢ-left , ᵢ , ∅
+-⊇ {chan} ᵢ ℓᵢ-right = _ , ℓᵢ-right , ∅ , ᵢ
+-⊇ {chan} ₒ ℓₒ-left = _ , ℓₒ-left , ₒ , ∅
+-⊇ {chan} ₒ ℓₒ-right = _ , ℓₒ-right , ∅ , ₒ
+-⊇ {chan} ᵢₒ ℓᵢₒ-left = _ , ℓᵢₒ-left , ᵢₒ , ∅
+-⊇ {chan} ᵢₒ ℓᵢₒ-right = _ , ℓᵢₒ-right , ∅ , ᵢₒ
+-⊇ {chan} ᵢₒ ℓᵢₒ = _ , ℓᵢₒ , ᵢ , ₒ
+-⊇ {chan} ᵢₒ ℓₒᵢ = _ , ℓₒᵢ , ₒ , ᵢ
+-⊇ {type} pure pure = _ , pure , pure , pure
+-⊇ {type} (chan sub) (chan spl) = let _ , spl' , subl' , subr' = +-⊇ sub spl in _ , chan spl' , chan subl' , chan subr'
+-⊇ {type} (prod sub sub₁) prod-left = _ , prod-left , prod sub sub₁ , pure
+-⊇ {type} (prod sub sub₁) prod-right = _ , prod-right , pure , prod sub sub₁
+-⊇ {ctx} [] [] = _ , [] , [] , []
+-⊇ {ctx} (sub ∷ sub₁) (spl ∷ spl₁) =
  let
    _ , spl , subl , subr = +-⊇ sub spl
    _ , spls , subls , subrs = +-⊇ sub₁ spl₁
  in _ , spl ∷ spls , subl ∷ subls , subr ∷ subrs

data Occurs? : Ctx → TypedValue → TypedValue → Set₁ where
  yes : ∀ {xs x} → Null xs → Occurs? xs x x
  no  : ∀ {xs x y} → Null x → xs ∋ y → Occurs? xs x y

occurs? : ∀ {n t xs ys s} → InsertAt n t xs ys → ys ∋ s → Occurs? xs t s
occurs? here (here x) = yes x
occurs? here (there x ni) = no x ni
occurs? (there ins) (here x) =
  let t-null , xs-null = insert-null ins x in
  no t-null (here xs-null)
occurs? (there ins) (there x-null ni) with occurs? ins ni
... | yes xs-null = yes (x-null ∷ xs-null)
... | no t-null ni = no t-null (there x-null ni)


var-split : ∀ {xs x y z} → xs ∋ x → x ≔ y + z → Σ[ (ys , zs) ∈ Ctx × Ctx ] xs ≔ ys + zs × ys ∋ y × zs ∋ z
var-split {_ ∷ xs} (here null) spl
  = _ , spl ∷ +-idʳ xs , here null , here (neutral-null xs)
var-split {xs = x ∷ _} (there n vr) spl
  with _ , spl' , inl , inr ← var-split vr spl
  = _ , +-idʳ x ∷ spl' , there n inl , there (neutral-null x) inr

term-split : ∀ {xs x y z} → Term xs x → x ≔ y + z → Σ[ (ys , zs) ∈ Ctx × Ctx ] xs ≔ ys + zs × Term ys y × Term zs z
term-split (var x) spl
  with _ , spl1 , lvr , rvr ← var-split x spl
  = _ , spl1 , var lvr , var rvr
term-split {xs} (pure a x) pure
  = _ , null-unrestr x , pure a x , pure a x
term-split {xs} (pair spl1 lterm rterm) prod-left
  = _ , +-idʳ xs , pair spl1 lterm rterm , pure tt (neutral-null xs)
term-split {xs} (pair spl1 lterm rterm) prod-right
  = _ , +-idˡ xs , pure tt (neutral-null xs) , pair spl1 lterm rterm

⊇-insert : ∀ {n t' xs' 1+xs' 1+xs} → InsertAt n t' xs' 1+xs' → 1+xs' ⊇ 1+xs → Σ[ (xs , t) ∈ Ctx × TypedValue ] xs' ⊇ xs × t' ⊇ t × InsertAt n t xs 1+xs
⊇-insert here (sub ∷ subs) = _ , subs , sub , here
⊇-insert (there ins) (sub ∷ subs) =
  let _ , subs' , sub' , ins' = ⊇-insert ins subs in
  _ , sub ∷ subs' , sub' , there ins'

-- insert-⊇-balance : InsertAt n t' xs ys 
postulate pull-+-⊇ : ∀ {as' bs' cs' cs} → as' ≔ bs' + cs' → cs' ⊇ cs → Σ[ (as , bs) ∈ Ctx × Ctx ] as ≔ bs + cs × as' ⊇ as × bs' ⊇ bs

redistribute : ∀ {orig' orig left right n t elim enrich extra}
  → orig' ⊇ orig
  → orig ≔ left + right
  → InsertAt n t elim orig'
  → enrich ≔ extra + elim
  → Term extra t
  → Σ[ (enrichsub , as , bs , cs , ds , es , fs , a , b) ∈ Ctx × Ctx × Ctx × Ctx × Ctx × Ctx × Ctx × TypedValue × TypedValue ]
    enrich ⊇ enrichsub
  × enrichsub ≔ as + bs
  × as ≔ cs + ds
  × bs ≔ es + fs
  × Term cs a
  × Term es b
  × InsertAt n a ds left
  × InsertAt n b fs right
redistribute sub orig ins enrich term
  with _ , subctx , subtype , ins' ← ⊇-insert ins sub
  with _ , enrich' , subenrich , subextra ← pull-+-⊇ enrich subctx
  with _ , tspl , cspl , insl , insr ← extract ins' orig
  with _ , tspl' , subtypel , subtyper ← +-⊇ subtype tspl
  with _ , spl2 , lterm , rterm ← term-split term tspl'
  with _ , spl' , lspl' , rspl' ← reorient enrich' {!spl2!} cspl
  -- = _ , {!!} , spl' , lspl' , rspl' , lterm , rterm , {!insl!} , {!subctxl !}
  = _ , subenrich , {!!} , {!!} , {!!} , {!!} , {!rterm!} , insl , insr

{-
subst-var : ∀ {xs ys zs t n ws s}
           → xs ≔ ys + zs
           → Term ys t
           → InsertAt n t zs ws
           → ws ∋ s
           → Term xs s
subst-var spl term ins ni with occurs? ins ni
... | yes zs-null rewrite +-cancel spl zs-null = term
... | no t-null zs∋s rewrite +-cancel (+-comm spl) (Null-Term t-null term) = var zs∋s


subst-term : ∀ {xs ys zs t n ws s}
           → xs ≔ ys + zs
           → Term ys t
           → InsertAt n t zs ws
           → Term ws s
           → Term xs s
subst-term spl term ins (var x) = subst-var spl term ins x
subst-term spl term ins (pure a ws-null)
  with t-null , zs-null ← insert-null ins ws-null
  rewrite +-cancel spl zs-null
  = pure a (Null-Term t-null term)
subst-term spl term ins (pair (spl1 , sub1) l r)
  with a , spl1' , subl , subr ← +-⊇ sub1 spl1
  with b , tspl , cspl , insl , insr ← extract ins spl1'
  with c , spl2 , lterm , rterm ← term-split term tspl
  with d , spl' , lspl' , rspl' ← reorient spl spl2 cspl
  = pair ({!subtl'!} , {!!}) (subst-term {!lspl'!} lterm {!subl!} l) (subst-term {!!} rterm {!insr!} r)

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
subst-proc spl term ins (par (spl1 , sub1) p q) = par ({!!} , {!!}) (subst-proc {!!} {!!} {!!} p) (subst-proc {!!} {!!} {!!} q)
{-
  with a , spl1' , subl , subr ← +-⊇ sub1 spl1
  with _ , spl' , lspl' , rspl' , lterm , rterm , insl , insr ← redistribute spl1' ins spl term
  = par ({!spl'!} , {!!}) (subst-proc {!lspl'!} lterm {!insl!} p) (subst-proc {!rspl'!} rterm {!insr!} q)
  -}
subst-proc spl term ins (new x p)
  = new x (subst-proc (chan (+-idˡ x) ∷ spl) (Term-lift (chan (neutral-null x)) term) (there ins) p)
subst-proc spl term ins (rep ws-null p)
  with t-null , zs-null ← insert-null ins ws-null
  with refl ← +-cancel spl zs-null
  = rep (Null-Term t-null term) (subst-proc spl term ins p)
subst-proc spl term ins (send {ms} {ls} {rs} spl-payload payload spl-channel channel p)
  -- with _ , spl-payload2 , lspl-term , spl-rest2 , term-l , term-rest , ins-payload , ins-rest ← redistribute spl-payload ins spl term
  -- with _ , spl-channel2 , spl-term-chan , spl-term-cont , term-channel , term-cont , ins-channel , ins-cont ← redistribute spl-channel ins-rest spl-rest2 term-rest
  = {!!} -- send spl-payload2 (subst-term lspl-term term-l ins-payload payload)
  -- spl-channel2 (subst-term spl-term-chan term-channel ins-channel channel)
  -- (subst-proc spl-term-cont term-cont ins-cont p)
subst-proc spl term ins (recv {T = T} spl-channel channel cont)
  -- with _ , spl' , lspl' , rspl' , lterm , rterm , insl , insr ← redistribute spl-channel ins spl term
  = {!!} -- recv spl' (subst-term lspl' lterm insl channel) λ t →
    -- subst-proc (+-idˡ _ ∷ rspl') (Term-lift (neutral-null _) rterm) (there insr) (cont t)
subst-proc spl term ins (letprod {A = A} {B} {a} {b} spl-prod prd p)
  -- with _ , spl' , lspl' , rspl' , lterm , rterm , insl , insr ← redistribute spl-prod ins spl term
  = {!!} -- letprod spl' (subst-term lspl' lterm insl prd)
  -- (subst-proc (+-idˡ _ ∷ +-idˡ _ ∷ rspl') (Term-lift (neutral-null _) (Term-lift (neutral-null _) rterm)) (there (there insr)) p)
-}

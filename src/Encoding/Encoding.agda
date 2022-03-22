open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst; cong; cong₂; sym; trans)
open import Function using (_∘_; _$_)
open import Data.Unit using (⊤; tt)
open import Data.Product as Product using (Σ; Σ-syntax; _×_; _,_; proj₁; proj₂)
open import Data.List.Base as List

import SessionPi as S

module Encoding where

module L where
  open import LinearPi.TypeSystem public
  open import LinearPi.Weakening public
  -- open import LinearPi.Substitution public
  open import LinearPi.Exchange public


infix 4 !_
pattern !_ x = _ , x

-- Encoding of dual session types
-- ⟦ ?A. !B. end ⟧ ≜ chan 1 0 (⟦ A ⟧ × (chan 0 1 (⟦ B ⟧ × chan 0 0 ⊤)))
-- ⟦ !A. ?B. end ⟧ ≜ chan 0 1 (⟦ A ⟧ × (chan 1 0 (⟦ B ⟧ × chan 0 0 ⊤)))

flip-chan : L.Channel → L.Channel
flip-chan L.ℓ∅ = L.ℓ∅
flip-chan (L.ℓᵢ x) = L.ℓₒ x
flip-chan (L.ℓₒ x) = L.ℓᵢ x
flip-chan (L.ℓᵢₒ x) = L.ℓᵢₒ x
flip-chan (L.# x) = L.# x

mutual
  ⟦_⟧ₑ-type : S.Type → L.Type
  ⟦ S.pure x ⟧ₑ-type = L.pure x
  ⟦ S.sesh x ⟧ₑ-type = L.chan ⟦ x ⟧ₑ-session
  ⟦ S.chan x ⟧ₑ-type = L.chan (L.# ⟦ x ⟧ₑ-type)

  ⟦_⟧ₑ-session : S.Session → L.Channel
  ⟦ S.end ⟧ₑ-session = L.ℓ∅
  ⟦ S.send T C ⟧ₑ-session = L.ℓₒ (L.prod ⟦ T ⟧ₑ-type (encode-cont-flip T C))
  ⟦ S.recv T C ⟧ₑ-session = L.ℓᵢ (L.prod ⟦ T ⟧ₑ-type (encode-cont T C))
  ⟦ S.cont T C ⟧ₑ-session = L.ℓ∅

  ⟦_⟧ₑ-typedvalue : S.TypedValue → L.TypedValue
  ⟦ T , t ⟧ₑ-typedvalue = ⟦ T ⟧ₑ-type , (encode T t)

  ⟦_⟧ₑ-ctx : S.Ctx → L.Ctx
  ⟦_⟧ₑ-ctx = List.map ⟦_⟧ₑ-typedvalue

  decode : ∀ T → L.⟦ ⟦ T ⟧ₑ-type ⟧ₜ → S.⟦ T ⟧ₜ
  decode (S.pure A) x = x
  decode (S.sesh _) _ = tt
  decode (S.chan _) _ = tt

  encode : ∀ T → S.⟦ T ⟧ₜ → L.⟦ ⟦ T ⟧ₑ-type ⟧ₜ
  encode (S.pure A) x = x
  encode (S.sesh _) _ = tt
  encode (S.chan _) _ = tt

  encode-cont : (T : S.Type) (C : S.⟦ T ⟧ₜ → S.Session) → (L.⟦ ⟦ T ⟧ₑ-type ⟧ₜ → L.Type)
  encode-cont T C = L.chan ∘ ⟦_⟧ₑ-session ∘ C ∘ decode T

  encode-cont-flip : (T : S.Type) (C : S.⟦ T ⟧ₜ → S.Session) → (L.⟦ ⟦ T ⟧ₑ-type ⟧ₜ → L.Type)
  encode-cont-flip T C = L.chan ∘ flip-chan ∘ ⟦_⟧ₑ-session ∘ C ∘ decode T

decode-encode : ∀ T {t} → decode T (encode T t) ≡ t
decode-encode (S.pure x) = refl
decode-encode (S.sesh x) = refl
decode-encode (S.chan x) = refl

encode-decode : ∀ T {t} → encode T (decode T t) ≡ t
encode-decode (S.pure x) = refl
encode-decode (S.sesh x) = refl
encode-decode (S.chan x) = refl

⟦_⟧-null-typedvalue : ∀ {x} → S.Null x → L.Null ⟦ x ⟧ₑ-typedvalue
⟦ S.pure ⟧-null-typedvalue = L.pure
⟦ S.sesh-end ⟧-null-typedvalue = L.chan L.ℓ∅
⟦ S.chan ⟧-null-typedvalue = L.chan L.#

⟦_⟧-null : ∀ {xs : S.Ctx} → S.Null xs → L.Null ⟦ xs ⟧ₑ-ctx
⟦ S.[] ⟧-null = L.[]
⟦ n S.∷ ns ⟧-null = ⟦ n ⟧-null-typedvalue L.∷ ⟦ ns ⟧-null

neutral-session : ∀ S → L.neutral ⟦ S ⟧ₑ-session ≡ L.ℓ∅
neutral-session S.end = refl
neutral-session (S.recv T x) = refl
neutral-session (S.send T x) = refl
neutral-session (S.cont T x) = refl

⟦_⟧-≔-+-typedvalue : ∀ {x y z} → x S.≔ y + z → ⟦ x ⟧ₑ-typedvalue L.≔ ⟦ y ⟧ₑ-typedvalue + ⟦ z ⟧ₑ-typedvalue
⟦ S.pure ⟧-≔-+-typedvalue = L.pure
⟦ S.sesh-left {S} ⟧-≔-+-typedvalue
  with spl ← L.+-idʳ ⟦ S ⟧ₑ-session
  rewrite neutral-session S
  = L.chan spl
⟦ S.sesh-right {S} ⟧-≔-+-typedvalue
  with spl ← L.+-idˡ ⟦ S ⟧ₑ-session
  rewrite neutral-session S
  = L.chan spl
⟦ S.chan ⟧-≔-+-typedvalue = L.chan L.#

⟦_⟧-≔-+ : ∀ {xs ys zs} → xs S.≔ ys + zs → ⟦ xs ⟧ₑ-ctx L.≔ ⟦ ys ⟧ₑ-ctx + ⟦ zs ⟧ₑ-ctx
⟦ S.[] ⟧-≔-+ = L.[]
⟦ spl S.∷ spls ⟧-≔-+ = ⟦ spl ⟧-≔-+-typedvalue L.∷ ⟦ spls ⟧-≔-+

∋ₜ-exhaust : ∀ {xs n zs T t} → xs S.∋ₜ S.at n (S.payload T t) ▹ zs
           → Σ[ ys ∈ L.Ctx ] ⟦ xs ⟧ₑ-ctx L.≔ ys + ⟦ zs ⟧ₑ-ctx × ys L.∋ (⟦ T ⟧ₑ-type , encode T t)
∋ₜ-exhaust (S.here (S.payload-pure _ _)) = _ , L.+-idʳ _ L.∷ L.+-idˡ _ , L.here (L.neutral-null _)
∋ₜ-exhaust (S.here (S.payload-sesh {x}))
  with spl ← L.+-idʳ ⟦ x ⟧ₑ-session
  rewrite neutral-session x
  = _ , L.chan spl L.∷ L.+-idˡ _ , L.here (L.neutral-null _)
∋ₜ-exhaust (S.here S.payload-chan)
  = _ , L.chan L.# L.∷ L.+-idˡ _ , L.here (L.neutral-null _)
∋ₜ-exhaust (S.there x)
  with _ , spl , x' ← ∋ₜ-exhaust x
  = _ , L.+-idˡ _ L.∷ spl , L.there (L.neutral-null _) x'

{-
∋ₜ-recv : ∀ {xs n zs T C}
        → xs S.∋ₜ S.at n (S.recv T C) ▹ zs
        → Σ[ ys ∈ L.Ctx ] ⟦ xs ⟧ₑ-ctx L.≔ ys + ⟦ zs ⟧ₑ-ctx × ys L.∋ (L.chan (L.ℓᵢ (L.prod ⟦ T ⟧ₑ-type (encode-cont T C))) , tt)
∋ₜ-recv {xs = _ ∷ xs} (S.here (S.sesh S.recv)) = _ , L.chan (L.+-idʳ _) L.∷ L.+-idˡ _ , L.here (L.neutral-null _)
∋ₜ-recv {xs = x ∷ _} (S.there n)
  with _ , spl , var ← ∋ₜ-recv n
  = _ , L.+-idˡ _ L.∷ spl , L.there (L.neutral-null _) var
  -}


∋ₜ-send : ∀ {ys n zs T t}
        → ys S.∋ₜ S.at n (S.send T (decode T t)) ▹ zs
        → Σ[ (xs , Cont) ∈ L.Ctx × (S.⟦ T ⟧ₜ → S.Session) ]
          L.InsertAt n (L.chan (L.ℓₒ (L.prod ⟦ T ⟧ₑ-type (encode-cont-flip T Cont))) , tt) xs ⟦ ys ⟧ₑ-ctx
        × L.InsertAt n (encode-cont T Cont t , tt) xs ⟦ zs ⟧ₑ-ctx
∋ₜ-send (S.here (S.send-sesh {C = C})) = (_ , C) , L.here , L.here
∋ₜ-send (S.here S.send-chan) = _ , {!L.here!} , {!!}
∋ₜ-send (S.there x) = {!!}


{-
∋ₜ-cont : ∀ {n T t C zs ys}
        → ys S.∋ₜ S.at n (S.cont T (decode T t) C) ▹ zs
        → Σ[ xs ∈ L.Ctx ]
          L.InsertAt n (L.chan L.ℓ∅ , tt) xs ⟦ ys ⟧ₑ-ctx
        × L.InsertAt n (encode-cont T C t , tt) xs ⟦ zs ⟧ₑ-ctx
∋ₜ-cont (S.here (S.sesh S.cont)) = _ , L.here , L.here
∋ₜ-cont (S.there ins)
  with ! ins1 , ins2 ← ∋ₜ-cont ins
  = _ , L.there ins1 , L.there ins2
  -}



mutual
  ⟦_⟧ₚ : ∀ {Γ} → S.Process Γ → L.Process ⟦ Γ ⟧ₑ-ctx
  ⟦ S.end n ⟧ₚ = L.end ⟦ n ⟧-null
  ⟦ S.par s p q ⟧ₚ = L.par (⟦ s ⟧-≔-+ L., L.⊇-refl _) ⟦ p ⟧ₚ ⟦ q ⟧ₚ
  ⟦ S.new (S.chan t) p ⟧ₚ = L.new (L.# ⟦ t ⟧ₑ-type) (L.new (L.# ⟦ t ⟧ₑ-type) ⟦ p ⟧ₚ)
  ⟦ S.new (S.sesh s) p ⟧ₚ = L.new ⟦ S.dual s ⟧ₑ-session (L.new ⟦ s ⟧ₑ-session ⟦ p ⟧ₚ)
  ⟦ S.rep n p ⟧ₚ = L.rep ⟦ n ⟧-null ⟦ p ⟧ₚ
  ⟦ S.send {T = T} {t = t} v c p ⟧ₚ = {!!}
  {-
    let SC = ⟦ C t ⟧ₑ-session in
    let ! spv , tv = ∋ₜ-exhaust v in
    let ! spc , ch = ∋ₜ-send s in
    let Δ , ins1 , ins2 = ∋ₜ-cont (subst (λ ● → _ S.∋ₜ S.at _ (S.cont T ● C) ▹ _) (sym (decode-encode T)) c) in
    let foo = subst (λ ● → _ L.≔ L.neutral (L.chan (flip-chan ⟦ C t ⟧ₑ-session) , tt) + (L.chan (flip-chan ⟦ C ● ⟧ₑ-session) , tt) ) (sym (decode-encode T)) (L.+-idˡ _) in
    let bar = subst (λ ● → L.InsertAt _ (L.chan ⟦ C ● ⟧ₑ-session , tt) Δ (_ ∷ Δ)) (sym (decode-encode T)) L.here in
    L.new SC
    $ L.new (flip-chan SC)
    $ L.send
      (L.+-idʳ _ L.∷ L.+-idˡ _ L.∷ spv)
        (L.pair (foo L.∷ L.+-idˡ _ L.∷ L.+-idʳ _)
                (L.Term-lift (L.chan L.ℓ∅) (L.Term-lift (L.chan L.ℓ∅) (L.var tv)))
                (L.var (L.here (L.chan L.ℓ∅ L.∷ L.neutral-null _))))
      (L.+-idˡ _ L.∷ L.+-idˡ _ L.∷ spc)
        (L.Term-lift (L.chan L.ℓ∅) (L.Term-lift (L.chan L.ℓ∅) (L.var ch)))
    $ L.exchange-proc L.here (L.there (L.there ins1))
    $ L.exchange-proc (L.there (L.there ins2)) (L.there (L.there bar))
    $ L.Process-null-insert (L.chan L.ℓ∅) L.here
    $ L.Process-null-insert (L.chan L.ℓ∅) L.here
    $ ⟦ p ⟧ₚ
  ⟦ S.recv {ys = ys} {T = T} {C = C}s p ⟧ₚ
    =
    let ! spl , channel = ∋ₜ-recv s in
    L.recv spl (L.var channel) λ (t , tt) →
    let var-cont , proc-cont = p (decode T t) in
    let ! ins1 , ins2 = ∋ₜ-cont var-cont in
    L.letprod (L.+-idʳ _ L.∷ L.+-idˡ _) (L.var (L.here (L.neutral-null _)))
    $ L.Process-null-insert L.pure (L.there (L.there L.here))
    $ subst (λ ● → L.Process ((⟦ T ⟧ₑ-type , ●) ∷ (encode-cont T C t , tt) ∷ ⟦ ys ⟧ₑ-ctx)) (encode-decode T)
    $ L.exchange-proc (L.there (L.there L.here)) (L.there (L.there ins1))
    $ L.Process-null-insert (L.chan L.ℓ∅) (L.there (L.there L.here))
    $ L.exchange-proc (L.there ins2) (L.there L.here)
    $ ⟦ proc-cont ⟧ₚ
-}

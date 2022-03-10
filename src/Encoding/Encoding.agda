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
  open import LinearPi.Substitution public
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

mutual
  ⟦_⟧ₑ-type : S.Type → L.Type
  ⟦ S.pure x ⟧ₑ-type = L.pure x
  ⟦ S.chan x ⟧ₑ-type = L.chan ⟦ x ⟧ₑ-session

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
  decode (S.chan _) _ = tt

  encode : ∀ T → S.⟦ T ⟧ₜ → L.⟦ ⟦ T ⟧ₑ-type ⟧ₜ
  encode (S.pure A) x = x
  encode (S.chan _) _ = tt

  encode-cont : (T : S.Type) (C : S.⟦ T ⟧ₜ → S.Session) → (L.⟦ ⟦ T ⟧ₑ-type ⟧ₜ → L.Type)
  encode-cont T C = L.chan ∘ ⟦_⟧ₑ-session ∘ C ∘ decode T

  encode-cont-flip : (T : S.Type) (C : S.⟦ T ⟧ₜ → S.Session) → (L.⟦ ⟦ T ⟧ₑ-type ⟧ₜ → L.Type)
  encode-cont-flip T C = L.chan ∘ flip-chan ∘ ⟦_⟧ₑ-session ∘ C ∘ decode T

flip-dual : ∀ S → ⟦ S.dual S ⟧ₑ-session ≡ flip-chan ⟦ S ⟧ₑ-session
flip-dual S.end = refl
flip-dual (S.recv T C) = cong L.ℓₒ (cong (L.prod _) {!!})
flip-dual (S.send T x) = cong L.ℓᵢ (cong (L.prod _) {!!})
flip-dual (S.cont T x) = refl

decode-encode : ∀ T {t} → decode T (encode T t) ≡ t
decode-encode (S.pure x) = refl
decode-encode (S.chan x) = refl

encode-decode : ∀ T {t} → encode T (decode T t) ≡ t
encode-decode (S.pure x) = refl
encode-decode (S.chan x) = refl

⟦_⟧-null-typedvalue : ∀ {x} → S.Null x → L.Null ⟦ x ⟧ₑ-typedvalue
⟦ S.pure ⟧-null-typedvalue = L.pure
⟦ S.chan S.end ⟧-null-typedvalue = L.chan L.ℓ∅

⟦_⟧-null : ∀ {xs : S.Ctx} → S.Null xs → L.Null ⟦ xs ⟧ₑ-ctx
⟦ S.[] ⟧-null = L.[]
⟦ n S.∷ ns ⟧-null = ⟦ n ⟧-null-typedvalue L.∷ ⟦ ns ⟧-null


⟦_⟧-≔-+-typedvalue : ∀ {x y z} → x S.≔ y + z → ⟦ x ⟧ₑ-typedvalue L.≔ ⟦ y ⟧ₑ-typedvalue + ⟦ z ⟧ₑ-typedvalue
⟦ S.pure ⟧-≔-+-typedvalue = L.pure
⟦ S.chan S.left ⟧-≔-+-typedvalue = L.chan (L.+-idʳ _)
⟦ S.chan S.right ⟧-≔-+-typedvalue = L.chan (L.+-idˡ _)

⟦_⟧-≔-+ : ∀ {xs ys zs} → xs S.≔ ys + zs → ⟦ xs ⟧ₑ-ctx L.≔ ⟦ ys ⟧ₑ-ctx + ⟦ zs ⟧ₑ-ctx
⟦ S.[] ⟧-≔-+ = L.[]
⟦ spl S.∷ spls ⟧-≔-+ = ⟦ spl ⟧-≔-+-typedvalue L.∷ ⟦ spls ⟧-≔-+

postulate ∋ₜ-exhaust : ∀ {xs n zs T t} → xs S.∋ₜ S.at n (S.exhaust (T , t)) ▹ zs
                     → Σ[ ys ∈ L.Ctx ] ⟦ xs ⟧ₑ-ctx L.≔ ys + ⟦ zs ⟧ₑ-ctx × L.Term ys (⟦ T ⟧ₑ-type , encode T t)

∋ₜ-recv : ∀ {xs n zs T C}
        → xs S.∋ₜ S.at n (S.recv T C) ▹ zs
        → Σ[ ys ∈ L.Ctx ] ⟦ xs ⟧ₑ-ctx L.≔ ys + ⟦ zs ⟧ₑ-ctx × ys L.∋ (L.chan (L.ℓᵢ (L.prod ⟦ T ⟧ₑ-type (encode-cont T C))) , tt)
∋ₜ-recv {xs = _ ∷ xs} (S.here (S.chan S.recv)) = _ , L.chan (L.+-idʳ _) L.∷ L.+-idˡ _ , L.here (L.neutral-null _)
∋ₜ-recv {xs = x ∷ _} (S.there n)
  with _ , spl , var ← ∋ₜ-recv n
  = _ , L.+-idˡ _ L.∷ spl , L.there (L.neutral-null _) var

∋ₜ-cont : ∀ {n T t C zs ys}
        → ys S.∋ₜ S.at n (S.cont T (decode T t) C) ▹ zs
        → Σ[ xs ∈ L.Ctx ]
          L.InsertAt n (L.chan L.ℓ∅ , tt) xs ⟦ ys ⟧ₑ-ctx
        × L.InsertAt n (encode-cont T C t , tt) xs ⟦ zs ⟧ₑ-ctx
∋ₜ-cont (S.here (S.chan S.cont)) = _ , L.here , L.here
∋ₜ-cont (S.there ins)
  with ! ins1 , ins2 ← ∋ₜ-cont ins
  = _ , L.there ins1 , L.there ins2

{-
∋ₜ-send : ∀ {xs n T C ys zs}
        → xs S.∋ₜ S.at n (S.send T C) ▹ ys
        → ⟦ ys ⟧ₑ-ctx L.[ n ↦ L.chan L.#0 L.#0 (L.prod ⟦ T ⟧ₑ-type (encode-cont-flip T C)), tt ]≔ zs
        → Σ[ ms ∈ L.Ctx ]
          ⟦ xs ⟧ₑ-ctx L.≔ ms + zs
        × L.Term ms (L.chan L.#0 L.#1 (L.prod ⟦ T ⟧ₑ-type (encode-cont-flip T C)) , tt)
∋ₜ-send {_ ∷ xs} (S.here (S.chan S.send)) L.here
  with ! id , null ← L.+-idˡ ⟦ xs ⟧ₑ-ctx
  = ! L.chan L.#0 L.#1-left L.∷ id , L.var (L.here null (L.chan L.#0 L.#1 refl))
∋ₜ-send {(T , t) ∷ _} (S.there x) (L.there s)
  with ! id , null ← L.+-idˡ (⟦ T ⟧ₑ-type , encode T t)
  = Product.map _ (Product.map (id L.∷_) (L.Term-lift null)) (∋ₜ-send x s)
  -}


mutual
  ⟦_⟧ₚ : ∀ {Γ} → S.Process Γ → L.Process ⟦ Γ ⟧ₑ-ctx
  ⟦ S.end n ⟧ₚ = L.end ⟦ n ⟧-null
  ⟦ S.par s p q ⟧ₚ = L.par ⟦ s ⟧-≔-+ ⟦ p ⟧ₚ ⟦ q ⟧ₚ
  ⟦ S.new S p ⟧ₚ = L.new ⟦ S.dual S ⟧ₑ-session (L.new ⟦ S ⟧ₑ-session ⟦ p ⟧ₚ)
  ⟦ S.rep n p ⟧ₚ = L.rep ⟦ n ⟧-null ⟦ p ⟧ₚ
  ⟦ S.send {T = T} {t = t} {C = C} v s c p ⟧ₚ
    with SC ← ⟦ C t ⟧ₑ-session in eq
    with Δ , spv , tv ← ∋ₜ-exhaust v
    -- with ! spc , tc ← {!∋ₜ-send s {!!}!}
    -- with ! spp , np ← L.+-idʳ Δ
    -- with a , t-right , t-nleft ← L.+-idˡ (L.chan SC , tt)
    -- with b , t̂-left , t̂-nright ← L.+-idʳ (L.chan (flip-chan SC) , tt)
    -- with ! t̂-right , t̂-nleft ← L.+-idˡ (L.chan (flip-chan SC) , tt)
    -- with ! a-right , a-nleft ← L.+-idˡ a
    -- with ! b-right , b-nleft ← L.+-idˡ b
    -- with ! Δ-left , Δ-null ← L.+-idʳ Δ
    = L.new {!!} -- ci co ct
    $ L.new {!!} -- co ci ct
    $ {!!}
    {-
    $ L.send
      (t̂-left L.∷ t-right  L.∷ spv)
      (L.pair (t̂-right L.∷ a-right L.∷ Δ-left)
              (L.Term-lift t̂-nleft (L.Term-lift a-nleft tv))
              (L.var (L.here (t-nleft L.∷ Δ-null) (L.chan
                (subst (λ ● → proj₁ (proj₂ (⟦ C ● ⟧ₑ-session)) L.⊆ co) (sym (decode-encode T {t})) (subst (L._⊆ co) (cong (proj₁ ∘ proj₂) (sym eq)) (L.⊆-refl _)))
                (subst (λ ● → proj₁ (⟦ C ● ⟧ₑ-session) L.⊆ ci)         (sym (decode-encode T {t})) (subst (L._⊆ ci) (cong (proj₁)         (sym eq)) (L.⊆-refl _)))
                (trans (cong (λ ● → proj₂ (proj₂ ⟦ C ● ⟧ₑ-session)) (decode-encode T {t})) (cong (proj₂ ∘ proj₂) eq))))))
      (b-right L.∷ t-right L.∷ {!spc!})
      (L.Term-lift b-nleft (L.Term-lift t-nleft {!tc!}))
      (L.Process-lift t̂-nright (L.subst-proc (L.chan {!!} {!!} L.∷ {!!}) {!!} {!!} ⟦ p ⟧ₚ) )
      -}
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

open import Function using (_∘_; _$_)
open import Data.Unit using (⊤; tt)
open import Data.Product as Product using (Σ; Σ-syntax; _×_; _,_; proj₁; proj₂)
open import Data.List.Base as List

import SessionPi as S
import LinearPi as L


mutual
  ⟦_⟧ₑ-type : S.Type → L.Type
  ⟦ S.pure x ⟧ₑ-type = L.pure x
  ⟦ S.chan x ⟧ₑ-type = ⟦ x ⟧ₑ-session

  ⟦_⟧ₑ-session : S.Session → L.Type
  ⟦ S.end ⟧ₑ-session = L.chan L.0∙ L.0∙ (L.pure ⊤)
  ⟦ S.recv T C ⟧ₑ-session = L.chan L.1∙ L.0∙ (L.prod ⟦ T ⟧ₑ-type (⟦_⟧ₑ-session ∘ C ∘ decode T))
  ⟦ S.send T C ⟧ₑ-session = L.chan L.0∙ L.1∙ (L.prod ⟦ T ⟧ₑ-type (⟦_⟧ₑ-session ∘ C ∘ decode T))

  ⟦_⟧ₑ-ctx : S.Ctx → L.Ctx
  ⟦_⟧ₑ-ctx = List.map λ (T , t) → ⟦ T ⟧ₑ-type , encode T t

  decode : ∀ T → L.⟦ ⟦ T ⟧ₑ-type ⟧ₜ → S.⟦ T ⟧ₜ
  decode (S.pure A) x = x
  decode (S.chan x₁) _ = tt

  encode : ∀ T → S.⟦ T ⟧ₜ → L.⟦ ⟦ T ⟧ₑ-type ⟧ₜ
  encode (S.pure A) x = x
  encode (S.chan S.end) _ = tt
  encode (S.chan (S.recv T _)) _ = tt
  encode (S.chan (S.send T _)) _ = tt


postulate ⟦_⟧-null : ∀ {xs : S.Ctx}
                   → S.Null xs
                   → L.Null ⟦ xs ⟧ₑ-ctx

postulate ⟦_⟧-≔-+ : ∀ {xs ys zs}
                  → xs S.≔ ys + zs
                  → ⟦ xs ⟧ₑ-ctx L.≔ ⟦ ys ⟧ₑ-ctx + ⟦ zs ⟧ₑ-ctx

postulate ∋ₜ-exhaust : ∀ {xs zs T t}
                     → xs S.∋ₜ S.exhaust (T , t) ▹ zs
                     → Σ[ ys ∈ L.Ctx ]
                       ⟦ xs ⟧ₑ-ctx L.≔ ys + ⟦ zs ⟧ₑ-ctx ×
                       L.Term ys (⟦ T ⟧ₑ-type , encode T t)

postulate ∋ₜ-send : ∀ {xs zs T t C}
                  → xs S.∋ₜ S.send T t C ▹ zs
                  → Σ[ ys ∈ L.Ctx ]
                      ⟦ xs ⟧ₑ-ctx L.≔ ys + ⟦ zs ⟧ₑ-ctx ×
                      L.Term ys (L.chan L.0∙ L.1∙ (L.prod ⟦ T ⟧ₑ-type (⟦_⟧ₑ-session ∘ C ∘ decode T)) , tt)

postulate Term-lift : ∀ {x xs t}
                    → L.Null x
                    → L.Term xs t
                    → L.Term (x ∷ xs) t

create : ∀ {xs} → (S : S.Session) → L.Process ((⟦ S ⟧ₑ-session , encode (S.chan S) tt) ∷ (⟦ S.dual S ⟧ₑ-session , encode (S.chan (S.dual S)) tt) ∷ xs) → L.Process xs
create S.end p = L.new L.0∙ L.0∙ (L.pure ⊤) (L.new L.0∙ L.0∙ (L.pure ⊤) p)
create (S.recv T C) p
  = L.new L.0∙ L.1∙ (L.prod ⟦ T ⟧ₑ-type (⟦_⟧ₑ-session ∘ S.dual ∘ C ∘ decode T))
  $ L.new L.1∙ L.0∙ (L.prod ⟦ T ⟧ₑ-type (⟦_⟧ₑ-session ∘ C ∘ decode T)) p
create (S.send T C) p
  = L.new L.1∙ L.0∙ (L.prod ⟦ T ⟧ₑ-type (⟦_⟧ₑ-session ∘ S.dual ∘ C ∘ decode T))
  $ L.new L.0∙ L.1∙ (L.prod ⟦ T ⟧ₑ-type (⟦_⟧ₑ-session ∘ C ∘ decode T)) p

-- Encoding of dual session types
-- ⟦ ?A. !B. end ⟧ ≜ chan 1 0 (⟦ A ⟧ × (chan 0 1 (⟦ B ⟧ × chan 0 0 ⊤)))
-- ⟦ !A. ?B. end ⟧ ≜ chan 0 1 (⟦ A ⟧ × (chan 1 0 (⟦ B ⟧ × chan 0 0 ⊤)))
mutual
  ⟦_⟧ₚ : ∀ {Γ} → S.Process Γ → L.Process ⟦ Γ ⟧ₑ-ctx
  ⟦ S.end n ⟧ₚ = L.end ⟦ n ⟧-null
  ⟦ S.par s p q ⟧ₚ = L.par ⟦ s ⟧-≔-+ ⟦ p ⟧ₚ ⟦ q ⟧ₚ
  ⟦ S.new S.end p ⟧ₚ
    = L.new L.0∙ L.0∙ (L.pure ⊤)
    $ L.new L.0∙ L.0∙ (L.pure ⊤)
    $ ⟦ p ⟧ₚ
  ⟦ S.new (S.recv T C) p ⟧ₚ
    = L.new L.0∙ L.1∙ (L.prod ⟦ T ⟧ₑ-type (⟦_⟧ₑ-session ∘ S.dual ∘ C ∘ decode T))
    $ L.new L.1∙ L.0∙ (L.prod ⟦ T ⟧ₑ-type (⟦_⟧ₑ-session  ∘ C ∘ decode T))
    $ ⟦ p ⟧ₚ
  ⟦ S.new (S.send T C) p ⟧ₚ
    = L.new L.1∙ L.0∙ (L.prod ⟦ T ⟧ₑ-type (⟦_⟧ₑ-session ∘ S.dual ∘ C ∘ decode T))
    $ L.new L.0∙ L.1∙ (L.prod ⟦ T ⟧ₑ-type (⟦_⟧ₑ-session  ∘ C ∘ decode T))
    $ ⟦ p ⟧ₚ
  ⟦ S.rep n p ⟧ₚ = L.rep ⟦ n ⟧-null ⟦ p ⟧ₚ
  ⟦ S.send {T = T} {t = t} {C = C} v c p ⟧ₚ
    with Δ , spv , tv ← ∋ₜ-exhaust v
    with _ , spc , tc ← ∋ₜ-send c
    with _ , spp , np ← L.+-idʳ Δ
    = create (C t)
    $ L.send
      ({!!} L.∷ {!!} L.∷ {!!})
      (L.pair ({!!} L.∷ {!!} L.∷ {!!}) (Term-lift (L.chan L.0∙ L.0∙) (Term-lift (L.chan L.0∙ L.0∙) tv)) {!tv!})
      ({!!} L.∷ {!!})
      {!!}
      {!!}
    {-
    = L.new L.1∙ L.1∙ ⟦ T ⟧ₑ-type
    $ L.send
      (L.chan {!!} {!!} L.∷ spv)
      (L.pair (L.chan {!!} {!!} L.∷ spp) (Term-lift (L.chan L.0∙ L.0∙) tv) (L.var (L.here np {!!})))
      (L.chan L.1∙-right L.0∙ L.∷ spc)
      (Term-lift (L.chan L.0∙ L.0∙) tc)
    $ {! ⟦ p ⟧ₚ !}
    -}
  ⟦ S.recv c ⟧ₚ = L.recv {!!} {!!} {!!}

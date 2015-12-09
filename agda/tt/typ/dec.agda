module tt.typ.dec where

open import Data.Nat hiding (_≟_)
open import Data.Fin
open import Data.Product
open import Function
open import Relation.Nullary
open import Relation.Binary.PropositionalEquality as PEq

open import tt.Data.NatOmega
open import tt.raw
open import tt.con
open import tt.red
open import tt.env
open import tt.sem
open import tt.typ
open import tt.typ.inv
open import tt.typ.red

module typeCheck
       (_↝_  : IRel Type) (Red : Reduction SType _↝_) (TRed : TypeReduction _↝_)
       (whnf  : Type ⇒ Type) (wh  : WeakHead whnf _↝_)
       where

  open Typing _↝_
  open WeakHead wh
  open Reduction Red
  open TypeReduction TRed

  open TypingInversion _↝_ Red β↝* `pi↝*-inv `sig↝*-inv
  module ExpandTyping = ExpandContextTyping _↝_ weak↝
  module ReduceTyping = ReduceContextTyping _↝_ Red β↝* `set↝*-inv `nat↝*-inv `pi↝*-inv `sig↝*-inv

  -- Type Inference for variables is total: it's a simple lookup
  -- in the context!

  typeInferVar : {n : ℕ} (Γ : ContextT n) (k : Fin n) → ∃ λ A → Γ ⊢var k ∈ A
  typeInferVar (_ ∙⟩ A) zero    = , zro
  typeInferVar (Γ ∙⟩ _) (suc k) = map (weakT extend) suc $ typeInferVar Γ k

  -- The decidability of Type Checking and Type Inference can then be
  -- proven by a mutual induction

  typeType : {n : ℕ} (Γ : ContextT n) (ℓ : ℕω) (A : Type n) → Dec (Γ ⊢set ℓ ∋ A)
  typeCheck : {n : ℕ} (Γ : ContextT n) (A : Type n) (a : Check n) → Dec (Γ ⊢ A ∋ a)
  typeInfer : {n : ℕ} (Γ : ContextT n) (e : Infer n) → Dec (∃ λ A → Γ ⊢ e ∈ A)


  typeType Γ ℓ (`sig A B) with typeType Γ ℓ A | typeType (Γ ∙⟩ A) ℓ B
  ... | yes hA | yes hB = yes (`sig hA hB)
  ... | no ¬hA | _      = no (¬hA ∘ proj₁ ∘ Γ⊢set∋ΣAB-inv)
  ... | yes hA | no ¬hB = no (¬hB ∘ proj₂ ∘ Γ⊢set∋ΣAB-inv)

  typeType Γ ℓ (`pi A B)  with typeType Γ ℓ A | typeType (Γ ∙⟩ A) ℓ B
  ... | yes hA | yes hB = yes (`pi hA hB)
  ... | no ¬hA | _      = no (¬hA ∘ proj₁ ∘ Γ⊢set∋ΠAB-inv)
  ... | yes hA | no ¬hB = no (¬hB ∘ proj₂ ∘ Γ⊢set∋ΠAB-inv)
  
  typeType Γ (↑ ℓ) `nat = yes `nat
  typeType Γ ω     `nat = no λ ()
  
  typeType Γ ℓ (`set ℓ′) with ↑ ℓ′ <? ℓ
  ... | yes lt = yes (`set lt)
  ... | no ¬lt = no (¬lt ∘ Γ⊢set∋set-inv)
  
  typeType Γ ℓ (`elt e) with typeInfer Γ e
  ... | yes (A , Γ⊢e∈A) with whnf A | yieldsReduct A | uncoversHead A
  ... | `set ℓ′ | A↝*setℓ′ | spec with ℓ ≟ ↑ ℓ′ 
  ... | yes p rewrite p = yes (`elt (reduceInfer A↝*setℓ′ Γ⊢e∈A))
  ... | no ¬p =

    no $ λ p →
       let (ℓ′′ , ℓ≡ℓ′′ , Γ⊢e∈set) = Γ⊢set∋elt-inv p
           (R , A↝R , set↝R)       = Γ⊢e∈-unique Γ⊢e∈A Γ⊢e∈set
           (U , R↝U , set↝U)       = confluence A↝R A↝*setℓ′
           U≡set                   = `set↝*-inv set↝U
           U≡set′                  = `set↝*-inv $ mores set↝R R↝U
       in ¬p $ PEq.trans ℓ≡ℓ′′ $ PEq.cong ↑_ $ `set-inj $ PEq.trans (PEq.sym U≡set′) U≡set

  typeType Γ ℓ (`elt e) | yes (A , Γ⊢e∈A) | `sig _ _ | _ | spec =
  
    no $ λ p →
       let (_ , _ , Γ⊢e∈set)  = Γ⊢set∋elt-inv p
           (R  , A↝R , set↝R) = Γ⊢e∈-unique Γ⊢e∈A Γ⊢e∈set
           R≡set              = `set↝*-inv set↝R
           coerce₁            = PEq.subst (Type _ ≡^Con_) R≡set
           coerce₂            = PEq.subst (λ p → Type p ≡^Con p) (PEq.sym R≡set)
       in case coerce₁ (spec (R , A↝R , coerce₂ (`set _))) of λ ()

  typeType Γ ℓ (`elt e) | yes (A , Γ⊢e∈A) | `pi _ _  | _ | spec =
  
    no $ λ p →
       let (_ , _ , Γ⊢e∈set)  = Γ⊢set∋elt-inv p
           (R  , A↝R , set↝R) = Γ⊢e∈-unique Γ⊢e∈A Γ⊢e∈set
           R≡set              = `set↝*-inv set↝R
           coerce₁            = PEq.subst (Type _ ≡^Con_) R≡set
           coerce₂            = PEq.subst (λ p → Type p ≡^Con p) (PEq.sym R≡set)
       in case coerce₁ (spec (R , A↝R , coerce₂ (`set _))) of λ ()

  typeType Γ ℓ (`elt e) | yes (A , Γ⊢e∈A) | `nat     | _ | spec =
  
    no $ λ p →
       let (_ , _ , Γ⊢e∈set)  = Γ⊢set∋elt-inv p
           (R  , A↝R , set↝R) = Γ⊢e∈-unique Γ⊢e∈A Γ⊢e∈set
           R≡set              = `set↝*-inv set↝R
           coerce₁            = PEq.subst (Type _ ≡^Con_) R≡set
           coerce₂            = PEq.subst (λ p → Type p ≡^Con p) (PEq.sym R≡set)
       in case coerce₁ (spec (R , A↝R , coerce₂ (`set _))) of λ ()

  typeType Γ ℓ (`elt e) | yes (A , Γ⊢e∈A) | `elt _   | _ | spec =
  
    no $ λ p →
       let (_ , _ , Γ⊢e∈set)  = Γ⊢set∋elt-inv p
           (R  , A↝R , set↝R) = Γ⊢e∈-unique Γ⊢e∈A Γ⊢e∈set
           R≡set              = `set↝*-inv set↝R
           coerce₁            = PEq.subst (Type _ ≡^Con_) R≡set
           coerce₂            = PEq.subst (λ p → Type p ≡^Con p) (PEq.sym R≡set)
       in case coerce₁ (spec (R , A↝R , coerce₂ (`set _))) of λ ()

  typeType Γ ℓ (`elt e) | no ¬p = no (¬p ∘ ,_ ∘ proj₂ ∘ proj₂ ∘ Γ⊢set∋elt-inv)


  -- TYPE CHEKING

  typeCheck Γ A (`typ B) with whnf A | yieldsReduct A | uncoversHead A
  ... | `set ℓ | A↝*set | spec with typeType Γ (↑ ℓ) B
  ... | yes p = yes (expandCheck A↝*set (`typ p))
  ... | no ¬p =

    no $ λ Γ⊢A∋typB →
       let (ℓ′ , A↝set , Γ⊢set∋B) = Γ⊢A∋typ-inv Γ⊢A∋typB
           (R , set↝R , set′↝R)   = confluence A↝set A↝*set
           ℓ≡ℓ′                   = `set-inj $ PEq.trans (PEq.sym $ `set↝*-inv set↝R) (`set↝*-inv set′↝R)
           coerce                 = PEq.subst (Γ ⊢set_∋ B) $ PEq.cong ↑_ ℓ≡ℓ′
       in ¬p (coerce Γ⊢set∋B)

  typeCheck Γ A (`typ B) | `sig _ _ | _ | sp = no (λ p → case sp (, proj₁ (proj₂ (Γ⊢A∋typ-inv p)) , `set _) of λ ())
  typeCheck Γ A (`typ B) | `pi _ _  | _ | sp = no (λ p → case sp (, proj₁ (proj₂ (Γ⊢A∋typ-inv p)) , `set _) of λ ())
  typeCheck Γ A (`typ B) | `nat     | _ | sp = no (λ p → case sp (, proj₁ (proj₂ (Γ⊢A∋typ-inv p)) , `set _) of λ ())
  typeCheck Γ A (`typ B) | `elt _   | _ | sp = no (λ p → case sp (, proj₁ (proj₂ (Γ⊢A∋typ-inv p)) , `set _) of λ ())


  typeCheck Γ A (`lam b) with whnf A | yieldsReduct A | uncoversHead A
  ... | `pi S T | A↝*ΠST | _ with typeCheck (Γ ∙⟩ S) T b
  ... | yes p = yes (expandCheck A↝*ΠST (`lam p))
  ... | no ¬p = no $ λ p →
                     let ((P , Q) , A↝*ΠPQ , Γ∙⟩P⊢Q∋b)      = Γ⊢A∋λb-inv p
                         (B , (ΠST↝*B , ΠPQ↝*B))            = confluence A↝*ΠST A↝*ΠPQ
                         ((E , F) , eqEF , redEF₁ , redEF₂) = `pi↝*-inv ΠPQ↝*B
                         ((G , H) , eqGH , redGH₁ , redGH₂) = `pi↝*-inv ΠST↝*B
                     in ¬p $ ExpandTyping.lemma∋ (pure _ (λ _ → done) , redGH₁)
                           $ expandCheck redGH₂
                           $ uncurry (PEq.subst₂ (λ S T → _ ∙⟩ S ⊢ T ∋ _)) (`pi-inj $ PEq.trans (sym eqEF) eqGH)
                           $ ReduceTyping.lemma∋ (pure _ (λ _ → done) , redEF₁) redEF₂ Γ∙⟩P⊢Q∋b

  typeCheck Γ A (`lam b) | `sig _ _ | _ | spec = no (λ p → case spec (, proj₁ (proj₂ (Γ⊢A∋λb-inv p)) , `pi) of λ ())
  typeCheck Γ A (`lam b) | `nat     | _ | spec = no (λ p → case spec (, proj₁ (proj₂ (Γ⊢A∋λb-inv p)) , `pi) of λ ())
  typeCheck Γ A (`lam b) | `set _   | _ | spec = no (λ p → case spec (, proj₁ (proj₂ (Γ⊢A∋λb-inv p)) , `pi) of λ ())
  typeCheck Γ A (`lam b) | `elt _   | _ | spec = no (λ p → case spec (, proj₁ (proj₂ (Γ⊢A∋λb-inv p)) , `pi) of λ ())


  typeCheck Γ A (`per a b) with whnf A | yieldsReduct A | uncoversHead A
  ... | `sig S T | A↝*ΣST | _ with typeCheck Γ S a | typeCheck Γ (Substitution ⊨ T ⟨ `ann a S /0⟩T) b
  ... | yes p₁ | yes p₂ = yes (expandCheck A↝*ΣST (`per p₁ p₂))
  ... | no ¬p₁ | _      =
    no $ λ p → 
         let ((P  , Q) , red , typa , typb)      = Γ⊢A∋a,b-inv p
             (R , ΣST↝R , ΣPQ↝R)                 = confluence A↝*ΣST red
             ((U₁ , V₁) , R≡ΣU₁V₁ , S↝U₁ , T↝V₁) = `sig↝*-inv ΣST↝R
             ((U₂ , V₂) , R≡ΣU₂V₂ , P↝U₂ , Q↝V₂) = `sig↝*-inv ΣPQ↝R
             U₁≡U₂                               = proj₁ $ `sig-inj $ PEq.trans (PEq.sym R≡ΣU₁V₁) R≡ΣU₂V₂
             coerce                              = PEq.subst (_ ⊢_∋ _) (PEq.sym U₁≡U₂) 
         in ¬p₁ $ expandCheck S↝U₁ $ coerce
                $ ReduceTyping.lemma∋ (pure _ (λ _ → done)) P↝U₂ typa

  ... | yes p₁ | no ¬p₂ =
    no $ λ p → 
         let ((P  , Q) , red , typa , typb)      = Γ⊢A∋a,b-inv p
             (R , ΣST↝R , ΣPQ↝R)                 = confluence A↝*ΣST red
             ((U₁ , V₁) , R≡ΣU₁V₁ , S↝U₁ , T↝V₁) = `sig↝*-inv ΣST↝R
             ((U₂ , V₂) , R≡ΣU₂V₂ , P↝U₂ , Q↝V₂) = `sig↝*-inv ΣPQ↝R
             (U₂≡U₁ , V₂≡V₁)                     = `sig-inj $ PEq.trans (PEq.sym R≡ΣU₂V₂) R≡ΣU₁V₁
             patt                                = λ U V → _ ⊢ Substitution ⊨ V ⟨ `ann a U /0⟩T ∋ _
             coerce                              = PEq.subst₂ patt U₂≡U₁ V₂≡V₁
         in ¬p₂ $ expandCheck (mores (subst↝* (_ ∙ `ann a _) T↝V₁) (β↝* V₁ S↝U₁)) $ coerce
                $ ReduceTyping.lemma∋ (pure _ (λ _ → done)) (mores (β↝* Q P↝U₂) (subst↝* (_ ∙ `ann a _) Q↝V₂)) typb

  typeCheck Γ A (`per a b) | `pi _ _ | _ | sp = no (λ p → case sp (, proj₁ (proj₂ (Γ⊢A∋a,b-inv p)) , `sig) of λ ())
  typeCheck Γ A (`per a b) | `nat  | _ | sp = no (λ p → case sp (, proj₁ (proj₂ (Γ⊢A∋a,b-inv p)) , `sig) of λ ())
  typeCheck Γ A (`per a b) | `set _ | _ | sp = no (λ p → case sp (, proj₁ (proj₂ (Γ⊢A∋a,b-inv p)) , `sig) of λ ())
  typeCheck Γ A (`per a b) | `elt _ | _ | sp = no (λ p → case sp (, proj₁ (proj₂ (Γ⊢A∋a,b-inv p)) , `sig) of λ ())


  typeCheck Γ A `zro with whnf A | yieldsReduct A | uncoversHead A
  ... | `nat    | A↝*ℕ  | _ = yes (expandCheck A↝*ℕ `zro)
  ... | `sig _ _  | A↝*ty | spec = no (λ p → case spec (`nat , Γ⊢A∋0-inv p , `nat) of (λ ()))
  ... | `pi  _ _  | A↝*ty | spec = no (λ p → case spec (`nat , Γ⊢A∋0-inv p , `nat) of (λ ()))
  ... | `set _  | A↝*ty | spec = no (λ p → case spec (`nat , Γ⊢A∋0-inv p , `nat) of (λ ()))
  ... | `elt _ | A↝*ty | spec = no (λ p → case spec (`nat , Γ⊢A∋0-inv p , `nat) of (λ ()))


  typeCheck Γ A (`suc a) with whnf A | yieldsReduct A | uncoversHead A
  ... | `nat   | A↝*ℕ  | _ with typeCheck Γ `nat a
  ... | yes p = yes (expandCheck A↝*ℕ (`suc p))
  ... | no ¬p = no (¬p ∘ Γ⊢A∋Sm-inv′)
  typeCheck Γ A (`suc a) | `sig _ _  | A↝*ty | spec = no (λ p → case spec (, Γ⊢A∋Sm-inv p , `nat) of (λ ()))
  typeCheck Γ A (`suc a) | `pi  _ _  | A↝*ty | spec = no (λ p → case spec (, Γ⊢A∋Sm-inv p , `nat) of (λ ()))
  typeCheck Γ A (`suc a) | `set _  | A↝*ty | spec = no (λ p → case spec (, Γ⊢A∋Sm-inv p , `nat) of (λ ()))
  typeCheck Γ A (`suc a) | `elt _  | A↝*ty | spec = no (λ p → case spec (, Γ⊢A∋Sm-inv p , `nat) of (λ ()))



  typeCheck Γ A (`emb e) with typeInfer Γ e
  ... | yes p = {!!}
  ... | no ¬p = no (¬p ∘ Γ⊢A∋emb-inv)


  -- TYPE INFERENCE


  -- Γ ⊢ `var k ∈ Γ ‼ k
  typeInfer Γ (`var k)   = yes $ map id `var $ typeInferVar Γ k

  -- Γ ⊢ A ∋ t
  -------------------------------
  -- Γ ⊢ `ann t A ∈ A
  typeInfer Γ (`ann t A) with typeType Γ ω A | typeCheck Γ A t
  ... | yes Γ⊢set∋A | yes Γ⊢A∋t = yes (A , `ann Γ⊢set∋A Γ⊢A∋t)
  ... | no ¬Γ⊢set∋A | _         = no (¬Γ⊢set∋A ∘ proj₁ ∘ Γ⊢anntA∈A-inv ∘ proj₂)
  ... | yes Γ⊢set∋A | no ¬Γ⊢A∋t = no (¬Γ⊢A∋t   ∘ proj₂ ∘ Γ⊢anntA∈A-inv ∘ proj₂)

  -- Γ ⊢ e ∈ A    A ↝* `pi S T   Γ ⊢ S ∋ u
  -----------------------------------------
  -- Γ ⊢ `app e u ∈ T ⟨ u /0⟩
  typeInfer Γ (`app e u) with typeInfer Γ e
  ... | no ¬p = no $ λ p → let ((S , T) , typ , _) = Γ⊢appeu∈T-inv (proj₂ p) in ¬p (`pi S T , typ)
  ... | yes (A , Γ⊢e∈A) with whnf A | yieldsReduct A | uncoversHead A
  ... | `pi S T | A↝*ΠST | _ with typeCheck Γ S u
  ... | yes prf = yes (Substitution ⊨ T ⟨ `ann u S /0⟩T , `app (reduceInfer A↝*ΠST Γ⊢e∈A) prf)
  ... | no ¬prf =
  
    no $ uncurry $ λ B Γ⊢app∈B →
       let ((P , Q) , Γ⊢e∈ΠPQ , Γ⊢Q∋u)           = Γ⊢appeu∈T-inv Γ⊢app∈B
           (ΠUV , A↝ΠUV , ΠPQ↝ΠUV)               = Γ⊢e∈-unique Γ⊢e∈A Γ⊢e∈ΠPQ
           ((U , V) , ΠUV≡ΠUV , P↝U , Q↝V)       = `pi↝*-inv ΠPQ↝ΠUV
           (ΠXY , ΠST↝ΠXY , ΠUV↝ΠXY)             = confluence A↝*ΠST A↝ΠUV
           ((X₁ , Y₁) , ΠXY≡ΠX₁Y₁ , S↝X₁ , T↝Y₁) = `pi↝*-inv ΠST↝ΠXY
           ((X₂ , Y₂) , ΠXY≡ΠX₂Y₂ , U↝X₂ , V↝Y₂) = `pi↝*-inv $ PEq.subst (_[ _↝_ ⟩* ΠXY) ΠUV≡ΠUV ΠUV↝ΠXY
           (X₂≡X₁ , Y₂≡Y₁)                       = `pi-inj $ PEq.trans (PEq.sym ΠXY≡ΠX₂Y₂) ΠXY≡ΠX₁Y₁
           coerce                                = PEq.subst (_ ⊢_∋ _) X₂≡X₁
       in ¬prf $ expandCheck S↝X₁ $ coerce
               $ ReduceTyping.lemma∋ (pure _ (λ _ → done)) (mores P↝U U↝X₂) Γ⊢Q∋u


  typeInfer Γ (`app e u) | yes (A , Γ⊢e∈A) | `sig _ _  | A↝ΣST | spec =

    no $ uncurry $ λ B Γ⊢app∈B →
       let ((P , Q) , Γ⊢e∈ΠPQ , Γ⊢Q∋u)    = Γ⊢appeu∈T-inv Γ⊢app∈B
           (ΠUV , A↝ΠUV , ΠPQ↝ΠUV)        = Γ⊢e∈-unique Γ⊢e∈A Γ⊢e∈ΠPQ
           (R , ΣST↝R , ΠUV↝R)            = confluence A↝ΣST A↝ΠUV
           ((X₁ , Y₁) , R≡ΠX₁Y₁ , _ , _ ) = `pi↝*-inv (mores ΠPQ↝ΠUV ΠUV↝R)
           ((X₂ , Y₂) , R≡ΣX₂Y₂ , _ , _ ) = `sig↝*-inv ΣST↝R
       in case PEq.trans (PEq.sym R≡ΠX₁Y₁) R≡ΣX₂Y₂ of λ ()
    
  typeInfer Γ (`app e u) | yes (A , Γ⊢e∈A) | `nat      | A↝ℕ | spec =

    no $ uncurry $ λ B Γ⊢app∈B →
       let ((P , Q) , Γ⊢e∈ΠPQ , Γ⊢Q∋u)    = Γ⊢appeu∈T-inv Γ⊢app∈B
           (ΠUV , A↝ΠUV , ΠPQ↝ΠUV)        = Γ⊢e∈-unique Γ⊢e∈A Γ⊢e∈ΠPQ
           (R , ℕ↝R , ΠUV↝R)              = confluence A↝ℕ A↝ΠUV
           ((X₁ , Y₁) , R≡ΠX₁Y₁ , _ , _ ) = `pi↝*-inv (mores ΠPQ↝ΠUV ΠUV↝R)
           R≡ℕ                            = `nat↝*-inv ℕ↝R
       in case PEq.trans (PEq.sym R≡ΠX₁Y₁) R≡ℕ of λ ()
       
  typeInfer Γ (`app e u) | yes (A , Γ⊢e∈A) | `set _    | A↝Set | spec =

    no $ uncurry $ λ B Γ⊢app∈B →
       let ((P , Q) , Γ⊢e∈ΠPQ , Γ⊢Q∋u)    = Γ⊢appeu∈T-inv Γ⊢app∈B
           (ΠUV , A↝ΠUV , ΠPQ↝ΠUV)        = Γ⊢e∈-unique Γ⊢e∈A Γ⊢e∈ΠPQ
           (R , Set↝R , ΠUV↝R)            = confluence A↝Set A↝ΠUV
           ((X₁ , Y₁) , R≡ΠX₁Y₁ , _ , _ ) = `pi↝*-inv (mores ΠPQ↝ΠUV ΠUV↝R)
           R≡Set                            = `set↝*-inv Set↝R
       in case PEq.trans (PEq.sym R≡ΠX₁Y₁) R≡Set of λ ()
       
  typeInfer Γ (`app e u) | yes (A , Γ⊢e∈A) | `elt _    | A↝elt | spec =

    no $ uncurry $ λ B Γ⊢app∈B →
       let ((P , Q) , Γ⊢e∈ΠPQ , Γ⊢Q∋u) = Γ⊢appeu∈T-inv Γ⊢app∈B
           (ΠUV , A↝ΠUV , ΠPQ↝ΠUV)     = Γ⊢e∈-unique Γ⊢e∈A Γ⊢e∈ΠPQ
           ((X , Y) , R≡ΠXY , _ , _ )  = `pi↝*-inv ΠPQ↝ΠUV
           coerce                      = PEq.subst (A [ _↝_ ⟩*_) R≡ΠXY
       in case spec (`pi X Y , coerce A↝ΠUV , `pi) of λ ()
       

  typeInfer Γ (`fst e) with typeInfer Γ e
  ... | yes (A , Γ⊢e∈A) with whnf A | yieldsReduct A | uncoversHead A
  ... | `sig S T | A↝*ΣST | _ = yes (S , `fst (reduceInfer A↝*ΣST Γ⊢e∈A))
  
  typeInfer Γ (`fst e) | yes (A , Γ⊢e∈A) | `pi _ _  | _ | spec =
  
    no $ uncurry $ λ B Γ⊢fste∈B →
       let ((P , Q) , Γ⊢e∈ΣPQ)       = Γ⊢fste∈A-inv Γ⊢fste∈B
           (R , A↝R , ΣPQ↝R)         = Γ⊢e∈-unique Γ⊢e∈A Γ⊢e∈ΣPQ
           ((U , V) , R≡ΣPQ , _ , _) = `sig↝*-inv ΣPQ↝R
           coerce                    = PEq.subst (A [ _↝_ ⟩*_) R≡ΣPQ
       in case spec (, coerce A↝R , `sig) of λ ()
  
  typeInfer Γ (`fst e) | yes (A , Γ⊢e∈A) | `set _   | _ | spec =
  
    no $ uncurry $ λ B Γ⊢fste∈B →
       let ((P , Q) , Γ⊢e∈ΣPQ)       = Γ⊢fste∈A-inv Γ⊢fste∈B
           (R , A↝R , ΣPQ↝R)         = Γ⊢e∈-unique Γ⊢e∈A Γ⊢e∈ΣPQ
           ((U , V) , R≡ΣPQ , _ , _) = `sig↝*-inv ΣPQ↝R
           coerce                    = PEq.subst (A [ _↝_ ⟩*_) R≡ΣPQ
       in case spec (, coerce A↝R , `sig) of λ ()

  typeInfer Γ (`fst e) | yes (A , Γ⊢e∈A) | `nat     | _ | spec = 
  
    no $ uncurry $ λ B Γ⊢fste∈B →
       let ((P , Q) , Γ⊢e∈ΣPQ)       = Γ⊢fste∈A-inv Γ⊢fste∈B
           (R , A↝R , ΣPQ↝R)         = Γ⊢e∈-unique Γ⊢e∈A Γ⊢e∈ΣPQ
           ((U , V) , R≡ΣPQ , _ , _) = `sig↝*-inv ΣPQ↝R
           coerce                    = PEq.subst (A [ _↝_ ⟩*_) R≡ΣPQ
       in case spec (, coerce A↝R , `sig) of λ ()

  typeInfer Γ (`fst e) | yes (A , Γ⊢e∈A) | `elt _   | _ | spec =
  
    no $ uncurry $ λ B Γ⊢fste∈B →
       let ((P , Q) , Γ⊢e∈ΣPQ)       = Γ⊢fste∈A-inv Γ⊢fste∈B
           (R , A↝R , ΣPQ↝R)         = Γ⊢e∈-unique Γ⊢e∈A Γ⊢e∈ΣPQ
           ((U , V) , R≡ΣPQ , _ , _) = `sig↝*-inv ΣPQ↝R
           coerce                    = PEq.subst (A [ _↝_ ⟩*_) R≡ΣPQ
       in case spec (, coerce A↝R , `sig) of λ ()

  typeInfer Γ (`fst e) | no ¬p = no (¬p ∘ map (uncurry `sig) id ∘ Γ⊢fste∈A-inv ∘ proj₂)


  typeInfer Γ (`snd e)    with typeInfer Γ e
  ... | yes (A , Γ⊢e∈A) with whnf A | yieldsReduct A | uncoversHead A
  ... | `sig S T | A↝*ΣST | _ = yes (Substitution ⊨ T ⟨ `fst e /0⟩T , `snd (reduceInfer A↝*ΣST Γ⊢e∈A))
  ... | `pi _ _  | red | spec =
  
    no $ uncurry $ λ B Γ⊢snde∈B →
       let ((P , Q) , Γ⊢e∈ΣPQ)             = Γ⊢snde∈A-inv Γ⊢snde∈B
           (R , A↝R , ΣPQ↝R)               = Γ⊢e∈-unique Γ⊢e∈A Γ⊢e∈ΣPQ
           (ΠUV , R↝ΠUV , ΠST↝ΠUV)         = confluence A↝R red
           ((U , V) , ΠUV≡ΠUV , S↝U , T↝V) = `pi↝*-inv ΠST↝ΠUV
           ((U , V) , ΠUV≡ΣUV , P↝U , Q↝V) = `sig↝*-inv (mores ΣPQ↝R R↝ΠUV)
       in case PEq.trans (PEq.sym ΠUV≡ΠUV) ΠUV≡ΣUV of λ ()
   
  ... | `nat     | red | spec =
  
    no $ uncurry $ λ B Γ⊢snde∈B →
       let ((P , Q) , Γ⊢e∈ΣPQ)           = Γ⊢snde∈A-inv Γ⊢snde∈B
           (R , A↝R , ΣPQ↝R)             = Γ⊢e∈-unique Γ⊢e∈A Γ⊢e∈ΣPQ
           (ℕ , R↝ℕ , ℕ↝ℕ)               = confluence A↝R red
           ℕ≡ℕ                           = `nat↝*-inv ℕ↝ℕ
           ((U , V) , ℕ≡ΣUV , P↝U , Q↝V) = `sig↝*-inv (mores ΣPQ↝R R↝ℕ)
       in case PEq.trans (PEq.sym ℕ≡ℕ) ℕ≡ΣUV of λ ()
       
  ... | `set _   | red | spec =
  
    no $ uncurry $ λ B Γ⊢snde∈B →
       let ((P , Q) , Γ⊢e∈ΣPQ)           = Γ⊢snde∈A-inv Γ⊢snde∈B
           (R , A↝R , ΣPQ↝R)             = Γ⊢e∈-unique Γ⊢e∈A Γ⊢e∈ΣPQ
           (S , R↝S , set↝S)             = confluence A↝R red
           S≡set                         = `set↝*-inv set↝S
           ((U , V) , S≡ΣUV , P↝U , Q↝V) = `sig↝*-inv (mores ΣPQ↝R R↝S)
       in case PEq.trans (PEq.sym S≡set) S≡ΣUV of λ ()

  ... | `elt _   | red | spec =
  
    no $ uncurry $ λ B Γ⊢fste∈B →
       let ((P , Q) , Γ⊢e∈ΣPQ)       = Γ⊢snde∈A-inv Γ⊢fste∈B
           (R , A↝R , ΣPQ↝R)         = Γ⊢e∈-unique Γ⊢e∈A Γ⊢e∈ΣPQ
           ((U , V) , R≡ΣPQ , _ , _) = `sig↝*-inv ΣPQ↝R
           coerce                    = PEq.subst (A [ _↝_ ⟩*_) R≡ΣPQ
       in case spec (, coerce A↝R , `sig) of λ ()
  
  typeInfer Γ (`snd e) | no ¬p = no (¬p ∘ map (uncurry `sig) id ∘ Γ⊢snde∈A-inv ∘ proj₂)


  typeInfer Γ (`ind p z s e)
    with typeType (Γ ∙⟩ `nat) ω p
       | typeCheck Γ (Substitution ⊨ p ⟨ `ann `zro `nat /0⟩T) z
       | typeCheck Γ (IH p) s
       | typeInfer Γ e
       
  ... | yes Hp | yes Hz | yes Hs | yes (A , Γ⊢e∈A) with whnf A | yieldsReduct A | uncoversHead A
  ... | `nat     | A↝ℕ   | spec = yes (, `ind Hp Hz Hs (reduceInfer A↝ℕ Γ⊢e∈A))
  ... | `pi _ _  | A↝ΠST | spec =

    no $ uncurry $ λ B Γ⊢ind∈B →
       let (_ , _ , _ , Γ⊢e∈ℕ) = Γ⊢ind∈-inv Γ⊢ind∈B
           (R , A↝R , ℕ↝R)     = Γ⊢e∈-unique Γ⊢e∈A Γ⊢e∈ℕ
           eq                  = `nat↝*-inv ℕ↝R
           coerce              = PEq.subst (A [ _↝_ ⟩*_) eq
       in case spec (`nat , coerce A↝R , `nat) of λ ()
    
  ... | `sig _ _ | A↝ΣST | spec =

    no $ uncurry $ λ B Γ⊢ind∈B →
       let (_ , _ , _ , Γ⊢e∈ℕ) = Γ⊢ind∈-inv Γ⊢ind∈B
           (R , A↝R , ℕ↝R)     = Γ⊢e∈-unique Γ⊢e∈A Γ⊢e∈ℕ
           eq                  = `nat↝*-inv ℕ↝R
           coerce              = PEq.subst (A [ _↝_ ⟩*_) eq
       in case spec (`nat , coerce A↝R , `nat) of λ ()

  ... | `set _   | A↝set | spec =

    no $ uncurry $ λ B Γ⊢ind∈B →
       let (_ , _ , _ , Γ⊢e∈ℕ) = Γ⊢ind∈-inv Γ⊢ind∈B
           (R , A↝R , ℕ↝R)     = Γ⊢e∈-unique Γ⊢e∈A Γ⊢e∈ℕ
           eq                  = `nat↝*-inv ℕ↝R
           coerce              = PEq.subst (A [ _↝_ ⟩*_) eq
       in case spec (`nat , coerce A↝R , `nat) of λ ()

  ... | `elt _   | A↝elt | spec =

    no $ uncurry $ λ B Γ⊢ind∈B →
       let (_ , _ , _ , Γ⊢e∈ℕ) = Γ⊢ind∈-inv Γ⊢ind∈B
           (R , A↝R , ℕ↝R)     = Γ⊢e∈-unique Γ⊢e∈A Γ⊢e∈ℕ
           eq                  = `nat↝*-inv ℕ↝R
           coerce              = PEq.subst (A [ _↝_ ⟩*_) eq
       in case spec (`nat , coerce A↝R , `nat) of λ ()


  typeInfer Γ (`ind p z s e) | no ¬Hp | _ | _ | _ = no (¬Hp ∘ proj₁ ∘ Γ⊢ind∈-inv ∘ proj₂)
  typeInfer Γ (`ind p z s e) | _ | no ¬Hz | _ | _ = no (¬Hz ∘ proj₁ ∘ proj₂ ∘ Γ⊢ind∈-inv ∘ proj₂)
  typeInfer Γ (`ind p z s e) | _ | _ | no ¬Hs | _ = no (¬Hs ∘ proj₁ ∘ proj₂ ∘ proj₂ ∘ Γ⊢ind∈-inv ∘ proj₂)
  typeInfer Γ (`ind p z s e) | _ | _ | _ | no ¬Hq = no (¬Hq ∘ ,_ ∘ proj₂ ∘ proj₂ ∘ proj₂ ∘ Γ⊢ind∈-inv ∘ proj₂)

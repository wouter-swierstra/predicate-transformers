{-# OPTIONS --type-in-type #-}
module RegularLanguage where

open import Prelude
open import Combined hiding (_++_)
open import Maybe

open import Data.Char -- hiding (_==_)
--open import Data.String
String = List Char

module Recursion (I : Set) (O : I → Set) where
  ERec : Effect
  ERec = I , O
  ESRec : PT ERec → EffectSpec
  ESRec pt = es ERec pt

module Nondet where
  -- The type of nondeterministic computation:
  -- at each step, we might give up, or choose between two alternatives.
  data CNondet : Set where
    Fail : Set → CNondet
    Split : CNondet
  RNondet : CNondet -> Set
  RNondet (Fail a) = a
  RNondet (Split) = Bool
  ENondet : Effect
  ENondet = CNondet , RNondet
  PTNondet : PT ENondet
  PTNondet (Fail a) wp = ¬ a
  PTNondet Split wp = Pair (wp True) (wp False)
  ESNondet : EffectSpec
  ESNondet = es ENondet PTNondet

  -- The constructors from `Just do it!'
  fail : ∀ {a n} {Es : Vec n Effect} → Free (ESpec :: ENondet :: Es) a
  fail {a} = Step (FS F0) (Fail a) Pure
  _[]_ : ∀ {a n} {Es : Vec n Effect} → Free (ESpec :: ENondet :: Es) a → Free (ESpec :: ENondet :: Es) a → Free (ESpec :: ENondet :: Es) a
  p [] q = Step (FS F0) Split \c -> if c then p else q

  open Recursion
  record SplitList {a : Set} (xs : List a) : Set where
    constructor splitList
    field
      lhs : List a
      rhs : List a
      cat : xs == lhs ++ rhs

  -continuation : ∀ {a} {xs : List a} (x : a) → SplitList xs → SplitList (x :: xs)
  -continuation x spl = splitList (x :: SplitList.lhs spl) (SplitList.rhs spl) (cong (Cons x) (SplitList.cat spl))
  -- Split the list nondeterministically into two pieces.
  split : ∀ {a n} {Es : Vec n Effect} → (xs : List a) → Free (ESpec :: ENondet :: ERec (List a) SplitList :: Es) (SplitList xs)
  split Nil = Pure (splitList Nil Nil refl)
  split (x :: xs) =
    Pure (splitList Nil (x :: xs) refl)
    []
    (Step (FS (FS F0)) xs λ spl → Pure (-continuation x spl))


-- Syntax of regular expressions.
data Regex : Set where
  Empty : Regex -- The empty language, which doesn't contain the empty string!
  Epsilon : Regex
  Singleton : (c : Char) → Regex
  _∪_ : (l r : Regex) → Regex
  _·_ : (l r : Regex) → Regex
  _* : Regex → Regex

-- Inductively define when a string is in the regular language given by an expression.
data _∈[_] : String → Regex → Set where
  inEpsilon : Nil ∈[ Epsilon ]
  inSingleton : ∀ c → (c :: Nil) ∈[ Singleton c ]
  inUnionL : ∀ xs l r → xs ∈[ l ] → xs ∈[ l ∪ r ]
  inUnionR : ∀ xs l r → xs ∈[ r ] → xs ∈[ l ∪ r ]
  inConcat : ∀ xs ys zs l r → xs == ys ++ zs → ys ∈[ l ] → zs ∈[ r ] → xs ∈[ l · r ]
  inStarNil : ∀ r → Nil ∈[ r * ]
  inStarCons : ∀ xs r → xs ∈[ r · (r *) ] → xs ∈[ r * ]

module Match where
  open Nondet
  open Recursion
  -match-continuation : ∀ xs l r → SplitList xs → Free (ESpec :: ENondet :: ERec String SplitList :: ERec (Pair String Regex) (uncurry _∈[_]) :: vNil) (xs ∈[ l · r ])
  -match-continuation xs l r (splitList ys zs cat) =
    Step (FS (FS (FS F0))) (ys , l) λ ys∈l →
    Step (FS (FS (FS F0))) (zs , r) λ zs∈r →
    Pure (inConcat xs ys zs l r cat ys∈l zs∈r)

  -- Try to prove that the string is in the language.
  -- If this is not the case, the nondeterministic computation fails.
  -- We recurse both on the regex and the string,
  -- so we need them both in the recursive call.
  match : (i : Pair String Regex) → Free (ESpec :: ENondet :: ERec String SplitList :: ERec (Pair String Regex) (uncurry _∈[_]) :: vNil) (uncurry _∈[_] i)
  match (xs , Empty) = fail

  match (Nil , Epsilon) = Pure inEpsilon
  match ((x :: xs) , Epsilon) = fail

  match (Nil , Singleton _) = fail
  match ((x :: Nil) , Singleton c) with x ≟ c
  ... | yes refl = Pure (inSingleton c)
  ... | no _ = fail
  match ((_ :: _ :: _) , Singleton _) = fail

  match (xs , (l ∪ r)) =
    Step (FS (FS (FS F0))) (xs , l) (λ x → Pure (inUnionL xs l r x))
    []
    Step (FS (FS (FS F0))) (xs , r) (λ x → Pure (inUnionR xs l r x))

  match (xs , (l · r)) = Step (FS (FS F0)) xs (-match-continuation xs l r)

  match (Nil , (r *)) = Pure (inStarNil r)
  match (xs@(_ :: _) , (r *)) = Step (FS (FS (FS F0))) (xs , (r · (r *))) λ x →
    Pure (inStarCons xs r x)

  apply-split : ∀ {a} {xs : List a} →
    (P : (xs ys zs : List a) → Set) →
    SplitList xs → Set
  apply-split {a} {xs} P spl = P xs (SplitList.lhs spl) (SplitList.rhs spl)

  pt-split : ∀ {a} → PT (ERec (List a) SplitList)
  pt-split xs wp = (spl : SplitList xs) → wp spl

  split-partially-correct : ∀ {a n} {Es : Vec n EffectSpec} →
    (P : (xs ys zs : List a) → Set) →
    ((xs ys zs : List a) → xs == ys ++ zs → P xs ys zs) →
    (xs ys zs : List a) → WP.wp (ESNondet :: ESRec _ _ pt-split :: Es) (split xs) (apply-split P)
  split-partially-correct P x Nil ys zs = x Nil Nil Nil refl
  split-partially-correct P x (x₁ :: xs) ys zs = (x (x₁ :: xs) Nil (x₁ :: xs) refl) , λ spl → x (x₁ :: xs) (x₁ :: SplitList.lhs spl) (SplitList.rhs spl) (cong (Cons x₁) (SplitList.cat spl))

  -- Specification for match: if xs ∈[ r ] , then match finds a proof.
  -- However, the predicate shouldn't care which proof we find.
  -- (Since match finds all proofs, and derivative-match only one.)
  pt-match : PT (ERec (Pair String Regex) (uncurry _∈[_]))
  pt-match (xs , r) wp = (pf : xs ∈[ r ]) → wp pf

  match-partially-correct : (xs : String) (r : Regex) → xs ∈[ r ] → WP.wp (ESNondet :: ESRec _ _ pt-split :: ESRec _ _ pt-match :: vNil) (match (xs , r)) (const ⊤)
  match-partially-correct .Nil .Epsilon inEpsilon = tt

  match-partially-correct .(c :: Nil) .(Singleton c) (inSingleton c) with c ≟ c
  match-partially-correct .(c :: Nil) .(Singleton c) (inSingleton c) | yes refl = tt
  match-partially-correct .(c :: Nil) .(Singleton c) (inSingleton c) | no ¬p = magic (¬p refl)

  match-partially-correct xs .(l ∪ r) (inUnionL .xs l r pf) = (λ x → tt) , (λ x → tt)
  match-partially-correct xs .(l ∪ r) (inUnionR .xs l r pf) = (λ x → tt) , (λ x → tt)

  match-partially-correct xs .(l · r) (inConcat .xs ys zs l r xs=ys++zs pf pf₁) spl pf' pf'' = tt

  match-partially-correct .Nil .(r *) (inStarNil r) = tt

  match-partially-correct Nil .(r *) (inStarCons .Nil r pf) = tt
  match-partially-correct (x :: xs) .(r *) (inStarCons .(x :: xs) r pf) = λ pf₁ → tt

-- Now we show an alternative matching strategy, using derivatives.
module Derivatives where
  -- First, we need to be able to decide whether the regex matches the empty string.
  matches-empty : (r : Regex) → Dec (Nil ∈[ r ])
  matches-empty Empty = no (λ ())
  matches-empty Epsilon = yes inEpsilon
  matches-empty (Singleton c) = no (λ ())
  matches-empty (l ∪ r) with matches-empty l | matches-empty r
  matches-empty (l ∪ r) | yes p | mr = yes (inUnionL Nil l r p)
  matches-empty (l ∪ r) | no ¬l | yes p = yes (inUnionR Nil l r p)
  matches-empty (l ∪ r) | no ¬l | no ¬r = no (unInUnion ¬l ¬r)
    where
    unInUnion : ∀ {a xs l r} → (xs ∈[ l ] → a) → (xs ∈[ r ] → a) → xs ∈[ l ∪ r ] → a
    unInUnion f g (inUnionL xs l r iu) = f iu
    unInUnion f g (inUnionR xs l r iu) = g iu
  matches-empty (l · r) with matches-empty l | matches-empty r
  matches-empty (l · r) | yes p | yes p' = yes (inConcat Nil Nil Nil l r refl p p')
  matches-empty (l · r) | yes p | no ¬p = no (unInConcatR λ ys zs x x₁ → ¬p (coerce (cong (_∈[ r ]) (Pair.snd (when-++-is-nil ys zs x))) x₁))
    where
    unInConcatR : ∀ {a xs l r} → (∀ ys zs → xs == ys ++ zs → zs ∈[ r ] → a) → xs ∈[ l · r ] → a
    unInConcatR f (inConcat xs ys zs l r x icl icr) = f ys zs x icr
  matches-empty (l · r) | no ¬p | mr = no (unInConcatL λ ys zs x x₁ → ¬p (coerce (cong (_∈[ l ]) (Pair.fst (when-++-is-nil ys zs x))) x₁))
    where
    unInConcatL : ∀ {a xs l r} → (∀ ys zs → xs == ys ++ zs → ys ∈[ l ] → a) → xs ∈[ l · r ] → a
    unInConcatL f (inConcat xs ys zs l r x icl icr) = f ys zs x icl
  matches-empty (r *) = yes (inStarNil r)

  -- The derivative of a regular language (expression) with respect to a character c is
  -- the set of all strings x such that c :: x is in the original language.
  infix 21 d_/d_
  d_/d_ : Regex → Char → Regex
  d Empty /d c = Empty
  d Epsilon /d c = Empty
  d Singleton x /d c with c ≟ x
  ... | yes refl = Epsilon
  ... | no _ = Empty
  d l ∪ r /d c = d l /d c ∪ d r /d c
  d l · r /d c with matches-empty l
  ... | yes _ = (d l /d c · r) ∪ d r /d c
  ... | no _ = d l /d c · r
  d r * /d c = d r /d c · (r *)

  -- Prove that the above definition of the derivative is correct.
  derivative-correct-if : ∀ x xs r → (x :: xs) ∈[ r ] → xs ∈[ d r /d x ]
  derivative-correct-if x xs r (inSingleton c) with c ≟ c
  ... | yes refl = inEpsilon
  ... | no ¬p = magic (¬p refl)
  derivative-correct-if x xs _ (inUnionL .(_ :: _) l r x₁) = inUnionL _ (d l /d x) (d r /d x) (derivative-correct-if x xs l x₁)
  derivative-correct-if x xs _ (inUnionR .(_ :: _) l r x₁) = inUnionR _ (d l /d x) (d r /d x) (derivative-correct-if x xs r x₁)
  derivative-correct-if x xs _ (inConcat .(_ :: _) ys zs l r x₁ x₂ x₃) with matches-empty l
  derivative-correct-if x xs _ (inConcat .(x :: xs) Nil .(x :: xs) l r refl x₂ x₃) | yes p = inUnionR xs ((d l /d x) · r) (d r /d x) (derivative-correct-if x xs r x₃)
  derivative-correct-if x .(ys ++ zs) _ (inConcat .(x :: ys ++ zs) (.x :: ys) zs l r refl x₂ x₃) | yes p = inUnionL (ys ++ zs) _ _ (inConcat (ys ++ zs) ys zs _ _ refl (derivative-correct-if x ys l x₂) x₃)
  derivative-correct-if x xs _ (inConcat .(x :: xs) Nil zs l r x₁ x₂ x₃) | no ¬p = magic (¬p x₂)
  derivative-correct-if x .(ys ++ zs) _ (inConcat .(x :: ys ++ zs) (.x :: ys) zs l r refl x₂ x₃) | no ¬p = inConcat (ys ++ zs) ys zs _ _ refl (derivative-correct-if x ys l x₂) x₃
  derivative-correct-if x xs _ (inStarCons .(x :: xs) r (inConcat .(x :: xs) Nil .(x :: xs) .r .(r *) refl x₂ x₃)) = derivative-correct-if x xs (r *) x₃
  derivative-correct-if x .(ys ++ zs) _ (inStarCons .(x :: ys ++ zs) r (inConcat .(x :: ys ++ zs) (.x :: ys) zs .r .(r *) refl x₂ x₃)) = inConcat (ys ++ zs) ys zs (d r /d x) (r *) refl (derivative-correct-if x ys r x₂) x₃
  derivative-correct-onlyIf : ∀ x xs r → xs ∈[ d r /d x ] → (x :: xs) ∈[ r ]
  derivative-correct-onlyIf x xs Empty ()
  derivative-correct-onlyIf x xs Epsilon ()
  derivative-correct-onlyIf x xs (Singleton c) pf with x ≟ c
  derivative-correct-onlyIf x .Nil (Singleton .x) inEpsilon | yes refl = inSingleton x
  derivative-correct-onlyIf x xs (Singleton c) () | no ¬p
  derivative-correct-onlyIf x xs (l ∪ r) (inUnionL .xs .(d l /d x) .(d r /d x) pf) = inUnionL (x :: xs) l r (derivative-correct-onlyIf x xs l pf)
  derivative-correct-onlyIf x xs (l ∪ r) (inUnionR .xs .(d l /d x) .(d r /d x) pf) = inUnionR (x :: xs) l r (derivative-correct-onlyIf x xs r pf)
  derivative-correct-onlyIf x xs (l · r) pf with matches-empty l
  derivative-correct-onlyIf x .(ys ++ zs) (l · r) (inUnionL .(ys ++ zs) .((d l /d x) · r) .(d r /d x) (inConcat .(ys ++ zs) ys zs .(d l /d x) .r refl pf pf₁)) | yes p = inConcat (x :: ys ++ zs) (x :: ys) zs l r refl (derivative-correct-onlyIf x ys l pf) pf₁
  derivative-correct-onlyIf x xs (l · r) (inUnionR .xs .((d l /d x) · r) .(d r /d x) pf) | yes p = inConcat (x :: xs) Nil (x :: xs) l r refl p (derivative-correct-onlyIf x xs r pf)
  derivative-correct-onlyIf x .(ys ++ zs) (l · r) (inConcat .(ys ++ zs) ys zs .(d l /d x) .r refl pf pf₁) | no ¬p = inConcat (x :: ys ++ zs) (x :: ys) zs l r refl (derivative-correct-onlyIf x ys l pf) pf₁
  derivative-correct-onlyIf x xs (r *) (inConcat .xs ys zs .(d r /d x) .(r *) x₁ pf pf₁) = inStarCons (x :: xs) r (inConcat (x :: xs) (x :: ys) zs r (r *) (cong (x ::_) x₁) (derivative-correct-onlyIf x ys r pf) pf₁)


-- Use the derivative to find a match.
module DerivativeMatch where
  open Nondet
  open Recursion
  open Match
  open Derivatives

  wp : ∀ {I O} {a} →
    PT (ERec I O) →
    Free (ESpec :: ENondet :: ERec I O :: vNil) a →
    (a → Set) → Set
  wp {I} {O} pt = WP.wp (ESNondet :: ESRec I O pt :: vNil)

  derivative-match : (i : Pair String Regex) → Free (ESpec :: ENondet :: ERec String SplitList :: ERec (Pair String Regex) (uncurry _∈[_]) :: vNil) (uncurry _∈[_] i)
  derivative-match (Nil , r) with matches-empty r
  ... | yes p = Pure p
  ... | no ¬p = fail
  derivative-match ((x :: xs) , r) = Step (FS (FS (FS F0))) (xs , (d r /d x)) λ xs∈dr/dx →
    Pure (derivative-correct-onlyIf x xs r xs∈dr/dx)

  -- We claim that derivative-match is a refinement of match.
  -- Since match might give multiple different proofs
  -- where derivative-match only gives one,
  -- this is the direction we can prove in the all-semantics.
  -- For the exists-semantics, we can prove the other direction.
  match-⊑-dmatch : ∀ xs r P → WP.wp (ESNondet :: ESRec _ _ pt-split :: ESRec _ _ pt-match :: vNil) (match (xs , r)) P → WP.wp (ESNondet :: ESRec _ _ pt-split :: ESRec _ _ pt-match :: vNil) (derivative-match (xs , r)) P
  match-⊑-dmatch Nil Empty P pf = pf
  match-⊑-dmatch (x :: xs) Empty P pf = λ ()
  match-⊑-dmatch Nil Epsilon P pf = pf
  match-⊑-dmatch (x :: xs) Epsilon P pf = λ ()
  match-⊑-dmatch Nil (Singleton c) P pf = pf
  match-⊑-dmatch (x :: Nil) (Singleton c) P pf pf' with x ≟ c
  match-⊑-dmatch (x :: Nil) (Singleton .x) P pf inEpsilon | yes refl = pf
  match-⊑-dmatch (x :: Nil) (Singleton c) P pf () | no ¬p
  -- Although both cases end up in contradiction,
  -- we have to check why: either c != x or the remainder is too long.
  match-⊑-dmatch (x :: _ :: _) (Singleton c) P pf with x ≟ c
  match-⊑-dmatch (x :: _ :: _) (Singleton .x) P pf | yes refl = λ ()
  match-⊑-dmatch (x :: _ :: _) (Singleton c) P pf | no ¬p = λ ()
  match-⊑-dmatch Nil (l ∪ r) P (fst , snd) with matches-empty l | matches-empty r
  match-⊑-dmatch Nil (l ∪ r) P (fst , snd) | yes p | mr = fst p
  match-⊑-dmatch Nil (l ∪ r) P (fst , snd) | no ¬p | yes p = snd p
  match-⊑-dmatch Nil (l ∪ r) P (fst , snd) | no ¬p | no ¬p₁ = λ x → unInUnion ¬p ¬p₁ x
    where
    unInUnion : ∀ {a xs l r} → (xs ∈[ l ] → a) → (xs ∈[ r ] → a) → xs ∈[ l ∪ r ] → a
    unInUnion f g (inUnionL xs l r iu) = f iu
    unInUnion f g (inUnionR xs l r iu) = g iu
  match-⊑-dmatch (x :: xs) (l ∪ r) P (fst , snd) (inUnionL .xs .(d l /d x) .(d r /d x) pf') = fst (derivative-correct-onlyIf x xs l pf')
  match-⊑-dmatch (x :: xs) (l ∪ r) P (fst , snd) (inUnionR .xs .(d l /d x) .(d r /d x) pf') = snd (derivative-correct-onlyIf x xs r pf')
  match-⊑-dmatch Nil (l · r) P pf with matches-empty l | matches-empty r
  match-⊑-dmatch Nil (l · r) P pf | yes p | yes p₁ = pf (splitList Nil Nil refl) p p₁
  match-⊑-dmatch Nil (l · r) P pf | yes p | no ¬p = unInConcatR λ ys zs Nil=ys++zs zs∈r → ¬p (coerce (cong (_∈[ r ]) (Pair.snd (when-++-is-nil ys zs Nil=ys++zs))) zs∈r)
    where
    unInConcatR : ∀ {a xs l r} → (∀ ys zs → xs == ys ++ zs → zs ∈[ r ] → a) → xs ∈[ l · r ] → a
    unInConcatR f (inConcat xs ys zs l r x icl icr) = f ys zs x icr
  match-⊑-dmatch Nil (l · r) P pf | no ¬p | _ = unInConcatL λ ys zs Nil=ys++zs ys∈l → ¬p (coerce (cong (_∈[ l ]) (Pair.fst (when-++-is-nil ys zs Nil=ys++zs))) ys∈l)
    where
    unInConcatL : ∀ {a xs l r} → (∀ ys zs → xs == ys ++ zs → ys ∈[ l ] → a) → xs ∈[ l · r ] → a
    unInConcatL f (inConcat xs ys zs l r x icl icr) = f ys zs x icl
  match-⊑-dmatch (x :: xs) (l · r) P pf pf' with matches-empty l
  match-⊑-dmatch (x :: .(ys ++ zs)) (l · r) P pf (inUnionL .(ys ++ zs) .((d l /d x) · r) .(d r /d x) (inConcat .(ys ++ zs) ys zs .(d l /d x) .r refl pf' pf'')) | yes p = pf (splitList (x :: ys) zs refl) (derivative-correct-onlyIf x ys l pf') pf''
  match-⊑-dmatch (x :: xs) (l · r) P pf (inUnionR .xs .((d l /d x) · r) .(d r /d x) pf') | yes p = pf (splitList Nil (x :: xs) refl) p (derivative-correct-onlyIf x xs r pf')
  match-⊑-dmatch (x :: .(ys ++ zs)) (l · r) P pf (inConcat .(ys ++ zs) ys zs .(d l /d x) .r refl pf' pf'') | no ¬p = pf (splitList (x :: ys) zs refl) (derivative-correct-onlyIf x ys l pf') pf''
  match-⊑-dmatch Nil (r *) P pf = pf
  match-⊑-dmatch (x :: xs) (r *) P pf (inConcat .xs ys zs .(d r /d x) .(r *) x₁ pf' pf'') = pf (inConcat (x :: xs) (x :: ys) zs r (r *) (cong (_::_ x) x₁) (derivative-correct-onlyIf x ys r pf') pf'')

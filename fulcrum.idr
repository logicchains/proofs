-- Local Variables:
-- idris-load-packages: ("contrib")
-- End:
module Main
import Data.ZZ
import Data.Vect
import ZZMinimum

%default total

sum : Vect n ZZ -> ZZ
sum [] = 0
sum (x::xs) = x + sum(xs)

sumL : List ZZ -> ZZ
sumL [] = 0
sumL (x::xs) = x + sumL(xs)

sumlSubSumr : Vect n ZZ -> Vect m ZZ -> ZZ
sumlSubSumr v1 v2 = sum v1 - sum v2

fcSimpleHelper : Vect n ZZ -> Vect m ZZ -> Vect (S n) ZZ
fcSimpleHelper [] acc  = [sumlSubSumr acc []]
fcSimpleHelper l@(h::t) acc  = sumlSubSumr acc l :: fcSimpleHelper t (h::acc)

fcSimpleHelperRightConsIsSum : (v: ZZ) -> (y:_) -> (xs:_) -> fcSimpleHelper xs (v::y) = fcSimpleHelper xs [v + sum(y)]
fcSimpleHelperRightConsIsSum v y [] = rewrite plusZeroRightNeutralZ (plusZ (plusZ v (sum y)) (Pos 0)) in Refl
fcSimpleHelperRightConsIsSum v y (x::xs) = rewrite fcSimpleHelperRightConsIsSum x (v::y) xs in 
                                            rewrite fcSimpleHelperRightConsIsSum x [plusZ v (sum y)] xs in 
                                            rewrite plusZeroRightNeutralZ (plusZ v (sum y)) in Refl

||| The idea here is to prove a simple version of the function is isometric to the more complicated, efficient one, then reason in terms of the simple version
fcSimple : Vect n ZZ -> Vect (S n) ZZ
fcSimple [] = [0]
fcSimple l@(h::t) = sumlSubSumr [] l :: fcSimpleHelper t [h]

fcComplexHelper : Vect n ZZ -> ZZ -> Vect n ZZ
fcComplexHelper [] _ = []
fcComplexHelper rest@(h::t) acc = let here = h + h + acc in here :: fcComplexHelper t here

||| This is the complex version of the function, running in just O(n) time.
fcComplex : Vect n ZZ -> Vect (S n) ZZ
fcComplex [] = [0]
fcComplex l@(h::t) = let all = sumlSubSumr [] l in all :: fcComplexHelper l all

helpersSame : (x:_) -> (xs:_) -> x - sum xs :: fcComplexHelper xs (x - sum xs) = fcSimpleHelper xs [x]
helpersSame v [] = rewrite plusZeroRightNeutralZ v in
                   rewrite plusZeroRightNeutralZ v in Refl
helpersSame v (x::xs) = rewrite plusZeroRightNeutralZ v in 
                             rewrite fcSimpleHelperRightConsIsSum x [v] xs in 
                             rewrite plusZeroRightNeutralZ v in 
                             rewrite plusCommutativeZ v (- (x + sum xs)) in 
                             rewrite negateDistributesPlus x (sum xs) in 
                             rewrite plusAssociativeZ (x + x) ((-x) + (- sum xs)) v in 
                             rewrite plusAssociativeZ (x + x) (-x) (-(sum xs)) in 
                             rewrite sym $ plusAssociativeZ x x (-x) in 
                             rewrite plusNegateInverseLZ x in 
                             rewrite plusZeroRightNeutralZ x in 
                             rewrite plusCommutativeZ (x - sum xs) v in 
                             rewrite sym $ helpersSame (x + v) xs in 
                             rewrite plusAssociativeZ v x (-(sum xs)) in 
                             rewrite plusCommutativeZ v x in Refl

simpleComplexIso : (v: Vect _ _) -> fcComplex v = fcSimple v
simpleComplexIso [] = Refl
simpleComplexIso (x :: xs) = rewrite plusZeroLeftNeutralZ (-(x + sum xs)) in 
                                 rewrite negateDistributesPlus x (sum xs) in 
                                 rewrite plusAssociativeZ (x + x) (-x) (-(sum xs)) in
                                 rewrite sym $ plusAssociativeZ x x (-x) in 
                                 rewrite plusNegateInverseLZ x in 
                                 rewrite plusZeroRightNeutralZ x in 
                                 rewrite helpersSame x xs in Refl

||| Here we should rewrite with simpleComplexIso, so we apply the complex version but return a proof that the minimum is or is not present for the simple version.
||| How to stop it unfolding before rewriting?
findMinimalFulcrum : (v: Vect _ _) -> Either (dupMin ** NoMinimum (fcSimple v) dupMin) (minn ** HasMinimum (fcSimple v) minn)
--findMinimalFulcrum v = let fulcrums = rewrite simpleComplexIso v in delay (fcComplex v) in ?huh-- findMin fulcums
findMinimalFulcrum v = findMin (fcSimple v)

toListV : Vect _ a -> List a
toListV [] = []
toListV (x::xs) = x::(toListV xs)

sumsSame: (xs: Vect _ _) -> sum xs = sumL (toListV xs)
sumsSame [] = Refl
sumsSame (x :: xs) =  rewrite sumsSame xs in Refl

||| Here we define a version of fc that's as close as possible to the spec, then prove this is equivalent to indexing into the result of fcSimple
fcSpec : (n:Nat) -> Vect _ ZZ -> ZZ
fcSpec n v = sumL (take n (toListV v)) - sumL (drop n (toListV v))

indexN : (i: Nat) -> (len: Nat) -> Vect len elem -> (LT i len) -> elem
indexN Z _     (x::xs) _ = x
indexN (S k) _ [] p = absurd p
indexN Z _     [] p = absurd p
indexN (S k) (S len) (x::xs) p = indexN k len xs (fromLteSucc p)

indexN0 : (x: _) -> (y: Vect _ _) -> (p: _) -> indexN 0 (S n) (fcSimpleHelper y [x]) p = sumlSubSumr [x] y
indexN0 _ [] _ = Refl
indexN0 _ (x :: xs) _ = Refl

fcSimpleHelperLemma : (k: Nat) -> (x, y: ZZ) -> (y: Vect _ _) -> (p: _) -> x + (sum (take k y)) - (sum (drop k y)) = indexN k _ (fcSimpleHelper y [x]) p
fcSimpleHelperLemma Z x y v p = rewrite indexN0 x v p in Refl
fcSimpleHelperLemma (S k) x y v p = ?fcSimpleHelperLemma_rhs_1

||| Here we're trying to prove that indexing into the result of fcSimple is equivalent to the spec.
fcSimpleMeetsSpec : (n: Nat) -> (v: Vect (S len) ZZ) -> (inBounds: _) -> fcSpec n v = indexN n _ (fcSimple v) inBounds
fcSimpleMeetsSpec Z [x] _ = Refl
fcSimpleMeetsSpec Z (x::y::xs) _ = rewrite sumsSame xs in Refl
fcSimpleMeetsSpec (S k) (x::y) inBounds = ?fcSimplRe --rewrite fcSimpleMeetsSpec k xs in Refl

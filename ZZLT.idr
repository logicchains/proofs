-- Local Variables:
-- idris-load-packages: ("contrib")
-- End:

import Data.ZZ

%default total
export
data LTZ : ZZ -> ZZ -> Type where
  PosZLT : LTZ (Pos 0) (Pos (S n))
  LTNegZ : LTZ (NegS (S n)) (NegS 0)
  NegLTPos : LTZ (NegS m) (Pos n)
  NegLTSuc : LTZ (NegS m) (NegS n) -> LTZ (NegS (S m)) (NegS (S n))
  PosLTSuc : LTZ (Pos m) (Pos n) -> LTZ (Pos (S m)) (Pos (S n))

Uninhabited (Pos 0 = Pos (S n)) where
  uninhabited Refl impossible

Uninhabited (Pos (S n) = Pos 0) where
  uninhabited Refl impossible

Uninhabited (NegS 0 = NegS (S n)) where
  uninhabited Refl impossible

Uninhabited (NegS (S n) = NegS 0) where
  uninhabited Refl impossible


posSuccNotLTZZero : Not (Pos (S m) `LTZ` (Pos 0))
posSuccNotLTZZero PosZLT impossible

posZeroNotLTZZero : Not ((Pos 0) `LTZ` (Pos 0))
posZeroNotLTZZero PosZLT impossible

negZeroNotLTZZero : Not ((NegS 0) `LTZ` (NegS 0))
negZeroNotLTZZero LTNegZ impossible

negSuccNotLTZZero : Not (NegS 0 `LTZ` (NegS (S m)))
negSuccNotLTZZero LTNegZ impossible

posNotLTNeg : Not ((Pos n) `LTZ` (NegS m))
posNotLTNeg NegLTPos impossible

fromLteSuccPos : (Pos (S m) `LTZ` Pos (S n)) -> ((Pos m) `LTZ` (Pos n))
fromLteSuccPos (PosLTSuc x) = x

fromLteSuccNeg : (NegS (S m) `LTZ` NegS (S n)) -> ((NegS m) `LTZ` (NegS n))
fromLteSuccNeg (NegLTSuc x) = x

export 
isLTZ : (m, n : ZZ) -> Dec (m `LTZ` n)
isLTZ (NegS Z) (NegS Z) = No negZeroNotLTZZero
isLTZ (Pos Z) (Pos Z) = No posZeroNotLTZZero
isLTZ (NegS _) (Pos _) = Yes NegLTPos
isLTZ (Pos _) (NegS _) = No posNotLTNeg
isLTZ (Pos Z) (Pos (S x)) = Yes PosZLT
isLTZ (Pos (S x)) (Pos Z) = No posSuccNotLTZZero
isLTZ (NegS (S x)) (NegS Z) = Yes LTNegZ 
isLTZ (NegS Z) (NegS (S x)) = No negSuccNotLTZZero
isLTZ (NegS (S x)) (NegS (S y)) with (isLTZ (assert_smaller (NegS (S x)) (NegS x)) (assert_smaller (NegS (S y)) (NegS y)))
  isLTZ (NegS (S x)) (NegS (S y)) | (Yes prf) = Yes $ NegLTSuc prf
  isLTZ (NegS (S x)) (NegS (S y)) | (No contra) = No (contra . fromLteSuccNeg)
isLTZ (Pos (S x)) (Pos (S y)) with (isLTZ (assert_smaller (Pos (S x)) (Pos x)) (assert_smaller (Pos (S y)) (Pos y)))
  isLTZ (Pos (S x)) (Pos (S y)) | (Yes prf) = Yes $ PosLTSuc prf
  isLTZ (Pos (S x)) (Pos (S y)) | (No contra) = No (contra . fromLteSuccPos)

export 
ltzTransitive : LTZ m n -> LTZ n o -> LTZ m o
ltzTransitive NegLTPos (PosLTSuc x) = NegLTPos
ltzTransitive NegLTPos PosZLT = NegLTPos
ltzTransitive (NegLTSuc x) LTNegZ = LTNegZ
ltzTransitive (NegLTSuc x) NegLTPos = NegLTPos
ltzTransitive (NegLTSuc x) (NegLTSuc y) = NegLTSuc $ ltzTransitive x y
ltzTransitive (PosLTSuc x) (PosLTSuc y) = PosLTSuc $ ltzTransitive x y
ltzTransitive PosZLT (PosLTSuc _) = PosZLT
ltzTransitive LTNegZ NegLTPos = NegLTPos

ltzPosSuccBack : LTZ (Pos (S x)) (Pos (S y)) -> LTZ (Pos x) (Pos y)
ltzPosSuccBack (PosLTSuc x) = x

notLtzPosSuccBack : Not (LTZ (Pos (S x)) (Pos (S y))) -> Not (LTZ (Pos x) (Pos y))
notLtzPosSuccBack contra = (\ p => contra $ PosLTSuc p)

ltzNegSuccBack : LTZ (NegS (S x)) (NegS (S y)) -> LTZ (NegS x) (NegS y)
ltzNegSuccBack (NegLTSuc x) = x

notLtzNegSuccBack : Not (LTZ (NegS (S x)) (NegS (S y))) -> Not (LTZ (NegS x) (NegS y))
notLtzNegSuccBack contra = (\ p => contra $ NegLTSuc p)

ltzPosInj : (x, y: Nat) -> (Pos x) = (Pos y) -> x = y
ltzPosInj x _ Refl = Refl

ltzNegInj : (x, y: Nat) -> (NegS x) = (NegS y) -> x = y
ltzNegInj x _ Refl = Refl

ltzSucPosAlsoEq : (x, y: Nat) -> (Pos x) = (Pos y) -> (Pos (S x)) = Pos ((S y))
ltzSucPosAlsoEq x y prf = rewrite (ltzPosInj x y prf) in Refl

ltzSucNegAlsoEq : (x, y: Nat) -> (NegS x) = (NegS y) -> (NegS (S x)) = NegS ((S y))
ltzSucNegAlsoEq x y prf = rewrite (ltzNegInj x y prf) in Refl

bothNotLtAreEq : (x, y: ZZ) -> Not (LTZ x y) -> Not (LTZ y x) -> x = y
bothNotLtAreEq (Pos Z) (Pos Z) _ _ = Refl
bothNotLtAreEq (Pos Z) (Pos (S k)) xNLtY _ = absurd $ xNLtY PosZLT 
bothNotLtAreEq (Pos Z) (NegS k) _ yNLtX = absurd $ yNLtX NegLTPos
bothNotLtAreEq (Pos (S k)) (Pos Z) _ yNLtX = absurd $ yNLtX PosZLT
bothNotLtAreEq a@(Pos (S k)) b@(Pos (S j)) xNLtY yNLtX = let subOneEq = bothNotLtAreEq (assert_smaller a (Pos k)) (assert_smaller b (Pos j)) (notLtzPosSuccBack xNLtY) (notLtzPosSuccBack yNLtX) in ltzSucPosAlsoEq k j subOneEq
bothNotLtAreEq (Pos (S k)) (NegS j) _ yNLtX = absurd $ yNLtX NegLTPos
bothNotLtAreEq (NegS k) (Pos Z) xNLtY _ = absurd $ xNLtY NegLTPos
bothNotLtAreEq (NegS k) (Pos (S j)) xNLtY _ = absurd $ xNLtY NegLTPos
bothNotLtAreEq (NegS (S k)) (NegS Z) xNLtY yNLtX = absurd $ xNLtY LTNegZ 
bothNotLtAreEq (NegS Z) (NegS Z) _ _ = Refl
bothNotLtAreEq (NegS Z) (NegS (S n)) _ yNLtX = absurd $ yNLtX LTNegZ
bothNotLtAreEq a@(NegS (S k)) b@(NegS (S j)) xNLtY yNLtX = let subOneEq = bothNotLtAreEq (assert_smaller a (NegS k)) (assert_smaller b (NegS j)) (notLtzNegSuccBack xNLtY) (notLtzNegSuccBack yNLtX) in ltzSucNegAlsoEq k j subOneEq

public export
data CmpRes : ZZ -> ZZ -> Type where
  IsLT : (x, y: ZZ) -> LTZ x y -> CmpRes x y
  IsEQ : (x, y: ZZ) -> x = y -> CmpRes x y
  IsGT : (x, y: ZZ) -> LTZ y x -> CmpRes x y

export
compareZ : (x: ZZ) -> (y: ZZ) -> CmpRes x y
compareZ x y with (isLTZ x y)
  compareZ x y | (Yes xLtY) = IsLT x y xLtY
  compareZ x y | (No xNLtY) with (isLTZ y x)
    compareZ x y | (No _) | (Yes yLtX) = IsGT x y yLtX
    compareZ x y | (No xNLtY) | (No yNLtX) = IsEQ x y (bothNotLtAreEq x y xNLtY yNLtX)


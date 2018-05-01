-- Local Variables:
-- idris-load-packages: ("contrib")
-- End:

module ZZMinimum

import Data.ZZ
import Data.Vect
import ZZLT

%default total

mutual
  export
  data HasMinimum : Vect n ZZ -> ZZ -> Type where
    MinSing : (x: ZZ) -> HasMinimum [x] x
    MinConsLT : (x: ZZ) -> HasMinimum xs min -> LTZ x min -> HasMinimum (x::xs) x
    MinConsGT : (x: ZZ) -> HasMinimum xs min -> LTZ min x -> HasMinimum (x::xs) min
    NoMinConsLT : (x: ZZ) -> NoMinimum xs min -> LTZ x min -> HasMinimum (x::xs) x
  export
  data NoMinimum : Vect n ZZ -> ZZ -> Type where
    MinConsEq : (x: ZZ) -> HasMinimum xs min -> (x = min) -> NoMinimum (x::xs) min
    NoMinConsGT : (x: ZZ) -> NoMinimum xs min -> LTZ min x -> NoMinimum (x::xs) min
    NoMinConsEq : (x: ZZ) -> NoMinimum xs min -> (x = min) -> NoMinimum (x::xs) min

export
findMin : (v: Vect (S n) ZZ) -> Either (dupMin ** NoMinimum v dupMin) (minn ** HasMinimum v minn)
findMin [x] = Right (x ** MinSing x)
findMin (x::x2::xs) = case findMin (x2::xs) of
  Right (y ** okay) =>  case compareZ x y of
    IsLT x y xLtY => Right (x ** MinConsLT x okay xLtY)
    IsEQ x y xEqY => Left (y ** MinConsEq x okay xEqY)
    IsGT x y yLtX => Right (y ** MinConsGT x okay yLtX)   
  Left (y ** notOkay) =>  case compareZ x y of
    IsLT x y xLtY => Right (x ** NoMinConsLT x notOkay xLtY)
    IsEQ x y xEqY => Left (y ** NoMinConsEq x notOkay xEqY)
    IsGT x y yLtX => Left (y ** NoMinConsGT x notOkay yLtX)     

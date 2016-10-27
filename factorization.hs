{-# LANGUAGE KindSignatures, DataKinds, TypeFamilies, TypeOperators, UndecidableInstances,
             MultiParamTypeClasses, FlexibleInstances, FlexibleContexts, PolyKinds #-}

{-
 - Brute force solution to a bonus problem in MATH 4020.
 - Determines the factors of the polynomial x^10 - 1 in Z_11.
 - Silvio Mayolo
 -}

import GHC.TypeLits
import Data.Function
import Data.Ratio
import Data.Maybe
import Control.Monad

type family And (a :: Bool) (b :: Bool) where
    And 'False b = 'False
    And 'True  b = b

type family Not (a :: Bool) where
    Not 'True  = 'False
    Not 'False =  'True

type family Monus a b where
    Monus 0 b = 0
    Monus b 0 = b
    Monus a b = Monus (a - 1) (b - 1)

type family a / b where
    0 / b = 0
    a / b = 1 + (a `Monus` b) / b

type family a == b where
    a == a = 'True
    a == b = 'False

type Divides a b = (((b / a) * a) == b)

type family Prime' (p :: Nat) (a :: Nat) where
    Prime' p 1 = 'True
    Prime' p n = (Not (Divides n p)) `And` (Prime' p (n - 1))

class Prime (p :: Nat) (x :: Bool)

instance (2 <= p, p1 ~ (p - 1), Prime' p p1 ~ x) => Prime p x

newtype ZN (n :: Nat) = ZN Integer

newtype Poly a = Poly [a]
    deriving (Eq, Show)

unPoly :: Poly a -> [a]
unPoly (Poly a) = a

normalize :: (Num a, Eq a) => Poly a -> Poly a
normalize (Poly xs) = Poly $ reverse (dropWhile (== 0) $ reverse xs)

-- Here, degree is the number of coefficients. No, that's not how any rational mathematician
-- defines polynomial degree, but for the purposes of this program it does its job.
degree :: (Num a, Eq a) => Poly a -> Int
degree = length . unPoly

-- May not return what you expect if the polynomial is not normalized.
leadingTerm :: Num a => Poly a -> Poly a
leadingTerm (Poly []) = Poly []
leadingTerm (Poly xs) = Poly $ (0 <$ init xs) ++ [last xs]

leadingCoef :: Num a => Poly a -> a
leadingCoef (Poly []) = 0
leadingCoef (Poly xs) = last xs

cpoly :: a -> Poly a
cpoly = Poly . pure

line :: Num a => Poly a
line = simpleNth 1

simpleNth :: Num a => Int -> Poly a
simpleNth n = Poly $ replicate n 0 ++ [1]

znRepr :: KnownNat n => ZN n -> Integer
znRepr zn@(ZN n0) = n0 `mod` natVal zn

instance KnownNat n => Eq (ZN n) where
    (==) = (==) `on` znRepr

instance KnownNat n => Show (ZN n) where
    show = show . znRepr

instance KnownNat n => Num (ZN n) where
    ZN a + ZN b = ZN $ a + b
    ZN a * ZN b = ZN $ a * b
    negate (ZN a) = ZN (- a)
    abs = id
    signum _ = 1
    fromInteger = ZN

instance (Prime p 'True, KnownNat p) => Fractional (ZN p) where
    fromRational frac = ZN (numerator frac) / ZN (denominator frac)
    recip zp = let p = natVal zp
                   m = znRepr zp
               in if zp == ZN 1 then
                      1
                  else
                      ZN $ m ^ (p - 2)

instance Num a => Num (Poly a) where
    Poly  []    + Poly  []    = Poly []
    Poly  []    + Poly  y     = Poly y
    Poly  x     + Poly  []    = Poly x
    Poly (x:xs) + Poly (y:ys) = Poly $ (x + y) : unPoly (Poly xs + Poly ys)
    Poly [] * Poly _ = Poly []
    Poly (x:xs) * Poly y = let firstTerm = (map (x *) y)
                               Poly restTerm = Poly xs * Poly y
                           in Poly firstTerm + Poly (0 : restTerm)
    abs (Poly xs) = Poly $ map abs xs
    signum (Poly xs) = Poly $ map signum xs
    negate (Poly xs) = Poly $ map negate xs
    fromInteger n = Poly [fromInteger n]

-- The divisor should be normalized and nonzero. The dividend has no such restriction.
(./) :: (Eq a, Fractional a) => Poly a -> Poly a -> (Poly a, Poly a)
_ ./ 0 = error "division by zero"
n ./ m | degree n < degree m = (0, n)
n ./ m = let multiplicand = simpleNth (degree n - degree m) * cpoly (leadingCoef n / leadingCoef m)
             n' = normalize $ n - multiplicand * m
             (q, r) = n' ./ m
         in (q + multiplicand, r)

deriv :: Num a => Poly a -> Poly a
deriv (Poly []) = Poly []
deriv (Poly xs) = Poly . tail $ zipWith (*) (map fromInteger [0..]) xs

-- Produces normalized polynomials of (mathematical) degree exactly n - 1 with leading coefficient 1
allPoly :: KnownNat n => Integer -> [Poly (ZN n)]
allPoly n = let result = Poly <$> allPoly' modn n
                modn = natVal (head . unPoly . head $ result) -- All lazy evaluated so the argument is ignored
            in result
    where allPoly' _    0 = pure []
          allPoly' _    1 = pure [ZN 1] -- Leading coefficient is one
          allPoly' modn m = (:) <$> map ZN [0..modn-1] <*> allPoly' modn (m - 1)

bruteForceReduce :: (KnownNat p, Fractional (ZN p)) => Poly (ZN p) -> [Poly (ZN p)]
bruteForceReduce poly = bfr poly 2
    where deg :: Int
          deg = degree poly
          bfr :: (KnownNat p0, Fractional (ZN p0)) => Poly (ZN p0) -> Int -> [Poly (ZN p0)]
          bfr poly1 n | 2 * (n - 1) > deg - 1 = [poly1]
          bfr poly1 n = maybe (bfr poly1 $ n + 1) id (tryDeg poly1 n)
          tryDeg :: (KnownNat p1, Fractional (ZN p1)) => Poly (ZN p1) -> Int -> Maybe [Poly (ZN p1)]
          tryDeg poly1 n = listToMaybe $ do
                             poly2 <- allPoly $ toInteger n
                             let (q, r) = poly1 ./ poly2
                             guard $ normalize r == Poly []
                             pure (bruteForceReduce poly2 ++ bruteForceReduce q)

main :: IO ()
main = print (bruteForceReduce (Poly [-1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1]) :: [Poly (ZN 11)])

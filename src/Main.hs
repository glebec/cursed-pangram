{-# LANGUAGE PatternSynonyms #-}

module Main where

import Prelude hiding (not, and, or, succ, fst, snd, pred)

main :: IO ()
main = do
  print $ lcToInt $ normalize :$ n96 .+ n1

-- Resources include TAPL (Pierce)

-- * The untyped λ-calculus via de Bruijn indices

-- | Syntax: variables, lambdas, and applications.
data LC
  = Var Int
  | Lam LC
  | App LC LC
  deriving Eq

-- Some synonyms for convenience

λ :: LC -> LC
λ = Lam

pattern l :$ r = App l r
infixl 1 :$

v0, v1, v2 :: LC
v0 = Var 0
v1 = Var 1
v2 = Var 2
v3 = Var 3
v4 = Var 4

-- Custom Show for more legible output
instance Show LC where
  showsPrec p e =
    let showConst = showParen (p > 10) . showString
     in case e of
          -- Hard-coded instances for convenience
          Lam (Lam (Var 1)) -> showConst "T~K"
          Lam (Lam (Var 0)) -> showConst "F~KI"
          -- Generic display
          Var i -> showParen (p > 10) $ showString "Var " . showsPrec 11 i
          Lam t -> showParen (p > 10) $ showString "Lam " . showsPrec 11 t
          App t1 t2 ->
            showParen (p > 5) $
            showsPrec 5 t1 .
            showString " :$ " .
            showsPrec 6 t2

-- | β-reduction
beta :: LC -> LC
beta term = case term of
  var@(Var _) -> var
  Lam body -> Lam $ beta body
  App t1 t2 ->
    let t1' = beta t1
        t2' = beta t2
     in case t1' of
          Lam body -> body'
            where
              subd = substitute 0 (shift 1 0 t2) body
              body' = beta $ shift (-1) 0 subd
          _ -> App t1' t2'

β :: LC -> LC
β = beta

-- | [s ↦ i]t
-- Replace index i with exp s in term t
substitute :: Int -> LC -> LC -> LC
substitute ix new term = case term of
  var@(Var ix') | ix == ix' -> new
                | otherwise -> var
  Lam body -> Lam $ substitute (ix + 1) (shift 1 0 new) body
  App t1 t2 -> App (substitute ix new t1) (substitute ix new t2)

-- | ↑(d/c)t
-- Shift indices > c by d places in term t
shift :: Int -> Int -> LC -> LC
shift amt floor term = case term of
  var@(Var ix) | ix >= floor -> Var $ ix + amt
               | otherwise -> var
  Lam body -> Lam $ shift amt (floor + 1) body
  App t1 t2 -> App (shift amt floor t1) (shift amt floor t2)

-- * Encodings of programming concepts in the lambda calculus

-- ** Combinators

i, k, ki, c :: LC
-- | I = \x . x
-- aka `id`
i = λ $ v0
-- | K = \a . \b . a
-- aka `const`
k = λ . λ $ v1
-- | KI = \a . \b . b
ki = λ . λ $ v0 -- k :$ i
-- | C = \f . \a . \b . f b a
-- aka `flip`
c = λ . λ . λ $ v2 :$ v0 :$ v1

-- ** Church-Encoded Booleans

t, f, not, and, or, beq :: LC
-- | T = K
t = k
-- | F = KI
f = ki
-- | NOT = C
not = c
-- | AND = \p . \q . p q p
and = λ . λ $ v1 :$ v0 :$ v1
-- | OR = \p . \q . p p q
or = λ . λ $ v1 :$ v1 :$ v0
-- | BEQ = \p . \q . p q (not q)
beq = λ . λ $ v1 :$ v0 :$ (not :$ v0)

-- Infix helpers

(.&&), (.||), (&=) :: LC -> LC -> LC
p .|| q = or :$ p :$ q
p .&& q = and :$ p :$ q
p &= q = beq :$ p :$ q
infixl 2 .||
infixl 3 .&&
infixl 4 &=

exampleBoolTest :: LC
exampleBoolTest = β $ (t .&& f) &= (f .|| f) -- T~K

-- ** Composition

-- | compose = \f . \g . \x . f (g x)
compose :: LC
compose = λ . λ . λ $ v2 :$ (v1 :$ v0)

-- | compose2 = \f . \g . \x . \y . f (g x y)
-- aka `blackbird`
compose2 :: LC
compose2 = compose :$ compose :$ compose

-- Infix helpers

(∘), (.:) :: LC -> LC -> LC
f ∘ g = compose :$ f :$ g
f .: g = compose2 :$ f :$ g
infixr 9 ∘
infixr 9 .:

-- ** Church-Encoded Naturals

n0, n1, n2, n3, n4, n5, succ :: LC
-- | N0 = \f . \x . x
n0 = f
-- | N1 = \f . \x . f x
n1 = λ . λ $ v1 :$ v0
-- | SUCC = \n . (\f . \x . f (n f x))
--        = \n . \f . f ∘ n f
succ = β $ λ . λ $ v0 ∘ (v1 :$ v0)
-- And some others for fun.
n2 = succ :$ n1
n3 = succ :$ n2
n4 = succ :$ n3
n5 = succ :$ n4

testNat :: LC
testNat = β $ (succ :$ n2 :$ not :$ t) &= f -- T~K

-- β-reductions are for optimization.

add, mul, pow :: LC
-- | ADD = \n . \m . \f . \x . n f (m f x) = n f ∘ m f
add = β $ λ . λ . λ $ (v2 :$ v0) ∘ (v1 :$ v0)
-- | MUL = \n . \m . \f . \x . n (m f) x
--       = \n . \m . \f . n (m f)
--       = \n . \m . n ∘ m
--       = ∘
mul = compose
-- | POW = \n . \m . \f . \x . (m n) f x
--       = \n . \m . m n
--       = C I
pow = β $ c :$ i

(.+), (.*), (.^) :: LC -> LC -> LC
n .+ m = add :$ n :$ m
n .* m = mul :$ n :$ m
n .^ m = pow :$ n :$ m
infixl 6 .+
infixl 7 .*
infixl 8 .^

-- (3^2 + 1 = 10) * not $ T = F
testMath :: LC
testMath = β $ n3 .^ n2 .+ n1 :$ not :$ t -- T~K

-- ** Data Structures

-- | VIREO = \a . \b . (\f . f a b)
vireo, pair :: LC
vireo = λ . λ . λ $ v0 :$ v2 :$ v1
pair = vireo

-- | FST = \p . p K
fst :: LC
fst = λ $ v0 :$ k

-- | SND = \p . p (KI)
snd :: LC
snd = λ $ v0 :$ ki

-- Infix helpers
(.&.) :: LC -> LC -> LC
x .&. y = pair :$ x :$ y

-- ** Enabling Numeric Subtraction and (In)Equality

-- | EQ0 = \n . n (K F) T
eq0 :: LC
eq0 = β $ λ $ v0 :$ (k :$ f) :$ t

-- | PHI = \p . PAIR (SND p) (SUCC (SND p))
phi :: LC
phi = β $ λ $ (snd :$ v0) .&. (succ :$ (snd :$ v0))

testPhi :: LC
testPhi = let n2n0 = n2 .&. n0 in
  β $
    (eq0 :$ (fst :$ (phi :$ n2n0)))
    .&& (snd :$ (phi :$ n2n0)) :$ not :$ f -- T~K

-- | PRED = \n . FST (n PHI (PAIR N0 N0))
pred :: LC
pred = β $ λ $ fst :$ (v0 :$ phi :$ (n0 .&. n0))

-- | SUB = \n . \k . k PRED n
sub :: LC
sub = λ . λ $ v0 :$ pred :$ v1

(.-) :: LC -> LC -> LC
n .- m = sub :$ n :$ m
infixl 6 .-

testSub :: LC
testSub = β $ (eq0 :$ n5 .- n5) .&& (not ∘ eq0 :$ n5 .- n4) -- T~K

-- | LEQ = \n . \k . EQ0 (SUB n k)
leq :: LC
leq = β $ λ . λ $ eq0 :$ v1 .- v0

(.<=) :: LC -> LC -> LC
n .<= k = leq :$ n :$ k
infix 4 .<=

-- | GT = \n . \k . NOT (LEQ n k)
gt :: LC
gt = β $ not .: leq

(.>) :: LC -> LC -> LC
n .> k = gt :$ n :$ k
infix 4 .>

-- | EQ = \n . \k . AND (LEQ n k) (LEQ k n)
eq :: LC
eq = λ . λ $ (v1 .<= v0) .&& (v0 .<= v1)

(#=) :: LC -> LC -> LC
n #= k = eq :$ n :$ k
infix 4 #=

testEq :: LC
testEq = β $ (succ :$ n5) #= (n2 .* (succ :$ n2)) -- T~K

-- ** Recursion

-- | Y = \f . (\x . f (x x)) (\x . f (x x))
y :: LC
y = λ $ (λ $ v1 :$ (v0 :$ v0)) :$ (λ $ v1 :$ (v0 :$ v0))

-- ** Lists

-- Could do nested pairs, but IMHO Scott encoding is nicer.
-- data List a = Nil | a : List a

-- | NIL =            \n . \c . n
--   CONS = \h . \t . \n . \c . c h t
nil, cons :: LC
nil = k
cons = λ . λ . λ . λ $ v0 :$ v3 :$ v2

(.::) :: LC -> LC -> LC
h .:: t = cons :$ h :$ t
infixr 5 .::

testList :: LC
testList = β $ ((n1 .:: n2 .:: n3 .:: nil) :$ f :$ t) #= n1

-- | map :: (a -> b) -> [a] -> [b]
map :: LC
map = y :$
  ( λ -- \map (Y-enabled recursion)
  . λ -- \mapper
  . λ -- \list (Scott encoding)
  $ v0
    :$ nil -- nil case (nil -> nil)
    :$     -- cons case
      ( λ -- \head
      . λ -- \tail
      $ (v3 :$ v1) .:: (v4 :$ v3 :$ v0) -- map head and cons to recursed tail
      )
  )

-- | Check if a given LC nat is in the LC list.
-- Nat -> List -> Bool
containsNat :: LC
containsNat = y :$
  ( λ -- \containsNat (Y-enabled recursion)
  . λ -- \n
  $ λ -- \list (Scott encoding)
    v0
    :$ f -- nil case
    :$   -- cons case
      ( λ -- \head
      . λ -- \tail
      $ (v1 #= v3) :$ t :$ (v4 :$ v3 :$ v0) -- if ==, true, else recurse
      )
  )

testContainsNat :: LC
testContainsNat = β $ containsNat :$ n3 :$ (n1 .:: n2 .:: n3 .:: nil) -- T~K

-- * Cursed Pangram

intToLC :: Int -> LC
intToLC 0 = n0
intToLC 10 = β $ n5 .* n2
intToLC 50 = β $ n5 .* n5 .* n2
intToLC n = β $ succ :$ (intToLC $ n - 1)

lcToInt :: LC -> Int
lcToInt = go 0 where
  go i f | β (eq0 :$ f) == t = i
         | otherwise = go (i + 1) (β $ pred :$ f)

strToLC :: String -> LC
strToLC "" = nil
strToLC (c:cs) = (intToLC . fromEnum $ c) .:: strToLC cs

testStrToLC :: LC
testStrToLC = β $ containsNat :$ (n5 .* n4 .* n3 .+ n5) :$ (strToLC "BBBBBBA") -- T~K

n32 :: LC
n32 = β $ n2 .^ n5

n96 :: LC
n96 = β $ n32 .* n3

-- | Convert lowercase to uppercase. If N > 96, subtract 32.
normalize :: LC
normalize = λ $ (v0 .> n96) :$ v0 .- n32 :$ v0

{-
check to see if an input contains all the letters in the
alphabet, case-insensitive. The input string may contain
non-alphabetic letters.

ASCII upper: 65–90
ASCII lower: 97–122

1. convert to LC list of Nats
1. filter for alphabet?
1. map normalize
1. find each letter
-}

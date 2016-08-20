{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE OverlappingInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE OverlappingInstances #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE OverlappingInstances #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE OverlappingInstances #-}
{-# LANGUAGE TemplateHaskell, TypeOperators, MultiParamTypeClasses,
  FlexibleInstances, FlexibleContexts, UndecidableInstances, PolyKinds,
  OverlappingInstances, ConstraintKinds, UnicodeSyntax , DataKinds, ConstraintKinds#-}
--------------------------------------------------------------------------------
-- |
-- Module      :  Examples.Eval
-- Copyright   :  (c) 2011 Patrick Bahr, Tom Hvitved
-- License     :  BSD3
-- Maintainer  :  Tom Hvitved <hvitved@diku.dk>
-- Stability   :  experimental
-- Portability :  non-portable (GHC Extensions)
--
-- Expression Evaluation
--
-- The example illustrates how to use compositional data types to implement
-- a small expression language, with a sub language of values, and an evaluation
-- function mapping expressions to values.
--
--------------------------------------------------------------------------------

module Examples.CDataTypeALaCarte where

data Fix f = In (f (Fix f ))
fold :: Functor f ⇒ (f c → c) → Fix f → c
fold alg (In x) = alg (fmap (fold alg) x)

data (f :+: g) a = Inl (f a) | Inr (g a)

instance (Functor f, Functor g) => Functor (f :+: g) where
   fmap = undefined

--data Expr = Val Int | Add Expr Expr


data Arith a = Val Int | Add a a deriving Functor
type Expr = Fix Arith 


data Mult a = Mult a a deriving Functor
type Expr' = Fix (Arith :+: Mult)


class Eval f where
  evalAlg :: f Int → Int


instance Eval Arith where
  evalAlg (Val n) = n
  evalAlg (Add x y) = x + y
instance Eval Mult where
  evalAlg (Mult x y) = x * y

instance (Eval f, Eval g) => Eval (f :+: g) where
  evalAlg = undefined

eval :: (Eval f , Functor f ) ⇒ Fix f → Int
eval = fold evalAlg

eval1 :: Expr → Int
eval1 = eval
eval2 :: Expr' → Int
eval2 = eval

--- generalise to other pattern than :+:
class f :≺: g where
  inj :: f a → g a
  prj :: g a → Maybe (f a)

inject :: (f :≺: g) ⇒ f (Fix g) → Fix g
inject = In . inj
project :: (f :≺: g) ⇒ Fix g → Maybe (f (Fix g))
project (In g) = prj g



instance f :≺: f where
  inj = id
  prj = Just
instance f :≺: (f :+: g) where
  inj = Inl
  prj (Inl f ) = Just f
  prj (Inr _ ) = Nothing
instance (f :≺: g) ⇒ f :≺: (h :+: g) where
  inj = Inr . inj
  prj (Inr g) = prj g
  prj (Inl _) = Nothing



-- how we obtain instances of f :≺: g ? :≺: is defined recursively for the
-- right-hand side of :+:, we only have a non-recursive instance declaration for
-- the left-hand side of :+:


-- Hence :≺: can be characterised syntactically as follows: we have an instance
-- f :≺: g iff g is of the form g1 :+: (. . . :+: (gn−1 :+: gn). . .) and f = gi
-- for some 1 ≤ i ≤ n

-- it's a pb for f1 :+: f2 :≺: f1 :+: f2 :+: f3, each part subsum, but not sum


--- Closed Type families
-------------------------

-- normal TF
type family Element l
type instance Element [a ] = a
type instance Element String = Char

-- closed
type family Curry t where
  Curry ((a, b) → c) = a → b → c
  Curry a = a -- overlapping

-- match not sufficient, required none before it match
-- Curry t does not simplify to t, Curry (s, t) simplify to (s, t)

-- type variables may occur more than once on the left-hand side of equations
type family Prod t where
  Prod (a, a) = Bool → a
  Prod a = a

-- t is isomorphic to Prod t, but results of computations not available during runtime.
--prod2 :: t → Prod t
--prod2 (x , y) = \b → if b then x else y -- fails
--prod2 x = x

-- term level witness
data Ty t t0 where
  IsProd :: Ty (a, a) (Bool → a)
  NotProd :: Ty t t

-- to write term-level, we need to introduce evidence by PM on gadt
-- on selectionne au runtime quelle fonction
prod0 :: Ty t (Prod t) → t → Prod t
prod0 IsProd (x , y) = \b → if b then x else y
prod0 NotProd x = x

-- We can then use a type class to infer the evidence automatically:
class GetTy t t0 where
  getTy :: Ty t t0

instance GetTy (a, a) (Bool → a) where
  getTy = IsProd -- term level found by instance search guided by type level

instance GetTy a a where
  getTy = NotProd


prod :: GetTy t (Prod t) ⇒ t → Prod t -- find type level proof
prod = prod0 getTy -- so you have term, give it to prod0


-- construction of explicit term-level evidence unnecessary as immediately
-- consumed by prod0. Instead, we can use the type class GetTy directly to
-- construct the function prod0 getTy

class GetTy' s t where
  prod0' :: s → t
instance GetTy' (a, a) (Bool → a) where
  prod0' (x , y) = \b → if b then x else y
instance GetTy' a a where
  prod0' x = x
prod' :: GetTy' t (Prod t) ⇒ t → Prod t
prod' = prod0'


-- Subsumption
----------------
type family Or a b where
  Or False False = False
  Or a b = True

type family Elem (e :: * -> *) (f :: * -> *) :: Bool where
  Elem e e = True
  Elem e (l :+: r ) = Or (Elem e l) (Elem e r )
  Elem e f = False

type f :≺≺: g = Elem f g ~ True -- on reifie le match de DTALC

-- above definition only covers one aspect of the original definition of :≺:.
-- The original type class :≺: also provided two functions inj and proj.

data Pos = Here | Left' Pos | Right' Pos
data Res = Found Pos | NotFound

type family Elem2 (e :: * → *) (p :: * → *) :: Res where
  Elem2 e e = Found Here
  Elem2 e (l :+: r ) = Choose (Elem2 e l) (Elem2 e r )
  Elem2 e p = NotFound
type family Choose (l :: Res) (r :: Res) :: Res where
  Choose (Found x ) y = Found (Left' x )
  Choose x (Found y) = Found (Right' y)
  Choose x y = NotFound


data Val' a = Val' Int  deriving Functor
data Add' a = Add' a a deriving Functor
type Arith'  = Val'  :+: Add'


data Proxy a = P
p = P :: Proxy (Val' :≺≺: (Arith' :+: Mult)) -- on peut recurser a gauche

class Subsume (res :: Res) f g where
  inj':: Proxy res -> f a → g a
  prj':: Proxy res -> g a → Maybe (f a)

-- importer Dict et faire Dict (Val' :≺≺: (Arith' :+: Mult))
-- Dict (Elem .. .. sans le ~ True)


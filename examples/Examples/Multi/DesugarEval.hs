{-# LANGUAGE TemplateHaskell, TypeOperators, MultiParamTypeClasses,
  FlexibleInstances, FlexibleContexts, UndecidableInstances, GADTs #-}
--------------------------------------------------------------------------------
-- |
-- Module      :  Examples.Multi.DesugarEval
-- Copyright   :  (c) 2011 Patrick Bahr, Tom Hvitved
-- License     :  BSD3
-- Maintainer  :  Tom Hvitved <hvitved@diku.dk>
-- Stability   :  experimental
-- Portability :  non-portable (GHC Extensions)
--
-- Generalised Compositional Data Types Example: Desugaring + Expression
-- Evaluation.
--
-- The example illustrates how to compose a term homomorphism and an algebra,
-- exemplified via a desugaring term homomorphism and an evaluation algebra.
--
--------------------------------------------------------------------------------

module Examples.Multi.DesugarEval where

import Data.Comp.Multi
import Data.Comp.Multi.Show ()
import Data.Comp.Multi.Derive

-- Signature for values, operators, and syntactic sugar
data Value e l where
  Const  ::        Int -> Value e Int
  Pair   :: e s -> e t -> Value e (s,t)
data Op e l where
  Add, Mult  :: e Int -> e Int   -> Op e Int
  Fst        ::          e (s,t) -> Op e s
  Snd        ::          e (s,t) -> Op e t
data Sugar e l where
  Neg   :: e Int   -> Sugar e Int
  Swap  :: e (s,t) -> Sugar e (t,s)

-- Source position information (line number, column number)
data Pos = Pos Int Int
           deriving Show

-- Signature for the simple expression language
type Sig = Op :+: Value
type SigP = Op :&: Pos :+: Value :&: Pos

-- Signature for the simple expression language, extended with syntactic sugar
type Sig' = Sugar :+: Op :+: Value
type SigP' = Sugar :&: Pos :+: Op :&: Pos :+: Value :&: Pos

-- Derive boilerplate code using Template Haskell (GHC 7 needed)
$(derive [instanceHFunctor, instanceHTraversable, instanceHFoldable,
          instanceHEqF, instanceHShowF, smartConstructors]
         [''Value, ''Op, ''Sugar])

-- Term homomorphism for desugaring of terms
class (HFunctor f, HFunctor g) => Desugar f g where
  desugHom :: TermHom f g
  desugHom = desugHom' . hfmap Hole
  desugHom' :: Alg f (Context g a)
  desugHom' x = appCxt (desugHom x)

instance (Desugar f h, Desugar g h) => Desugar (f :+: g) h where
  desugHom (Inl x) = desugHom x
  desugHom (Inr x) = desugHom x
  desugHom' (Inl x) = desugHom' x
  desugHom' (Inr x) = desugHom' x

instance (Value :<: v, HFunctor v) => Desugar Value v where
  desugHom = simpCxt . inj

instance (Op :<: v, HFunctor v) => Desugar Op v where
  desugHom = simpCxt . inj

instance (Op :<: v, Value :<: v, HFunctor v) => Desugar Sugar v where
  desugHom' (Neg x)  = iConst (-1) `iMult` x
  desugHom' (Swap x) = iSnd x `iPair` iFst x

-- Term evaluation algebra
class Eval f v where
  evalAlg :: Alg f (Term v)

instance (Eval f v, Eval g v) => Eval (f :+: g) v where
  evalAlg (Inl x) = evalAlg x
  evalAlg (Inr x) = evalAlg x

instance (Value :<: v) => Eval Value v where
  evalAlg = inject

instance (Value :<: v) => Eval Op v where
  evalAlg (Add x y)  = iConst $ (projC x) + (projC y)
  evalAlg (Mult x y) = iConst $ (projC x) * (projC y)
  evalAlg (Fst x)    = fst $ projP x
  evalAlg (Snd x)    = snd $ projP x

projC :: (Value :<: v) => Term v Int -> Int
projC v = case project v of Just (Const n) -> n

projP :: (Value :<: v) => Term v (s,t) -> (Term v s, Term v t)
projP v = case project v of Just (Pair x y) -> (x,y)

-- Compose the evaluation algebra and the desugaring homomorphism to an
-- algebra
eval :: Term Sig' :-> Term Value
eval = cata (evalAlg `compAlg` (desugHom :: TermHom Sig' Sig))

-- Example: evalEx = iPair (iConst 2) (iConst 1)
evalEx :: Term Value (Int,Int)
evalEx = eval $ iSwap $ iPair (iConst 1) (iConst 2)
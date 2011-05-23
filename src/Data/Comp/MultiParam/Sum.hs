{-# LANGUAGE TypeOperators, MultiParamTypeClasses, IncoherentInstances,
  FlexibleInstances, FlexibleContexts, GADTs, TypeSynonymInstances,
  ScopedTypeVariables, TemplateHaskell #-}
--------------------------------------------------------------------------------
-- |
-- Module      :  Data.Comp.MultiParam.Sum
-- Copyright   :  (c) 2011 Patrick Bahr, Tom Hvitved
-- License     :  BSD3
-- Maintainer  :  Tom Hvitved <hvitved@diku.dk>
-- Stability   :  experimental
-- Portability :  non-portable (GHC Extensions)
--
-- This module provides the infrastructure to extend signatures.
--
--------------------------------------------------------------------------------

module Data.Comp.MultiParam.Sum
    (
     (:<:),
     (:+:),

     -- * Projections for Signatures and Terms
     proj,
     proj2,
     proj3,
     proj4,
     proj5,
     proj6,
     proj7,
     proj8,
     proj9,
     proj10,
     project,
     project2,
     project3,
     project4,
     project5,
     project6,
     project7,
     project8,
     project9,
     project10,
     deepProject,
     deepProject2,
     deepProject3,
     deepProject4,
     deepProject5,
     deepProject6,
     deepProject7,
     deepProject8,
     deepProject9,
     deepProject10,

     -- * Injections for Signatures and Terms
     inj,
     inj2,
     inj3,
     inj4,
     inj5,
     inj6,
     inj7,
     inj8,
     inj9,
     inj10,
     inject,
     inject2,
     inject3,
     inject4,
     inject5,
     inject6,
     inject7,
     inject8,
     inject9,
     inject10,
     deepInject,
     deepInject2,
     deepInject3,
     deepInject4,
     deepInject5,
     deepInject6,
     deepInject7,
     deepInject8,
     deepInject9,
     deepInject10,

     -- * Injections and Projections for Constants
     injectConst,
     injectConst2,
     injectConst3,
     projectConst,
     injectCxt,
     liftCxt
    ) where

import Prelude hiding (sequence)
import Control.Monad hiding (sequence)
import Data.Comp.MultiParam.Term
import Data.Comp.MultiParam.Algebra
import Data.Comp.MultiParam.Ops
import Data.Comp.MultiParam.Derive.Projections
import Data.Comp.MultiParam.Derive.Injections
import Data.Comp.MultiParam.HDifunctor
import Data.Comp.MultiParam.HDitraversable

$(liftM concat $ mapM projn [2..10])

-- |Project the outermost layer of a term to a sub signature. If the signature
-- @g@ is compound of /n/ atomic signatures, use @project@/n/ instead.
project :: (g :<: f) => NatM Maybe (Cxt h f a b) (g a (Cxt h f a b))
project (Term t) = proj t
project (Hole _) = Nothing
project (Place _) = Nothing

$(liftM concat $ mapM projectn [2..10])

-- | Tries to coerce a term/context to a term/context over a sub-signature. If
-- the signature @g@ is compound of /n/ atomic signatures, use
-- @deepProject@/n/ instead.
deepProject :: (HDitraversable g Maybe Any, g :<: f) => CxtFunM Maybe f g
{-# INLINE deepProject #-}
deepProject = appSigFunM' proj

$(liftM concat $ mapM deepProjectn [2..10])
{-# INLINE deepProject2 #-}
{-# INLINE deepProject3 #-}
{-# INLINE deepProject4 #-}
{-# INLINE deepProject5 #-}
{-# INLINE deepProject6 #-}
{-# INLINE deepProject7 #-}
{-# INLINE deepProject8 #-}
{-# INLINE deepProject9 #-}
{-# INLINE deepProject10 #-}

$(liftM concat $ mapM injn [2..10])

-- |Inject a term where the outermost layer is a sub signature. If the signature
-- @g@ is compound of /n/ atomic signatures, use @inject@/n/ instead.
inject :: (g :<: f) => g a (Cxt h f a b) :-> Cxt h f a b
inject = Term . inj

$(liftM concat $ mapM injectn [2..10])

-- |Inject a term over a sub signature to a term over larger signature. If the
-- signature @g@ is compound of /n/ atomic signatures, use @deepInject@/n/
-- instead.
deepInject :: (HDifunctor g, g :<: f) => CxtFun g f
{-# INLINE deepInject #-}
deepInject = appSigFun inj

$(liftM concat $ mapM deepInjectn [2..10])
{-# INLINE deepInject2 #-}
{-# INLINE deepInject3 #-}
{-# INLINE deepInject4 #-}
{-# INLINE deepInject5 #-}
{-# INLINE deepInject6 #-}
{-# INLINE deepInject7 #-}
{-# INLINE deepInject8 #-}
{-# INLINE deepInject9 #-}
{-# INLINE deepInject10 #-}

{-{-| A variant of 'proj' for binary sum signatures.  -}
proj2 :: forall f g1 g2 a b i. (g1 :<: f, g2 :<: f) => f a b i
      -> Maybe ((g1 :+: g2) a b i)
proj2 x = case proj x of
            Just (y :: g1 a b i) -> Just $ inj y
            _ -> liftM inj (proj x :: Maybe (g2 a b i))

{-| A variant of 'proj' for ternary sum signatures.  -}
proj3 :: forall f g1 g2 g3 a b i. (g1 :<: f, g2 :<: f, g3 :<: f) => f a b i
      -> Maybe ((g1 :+: g2 :+: g3) a b i)
proj3 x = case proj x of
            Just (y :: g1 a b i) -> Just $ inj y
            _ -> case proj x of
                   Just (y :: g2 a b i) -> Just $ inj y
                   _ -> liftM inj (proj x :: Maybe (g3 a b i))

-- |Project the outermost layer of a term to a sub signature.
project :: (g :<: f) => NatM Maybe (Cxt h f a b) (g a (Cxt h f a b))
project (Term t) = proj t
project (Hole _) = Nothing
project (Place _) = Nothing

-- |Project the outermost layer of a term to a binary sub signature.
project2 :: (g1 :<: f, g2 :<: f)
            => NatM Maybe (Cxt h f a b) ((g1 :+: g2) a (Cxt h f a b))
project2 (Term t) = proj2 t
project2 (Hole _) = Nothing
project2 (Place _) = Nothing

-- |Project the outermost layer of a term to a ternary sub signature.
project3 :: (g1 :<: f, g2 :<: f, g3 :<: f)
            => NatM Maybe (Cxt h f a b) ((g1 :+: g2 :+: g3) a (Cxt h f a b))
project3 (Term t) = proj3 t
project3 (Hole _) = Nothing
project3 (Place _) = Nothing

-- | Tries to coerce a term/context to a term/context over a
-- sub-signature.
deepProject :: (HDitraversable g Maybe Any, g :<: f)
             => CxtFunM Maybe f g
deepProject = appSigFunM' proj

-- | This is a variant of 'deepProject' that can be used if the target
-- signature cannot be derived as being a sub-signature of the source
-- signature directly but its decomposition into two summands can.
deepProject2 :: (HDitraversable (g1 :+: g2) Maybe Any, g1 :<: f, g2 :<: f)
              => CxtFunM Maybe f (g1 :+: g2)
deepProject2 = appSigFunM' proj2

-- | This is a variant of 'deepProject' that can be used if the target
-- signature cannot be derived as being a sub-signature of the source
-- signature directly but its decomposition into three summands can.
deepProject3 ::(HDitraversable (g1 :+: g2 :+: g3) Maybe Any, g1 :<: f, g2 :<: f, g3 :<: f)
                 => CxtFunM Maybe f (g1 :+: g2 :+: g3)
deepProject3 = appSigFunM' proj3

{-| A variant of 'inj' for binary sum signatures.  -}
inj2 :: (f1 :<: g, f2 :<: g) => (f1 :+: f2) a b :-> g a b
inj2 (Inl x) = inj x
inj2 (Inr y) = inj y

{-| A variant of 'inj' for ternary sum signatures.  -}
inj3 :: (f1 :<: g, f2 :<: g, f3 :<: g) => (f1 :+: f2 :+: f3) a b :-> g a b
inj3 (Inl x) = inj x
inj3 (Inr y) = inj2 y

-- |Inject a term where the outermost layer is a sub signature.
inject :: (g :<: f) => g a (Cxt h f a b) :-> Cxt h f a b
inject = Term . inj

-- |Inject a term where the outermost layer is a binary sub signature.
inject2 :: (f1 :<: g, f2 :<: g) => (f1 :+: f2) a (Cxt h g a b) :-> Cxt h g a b
inject2 = Term . inj2

-- |Inject a term where the outermost layer is a ternary sub signature.
inject3 :: (f1 :<: g, f2 :<: g, f3 :<: g) => (f1 :+: f2 :+: f3) a (Cxt h g a b)
        :-> Cxt h g a b
inject3 = Term . inj3

-- |Inject a term over a sub signature to a term over larger signature.
deepInject :: (HDifunctor g, g :<: f) => CxtFun g f
deepInject = appSigFun inj

-- |Inject a term over a binary sub signature to a term over larger signature.
deepInject2 :: (HDifunctor (f1 :+: f2), f1 :<: g, f2 :<: g)  => CxtFun (f1 :+: f2) g
deepInject2 = appSigFun inj2

-- |Inject a term over a ternary signature to a term over larger signature.
deepInject3 :: (HDifunctor (f1 :+: f2 :+: f3), f1 :<: g, f2 :<: g, f3 :<: g)
               => CxtFun (f1 :+: f2 :+: f3) g
deepInject3 =  appSigFun inj3-}

injectConst :: (HDifunctor g, g :<: f) => Const g :-> Cxt h f Any a
injectConst = inject . hfmap (const undefined)

injectConst2 :: (HDifunctor f1, HDifunctor f2, HDifunctor g, f1 :<: g, f2 :<: g)
                => Const (f1 :+: f2) :-> Cxt h g Any a
injectConst2 = inject2 . hfmap (const undefined)

injectConst3 :: (HDifunctor f1, HDifunctor f2, HDifunctor f3, HDifunctor g,
                 f1 :<: g, f2 :<: g, f3 :<: g)
                => Const (f1 :+: f2 :+: f3) :-> Cxt h g Any a
injectConst3 = inject3 . hfmap (const undefined)

projectConst :: (HDifunctor g, g :<: f) => NatM Maybe (Cxt h f Any a) (Const g)
projectConst = fmap (hfmap (const (K ()))) . project

{-| This function injects a whole context into another context. -}
injectCxt :: (HDifunctor g, g :<: f) => Cxt h g a (Cxt h f a b) :-> Cxt h f a b
injectCxt (Term t) = inject $ hfmap injectCxt t
injectCxt (Hole x) = x
injectCxt (Place p) = Place p

{-| This function lifts the given functor to a context. -}
liftCxt :: (HDifunctor f, g :<: f) => g a b :-> Cxt Hole f a b
liftCxt g = simpCxt $ inj g

instance (Show (f a b i), Show (g a b i)) => Show ((f :+: g) a b i) where
    show (Inl v) = show v
    show (Inr v) = show v

instance (Ord (f a b i), Ord (g a b i)) => Ord ((f :+: g) a b i) where
    compare (Inl _) (Inr _) = LT
    compare (Inr _) (Inl _) = GT
    compare (Inl x) (Inl y) = compare x y
    compare (Inr x) (Inr y) = compare x y

instance (Eq (f a b i), Eq (g a b i)) => Eq ((f :+: g) a b i) where
    (Inl x) == (Inl y) = x == y
    (Inr x) == (Inr y) = x == y                   
    _ == _ = False
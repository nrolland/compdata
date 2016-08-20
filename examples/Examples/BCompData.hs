{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE DeriveFunctor #-}

{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TemplateHaskell, TypeOperators, MultiParamTypeClasses,
  FlexibleInstances, FlexibleContexts, UndecidableInstances, PolyKinds,
  ConstraintKinds, UnicodeSyntax , DataKinds, ConstraintKinds#-}
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

module Examples.BCompData where

--import Data.Typeable hiding (Proxy)
import Data.Comp.Ops hiding ((:<:))
-- import Examples.CDataTypeALaCarte(Mult)

import Data.Comp.SubsumeCommon

--import Data.Proxy

import GHC.Exts (Constraint)


-- Compdata
-----------

-- on veut parler de sous types f :<: g (construits avec combinateurs g :+: h etc..)
-- on pourrait faire Elem f g ~ True mais ca n'est pas assez, on veut des manipuler des
-- valeurs (des preuves et non des simples proprietes) et avoir par exemple inj : f -> g

-- Donc on renvoit non pas la table de verite de Elem f g, mais la preuve entiere :: Found Pos | NotFound
-- et on passe au niveau des valeurs avec instance Subsume (Found pos) f g
-- Subsume associe selectivement une valeur inj dans le cas Found
-- Plutot que de construire statiquement, nous aurions pu passer par un temoin Gadt pour reconstruire inj

-- data Path f g where
--   HereV  :: Path f f
--   LeftV  :: Path f g -> Path f (g :+: h)
--   RightV :: Path f g -> Path f (h :+: g)
--   SumV   :: Path f g -> Path f' g -> Path (f :+: f') g -- nb : introduce multiple ways to get same proof ?
--                                                        -- Dict n'a pas de coproduit et pour cause..

-- -- fonction getpath comme subsume
-- class GetPath (e :: Emb) (f :: * -> *) (g :: * -> *) where
--   getPath :: Proxy e -> Path f g

-- -- nb : how much of that could be replaced with Dict ? GetPath rendrait a la fois Dict et le path..
-- instance GetPath (Found Here) f f where -- reflexive category  f -> f
--     getPath _ = HereV
-- instance GetPath (Found p) f g => GetPath (Found (Le p)) f (g :+: g') where -- f -> g => f -> g + g' -- union symetrique
--     getPath _ = LeftV $ getPath (P :: Proxy (Found p))
-- instance GetPath (Found p) f g => GetPath (Found (Ri p)) f (g' :+: g) where -- f -> g => f -> g' + g -- comme poset avec Union
--     getPath _ = RightV $ getPath  (P :: Proxy (Found p))                    -- vient de ce que element de la Stone Algebra sont
--                                                                             -- sont fermes par union puisque
-- instance (GetPath (Found p1) f1 g, GetPath (Found p2) f2 g) -- f -> g, f' -> g => f + f' -> g comme poset avec union
--     => GetPath (Found (Sum p1 p2)) (f1 :+: f2) g where
--     getPath _ = SumV (getPath (P :: Proxy (Found p1))) ( getPath (P :: Proxy (Found p2)))



-- term level subsume qui prend un path

inj2 :: Path f g -> f a -> g a
inj2 (HereV       ) fa  = fa
inj2 (LeftV  p    ) fa = Inl . (inj2 p) $ fa
inj2 (RightV p    ) fa = Inr . (inj2 p) $ fa
inj2 (SumV   p1 p2) fa = case fa of Inl f1a -> inj2 p1 f1a; Inr f2a -> inj2 p2 f2a

-- class Subsume (e :: Emb) (f :: * -> *) (g :: * -> *) where
--   inj'  :: Proxy e -> f a -> g a
--   prj'  :: Proxy e -> g a -> Maybe (f a)
-- instance Subsume (Found Here) f f where
--     inj' _ = id
--     prj' _ = Just
-- instance Subsume (Found p) f g => Subsume (Found (Le p)) f (g :+: g') where
--     inj' _ = Inl . inj' (P :: Proxy (Found p))
--     prj' _ (Inl x) = prj' (P :: Proxy (Found p)) x
--     prj' _ _       = Nothing
-- instance Subsume (Found p) f g => Subsume (Found (Ri p)) f (g' :+: g) where
--     inj' _ = Inr . inj' (P :: Proxy (Found p))
--     prj' _ (Inr x) = prj' (P :: Proxy (Found p)) x
--     prj' _ _       = Nothing
-- instance (Subsume (Found p1) f1 g, Subsume (Found p2) f2 g)
--     => Subsume (Found (Sum p1 p2)) (f1 :+: f2) g where
--     inj' _ (Inl x) = inj' (P :: Proxy (Found p1)) x
--     inj' _ (Inr x) = inj' (P :: Proxy (Found p2)) x
--     prj' _ x = case prj' (P :: Proxy (Found p1)) x of
--                  Just y -> Just (Inl y)
--                  _      -> case prj' (P :: Proxy (Found p2)) x of
--                              Just y -> Just (Inr y)
--                              _      -> Nothing



-- Dans compdata on a

type f :<: g = (Subsume (ComprEmb (Elem f g)) f g)  -- preuve + value level fonction inj
inj :: forall f g a . (f :<: g) => f a -> g a -- purement type level
inj = inj' (P :: Proxy (ComprEmb (Elem f g)))


-- Ici on a

-- Elem f g trouve le chemin
-- f :<<: g est un contrainte qui donne acces a une preuve a value level
--type f :<<: g = (GetPath (Elem f g) f g)

-- on peut reconstituer inj -- avec + de calcul au runtime
inj3 :: forall f g a . (f :<<: g)  => f a -> g a
inj3 = inj2 (getPath (P :: Proxy (Elem f g))) 


-- mais surtout on peut avoir le chemin !
--path :: forall f g a . (f :<<: g)  => Path f g
--path = getPath (P :: Proxy (Elem f g))




-- nb : how much of that could be replaced with Dict ? GetPath rendrait a la fois Dict et le path..
-- peut on manipuler les dict et en deduire TC ?

data Dict (p ∷ Constraint) where  Dict ∷ p ⇒ Dict p -- contrainte → terme
newtype p :- q = Sub (p ⇒ Dict q)

hereSub  ::                     ()   :- GetPath (Found Here)        f  f            ; hereSub  = Sub Dict
leftSub  ::  GetPath (Found p) f g   :- GetPath (Found (Le p))      f (g :+: g')    ; leftSub  = Sub Dict
rightSub ::  GetPath (Found p) f g   :- GetPath (Found (Ri p))      f (g':+: g)     ; rightSub = Sub Dict
sumSub   :: (GetPath (Found p1) f1 g,
             GetPath (Found p2) f2 g):- GetPath (Found (Sum p1 p2)) (f1 :+: f2) g   ; sumSub   = Sub Dict



-- (&&&) :: (a :- b) -> (a :- c) -> a :- (b, c)
-- f &&& g = Sub $ Dict \\ f \\ g
-- (\\) ∷ p ⇒ (q ⇒ r) → (p :- q) → r -- modus ponens au niveau terme
-- qr \\ (Sub Dict) = qr


---

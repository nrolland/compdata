module Data.ALaCarte_Test where


import Data.ALaCarte
import Data.ALaCarte.Equality
import Data.ALaCarte.Arbitrary ()
import Data.ALaCarte.Show ()

import Test.Framework
import Test.Framework.Providers.QuickCheck2
import Test.QuickCheck
import Test.Utils

import qualified Data.ALaCarte.Equality_Test


--------------------------------------------------------------------------------
-- Test Suits
--------------------------------------------------------------------------------

main = defaultMain [tests]

tests = testGroup "ALaCarte" [
         Data.ALaCarte.Equality_Test.tests
        ]

--------------------------------------------------------------------------------
-- Properties
--------------------------------------------------------------------------------


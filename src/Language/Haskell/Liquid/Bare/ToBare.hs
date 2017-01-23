-- | This module contains functions that convert things
--   to their `Bare` versions, e.g. SpecType -> BareType etc.

module Language.Haskell.Liquid.Bare.ToBare
  ( -- * Types
    specToBare

    -- * Measures
  , measureToBare
  )
  where

import           DataCon
import           Data.Bifunctor
import           Language.Haskell.Liquid.GHC.Misc
import           Language.Haskell.Liquid.Types
import           Language.Haskell.Liquid.Measure
import           Language.Haskell.Liquid.Types.RefType

--------------------------------------------------------------------------------
measureToBare :: SpecMeasure -> BareMeasure
--------------------------------------------------------------------------------
measureToBare = bimap (fmap specToBare) dataConToBare

dataConToBare :: DataCon -> LocSymbol
dataConToBare = namedLocSymbol

specToBare :: SpecType -> BareType
specToBare = bareOfType . toType

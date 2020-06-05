module Check.TCState.FilterTypes (FilterTypes(..), mapTypes) where

class FilterTypes s where
  filterTypes :: Ord ty' => (ty -> Maybe ty') -> s ty -> s ty'

mapTypes :: (FilterTypes s, Ord ty') => (ty -> ty') -> s ty -> s ty'
mapTypes f = filterTypes (Just . f)


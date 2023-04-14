module Data.Patricia where

import Data.IntSet (IntSet)
import qualified Data.IntSet as IntSet

type Patricia a = IntSet

{-# INLINABLE member #-}
member :: Enum a => a -> Patricia a -> Bool
member x = IntSet.member (fromEnum x)

{-# INLINABLE insert #-}
insert :: Enum a => a -> Patricia a -> Patricia a
insert x = IntSet.insert (fromEnum x)

{-# INLINABLE delete #-}
delete :: Enum a => a -> Patricia a -> Patricia a
delete x = IntSet.delete (fromEnum x)

{-# INLINABLE fromList #-}
fromList :: Enum a => [a] -> Patricia a
fromList = IntSet.fromList . map fromEnum

{-# INLINABLE union #-}
union :: Patricia a -> Patricia a -> Patricia a
union = IntSet.union

{-# INLINABLE intersection #-}
intersection :: Patricia a -> Patricia a -> Patricia a
intersection = IntSet.intersection

{-# INLINABLE difference #-}
difference :: Patricia a -> Patricia a -> Patricia a
difference = IntSet.difference

{-# INLINABLE empty #-}
empty :: Patricia a
empty = IntSet.empty

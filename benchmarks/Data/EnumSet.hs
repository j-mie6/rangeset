{-# LANGUAGE CPP #-}
{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE RoleAnnotations #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE MagicHash #-}
{-# OPTIONS_GHC -Wunused-binds -Wunused-imports #-}
{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}
{-# HLINT ignore "Eta reduce" #-}

-----------------------------------------------------------------------------
-- |
-- Module      :  Data.Set.Internal
-- Copyright   :  (c) Daan Leijen 2002
-- License     :  BSD-style
-- Maintainer  :  libraries@haskell.org
-- Portability :  portable

module Data.EnumSet (
              EnumSet       -- instance Eq
            , Size

            , size
            , member

            , empty
            , singleton
            , insert
            , delete

            , union
            , difference
            , intersection

            , fromList
            ) where

import Prelude hiding (foldr, foldl)
import Data.Bits (shiftL, shiftR)
import qualified Data.Foldable as Foldable
import Control.DeepSeq (NFData(rnf))
import GHC.Exts  ( reallyUnsafePtrEquality#, isTrue#, lazy )

type EnumSet = Set

instance NFData a => NFData (Set a) where
    rnf Tip           = ()
    rnf (Bin _ y l r) = rnf y `seq` rnf l `seq` rnf r


data StrictPair a b = !a :*: !b
infixr 1 :*:

ptrEq :: a -> a -> Bool
ptrEq x y = isTrue# (reallyUnsafePtrEquality# x y)
{-# INLINE ptrEq #-}

infix 4 `ptrEq`

toPair :: StrictPair a b -> (a, b)
toPair (x :*: y) = (x, y)
{-# INLINE toPair #-}


data Set a    = Bin {-# UNPACK #-} !Size {-# UNPACK #-} !Int !(Set a) !(Set a)
              | Tip
type Size     = Int
type role Set nominal

size :: Set a -> Int
size Tip = 0
size (Bin sz _ _ _) = sz
{-# INLINE size #-}

member :: Enum a => a -> Set a -> Bool
member x = go (fromEnum x)
  where
    go !_ Tip = False
    go x (Bin _ y l r) = case compare x y of
      LT -> go x l
      GT -> go x r
      EQ -> True
{-# INLINABLE member #-}

empty  :: Set a
empty = Tip
{-# INLINE empty #-}

singleton :: Int -> Set a
singleton x = Bin 1 x Tip Tip
{-# INLINE singleton #-}

insert :: Enum a => a -> Set a -> Set a
insert x = insertE (fromEnum x)

insertE :: Int -> Set a -> Set a
insertE x0 = go x0 x0
  where
    go :: Int -> Int -> Set a -> Set a
    go orig !_ Tip = singleton (lazy orig)
    go orig !x t@(Bin sz y l r) = case compare x y of
        LT | l' `ptrEq` l -> t
           | otherwise -> balanceL y l' r
           where !l' = go orig x l
        GT | r' `ptrEq` r -> t
           | otherwise -> balanceR y l r'
           where !r' = go orig x r
        EQ | lazy orig `seq` (orig `ptrEq` y) -> t
           | otherwise -> Bin sz (lazy orig) l r
{-# INLINABLE insertE #-}

insertR :: Int -> Set a -> Set a
insertR x0 = go (fromEnum x0) (fromEnum x0)
  where
    go :: Int -> Int -> Set a -> Set a
    go orig !_ Tip = singleton (lazy orig)
    go orig !x t@(Bin _ y l r) = case compare x y of
        LT | l' `ptrEq` l -> t
           | otherwise -> balanceL y l' r
           where !l' = go orig x l
        GT | r' `ptrEq` r -> t
           | otherwise -> balanceR y l r'
           where !r' = go orig x r
        EQ -> t
{-# INLINABLE insertR #-}

delete :: Enum a => a -> Set a -> Set a
delete x = go (fromEnum x)
  where
    go :: Int -> Set a -> Set a
    go !_ Tip = Tip
    go x t@(Bin _ y l r) = case compare x y of
        LT | l' `ptrEq` l -> t
           | otherwise -> balanceR y l' r
           where !l' = go x l
        GT | r' `ptrEq` r -> t
           | otherwise -> balanceL y l r'
           where !r' = go x r
        EQ -> glue l r
{-# INLINABLE delete #-}

union :: Set a -> Set a -> Set a
union t1 Tip  = t1
union t1 (Bin 1 x _ _) = insertR x t1
union (Bin 1 x _ _) t2 = insertE x t2
union Tip t2  = t2
union t1@(Bin _ x l1 r1) t2 = case splitS x t2 of
  (l2 :*: r2)
    | l1l2 `ptrEq` l1 && r1r2 `ptrEq` r1 -> t1
    | otherwise -> link x l1l2 r1r2
    where !l1l2 = l1 `union` l2
          !r1r2 = r1 `union` r2
{-# INLINABLE union #-}

difference :: Set a -> Set a -> Set a
difference Tip _   = Tip
difference t1 Tip  = t1
difference t1 (Bin _ x l2 r2) = case split x t1 of
   (l1, r1)
     | size l1l2 + size r1r2 == size t1 -> t1
     | otherwise -> merge l1l2 r1r2
     where !l1l2 = difference l1 l2
           !r1r2 = difference r1 r2
{-# INLINABLE difference #-}

intersection :: Set a -> Set a -> Set a
intersection Tip _ = Tip
intersection _ Tip = Tip
intersection t1@(Bin _ x l1 r1) t2
  | b = if l1l2 `ptrEq` l1 && r1r2 `ptrEq` r1
        then t1
        else link x l1l2 r1r2
  | otherwise = merge l1l2 r1r2
  where
    !(l2, b, r2) = splitMember x t2
    !l1l2 = intersection l1 l2
    !r1r2 = intersection r1 r2
{-# INLINABLE intersection #-}

fromList :: (Ord a, Enum a) => [a] -> Set a
fromList [] = Tip
fromList [x] = Bin 1 (fromEnum x) Tip Tip
fromList (x0 : xs0) | not_ordered x0 xs0 = fromList' (Bin 1 (fromEnum x0) Tip Tip) xs0
                    | otherwise = go (1::Size) (Bin 1 (fromEnum x0) Tip Tip) xs0
  where
    not_ordered _ [] = False
    not_ordered x (y : _) = x >= y
    {-# INLINE not_ordered #-}

    fromList' t0 xs = Foldable.foldl' ins t0 xs
      where ins t x = insert x t

    go :: (Enum a, Ord a) => Size -> Set a -> [a] -> Set a
    go !_ t [] = t
    go _ t [x] = insertMax (fromEnum x) t
    go s l xs@(x : xss) | not_ordered x xss = fromList' l xs
                        | otherwise = case create s xss of
                            (r, ys, []) -> go (s `shiftL` 1) (link (fromEnum x) l r) ys
                            (r, _,  ys) -> fromList' (link (fromEnum x) l r) ys

    create :: (Enum a, Ord a) => Size -> [a] -> (Set a, [a], [a])
    create !_ [] = (Tip, [], [])
    create s xs@(x : xss)
      | s == 1 = if not_ordered x xss then (Bin 1 (fromEnum x) Tip Tip, [], xss)
                                      else (Bin 1 (fromEnum x) Tip Tip, xss, [])
      | otherwise = case create (s `shiftR` 1) xs of
                      res@(_, [], _) -> res
                      (l, [y], zs) -> (insertMax (fromEnum y) l, [], zs)
                      (l, ys@(y:yss), _) | not_ordered y yss -> (l, [], ys)
                                         | otherwise -> case create (s `shiftR` 1) yss of
                                                   (r, zs, ws) -> (link (fromEnum y) l r, zs, ws)
{-# INLINABLE fromList #-}

instance (Enum a, Eq a) => Eq (Set a) where
  t1 == t2  = (size t1 == size t2) && (toAscList t1 == toAscList t2)

foldr :: Enum a => (a -> b -> b) -> b -> Set a -> b
foldr f z = go z
  where
    go z' Tip           = z'
    go z' (Bin _ x l r) = go (f (toEnum x) (go z' r)) l
{-# INLINE foldr #-}

toAscList :: Enum a => Set a -> [a]
toAscList = foldr (:) []

split :: Int -> Set a -> (Set a,Set a)
split x t = toPair $ splitS x t
{-# INLINABLE split #-}

splitS :: Int -> Set a -> StrictPair (Set a) (Set a)
splitS _ Tip = Tip :*: Tip
splitS x (Bin _ y l r)
      = case compare x y of
          LT -> let (lt :*: gt) = splitS x l in (lt :*: link y gt r)
          GT -> let (lt :*: gt) = splitS x r in (link y l lt :*: gt)
          EQ -> l :*: r
{-# INLINABLE splitS #-}

splitMember :: Int -> Set a -> (Set a,Bool,Set a)
splitMember _ Tip = (Tip, False, Tip)
splitMember x (Bin _ y l r)
   = case compare x y of
       LT -> let (lt, found, gt) = splitMember x l
                 !gt' = link y gt r
             in (lt, found, gt')
       GT -> let (lt, found, gt) = splitMember x r
                 !lt' = link y l lt
             in (lt', found, gt)
       EQ -> (l, True, r)
{-# INLINABLE splitMember #-}

link :: Int -> Set a -> Set a -> Set a
link x Tip r  = insertMin x r
link x l Tip  = insertMax x l
link x l@(Bin sizeL y ly ry) r@(Bin sizeR z lz rz)
  | delta*sizeL < sizeR  = balanceL z (link x l lz) rz
  | delta*sizeR < sizeL  = balanceR y ly (link x ry r)
  | otherwise            = bin x l r

insertMax,insertMin :: Int -> Set a -> Set a
insertMax x t
  = case t of
      Tip -> singleton x
      Bin _ y l r
          -> balanceR y l (insertMax x r)

insertMin x t
  = case t of
      Tip -> singleton x
      Bin _ y l r
          -> balanceL y (insertMin x l) r

merge :: Set a -> Set a -> Set a
merge Tip r   = r
merge l Tip   = l
merge l@(Bin sizeL x lx rx) r@(Bin sizeR y ly ry)
  | delta*sizeL < sizeR = balanceL y (merge l ly) ry
  | delta*sizeR < sizeL = balanceR x lx (merge rx r)
  | otherwise           = glue l r

glue :: Set a -> Set a -> Set a
glue Tip r = r
glue l Tip = l
glue l@(Bin sl xl ll lr) r@(Bin sr xr rl rr)
  | sl > sr = let !(m :*: l') = maxViewSure xl ll lr in balanceR m l' r
  | otherwise = let !(m :*: r') = minViewSure xr rl rr in balanceL m l r'

minViewSure :: Int -> Set a -> Set a -> StrictPair Int (Set a)
minViewSure = go
  where
    go !x Tip r = x :*: r
    go x (Bin _ xl ll lr) r =
      case go xl ll lr of
        xm :*: l' -> xm :*: balanceR x l' r

maxViewSure :: Int -> Set a -> Set a -> StrictPair Int (Set a)
maxViewSure = go
  where
    go !x l Tip = x :*: l
    go x l (Bin _ xr rl rr) =
      case go xr rl rr of
        xm :*: r' -> xm :*: balanceL x l r'

delta,ratio :: Int
delta = 3
ratio = 2

balanceL :: Int -> Set a -> Set a -> Set a
balanceL x l r = case r of
  Tip -> case l of
           Tip -> Bin 1 x Tip Tip
           (Bin _ _ Tip Tip) -> Bin 2 x l Tip
           (Bin _ lx Tip (Bin _ lrx _ _)) -> Bin 3 lrx (Bin 1 lx Tip Tip) (Bin 1 x Tip Tip)
           (Bin _ lx ll@Bin{} Tip) -> Bin 3 lx ll (Bin 1 x Tip Tip)
           (Bin ls lx ll@(Bin lls _ _ _) lr@(Bin lrs lrx lrl lrr))
             | lrs < ratio*lls -> Bin (1+ls) lx ll (Bin (1+lrs) x lr Tip)
             | otherwise -> Bin (1+ls) lrx (Bin (1+lls+size lrl) lx ll lrl) (Bin (1+size lrr) x lrr Tip)

  (Bin rs _ _ _) -> case l of
           Tip -> Bin (1+rs) x Tip r

           (Bin ls lx ll lr)
              | ls > delta*rs  -> case (ll, lr) of
                   (Bin lls _ _ _, Bin lrs lrx lrl lrr)
                     | lrs < ratio*lls -> Bin (1+ls+rs) lx ll (Bin (1+rs+lrs) x lr r)
                     | otherwise -> Bin (1+ls+rs) lrx (Bin (1+lls+size lrl) lx ll lrl) (Bin (1+rs+size lrr) x lrr r)
                   (_, _) -> error "Failure in Data.Set.balanceL"
              | otherwise -> Bin (1+ls+rs) x l r
{-# NOINLINE balanceL #-}

balanceR :: Int -> Set a -> Set a -> Set a
balanceR x l r = case l of
  Tip -> case r of
           Tip -> Bin 1 x Tip Tip
           (Bin _ _ Tip Tip) -> Bin 2 x Tip r
           (Bin _ rx Tip rr@Bin{}) -> Bin 3 rx (Bin 1 x Tip Tip) rr
           (Bin _ rx (Bin _ rlx _ _) Tip) -> Bin 3 rlx (Bin 1 x Tip Tip) (Bin 1 rx Tip Tip)
           (Bin rs rx rl@(Bin rls rlx rll rlr) rr@(Bin rrs _ _ _))
             | rls < ratio*rrs -> Bin (1+rs) rx (Bin (1+rls) x Tip rl) rr
             | otherwise -> Bin (1+rs) rlx (Bin (1+size rll) x Tip rll) (Bin (1+rrs+size rlr) rx rlr rr)

  (Bin ls _ _ _) -> case r of
           Tip -> Bin (1+ls) x l Tip

           (Bin rs rx rl rr)
              | rs > delta*ls  -> case (rl, rr) of
                   (Bin rls rlx rll rlr, Bin rrs _ _ _)
                     | rls < ratio*rrs -> Bin (1+ls+rs) rx (Bin (1+ls+rls) x l rl) rr
                     | otherwise -> Bin (1+ls+rs) rlx (Bin (1+ls+size rll) x l rll) (Bin (1+rrs+size rlr) rx rlr rr)
                   (_, _) -> error "Failure in Data.Set.balanceR"
              | otherwise -> Bin (1+ls+rs) x l r
{-# NOINLINE balanceR #-}

bin :: Int -> Set a -> Set a -> Set a
bin x l r
  = Bin (size l + size r + 1) x l r
{-# INLINE bin #-}

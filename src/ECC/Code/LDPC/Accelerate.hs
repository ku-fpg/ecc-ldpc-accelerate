{-# LANGUAGE BangPatterns, RankNTypes, GeneralizedNewtypeDeriving, ScopedTypeVariables #-}
{-# LANGUAGE TupleSections, TypeOperators, TypeFamilies, StandaloneDeriving, DeriveDataTypeable #-}
module ECC.Code.LDPC.Accelerate where

-- Reference implementation of LDPC

import Data.Bit
import ECC.Code.LDPC.Utils
import ECC.Types
import ECC.Puncture
import Data.Char (isDigit)
import qualified Data.Matrix
import Data.Matrix ((!))
import Data.Matrix (nrows, ncols, getCol, getRow, colVector, rowVector)
import qualified Data.Vector as V
import qualified Data.Vector.Unboxed as U
import qualified Data.List as L

import Data.Semigroup ((<>), Monoid, mconcat)

--import Data.Array.Accelerate.Interpreter as I
import Data.Array.Accelerate.Cmp as I   -- The Cmp is for testing; it compares back ends

import Data.Array.Accelerate hiding ((++), product, take, all, (!), fst, snd, zipWith, not, zip, or, map)
import qualified Data.Array.Accelerate as A
--import qualified Data.Array.Accelerate.Array.Sugar as Sugar
--import qualified Data.Array.Accelerate.Array.Data as Data
--import qualified Data.Array.Accelerate.Type as Type
import Debug.Trace
import Data.Typeable
import Data.Word
import qualified Data.Bits as Bits
import Data.Matrix (Matrix)
import qualified Data.Matrix as M

import qualified ECC.Code.LDPC.Reference as Ref
import ECC.Code.LDPC.Model (Decoder(..), Share(..), share_minsum)
import qualified ECC.Code.LDPC.Model as Mod
import qualified Data.BitMatrix.Word64 as BM64
import qualified Data.BitVector.Word64 as BV64


code :: Code
code = mconcat [  mkLDPC_Code ("accel-" ++ show i ++ "-" ++ show j) e d
               | (i,e) <- [0..] `Prelude.zip` encoders
               , (j,d) <- [0..] `Prelude.zip` decoders
               ]

encoders = [Mod.encoder4,encoder]
decoders = [Mod.decoder Mod.decoder8,Mod.decoder decoder_acc1]

decoder :: Matrix Bit -> Int -> [Double] -> IO [Bit]
decoder = Mod.decoder Mod.decoder8

type G = Matrix Bit

---------------------------------------------------------------------

encoder :: G -> [Bit] -> IO [Bit]
--encoder g v | traceShow ("encoder",g,v) False = undefined
encoder g v = do
--        print ("encoder2",(use $ toAccBitArray g), (use $ toAccBitVector v),r,length r)
        return (v ++ r)
  where
        r = fromAccBitVector
            $ run
            $ mvm (use $ toAccBitArray g)
                  (use $ toAccBitVector v)
--            = getRow 1 (Data.Matrix.multStd (rowVector v) g)

toAccBitArray :: G -> Array DIM2 Word8
toAccBitArray mat = A.fromList (Z :. nrows mat :. ncols mat)
                [ Prelude.fromIntegral $ mat ! (m,n) | m <- [1..nrows mat], n <- [1..ncols mat]]

toAccBitVector :: [Bit] -> Vector Word8
toAccBitVector vec = A.fromList (Z :. length vec) $ fmap (Prelude.fromIntegral) vec

fromAccBitVector :: Vector Word8 -> [Bit]
fromAccBitVector = fmap mask . A.toList
  where mask :: Word8 -> Bit
--        mask = undefined
        mask = mkBit . flip Bits.testBit 0

mvm :: (Elt e, IsNum e) => Acc (Array DIM2 e) -> Acc (Vector e) -> Acc (Vector e)
mvm mat vec =
  let Z :. rows :. cols = unlift (shape mat) :: Z :. Exp Int :. Exp Int
      vec'              = A.replicate (lift (Z :. All :. cols)) vec
  in
--  traceShow ("mvm mat",run mat) $
--  traceShow ("mvm vec",run vec) $
--  traceShow ("mvm rows",rows) $
--  traceShow ("mvm vec'",run vec') $
  fold (+) 0 (A.transpose (A.zipWith (*) vec' mat))

takeRow :: (Elt e, IsNum e) => Exp Int -> Acc (Array DIM2 e) -> Acc (Vector e)
takeRow n mat =
  let Z :. _ :. cols = unlift (shape mat) :: Z:. Exp Int :. Exp Int
  in backpermute (index1 cols)
                 (\ix -> index2 n (unindex1 ix))
                 mat



-- First cut at using Accelerate
decoder_acc1 = Decoder
        { pre_a        =  \ h ->
                                let vs = [ (m,n) | m <- [1..nrows h], n <- [1..ncols h], h ! (m,n) == 1 ] in
                                ( h
                                        -- The bit vector for the parity check
                                , BM64.fromLists [[ h ! (m,n) | n <- [1..ncols h]] | m <- [1..nrows h]]
                                        -- all the left/right neibours
                                , U.fromList vs -- $ traceShow "X" vs
                                )
        , pre_lambda   = \ lam -> use $ A.fromList (Z :. length lam) lam
        , check_parity =  \ (m_opt,m,_) lamA -> not $ or $ BM64.parityMatVecMul m (BV64.fromList (fmap hard
                                        (A.toList (run lamA))))
        , post_lambda  =  map hard . A.toList . run
        , pre_ne       = \ (m_opt,_,mns) -> U.map (const 0) mns
        , comp_ne      = \  share (m_opt,_,mns) lamA ne ->

		let inf = 100000 :: Double in

        -- The old way

                let lam = U.fromList (A.toList (run lamA)) in

                let interm_arr = U.zipWith (\ (_,n) v -> - ((lam U.! (n-1)) - v)) mns ne in

                let sign = U.accumulate (\ a b -> if b < 0 then not a else a)
                                   (U.generate (nrows m_opt) (const False))
                                   (U.zip (U.map (pred . fst) mns) interm_arr) in

                let val = U.accumulate (\ (b,c) a -> if abs a <= b
                                                     then (abs a,b)
                                                     else (b,min (abs a) c))
                                   (U.generate (nrows m_opt) (const (inf,inf)))     -- IEEE magic
                                   (U.zip (U.map (pred . fst) mns) interm_arr) in

                let ans2 = U.zipWith (\ (m,_) v ->
                                        let sgn = if sign U.! (m-1) == (v < 0) then 1 else -1 in
                                        let (a,b) = val U.! (m-1) in
                                        if a == abs v
                                        then (-0.75) * sgn * b
                                        else (-0.75) * sgn * a
                                     ) mns interm_arr in

                let vs = U.toList mns in

                -- msA and nsA are (-1)'d to index into an array better
                let msA = use $ A.fromList (Z :. length vs) (map (pred . fst) vs) :: Acc (Array DIM1 Int) in
                let nsA = use $ A.fromList (Z :. length vs) (map (pred . snd) vs) :: Acc (Array DIM1 Int) in

                let esA = use $ A.fromList (Z :. length vs) [0..]                 :: Acc (Array DIM1 Int) in
                let neA = use $ A.fromList (Z :. length vs) (U.toList ne)         :: Acc (Array DIM1 Double) in

                let segA = use $ A.fromList (Z :. (nrows m_opt))
                               $ map Prelude.length
                               $ L.group
                               $ map (pred . fst)
                               $ vs

                                                             :: Acc (A.Vector Int) in


--                let lamA = use $ A.fromList (Z :. U.length lam) (U.toList lam) :: Acc (Array DIM1 Double) in

                -- The new way
                -- Flat array of values

                let interm_arrA' = A.zipWith (\ n v -> - ((lamA A.! index1 n) - v)) nsA neA in

                let interm_arrA = compareWith "interm_arrA" interm_arrA' interm_arr in


                -- We use 0 to represent false
                let falseA = A.generate (index1 (lift (nrows m_opt))) (\ _ -> lift (0 :: Word8)) in

                -- not use boolean (this messed up on the CUDA version)
                let signA' = fold1Seg (/=*)
                                (A.map (\ v -> (v <* 0)) interm_arrA)
                                segA :: Acc (Array DIM1 Bool) in

                let signA = compareWith "signA" signA' sign in

                let infsA = A.generate (index1 (lift (nrows m_opt))) (\ _ -> lift (inf,inf)) in


                let bad = 999 :: Double in

{-
                let valA' = A.permute
                                (\ a12 b12 -> let (a1,a2) = unlift a12
                                                  (b1,b2) = unlift b12
                                              in (a1 <=* b1)
                                               ? ( lift (a1, min a2 b1)
                                                 , lift (b1, min b2 a1)
                                                 ))
                                infsA
                                (\ ix -> index1 (msA A.! ix))
                                (A.map (\ v -> lift (abs v,inf)) interm_arrA) :: Acc (Array DIM1 (Double,Double)) in
-}


{-                -- first find the max on a line
                let mxA = A.permute min
                                (A.generate (index1 (lift (nrows m_opt))) (\ _ -> lift inf))
                                (\ ix -> index1 (msA A.! ix))
                                (A.map (\ v -> abs v) interm_arrA) :: Acc (Array DIM1 Double) in

                let mx_ixA = A.permute max -- highest one
                                (A.generate (index1 (lift (nrows m_opt))) (\ _ -> lift (-1 :: Int)))
                                (\ ix -> index1 (msA A.! ix))
                                (A.zipWith3 (\ v ix iy -> ((mxA A.! index1 ix) ==* v)
                                                        ? ( iy
                                                          , lift (-1 :: Int)
                                                          )
                                           ) interm_arrA msA esA) ::  Acc (Array DIM1 Int) in
-}

                let valA' = fold1Seg
                                (\ a12 b12 -> let (a1,a2) = unlift a12
                                                  (b1,b2) = unlift b12
                                              in (a1 <=* b1)
                                               ? ( lift (a1, min a2 b1)
                                                 , lift (b1, min b2 a1)
                                                 ))
                                (A.map (\ v -> lift (abs v,inf)) interm_arrA)
                                segA in

{-
                let valA' = (A.map (\ v -> lift (abs v,inf))
                        >-> (A.permute
                                (\ a12 b12 -> let (a1,a2) = unlift a12
                                                  (b1,b2) = unlift b12
                                              in (a1 <=* b1)
                                               ? ( lift (a1, min a2 b1)
                                                 , lift (b1, min b2 a1)
                                                 ))
                                infsA
                                (\ ix -> index1 (msA A.! ix)))) interm_arrA :: Acc (Array DIM1 (Double,Double)) in
-}

                let valA = compareWith "valA" valA' val in

                let ans2A' = A.zipWith (\ m v ->
                                        let sgn = (((signA A.! index1 m)) ==* (v <* 0)) ? (1,-1) :: Exp Double in
                                        let (a,b) = unlift (valA A.! index1 m) :: (Exp Double,Exp Double) in
                                        (a ==* abs v) ?
                                           ( (-0.75) * sgn * b
                                           , (-0.75) * sgn * a
                                           ) :: Exp Double
                                     ) msA interm_arrA in

                let ans2A = compareWith "ans2" ans2A' ans2 in

                (U.fromList (A.toList (run ans2A)))
--                (traceShow comp ans1)
        , comp_lam     = \ (m_opt,_,mns) orig_lam ne' -> use
                $ A.fromList (Z :. (length (A.toList (run orig_lam))))
                $ U.toList
                $ U.accum (+) (U.fromList (A.toList (run orig_lam))) [ (n-1,v) | ((_,n),v) <- U.toList mns `zip` U.toList ne' ]

        , share = share_minsum :: Share Double [(Int,Double)] Int -- ignored
        }

--encoder :: (Elt e, IsNum e) => G -> V e -> V e
--encoder g v = mvm g v

compareWith :: (U.Unbox d, Elt d, Eq d, Show d) =>  String -> Acc (Array DIM1 d) -> U.Vector d -> Acc (Array DIM1 d)
compareWith msg a b =
        if as == bs
        then a
        else error $ "compare failed for " ++ msg ++ show (length as, length bs, as,bs)
  where
        as = A.toList (run a)
        bs = U.toList b


{-# LANGUAGE BangPatterns, RankNTypes, GeneralizedNewtypeDeriving, ScopedTypeVariables #-}
{-# LANGUAGE TupleSections, TypeOperators, TypeFamilies, StandaloneDeriving, DeriveDataTypeable #-}
module ECC.Code.LDPC.Accelerate where

-- Reference implementation of LDPC

import Data.Bit
import Data.Bits ((.&.),(.|.))
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
encoder g = \ v -> return $ (v ++ (fromAccBitVector $ run1 f $ toAccBitVector v))
  where
        f = mvm' g'
        g' = use $ toAccBitArray g

run_mvm :: (Array DIM2 Word8,Vector Word8) -> Vector Word8
run_mvm = run1 (A.uncurry mvm)

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

mvm' :: (Elt e, IsNum e) => Acc (Array DIM2 e) -> Acc (Vector e) -> Acc (Vector e)
mvm' mat =
  let Z :. rows :. cols = unlift (shape mat) :: Z :. Exp Int :. Exp Int
      t = A.transpose mat
  in
        \ vec -> let vec' = A.replicate (lift (Z :. rows :. All)) vec
                 in fold (+) 0 (A.zipWith (*) t vec')

--  traceShow ("mvm mat",run mat) $
--  traceShow ("mvm vec",run vec) $
--  traceShow ("mvm rows",rows) $
--  traceShow ("mvm vec'",run vec') $



takeRow :: (Elt e, IsNum e) => Exp Int -> Acc (Array DIM2 e) -> Acc (Vector e)
takeRow n mat =
  let Z :. _ :. cols = unlift (shape mat) :: Z:. Exp Int :. Exp Int
  in backpermute (index1 cols)
                 (\ix -> index2 n (unindex1 ix))
                 mat


decoder_acc1 = Decoder
        { pre_a        =  \ h ->
                                let vs = [ (m,n) | m <- [1..nrows h],n <- [1..ncols h], h ! (m,n) == 1 ] in
                                ( h
                                        -- The bit vector for the parity check
                                , BM64.fromLists [[ h ! (m,n) | n <- [1..ncols h]] | m <- [1..nrows h]]
                                        -- all the left/right neibours
                                , U.fromList vs
                                )
        , pre_lambda   = \ lam -> use $ A.fromList (Z :. length lam) lam
        , check_parity =  \ (m_opt,m,_) lamA -> not $ or $ BM64.parityMatVecMul m (BV64.fromList (fmap hard
                                        (A.toList (run lamA))))
        , post_lambda  =  map hard . A.toList . run
        , pre_ne       = \ (m_opt,_,mns) -> U.map (const 0) mns
        , comp_ne      = \  share (m_opt,_,mns) lamA ne ->

                let lam = U.fromList (A.toList (run lamA)) in

                -- The new way
                -- Flat array of values
                let interm_arr = U.zipWith (\ (_,n) v -> - ((lam U.! (n-1)) - v)) mns ne in

                let inf = 10000 in

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

                let debug xs = traceShow (A.toList $ run xs) xs in

                let segA = use $ A.fromList (Z :. (nrows m_opt))
                               $ map Prelude.length
                               $ L.group
                               $ map (pred . fst)
                               $ vs
                                                             :: Acc (A.Vector Int) in

                let interm_arrA' = A.zipWith (\ n v -> - ((lamA A.! index1 n) - v)) nsA neA in

                let interm_arrA = compareWith "interm_arrA" interm_arrA' interm_arr in

                let interm_arr2A = A.map quant interm_arrA in

               -- not use boolean (this messed up on the CUDA version)
                let signA' = fold1Seg (/=*)
                                (A.map (\ v -> (v <* 0)) interm_arrA)
                                segA :: Acc (Array DIM1 Bool) in

                let !signA = compareWith "signA" signA' sign in

                let infsA = A.generate (index1 (lift (nrows m_opt))) (\ _ -> lift (inf,inf)) in

                let valA = fold1Seg
                                (\ a12 b12 -> let (a1,a2) = unpairQ a12
                                                  (b1,b2) = unpairQ b12
                                              in (a1 <=* b1)
                                               ? ( pairQ (a1, min a2 b1)
                                                 , pairQ (b1, min b2 a1)
                                                 ))
                                (A.map (\ v -> pairQ (v,infQ)) (interm_arr2A))
                                segA :: Acc (Array DIM1 Word32) in

--                let !valA' = compareWith "valA" valA (U.map (\ (a,b) -> unlift $ pairQ $ (quant $ lift a, quant $ lift b)) val) in

                let ans2A' = A.zipWith3 (\ m v v2 ->
                                        let sgn = (((signA A.! index1 m)) ==* (v <* 0)) ? (1,-1) :: Exp Double in
                                        let (a,b) = unpairQ (valA A.! index1 m) in
                                        (a ==* v2) ?
                                           ( (-0.75) * sgn * unquant b
                                           , (-0.75) * sgn * unquant a
                                           ) :: Exp Double
                                     ) msA interm_arrA interm_arr2A in

                let !ans2A = compareWith' "ans2" ans2A' (ans2) in

--                (U.fromList (A.toList (run ans2A)))
--                (traceShow comp ans1)
                ans2
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

--compareWith' :: (U.Unbox d, Elt d, Eq d, Show d) =>  String -> Acc (Array DIM1 d) -> U.Vector d -> Acc (Array DIM1 d)
compareWith' msg a b =
        if L.and [abs(a-b) < (0.01 :: Double) | (a,b) <- as `zip` bs ]
        then a
        else error $ "compare failed for " ++ msg ++ show (length as, length bs, as,bs)
  where
        as = A.toList (run a)
        bs = U.toList b


q :: Double -> Double
q n = Prelude.fromIntegral (Prelude.round (abs n * 256)) / 256

-- abs and into 16 bits of info
quant :: Exp Double -> Exp Word16
quant n = A.round (abs n * 256)

unquant :: Exp Word16 -> Exp Double
unquant n = A.fromIntegral n / 256

infQ :: Exp Word16
infQ = 0xffff           -- max value for Word16

unpairQ :: Exp Word32 -> (Exp Word16,Exp Word16)
unpairQ a = (A.fromIntegral ((a `shiftR` 16) .&. 0xffff),A.fromIntegral (a .&. 0xffff))

pairQ :: (Exp Word16,Exp Word16) -> Exp Word32
pairQ (a,b) = (A.fromIntegral a `shiftL` 16) .|. A.fromIntegral b

--------------------------------------------------------
{-
decoder2 :: (Semigroup ts) => Decoder m m_opt lam ne d ts i -> m -> Int -> [Double] -> IO [Bit]
decoder2 dec a = \ !maxIterations inp -> do
      let orig_lam = pre_lambda dec inp

          loop !n ne lam
            | check_parity dec a_opt lam   = lam
            | n >= maxIterations           = orig_lam
            | otherwise                    =
                 let ne'  = {-# SCC ne' #-} comp_ne dec (share dec) a_opt lam      ne
                     lam' = {-# SCC lam' #-} comp_lam dec a_opt orig_lam ne'
                 in loop (n+1) ne' lam'

      return $ post_lambda dec $ loop 0 orig_ne orig_lam
   where
      a_opt   = pre_a dec a
      orig_ne = pre_ne dec a_opt
-}



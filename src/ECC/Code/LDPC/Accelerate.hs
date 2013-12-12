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
import Data.Semigroup ((<>), Monoid, mconcat)

import Data.Array.Accelerate.Interpreter as I
import Data.Array.Accelerate hiding ((++), product, take, all, (!))
import qualified Data.Array.Accelerate as A

import qualified Data.Array.Accelerate.Array.Sugar as Sugar
import qualified Data.Array.Accelerate.Array.Data as Data
import qualified Data.Array.Accelerate.Type as Type
import Debug.Trace
import Data.Typeable
import Data.Word
import qualified Data.Bits as Bits
import Data.Matrix (Matrix)
import qualified Data.Matrix as M

import qualified ECC.Code.LDPC.Reference as Ref
import qualified ECC.Code.LDPC.Model as Mod

code :: Code
code = mconcat [  mkLDPC_Code ("accel-" ++ show i ++ "-" ++ show j) e d
               | (i,e) <- [0..] `Prelude.zip` encoders
               , (j,d) <- [0..] `Prelude.zip` decoders
               ]

encoders = [Mod.encoder4,encoder]
decoders = [Mod.decoder Mod.decoder8]

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

{-
--encoder :: (Elt e, IsNum e) => G -> V e -> V e
--encoder g v = mvm g v


instance Elt Bit where
  eltType _ = Type.PairTuple Type.UnitTuple (Type.SingleTuple Type.scalarType)
  fromElt v = ((), Sugar.fromElt' v)
  toElt ((), v) = Sugar.toElt' v

  eltType' _ = Type.SingleTuple Type.scalarType
  fromElt' v = if getBit v then 1 else 0
  toElt' 0 = 0
  toElt' 1 = 1
  toElt' _ = error "toElt' _ :: Bit"

type instance Sugar.EltRepr' Bit = Word8
type instance Sugar.EltRepr Bit = ((),Word8)

{-
instance Data.ArrayElt Bit where
-}

--instance Type.IsBounded Bit where
--  boundedType = Type.IntegralBoundedType Type.integralType

--instance Type.IsIntegral Bit where
--  integralType = error "Opps" -- Type.TypeInt Type.IntegralDict

instance Type.IsNum Bit where
  numType = Type.IntegralNumType undefined -- Type.integralType

instance Type.IsScalar Bit where
  scalarType = Type.NumScalarType Type.numType


{-

newtype Bit' = Bit' Word8

deriving instance Show Bit'
deriving instance Elt Bit'
deriving instance Typeable Bit'

type instance Sugar.EltRepr' Bit' = Word8
type instance Sugar.EltRepr Bit' = ((),Word8)
-}

---------------------------------------------------------------------

type M a = Data.Matrix.Matrix a
type V a = V.Vector a

ldpc :: M Bit -> Int -> V Double -> IO (V Bit)
ldpc a maxIterations orig_lam = return $ fmap hard $ loop 0 orig_ne orig_lam
  where
    orig_ne :: M Double
    orig_ne = fmap (const 0) a

    loop :: Int -> M Double -> V Double -> V Double
    loop !n ne lam
        | V.all (== 0) ans             = lam
        | n >= maxIterations           = orig_lam
        | otherwise                    = loop (n+1) ne' lam'
      where
        c_hat :: V Bit
        c_hat = fmap hard lam

        -- was bug here: needed to getCol, not getRow (which was a single element)
        ans :: V Bit
        ans = getCol 1 (a `Data.Matrix.multStd` colVector c_hat)

        -- was bug here: V's start at index 0, not 1
        ne' :: M Double
        ne' = Data.Matrix.matrix (nrows orig_ne) (ncols orig_ne) $ \ (m,n) ->
                if a ! (m,n) == 1
                then
                   -- was bug here: we need to cap atanh's answer
                    -2 * atanh' (product
                        [ tanh (- ((lam V.! (j-1) - ne ! (m,j)) / 2))
                        | j <- [1 .. V.length orig_lam]
                        , j /= n
                        , a ! (m,j) == 1
                        ])
                else 0

        -- Was bug here: needed to add the orig_lam
        lam' :: V Double
        lam' = V.fromList [ V.foldr (+) (orig_lam V.! (j - 1)) (getCol j ne')
                          | j <- [1 .. V.length lam]
                          ]


-}

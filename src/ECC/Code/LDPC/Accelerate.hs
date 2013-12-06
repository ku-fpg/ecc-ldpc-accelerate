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
import Data.Alist

import Data.Array.Accelerate.Interpreter
import Data.Array.Accelerate hiding ((++), product, take, all, (!))
import qualified Data.Array.Accelerate as A

import qualified Data.Array.Accelerate.Array.Sugar as Sugar
import qualified Data.Array.Accelerate.Array.Data as Data
import qualified Data.Array.Accelerate.Type as Type
import Debug.Trace
import Data.Typeable
import Data.Word


code :: Code
code = Code ["ldpc/reference/<matrix-name>/<max-rounds>[/<truncation-size>]"]
     $ \ xs -> case xs of
                ["ldpc","reference",m,n]
                        | all isDigit n -> fmap (: []) $ mkLDPC ("reference") m (read n) encoder ldpc
                ["ldpc","debug",m,n]
                        | all isDigit n -> fmap (: []) $ mkLDPC ("debug") m (read n) encoder ldpc
                ["ldpc","reference",m,n,t]
                        | all isDigit n
                       && all isDigit t -> fmap (: []) $ fmap (punctureTail (read t))
                                                       $ mkLDPC ("reference") m (read n) encoder ldpc
                _                       -> return []

---------------------------------------------------------------------
dotp :: (Elt e, IsNum e) => Acc (Vector e) -> Acc (Vector e) -> Acc (Scalar e)
dotp u v = fold (+) 0
         ( A.zipWith (*) u v )

mvm :: (Elt e, IsNum e) => Acc (Array DIM2 e) -> Acc (Vector e) -> Acc (Vector e)
mvm mat vec =
  let Z :. rows :. _ = unlift (shape mat) :: Z :. Exp Int :. Exp Int
  in generate (index1 rows)
              (\ix -> the (vec `dotp` takeRow (unindex1 ix) mat))

takeRow :: (Elt e, IsNum e) => Exp Int -> Acc (Array DIM2 e) -> Acc (Vector e)
takeRow n mat =
  let Z :. _ :. cols = unlift (shape mat) :: Z:. Exp Int :. Exp Int
  in backpermute (index1 cols)
                 (\ix -> index2 n (unindex1 ix))
                 mat

{-
encoder :: G -> V Bit -> V Bit
encoder g v = getRow 1 (Data.Matrix.multStd (rowVector v) g)

I do not think we need to use takeRow here because mvm returns a vector,
whereas multStd returns a matrix
-}
encoder :: (Elt e, IsNum e) => G -> V e -> V e
encoder g v = mvm g v


{-
instance Elt Bit where
  eltType _ = Type.PairTuple Type.UnitTuple (Type.SingleTuple Type.scalarType)
  fromElt v = ((), v)
  toElt ((), v) = v

  eltType' _ = Type.SingleTuple Type.scalarType
  fromElt' = id
  toElt' = id

type instance Sugar.EltRepr' Bit = Bit
type instance Sugar.EltRepr Bit = ((),Bit)

instance Data.ArrayElt Bit where

instance Type.IsBounded Bit where
  boundedType = Type.IntegralBoundedType integralType

instance Type.IsIntegral Bit where
  integralType = Type.TypeInt Type.IntegralDict

instance Type.IsNum Bit where
  numType = Type.IntegralNumType Type.integralType

instance Type.IsScalar Bit where
  scalarType = Type.NumScalarType Type.numType
-}

newtype Bit' = Bit' Word8

deriving instance Show Bit'
deriving instance Elt Bit'
deriving instance Typeable Bit'

type instance Sugar.EltRepr' Bit' = Word8
type instance Sugar.EltRepr Bit' = ((),Word8)

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




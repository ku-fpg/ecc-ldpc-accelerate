module Main where

import ECC.Tester
import ECC.Types
import Data.Monoid

import qualified ECC.Code.BPSK as BPSK
import qualified ECC.Code.LDPC.Reference as Reference
import qualified ECC.Code.LDPC.ElimTanh as ElimTanh

import qualified ECC.Code.LDPC.Accelerate as Accelerate

codes :: Code
codes = BPSK.code <> Reference.code <> Accelerate.code

-- usage: ./Main 0 2 4 6 8 0  bpsk
-- or, to run the LDPC reference implementation, at a single EBNO = 2.2
--        ./Main 2.2 ldpc/reference/jpl.1K/20
main :: IO ()
main = eccMain codes eccPrinter

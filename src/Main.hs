{-# LANGUAGE OverloadedStrings #-}
module Main where

import           Data.ByteString        (ByteString)
import qualified Data.ByteString        as BS
import qualified Data.ByteString.Unsafe as Unsafe

import           Data.ByteString.Base16 as Hex
import           Data.ByteString.Base64 as B64

import           Data.Bits              as Bits
import           Data.Char              (chr, isAlpha, isSpace, ord, toLower)
import           Data.List              (elemIndex, foldl', sortBy, sortOn)
import           Data.Ord               (comparing)
import           Data.Word

import           Data.Map.Strict        (Map)
import qualified Data.Map.Strict        as M

import           Control.Monad          (forM_)

import           Control.Lens

import           Crypto.Cipher.AES
import           Crypto.Cipher.Types
import           Crypto.Error

import           Data.Monoid

main :: IO ()
main = do

  pure ()
  pure ()



ex4 :: IO ()
ex4 = do
  txt <- BS.readFile "4.txt"
  let hexlines = linesBS txt
      sorted = sortOn (^. _2._3) $ zip hexlines $map (head . findMostEnglish . fromHex') hexlines
  forM_ (take 10 sorted) $ \(hline,(w,line,score)) ->
    print (w,wToChr w,score,hline,line)

ex5 :: IO ()
ex5 = do
  txt <- BS.readFile "ice.txt"
  print txt
  print . toHex . xorKey "ICE" $ txt

fromHex :: ByteString -> Maybe ByteString
fromHex bs = case Hex.decode bs of
  (hex,"") -> Just hex
  _        -> Nothing

fromHex' :: ByteString -> ByteString
fromHex' = maybe (error "fromHex': invalid hex") id . fromHex

toHex :: ByteString -> ByteString
toHex = Hex.encode

toBase64 :: ByteString -> ByteString
toBase64 = B64.encode

fromBase64 :: ByteString -> Maybe ByteString
fromBase64 bs = case B64.decode bs of
  Right b64 -> Just b64
  _        -> Nothing

fromBase64' :: ByteString -> ByteString
fromBase64' = B64.decodeLenient

fromBase64'' :: ByteString -> Maybe ByteString
fromBase64'' = fromBase64 . unlinesBS

unlinesBS :: ByteString -> ByteString
unlinesBS = BS.filter (/= chrToW '\n')

linesBS :: ByteString -> [ByteString]
linesBS = BS.split (chrToW '\n')

readBase64File :: String -> IO (Maybe ByteString)
readBase64File path = fromBase64'' <$> BS.readFile path

xorEqual :: ByteString -> ByteString -> ByteString
xorEqual a b = BS.pack $ BS.zipWith xor a b

xor1 :: Word8 -> ByteString -> ByteString
xor1 x = BS.map (xor x)

xorKey :: ByteString -> ByteString -> ByteString
xorKey key bs = BS.pack $
  zipWith
    (\x i -> x `xor` Unsafe.unsafeIndex key (i `mod` BS.length key))
    (BS.unpack bs)
    [0..]

onHex2 :: (ByteString -> ByteString -> a) -> ByteString -> ByteString -> Maybe a
onHex2 f a b = f <$> fromHex a <*> fromHex b

toHistogram :: ByteString -> Map Word8 Int
toHistogram = BS.foldl' (\m a -> M.insertWith (+) a 1 m) M.empty

sortedHistogram :: ByteString -> [(Word8,Int)]
sortedHistogram = sortBy (comparing snd) . M.toList . toHistogram

wToChr :: Word8 -> Char
wToChr = chr . fromIntegral

chrToW :: Char -> Word8
chrToW = fromIntegral . ord

findMostEnglish :: ByteString -> [(Word8,ByteString,Int)]
findMostEnglish bs = mostEnglish $ map (\n -> (n,xor1 n bs)) [0..]


mostEnglish :: [(Word8,ByteString)] -> [(Word8,ByteString,Int)]
mostEnglish = sortBy (comparing (\(_,_,x) -> x)) . map (\(n,b) -> (n,b,scoreFrequencies b))

scoreFrequencies :: ByteString -> Int
scoreFrequencies bs =
  let
    histo = sortedHistogram bs
    total = foldl' (\t (w,_) -> t + score w) 0 histo
            + sum [1|(x,_)<-histo
                    ,let c = wToChr x
                    ,not (isAlpha c || ' ' == c)
                    ]
  in total

score :: Word8 -> Int
score w = maybe (length frequentLetters + 1) id $
  elemIndex (toLower $ wToChr w) frequentLetters

frequentLetters :: String
frequentLetters = " etaoinshrdlcumwfgypbvkjxqz"

fi = fromIntegral

hamming :: ByteString -> ByteString -> Int
hamming a b = sum $ BS.zipWith (\x y -> popCount (xor x y)) a b

hammingDist :: Int -> ByteString -> Double
hammingDist n bs =
  let (b1,b2) = BS.splitAt n bs
      (b3,b4) = BS.splitAt n b2
      (b5,_) = BS.splitAt n b4
  in if BS.length bs > n+n
    then fi (hamming b1 b3 + hamming b3 b5) / fi (n+n)
    else fi (hamming b1 b3) / fi n

findLikelyKeySize :: Int -> ByteString -> [(Int,Double)]
findLikelyKeySize mx bs =
  sortBy (comparing snd)
  . map (\n -> (n,hammingDist n bs))
  $ [1..min mx (BS.length bs `div` 2)]

splits :: Int -> ByteString -> [ByteString]
splits n "" = []
splits n bs = let (h,t) = BS.splitAt n bs in h:splits n t

transpositions :: Int -> ByteString -> [ByteString]
transpositions n bs = BS.transpose (splits n bs)

findECBKeys :: Int -> ByteString -> [(Int,ByteString)]
findECBKeys mx bs =
  let kss = take 10 $ findLikelyKeySize mx bs
      tss = map (\(n,_d) -> (n,transpositions n bs)) kss
      xss = map (\(n,ts) -> (n,map (head . findMostEnglish) ts)) tss
      yss = map (\(n,xs) -> (n,BS.pack $ map (view _1) xs)) xss
  in yss

decryptECB :: Int -> ByteString -> [(Int,ByteString,ByteString)]
decryptECB mx bs =
  sortBy (comparing (view _1))
  . map (\(_n,key) -> let res = xorKey key bs in (scoreFrequencies res,key,res))
  . findECBKeys mx
  $ bs

decryptAES128ECB :: ByteString -> ByteString -> CryptoFailable ByteString
decryptAES128ECB key bs = do
  cipher <- cipherInit key :: CryptoFailable AES128
  pure (ecbDecrypt cipher bs)

detectAESECB :: ByteString -> Int
detectAESECB =
  sum
  . map snd
  . filter ((>1) . snd)
  . M.toList
  . foldl' (\m a -> M.insertWith (+) a 1 m) M.empty
  . splits 16


pkcs7 :: Int -> ByteString -> ByteString
pkcs7 n bs = let
  r = n - BS.length bs `mod` n
  in bs <> BS.replicate r (fromIntegral r)


cbc :: ByteString -> ByteString -> ByteString -> Either String ByteString
cbc key iv pt = let
  keySize = BS.length key

  in if keySize /= BS.length iv
    then Left "IV size does not match key size"
    else go bs where

  go

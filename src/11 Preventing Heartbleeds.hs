import Prelude as P hiding (take,null,head,tail,drop,span)
import Foreign.Ptr
import Foreign.ForeignPtr
import Foreign.Storable
import Data.Word
import System.IO.Unsafe (unsafePerformIO) -- for internal bytestring implementation only
import qualified Data.ByteString.Internal as BS (c2w, w2c)

-- Ignore "unsorted" errors
{-@ LIQUID "--prune-unsorted" @-}

-- Custom implementation of ByteStrings
{-@ 
  data ByteString = BS {
    bPtr :: ForeignPtr Word8,
    bOff :: {v:Nat | v <= fplen bPtr},
    bLen :: {v:Nat | v + bOff <= fplen bPtr}
  }
@-}
data ByteString = BS { bPtr :: ForeignPtr Word8, bOff :: !Int, bLen :: !Int }

instance Show ByteString where
  show = show . unpack

-- Type for bytestrings of a given size
{-@ type ByteStringN N = {v:ByteString | bLen v = N} @-}

-- Sized foreign pointers - the size is that of the allocated block
{-@ type ForeignPtrN a N = {v:ForeignPtr a | fplen v = N} @-}

-- Ensure that this function captures the desired block length
{-@ mallocForeignPtrBytes :: n:Nat -> IO (ForeignPtrN a n) @-}

-- Example of instantiating a bytestring
{-@ good1 :: IO (ByteStringN 5) @-}
good1 = do fp <- mallocForeignPtrBytes 5
           return (BS fp 0 5)

-- Example of a good bytestring with an offset into its block
{-@ good2 :: IO (ByteStringN 2) @-}
good2 = do fp <- mallocForeignPtrBytes 5
           return (BS fp 3 2)

-- Bad bytestring: buffer not long enough
{-bad1 = do fp <- mallocForeignPtrBytes 3-}
          {-return (BS fp 0 10)-}

-- Bad bytestring: off-by-one on buffer size
{-bad2 = do fp <- mallocForeignPtrBytes 3-}
          {-return (BS fp 2 2)-}

-- Create a new bytestring of the specified and fill it using the provided function. This is unsafe
-- if the provided function is unsafe, but does enforce the resulting block size
{-@ unsafeCreate :: n:Nat -> (PtrN Word8 n -> IO ()) -> ByteStringN n @-}
unsafeCreate     :: Int -> (Ptr Word8 -> IO ()) -> ByteString
unsafeCreate n f =  unsafePerformIO $ do
                      fp <- mallocForeignPtrBytes n
                      withForeignPtr fp f
                      return (BS fp 0 n)

-- Safely create a new bytestring from a string. Guaranteed to preserve length. Assumes 8-bit characters.
{-@ pack :: xs:String -> ByteStringN {len xs} @-}
pack     :: String -> ByteString
pack xs  =  unsafeCreate (length xs) $ \p -> go p xs 
  where
    {-@ go      :: p:Ptr Word8 -> {s:String | len s <= plen p} -> IO () @-}
    go _ []     =  return ()
    go p (x:xs) =  poke p (BS.c2w x) >> go (p `plusPtr` 1) xs

-- The empty Bytestring
{-@ empty :: ByteStringN 0 @-}
empty :: ByteString
empty = pack ""

-- Refinement type of just the "True" value in Bool
{-@ type TRUE = {v:Bool | v} @-}

-- Prove that packing a String always returns a Bytestring of the correct length
{-@ prop_pack_length  :: String -> TRUE @-}
prop_pack_length xs   = bLen (pack xs) == length xs

-- Another (also safe) version of pack, this time using Storable 
{-@ pack' :: xs:String -> ByteStringN {len xs} @-}
pack'     :: String -> ByteString
pack' xs = unsafeCreate (length xs) $ \p -> pLoop p xs'
  where
    xs' = map BS.c2w xs

    {-@ pLoop      :: Storable a => p:Ptr a -> {xs:[a] | len xs <= plen p} -> IO () @-}
    pLoop p (x:xs) = poke p x >> pLoop (plusPtr p 1) xs
    pLoop _ []     = return () 

-- Truly unsafe version of "take", leading to Heartbleed (here we can ask for n > l)
{-unsafeTake :: Int -> ByteString -> ByteString-}
{-unsafeTake n (BS p o l) = BS p o n -}

-- Safe (constant-time) version of take for bytestrings. This has the same Haskell-level type signature
-- as the unsafe version above but it's still safe due to refinement types! 
{-@ take           :: k:Nat -> {bs:ByteString | bLen bs >= k} -> ByteStringN k @-}
take               :: Int -> ByteString -> ByteString
take k (BS fp o l) =  BS fp o k

-- Safe (constant-time) version of drop for bytestrings. This ensures that offset + length doesn't exceed
-- the underlying block length
{-@ drop           :: k:Nat -> {bs:ByteString | bLen bs >= k} -> ByteStringN {bLen bs - k} @-}
drop               :: Int -> ByteString -> ByteString
drop k (BS fp o l) =  BS fp (o + k) (l - k)

-- Unpack a bytestring into a String of 8-bit characters. Guaranteed to preserve length (no off-by-one errors) 
{-@ unpack :: bs:ByteString -> {v:String | len v = bLen bs} @-}
unpack :: ByteString -> String
unpack bs@(BS fp o l) = unsafePerformIO $
                        withForeignPtr fp $ \p -> 
                          if l <= 0 then return []
                          else go (p `plusPtr` o) (l-1) []
  where
    {-@ go :: p:Ptr Word8 -> {i:Nat | i <= plen p - 1} -> acc:String -> IO {v:String | len v = len acc + i + 1} @-}
    go     :: Ptr Word8 -> Int -> String -> IO String
    go p 0 acc = peek p               >>= \w -> return (BS.w2c w : acc)
    go p n acc = peek (p `plusPtr` n) >>= \w -> go p (n-1) (BS.w2c w : acc)

-- Prove that unpacking a Bytestring always returns a String of the correct length 
{-@ prop_unpack_length :: ByteString -> TRUE @-}
prop_unpack_length b   = bLen b == length (unpack b)

-- A more complex function that could potentially bleed, except that we statically prevent that from happening:
{-@ chop :: s:String -> {n:Nat | n <= len s} -> {v:String | len v = n} @-}
chop :: String -> Int -> String
chop s n = b
  where
    s' = pack s
    b' = take n s'
    b  = unpack b'

-- Demonstration from the tutorial
{-demo     = [ex6, ex30]-}
  {-where-}
    {-ex   = ['L','I','Q','U','I','D']-}
    {-ex6  = chop ex 6   -- accepted by LH-}
    {-ex30 = chop ex 30  -- rejected by LH-}

-- Demonstrate that we can safely chop even when the String and length are obtained dynamically at runtime
-- Obviously it's now possible that chop could fail so we capture this possibility.
safeChop :: String -> Int -> Maybe String
safeChop s n = if (n <= length s) && (n >= 0) 
               then Just (chop s n) 
               else Nothing 

-- As dynamic as it gets: interact directly with the user and still statically enforce typesafe chopping
queryAndChop :: IO (Maybe String)
queryAndChop = do
  putStrLn "Give me a string: "
  str <- getLine
  putStrLn "Give me a number: "
  num <- getLine
  let n = read num :: Int
  return (safeChop str n) 

-- Test if a bytestring is empty in the logic
{-@ predicate Empty BS = bLen BS = 0 @-}

-- Refinement type of nonempty bytestrings
{-@ type ByteStringNE = {v:ByteString | not (Empty v)} @-}

-- Test if a bytestring is empty as a function
{-@ null        :: bs:ByteString -> {v:Bool | v <=> Empty bs} @-}
null            :: ByteString -> Bool
null (BS _ _ l) =  l == 0

-- Safely take the head of a nonempty bytestring
{-@ head         :: ByteStringNE -> Word8 @-}
head             :: ByteString -> Word8
head (BS fp o _) =  unsafePerformIO $
                    withForeignPtr fp $ \p -> peek (p `plusPtr` o)

-- Safely take the tail of a nonempty bytestring
{-@ tail         :: bs:ByteStringNE -> {v:ByteString | bLen v = bLen bs - 1} @-}
tail             :: ByteString -> ByteString
tail (BS fp o l) =  BS fp (o + 1) (l - 1)

-- Measure the length of a list of bytestrings
{-@ measure bsLen @-}
{-@ bsLen    :: [ByteString] -> Nat @-}
bsLen        :: [ByteString] -> Int
bsLen []     =  0
bsLen (b:bs) =  bLen b + bsLen bs

-- Helper lemma for termination checking: the sum of a positive and a natural is a positive that is 
-- strictly greater than the natural
{-@ lem   :: {x:Nat | x > 0} -> y:Nat -> {z:Nat | z = x + y} -> {v:Bool | y < z} @-}
lem       :: Int -> Int -> Int -> Bool
lem x y z =  y < z

-- Helper for making assertions that are erased after typechecking
assert     :: a -> b -> b
assert _ y =  y

-- Group runs of equal Word8s in a bytestring, producing a list of non-empty bytestrings whose total
-- length equals the input
{-@ group :: bs:ByteString -> {v:[ByteStringNE] | bsLen v = bLen bs} / [bLen bs] @-}
group     :: ByteString -> [ByteString]
group bs
  | null bs   = []
  | otherwise = let
                  (prefix, suffix) = span (head bs) bs
                in
                  case bLen prefix of
                    0         -> [bs] -- this can never happen anyway 
                    otherwise -> assert (lem (bLen prefix) (bLen suffix) (bLen bs)) $ 
                                 prefix : group suffix
  
-- Refined type for split bytestrings. Enforces correct lengths
{-@ type BSPair BS = {v:(ByteString, ByteString) | bLen (fst v) + bLen (snd v) = bLen BS} @-}

-- Assumption: "plen" is the same as "fplen" on the same pointer
{-@ withForeignPtr :: fp:ForeignPtr a -> ({p:Ptr a | plen p = fplen fp} -> IO b) -> IO b @-}

-- Span any nonempty bytestring on a given byte value, returning a pair of bytestrings which concatenate 
-- to the original bytestring
{-@ span :: w:Word8 -> bs:ByteString -> BSPair bs @-}
span     :: Word8 -> ByteString -> (ByteString, ByteString)
span w bs@(BS fp o l) = unsafePerformIO $ withForeignPtr fp $ \p -> go w (p `plusPtr` o) 0 
  where
    {-@ go :: w:Word8 -> {p:Ptr Word8 | bLen bs <= plen p} -> {i:Nat | i <= bLen bs} 
              -> IO (BSPair bs) / [bLen bs - i] @-}
    go :: Word8 -> Ptr Word8 -> Int -> IO (ByteString, ByteString)
    go w p i
      | i >= bLen bs = return (bs, empty) 
      | otherwise    = do
                         w' <- peek (p `plusPtr` i) 
                         if w /= w' then return (splitAt i)
                         else go w p (i+1)
    splitAt i = (take i bs, drop i bs)


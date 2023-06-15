{-# LANGUAGE GHC2021 #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE LinearTypes #-}
{-# LANGUAGE MagicHash #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE UnboxedTuples #-}
{-# OPTIONS_GHC -O -ddump-to-file #-}
{-# OPTIONS_HADDOCK hide #-}

module Compact.Pure.Internal where

import Control.Functor.Linear (Data)
import Control.Functor.Linear qualified as Control
import Control.Monad (forM)
import Data.Data (Proxy (Proxy))
import Data.Functor.Linear qualified as Data
import Data.Kind (Type)
import Data.List (intercalate)
import Data.Reflection (Reifies (reflect), reify)
import Data.Replicator.Linear.Internal (Replicator (Moved))
import Data.Semigroup (stimesMonoid)
import Data.Unrestricted.Linear.Internal.Consumable
import Data.Unrestricted.Linear.Internal.Dupable
import Data.Unrestricted.Linear.Internal.Ur
import Foreign (Storable (poke), peek, plusPtr)
import GHC.Compact (Compact (..), compact, compactAdd, getCompact)
import GHC.Exts
import GHC.Generics
import GHC.IO (unsafePerformIO, IO (..))
import GHC.TypeLits
import Unsafe.Coerce (unsafeCoerce, unsafeCoerceAddr)
import Unsafe.Linear (toLinear, toLinear2)
import GHC.MVar (MVar(..))

-------------------------------------------------------------------------------
-- Helpers for display/debug
-------------------------------------------------------------------------------

isProfilingEnabled :: Bool
isProfilingEnabled = unsafePerformIO $ do
  intInReg <- getCompact <$> compact (1 :: Word)
  let intAddr = aToRawPtr intInReg
  v <- peek $ intAddr `plusPtr` wordSize
  return $ v /= (1 :: Word)

wordSize :: Int
wordSize = 8

headerSize :: Int
headerSize = if isProfilingEnabled then 24 else 8

debugEnabled :: Bool
debugEnabled = False

placeholder :: Int
placeholder = 1339

putDebugLn# :: String -> (# State# RealWorld, res #) -> (# State# RealWorld, res #)
putDebugLn# text (# s0, res #) =
  if isDebugEnabled
    then case unIO (putStrLn s) of (# s1, () #) -> (# s1, res #)
    else (# s0, res #)
{-# INLINE putDebugLn# #-}

putDebugLn :: String -> IO ()
putDebugLn x =
  if isDebugEnabled
    then putStrLn x
    else return ()
{-# INLINE putDebugLn #-}

-------------------------------------------------------------------------------
-- Primitives to do unsafe things
-------------------------------------------------------------------------------

data Ptr' a = Ptr' a

ptrToPtr' :: Ptr a -> Ptr' a
ptrToPtr' p = let !r = p in unsafeCoerce r

ptr'ToPtr :: Ptr' a -> Ptr a
ptr'ToPtr p = let !r = p in unsafeCoerce r

instance (Show a) => Show (Ptr' a) where
  show (Ptr' x) = "Ptr' " ++ show x

{-# INLINE align# #-}
align# :: Int# -> Word# -> Word#
align# wordSize# w# =
  let mask = int2Word# (wordSize# -# 1#)
   in w# `and#` (not# mask)

-------------------------------------------------------------------------------
-- Helpers to do unsafe things derived from primitives above
-------------------------------------------------------------------------------

addr2Word# :: Addr# -> Word#
addr2Word# addr# = int2Word# (addr2Int# addr#)

word2Addr# :: Word# -> Addr#
word2Addr# word# = int2Addr# (word2Int# word#)

align :: Ptr a -> Ptr Word
align (Ptr addr#) = do
  let !(I# wordSize#) = wordSize
      word# = addr2Word# addr#
      wordAligned# = align# wordSize# word#
      addrAligned# = word2Addr# wordAligned#
   in Ptr addrAligned#

ptrToA :: Ptr a -> a
ptrToA p =
  case ptrToPtr' p of
    Ptr' res -> res

aToPtr :: a -> Ptr a
aToPtr x = ptr'ToPtr (Ptr' x)

aToRawPtr :: a -> Ptr Word
aToRawPtr x = align (aToPtr x)

aToWord :: a -> Word
aToWord x = ptrToWord (aToPtr x)

wordToA :: Word -> a
wordToA w = ptrToA (wordToPtr w)

ptrToWord :: Ptr a -> Word
ptrToWord (Ptr addr#) = W# (addr2Word# addr#)

wordToPtr :: Word -> Ptr a
wordToPtr (W# word#) = Ptr (word2Addr# word#)

intToWord :: Int -> Word
intToWord (I# int#) = W# (int2Word# int#)

wordToInt :: Word -> Int
wordToInt (W# word#) = I# (word2Int# word#)

wordToPtr' :: Word -> Ptr' a
wordToPtr' w = ptrToPtr' (wordToPtr w)

ptr'ToWord :: Ptr' a -> Word
ptr'ToWord p = ptrToWord (ptr'ToPtr p)

peekInfoPtr :: a -> IO Word
peekInfoPtr x = do
  let rawPtr = aToRawPtr x
  peek rawPtr

reflectCtorInfoPtr# :: forall {k} (liftedCtor :: k). (# #) -> Addr#
reflectCtorInfoPtr# _ = unsafeCoerceAddr (reflectInfoPtr# (# #) :: InfoPtrPlaceholder liftedCtor)
{-# INLINE reflectCtorInfoPtr# #-}

ctorInfoPtr :: forall {k} (liftedCtor :: k). Ptr Word
ctorInfoPtr = Ptr (reflectCtorInfoPtr# @liftedCtor (# #))
{-# INLINE ctorInfoPtr #-}

getCtorInfoPtrFromSym :: forall (symCtor :: Symbol) (a :: Type). (Generic a, GShallow symCtor (Rep a ())) => IO Word
getCtorInfoPtrFromSym = let !evaluated = shallowTerm @symCtor @a in getInfoPtr evaluated

showRaw :: Int -> a -> IO String
showRaw n x =
  unwords <$> do
    let p = aToRawPtr x
    h <- forM [0 .. (headerSize `div` wordSize) - 1] $ \k -> do
      w <- peek (p `plusPtr` (k * wordSize)) :: IO Word
      return $ "[" ++ show k ++ "]" ++ show w
    r <- forM [0 .. n - 1] $ \k -> do
      w <- peek (p `plusPtr` headerSize `plusPtr` (k * wordSize)) :: IO Word
      return $ "[h+" ++ show k ++ "]" ++ show w
    return $ h ++ r

isNullPtr :: Ptr a -> Bool
isNullPtr (Ptr addr#) = isTrue# (addr2Int# addr# ==# 0#)

nullPtr :: Ptr a
nullPtr = Ptr (int2Addr# 0#)

{-# NOINLINE _hide #-}
_hide :: a -> a
_hide x = x

ptrD :: Dest# a -> Ptr Word
ptrD = Ptr . unsafeCoerceAddr
{-# INLINE ptrD #-}

-------------------------------------------------------------------------------
-- Helpers to extract values from type-level info given by Generic
-------------------------------------------------------------------------------

data DatatypeData = DatatypeData
  { dtypeName :: String,
    dtypeModName :: String,
    dtypePackageName :: String,
    dtypeIsNewType :: Bool
  }

getDatatypeData :: forall meta. (Datatype meta) => DatatypeData
getDatatypeData =
  DatatypeData
    { dtypeName = datatypeName @meta undefined,
      dtypeModName = moduleName @meta undefined,
      dtypePackageName = packageName @meta undefined,
      dtypeIsNewType = isNewtype @meta undefined
    }

data CtorData = CtorData {ctorName :: String, ctorFixity :: Fixity, ctorIsRecord :: Bool}

getCtorData :: forall meta. (Constructor meta) => CtorData
getCtorData =
  CtorData
    { ctorName = conName @meta undefined,
      ctorFixity = conFixity @meta undefined,
      ctorIsRecord = conIsRecord @meta undefined
    }

data SelectorData = SelectorData
  { selecName :: String,
    selecUnpackedness :: SourceUnpackedness,
    selecSrcStrictness :: SourceStrictness,
    selecFinalStrictness :: DecidedStrictness
  }

getSelectorData :: forall meta. (Selector meta) => SelectorData
getSelectorData =
  SelectorData
    { selecName = let n = selName @meta undefined in if null n then "" else "." ++ n ++ " ", -- TODO: detect when no sel and return Nothing
      selecUnpackedness = selSourceUnpackedness @meta undefined,
      selecSrcStrictness = selSourceStrictness @meta undefined,
      selecFinalStrictness = selDecidedStrictness @meta undefined
    }

-------------------------------------------------------------------------------
-- Tools to display compact region memory
-------------------------------------------------------------------------------

class ShowHeap (a :: Type) where
  _showHeap :: Int -> String -> a -> IO String

instance {-# OVERLAPPING #-} ShowHeap Int where
  _showHeap = _showHeapPrim "Int" 1 0

instance {-# OVERLAPPING #-} ShowHeap Char where
  _showHeap = _showHeapPrim "Char" 1 'a'

instance (Generic a, repA ~ Rep a (), ctors ~ GCtorsOf repA, ShowTryCtors ctors a) => ShowHeap a where
  _showHeap = _showTryCtors @ctors @a

_showHeapPrim :: String -> Int -> a -> (Int -> String -> a -> IO String)
_showHeapPrim typeName n representative indent selectorRepr x = do
  let pX = aToRawPtr x
  evaluatedInfoPtr <- let !r = representative in peekInfoPtr r
  actualInfoPtr <- peekInfoPtr x
  if actualInfoPtr == evaluatedInfoPtr
    then do
      rawX <- showRaw n x
      return $
        (replicate (2 * indent) ' ')
          ++ selectorRepr
          ++ "@"
          ++ show (ptrToWord pX)
          ++ " = [value] :: "
          ++ typeName
          ++ " "
          ++ rawX
    else do
      rawX <- showRaw 0 x
      return $
        (replicate (2 * indent) ' ')
          ++ "@"
          ++ show (ptrToWord pX)
          ++ " = THUNK :: "
          ++ typeName
          ++ " "
          ++ rawX

class ShowTryCtors (ctors :: [(Meta, [(Meta, Type)])]) (a :: Type) where
  _showTryCtors :: Int -> String -> a -> IO String

instance (Generic a, repA ~ Rep a (), metaA ~ GDatatypeMetaOf repA, Datatype metaA) => ShowTryCtors '[] a where
  _showTryCtors indent selectorRepr x = do
    let pAddr = ptrToWord $ aToRawPtr x
        DatatypeData {..} = getDatatypeData @metaA
    rawP <- showRaw 0 x
    return $
      (replicate (2 * indent) ' ')
        ++ selectorRepr
        ++ "@"
        ++ show pAddr
        ++ " = THUNK :: "
        ++ dtypeName
        ++ " "
        ++ rawP

instance (Generic a, repA ~ Rep a (), metaA ~ GDatatypeMetaOf repA, Datatype metaA, Constructor metaCtor, 'MetaCons symCtor f r ~ metaCtor, GShallow symCtor repA, ShowTryCtors otherCtors a, ShowFields fields, arity ~ Length fields, KnownNat arity) => ShowTryCtors ('(metaCtor, fields) : otherCtors) a where
  _showTryCtors indent selectorRepr x = do
    evaluatedInfoPtr <- getCtorInfoPtrFromSym @symCtor @a
    actualInfoPtr <- peekInfoPtr x
    if evaluatedInfoPtr == actualInfoPtr
      then do
        let pX = aToRawPtr x
            arity = fromInteger $ natVal (Proxy :: Proxy arity)
            DatatypeData {..} = getDatatypeData @metaA
            CtorData {..} = getCtorData @metaCtor
        rawP <- showRaw arity x
        next <- _showFields @fields (indent + 1) pX 0
        return $
          (replicate (2 * indent) ' ')
            ++ selectorRepr
            ++ "@"
            ++ show (ptrToWord pX)
            ++ " = "
            ++ ctorName
            ++ " "
            ++ (stimesMonoid arity "_ ")
            ++ ":: "
            ++ dtypeName
            ++ " "
            ++ rawP
            ++ "\n"
            ++ next
      else _showTryCtors @otherCtors @a indent selectorRepr x

class ShowFields (fields :: [(Meta, Type)]) where
  _showFields :: Int -> Ptr a -> Int -> IO String

instance ShowFields '[] where
  _showFields _ _ _ = return ""

instance (ShowHeap fieldType, ShowFields others, Selector metaSel) => ShowFields ('(metaSel, fieldType) : others) where
  _showFields indent pX fieldOffset = do
    let SelectorData {..} = getSelectorData @metaSel
    fieldAsWord <- peek $ pX `plusPtr` headerSize `plusPtr` (wordSize * fieldOffset)
    showField <- case wordToPtr' fieldAsWord :: Ptr' t of Ptr' field -> _showHeap @fieldType indent selecName field
    showNext <- _showFields @others indent pX (fieldOffset + 1)
    return $ showField ++ "\n" ++ showNext

showHeap :: forall a. (ShowHeap a) => a -> String
showHeap x = unsafePerformIO $ _showHeap @a 0 "" x

class GShallow (n :: Symbol) a where
  gShallowTerm :: a

instance (GShallow n (f p), GShallow n (g p)) => GShallow n ((f :*: g) p) where
  gShallowTerm = gShallowTerm @n @(f p) :*: gShallowTerm @n @(g p)

instance GShallow n (U1 p) where
  gShallowTerm = U1

instance GShallow n (K1 i c p) where
  gShallowTerm = K1 (unsafeCoerce placeholder :: c)

instance (GShallow n (f p)) => GShallow n (M1 i c f p) where
  gShallowTerm = M1 (gShallowTerm @n @(f p))

instance (b ~ IsJust (GCtorInfoOf symCtor (f p)), IfT b (GShallow symCtor (f p)) (GShallow symCtor (g p)), KnownBool b) => GShallow symCtor ((f :+: g) p) where
  gShallowTerm = ifV @b (L1 $ gShallowTerm @symCtor @(f p)) (R1 $ gShallowTerm @symCtor @(g p))

shallowTerm :: forall (symCtor :: Symbol) a. (Generic a, GShallow symCtor (Rep a ())) => a
shallowTerm = to @a $ gShallowTerm @symCtor @(Rep a ())

-------------------------------------------------------------------------------
-- Region and dests
-------------------------------------------------------------------------------

data FirstInhabitant = FirstInhabitant Int

firstInhabitant :: FirstInhabitant
firstInhabitant = FirstInhabitant 1234

newtype Region = Region {root :: Compact FirstInhabitant}

data RegionToken r where RegionToken :: Region -> RegionToken r

instance Consumable (RegionToken r) where
  consume (RegionToken _) = ()

instance Dupable (RegionToken r) where
  dupR (RegionToken c) = Moved (RegionToken c)

type RegionContext r = Reifies r Region

data Dest r a = Dest (Dest# a)

newtype Incomplete r a b = Incomplete (IO (Ur a, b))

instance Control.Functor (Incomplete r a) where
  fmap f (Incomplete (IO t)) = Incomplete (IO (\s -> case t s of (# s', (a, b) #) -> let !r = f b in (# s', (a, r) #)))

getRegionRoot :: forall r. (RegionContext r) => Compact FirstInhabitant
getRegionRoot = root $ reflect (Proxy :: Proxy r)

withRegion :: forall b. (forall (r :: Type). (RegionContext r) => RegionToken r %1 -> Ur b) %1 -> Ur b
withRegion = toLinear _withRegion

{-# NOINLINE _withRegion #-}
_withRegion :: forall b. (forall (r :: Type). (RegionContext r) => RegionToken r %1 -> Ur b) -> Ur b
_withRegion f =
  unsafePerformIO $ do
    c <- (compact firstInhabitant)
    let !firstInhabitantInRegion = getCompact c
        firstPtr = ptrToWord $ aToRawPtr $ firstInhabitantInRegion
    putDebugLn $
      "withRegion: allocating new region around @"
        ++ (show firstPtr)
    return $! reify (Region {root = c}) (\(proxy :: Proxy s) -> f (RegionToken @s (reflect proxy)))

fillComp :: forall r a b. (RegionContext r) => Dest r a %1 -> Incomplete r a b %1 -> b
fillComp = toLinear2 _fillComp

fillLeaf :: forall r a. (RegionContext r) => Dest r a %1 -> a -> ()
fillLeaf = toLinear2 _fillLeaf

_fillComp :: forall r a b. (RegionContext r) => Dest r a -> Incomplete r a b -> b
_fillComp Dest {parentWriteLoc = bParentWriteLoc} Incomplete {rootReceiver = sRootReceiver, dests = sDests, pInitialParentWriteLoc} =
  unsafePerformIO $ do
    let pSRootReceiver = aToRawPtr sRootReceiver
    valueInSRootReceiver <- peek $ pSRootReceiver `plusPtr` headerSize
    poke bParentWriteLoc valueInSRootReceiver -- in case something as already been written to the initial dest, we write the value stored in rootReceiver of the small struct at parentWriteLoc of the big one.
    if (isNullPtr pInitialParentWriteLoc)
      then
        putDebugLn $
          "fillComp: @"
            ++ (show $ ptrToWord bParentWriteLoc)
            ++ " <- [value]"
      else do
        poke pInitialParentWriteLoc (ptrToWord bParentWriteLoc) -- in case the initial dest of the small struct hasn't been used yet, then we replace parentWriteLoc with the one of the big struct. That can only happen when the small struct is the result of a fresh alloc
        putDebugLn $
          "fillComp: @"
            ++ (show $ ptrToWord bParentWriteLoc)
            ++ " <- #"
            ++ (show $ valueInSRootReceiver)
            ++ " (copying address stored in root receiver of small struct)"
            ++ "  /\\  @"
            ++ (show $ ptrToWord pInitialParentWriteLoc)
            ++ " <- #"
            ++ (show $ ptrToWord bParentWriteLoc)
            ++ " (changing slot carried by initial dest of small struct)"
    return $ sDests

{-# NOINLINE _fillLeaf #-}
_fillLeaf :: forall r a. (RegionContext r) => Dest r a -> a -> ()
_fillLeaf Dest {parentWriteLoc} x =
  unsafePerformIO $ do
    !xInRegion <- getCompact <$> (compactAdd (getRegionRoot @r) x)
    let pXAsWord = aToWord xInRegion
    poke parentWriteLoc pXAsWord
    putDebugLn $
      "fillLeaf: @"
        ++ show (ptrToWord parentWriteLoc)
        ++ " <- #"
        ++ show pXAsWord
        ++ ": [value]"

complete :: forall r a. Incomplete r a () %1 -> Ur a
complete = toLinear _complete

completeExtract :: forall r a b. Incomplete r a (Ur b) %1 -> Ur (a, b)
completeExtract = toLinear _completeExtract

{-# NOINLINE _complete #-}
_complete :: forall r a. Incomplete r a () -> Ur a
_complete (Incomplete (IO f)) = case unsafePerformIO f of
  (ur, ()) -> _hide ur

-- TODO: should we put the new Ur wrapper inside the compact region?
{-# NOINLINE _completeExtract #-}
_completeExtract :: forall r a b. Incomplete r a (Ur b) -> Ur (a, b)
_completeExtract (Incomplete (IO f)) = case unsafePerformIO f of
  (ur, Ur y) -> case _hide ur of Ur x -> Ur (x, y)

-- TODO: should we add the redundant '(RegionContext r) =>' here?
intoR :: forall r a. RegionToken r %1 -> a -> Incomplete r a ()
intoR = toLinear2 _intoR

{-# NOINLINE _intoR #-}
_intoR :: forall r a. RegionToken r -> a -> Incomplete r a ()
_intoR (RegionToken (Region (Compact c# _ (MVar m#)))) x =
  case _alloc @r @a of
    (Incomplete (IO allocF)) -> Incomplete . IO $ \s0 -> case allocF s0 of
        (# s1, (rootReceiver, Dest d#) #) -> case compactAdd# c# x s1 of
          (# s2, xInRegion #) -> case takeMVar# m# s2 of
            (# s3, () #) -> case affect# d# xInRegion of
              (# s4, pX #) -> (# s4, (rootReceiver, ()) #)
                                & putDebugLn# (
                                        "intoR: " ++ (show . ptrToWord . ptrD $ d#) ++ " <- #"
                                          ++ (show . ptrToWord . Ptr $ pX)
                                          ++ ": [value]"
                                  )

-- TODO: should we add the redundant '(RegionContext r) =>' here?
alloc :: forall r a. RegionToken r %1 -> Incomplete r a (Dest r a)
alloc = toLinear _alloc

{-# INLINE _alloc #-}
_alloc :: forall r a. RegionToken r -> Incomplete r a (Dest r a)
_alloc (RegionToken (Region (Compact c# _ (MVar m#)))) =
  Incomplete . IO $ \s0 -> case takeMVar# m# s0 of
    (# s1, () #) -> case compactAddShallow# @(Ur a) c# (reflectCtorInfoPtr# @'Ur (# #)) s1 of
      (# s2, rootReceiver #) -> case anyToAddr# rootReceiver s2 of
        (# s3, pRootReceiver #) -> case getSlots1# rootReceiver s3 of
          (# s4, (# d# #) #) -> case putMVar# m# s4 of
            (# s5, () #) -> (# s5, (rootReceiver, Dest d#) #)
                              & putDebugLn# (
                                        "alloc: [region] <- #"
                                          ++ (show . ptrToWord . Ptr $ pRootReceiver)
                                          ++ ": Ur _@"
                                          ++ (show . ptrToWord . ptrD $ d#)
                                )

-------------------------------------------------------------------------------
-- Metaprogramming stuff for dests
-------------------------------------------------------------------------------

class LiftDest (liftedCtor :: k) (a :: Type) where
  liftDests :: forall r. DestsOf# liftedCtor a %1 -> DestsOf liftedCtor r a
  unliftDests :: forall r. DestsOf liftedCtor r a %1 -> DestsOf# liftedCtor a

instance (LiftedCtorToSymbol liftedCtor ~ symCtor, 'Just specCtor ~ GCtorInfoOf symCtor (Rep a ()), GLiftDest specCtor) => LiftDest liftedCtor a where
  liftDests = gLiftDest @specCtor
  {-# INLINE liftDests #-}
  unliftDests = gUnliftDests @specCtor
  {-# INLINE unliftDests #-}

-- {-# RULES
-- "gUnliftDests/gLiftDests"    forall x. gUnliftDest (gLiftDest x) = x
-- #-}
-- The other direction is might not be a NO-OP but a region coercion instead

class GLiftDest (specCtor :: (Meta, [(Meta, Type)])) where
  gLiftDest :: forall r. GDestsOf# specCtor %1 -> GDestsOf specCtor r
  gUnliftDests :: forall r. GDestsOf specCtor r %1 -> GDestsOf# specCtor

instance GLiftDest '(metaCtor, '[]) where
  gLiftDest (# #) = ()
  gUnliftDests () = (# #)
instance GLiftDest '(metaCtor, '[ '(mS0, t0)]) where
  gLiftDest (# d0# #) = Dest d0#
  gUnliftDests (Dest d0#) = (# d0# #)
instance GLiftDest '(metaCtor, '[ '(mS0, t0), '(mS1, t1)]) where
  gLiftDest (# d0#, d1# #) = (Dest d0#, Dest d1#)
  gUnliftDests (Dest d0#, Dest d1#) = (# d0#, d1# #)
instance GLiftDest '(metaCtor, '[ '(mS0, t0), '(mS1, t1), '(mS2, t2)]) where
  gLiftDest (# d0#, d1#, d2# #) = (Dest d0#, Dest d1#, Dest d2#)
  gUnliftDests (Dest d0#, Dest d1#, Dest d2#) = (# d0#, d1#, d2# #)
instance GLiftDest '(metaCtor, '[ '(mS0, t0), '(mS1, t1), '(mS2, t2), '(mS3, t3)]) where
  gLiftDest (# d0#, d1#, d2#, d3# #) = (Dest d0#, Dest d1#, Dest d2#, Dest d3#)
  gUnliftDests (Dest d0#, Dest d1#, Dest d2#, Dest d3#) = (# d0#, d1#, d2#, d3# #)
instance GLiftDest '(metaCtor, '[ '(mS0, t0), '(mS1, t1), '(mS2, t2), '(mS3, t3), '(mS4, t4)]) where
  gLiftDest (# d0#, d1#, d2#, d3#, d4# #) = (Dest d0#, Dest d1#, Dest d2#, Dest d3#, Dest d4#)
  gUnliftDests (Dest d0#, Dest d1#, Dest d2#, Dest d3#, Dest d4#) = (# d0#, d1#, d2#, d3#, d4# #)
instance GLiftDest '(metaCtor, '[ '(mS0, t0), '(mS1, t1), '(mS2, t2), '(mS3, t3), '(mS4, t4), '(mS5, t5)]) where
  gLiftDest (# d0#, d1#, d2#, d3#, d4#, d5# #) = (Dest d0#, Dest d1#, Dest d2#, Dest d3#, Dest d4#, Dest d5#)
  gUnliftDests (Dest d0#, Dest d1#, Dest d2#, Dest d3#, Dest d4#, Dest d5#) = (# d0#, d1#, d2#, d3#, d4#, d5# #)
instance GLiftDest '(metaCtor, '[ '(mS0, t0), '(mS1, t1), '(mS2, t2), '(mS3, t3), '(mS4, t4), '(mS5, t5), '(mS6, t6)]) where
  gLiftDest (# d0#, d1#, d2#, d3#, d4#, d5#, d6# #) = (Dest d0#, Dest d1#, Dest d2#, Dest d3#, Dest d4#, Dest d5#, Dest d6#)
  gUnliftDests (Dest d0#, Dest d1#, Dest d2#, Dest d3#, Dest d4#, Dest d5#, Dest d6#) = (# d0#, d1#, d2#, d3#, d4#, d5#, d6# #)

type family GDestsOf (specCtor :: (Meta, [(Meta, Type)])) r where
  GDestsOf '(_, '[]) _ = ()
  GDestsOf '(_, '[ '(_, t)]) r = Dest r t
  GDestsOf '(_, '[ '(_, t0), '(_, t1)]) r = (Dest r t0, Dest r t1)
  GDestsOf '(_, '[ '(_, t0), '(_, t1), '(_, t2)]) r = (Dest r t0, Dest r t1, Dest r t2)
  GDestsOf '(_, '[ '(_, t0), '(_, t1), '(_, t2), '(_, t3)]) r = (Dest r t0, Dest r t1, Dest r t2, Dest r t3)
  GDestsOf '(_, '[ '(_, t0), '(_, t1), '(_, t2), '(_, t3), '(_, t4)]) r = (Dest r t0, Dest r t1, Dest r t2, Dest r t3, Dest r t4)
  GDestsOf '(_, '[ '(_, t0), '(_, t1), '(_, t2), '(_, t3), '(_, t4), '(_, t5)]) r = (Dest r t0, Dest r t1, Dest r t2, Dest r t3, Dest r t4, Dest r t5)
  GDestsOf '(_, '[ '(_, t0), '(_, t1), '(_, t2), '(_, t3), '(_, t4), '(_, t5), '(_, t6)]) r = (Dest r t0, Dest r t1, Dest r t2, Dest r t3, Dest r t4, Dest r t5, Dest r t6)
  GDestsOf _ _ _ = TypeError ('Text "GDestsOf not implemented for constructors with more than 7 fields")

type family DestsOf (liftedCtor :: k) r (a :: Type) where
  DestsOf liftedCtor r a = GDestsOf (FromJust (GCtorInfoOf (LiftedCtorToSymbol liftedCtor) (Rep a ()))) r

-- TODO: remove State# RealWorld from type family
type family GDestsOf# (specCtor :: (Meta, [(Meta, Type)])) where
  GDestsOf# '(_, '[]) = (# #)
  GDestsOf# '(_, '[ '(_, t)]) = (# Dest# t #)
  GDestsOf# '(_, '[ '(_, t0), '(_, t1)]) = (# Dest# t0, Dest# t1 #)
  GDestsOf# '(_, '[ '(_, t0), '(_, t1), '(_, t2)]) = (# Dest# t0, Dest# t1, Dest# t2 #)
  GDestsOf# '(_, '[ '(_, t0), '(_, t1), '(_, t2), '(_, t3)]) = (# Dest# t0, Dest# t1, Dest# t2, Dest# t3 #)
  GDestsOf# '(_, '[ '(_, t0), '(_, t1), '(_, t2), '(_, t3), '(_, t4)]) = (# Dest# t0, Dest# t1, Dest# t2, Dest# t3, Dest# t4 #)
  GDestsOf# '(_, '[ '(_, t0), '(_, t1), '(_, t2), '(_, t3), '(_, t4), '(_, t5)]) = (# Dest# t0, Dest# t1, Dest# t2, Dest# t3, Dest# t4, Dest# t5 #)
  GDestsOf# '(_, '[ '(_, t0), '(_, t1), '(_, t2), '(_, t3), '(_, t4), '(_, t5), '(_, t6)]) = (# Dest# t0, Dest# t1, Dest# t2, Dest# t3, Dest# t4, Dest# t5, Dest# t6 #)
  GDestsOf# _ _ = TypeError ('Text "GDestsOf# not implemented for constructors with more than 7 fields")

type family DestsOf# (liftedCtor :: k) (a :: Type) where
  DestsOf# liftedCtor a = GDestsOf# (FromJust (GCtorInfoOf (LiftedCtorToSymbol liftedCtor) (Rep a ())))

class Fill# (liftedCtor :: k) (a :: Type) where
  fill# :: Compact# -> Dest# a -> State# RealWorld -> (# State# RealWorld, DestsOf# liftedCtor a #)

instance (LiftedCtorToSymbol liftedCtor ~ symCtor, 'Just specCtor ~ GCtorInfoOf symCtor (Rep a ()), GDestsOf# specCtor a ~ DestsOf# liftedCtor a, GFill# liftedCtor specCtor a) => Fill# liftedCtor a where
  fill# = gFill# @liftedCtor @specCtor @a
  {-# INLINE fill# #-}

-- x must be already in the same region as the value, and fully evaluated
affect# :: Dest# a -> a -> State# RealWorld -> (# State# RealWorld, Addr# #)
affect# dest xInRegion s0 = case anyToAddr# xInRegion s0 of
  (# s1, pX #) -> let s2 = writeAddrOffAddr# (unsafeCoerceAddr dest) 0# pX s1 in (# s2, pX #)
{-# INLINE affect# #-}

showFill :: Ptr Word -> Ptr Word -> String -> [Ptr Word] -> String
showFill parentWriteLoc xAddr ctorName slots =
  "fill"
    ++ (show n)
    ++ ": @"
    ++ show (ptrToWord parentWriteLoc)
    ++ " <- #"
    ++ show (ptrToWord xAddr)
    ++ ": "
    ++ ctorName
    ++ " "
    ++ showSlots slots
  where
    n = length slots
    showSlots = intercalate " " . fmap showSlot
    showSlot ptr = "_@" ++ (show $ ptrToWord ptr)

-- ctor :: (Meta, [(Meta, Type)])
class GFill# (liftedCtor :: k) (specCtor :: (Meta, [(Meta, Type)])) (a :: Type) where
  gFill# :: Compact# -> MVar# -> Dest# a -> State# RealWorld -> (# State# RealWorld, GDestsOf# specCtor #)

instance (Generic a, repA ~ Rep a (), metaA ~ GDatatypeMetaOf repA, Datatype metaA, 'MetaCons symCtor fix hasSel ~ metaCtor, Constructor metaCtor, LiftedCtorToSymbol liftedCtor ~ symCtor) => GFill# liftedCtor '(metaCtor, '[]) a where
  gFill# :: Compact# -> MVar# RealWorld () -> Dest# a -> State# RealWorld -> (# State# RealWorld, GDestsOf# specCtor #)
  gFill# compact mvar dest s0 =
    case takeMVar# mvar s0 of
      (# s1, () #) ->
        case compactAddShallow# compact (reflectCtorInfoPtr# @liftedCtor (# #)) s1 of
          (# s2, xInRegion #) -> case affect# dest xInRegion s2 of
            (# s3, addr# #) -> case putMVar# mvar () s3 of
              s4 -> (# s4, (# #) #) & putDebugLn# (showFill (Ptr $ unsafeCoerceAddr dest) (Ptr addr#) (ctorName $ getCtorData @metaCtor) [])
  {-# INLINE gFill# #-}

-- TODO: add constraints on ds_i variables to ensure no unpacking
instance (Generic a, repA ~ Rep a (), metaA ~ GDatatypeMetaOf repA, Datatype metaA, 'MetaCons symCtor fix hasSel ~ metaCtor, Constructor metaCtor, GShallow symCtor repA) => GFill# liftedCtor '(metaCtor, '[ '( 'MetaSel f0 u0 ss0 ds0, t0)]) a where
  gFill# :: Compact# -> MVar# RealWorld () -> Dest# a -> State# RealWorld -> (# State# RealWorld, GDestsOf# specCtor #)
  gFill# compact mvar dest s0 =
    case takeMVar# mvar s0 of
      (# s1, () #) ->
        case compactAddShallow# compact (reflectCtorInfoPtr# @liftedCtor (# #)) s1 of
          (# s2, xInRegion #) -> case affect# dest xInRegion s2 of
            (# s3, addr# #) -> case getSlots1# xInRegion s3 of
              (# s4, res@(# d0# #) #) -> case putMVar# mvar () s4 of
                s5 -> (# s5, res #) & putDebugLn# (showFill (Ptr $ unsafeCoerceAddr dest) (Ptr addr#) (ctorName $ getCtorData @metaCtor) [ptrD d0#])
  {-# INLINE gFill# #-}


-- TODO: add constraints on ds_i variables to ensure no unpacking
instance (Generic a, repA ~ Rep a (), metaA ~ GDatatypeMetaOf repA, Datatype metaA, 'MetaCons symCtor fix hasSel ~ metaCtor, Constructor metaCtor, GShallow symCtor repA) => GFill# liftedCtor '(metaCtor, '[ '( 'MetaSel f0 u0 ss0 ds0, t0), '( 'MetaSel f1 u1 ss1 ds1, t1)]) a where
  gFill# :: Compact# -> MVar# RealWorld () -> Dest# a -> State# RealWorld -> (# State# RealWorld, GDestsOf# specCtor #)
  gFill# compact mvar dest s0 =
    case takeMVar# mvar s0 of
      (# s1, () #) ->
        case compactAddShallow# compact (reflectCtorInfoPtr# @liftedCtor (# #)) s1 of
          (# s2, xInRegion #) -> case affect# dest xInRegion s2 of
            (# s3, addr# #) -> case getSlots2# xInRegion s3 of
              (# s4, res@(# d0#, d1# #) #) -> case putMVar# mvar () s4 of
                s5 -> (# s5, res #) & putDebugLn# (showFill (Ptr $ unsafeCoerceAddr dest) (Ptr addr#) (ctorName $ getCtorData @metaCtor) [ptrD d0#, ptrD d1#])
  {-# INLINE gFill# #-}


-- TODO: add constraints on ds_i variables to ensure no unpacking
instance (Generic a, repA ~ Rep a (), metaA ~ GDatatypeMetaOf repA, Datatype metaA, 'MetaCons symCtor fix hasSel ~ metaCtor, Constructor metaCtor, GShallow symCtor repA) => GFill# liftedCtor '(metaCtor, '[ '( 'MetaSel f0 u0 ss0 ds0, t0), '( 'MetaSel f1 u1 ss1 ds1, t1), '( 'MetaSel f2 u2 ss2 ds2, t2)]) a where
  gFill# :: Compact# -> MVar# RealWorld () -> Dest# a -> State# RealWorld -> (# State# RealWorld, GDestsOf# specCtor #)
  gFill# compact mvar dest s0 =
    case takeMVar# mvar s0 of
      (# s1, () #) ->
        case compactAddShallow# compact (reflectCtorInfoPtr# @liftedCtor (# #)) s1 of
          (# s2, xInRegion #) -> case affect# dest xInRegion s2 of
            (# s3, addr# #) -> case getSlots3# xInRegion s3 of
              (# s4, res@(# d0#, d1#, d2# #) #) -> case putMVar# mvar () s4 of
                s5 -> (# s5, res #) & putDebugLn# (showFill (Ptr $ unsafeCoerceAddr dest) (Ptr addr#) (ctorName $ getCtorData @metaCtor) [ptrD d0#, ptrD d1#, ptrD d2#])
  {-# INLINE gFill# #-}


-- TODO: add constraints on ds_i variables to ensure no unpacking
instance (Generic a, repA ~ Rep a (), metaA ~ GDatatypeMetaOf repA, Datatype metaA, 'MetaCons symCtor fix hasSel ~ metaCtor, Constructor metaCtor, GShallow symCtor repA) => GFill# liftedCtor '(metaCtor, '[ '( 'MetaSel f0 u0 ss0 ds0, t0), '( 'MetaSel f1 u1 ss1 ds1, t1), '( 'MetaSel f2 u2 ss2 ds2, t2), '( 'MetaSel f3 u3 ss3 ds3, t3)]) a where
  gFill# :: Compact# -> MVar# RealWorld () -> Dest# a -> State# RealWorld -> (# State# RealWorld, GDestsOf# specCtor #)
  gFill# compact mvar dest s0 =
    case takeMVar# mvar s0 of
      (# s1, () #) ->
        case compactAddShallow# compact (reflectCtorInfoPtr# @liftedCtor (# #)) s1 of
          (# s2, xInRegion #) -> case affect# dest xInRegion s2 of
            (# s3, addr# #) -> case getSlots4# xInRegion s3 of
              (# s4, res@(# d0#, d1#, d2#, d3# #) #) -> case putMVar# mvar () s4 of
                s5 -> (# s5, res #) & putDebugLn# (showFill (Ptr $ unsafeCoerceAddr dest) (Ptr addr#) (ctorName $ getCtorData @metaCtor) [ptrD d0#, ptrD d1#, ptrD d2#, ptrD d3#])
  {-# INLINE gFill# #-}


-- TODO: add constraints on ds_i variables to ensure no unpacking
instance (Generic a, repA ~ Rep a (), metaA ~ GDatatypeMetaOf repA, Datatype metaA, 'MetaCons symCtor fix hasSel ~ metaCtor, Constructor metaCtor, GShallow symCtor repA) => GFill# liftedCtor '(metaCtor, '[ '( 'MetaSel f0 u0 ss0 ds0, t0), '( 'MetaSel f1 u1 ss1 ds1, t1), '( 'MetaSel f2 u2 ss2 ds2, t2), '( 'MetaSel f3 u3 ss3 ds3, t3), '( 'MetaSel f4 u4 ss4 ds4, t4)]) a where
  gFill# :: Compact# -> MVar# RealWorld () -> Dest# a -> State# RealWorld -> (# State# RealWorld, GDestsOf# specCtor #)
  gFill# compact mvar dest s0 =
    case takeMVar# mvar s0 of
      (# s1, () #) ->
        case compactAddShallow# compact (reflectCtorInfoPtr# @liftedCtor (# #)) s1 of
          (# s2, xInRegion #) -> case affect# dest xInRegion s2 of
            (# s3, addr# #) -> case getSlots5# xInRegion s3 of
              (# s4, res@(# d0#, d1#, d2#, d3#, d4# #) #) -> case putMVar# mvar () s4 of
                s5 -> (# s5, res #) & putDebugLn# (showFill (Ptr $ unsafeCoerceAddr dest) (Ptr addr#) (ctorName $ getCtorData @metaCtor) [ptrD d0#, ptrD d1#, ptrD d2#, ptrD d3#, ptrD d4#])
  {-# INLINE gFill# #-}


-- TODO: add constraints on ds_i variables to ensure no unpacking
instance (Generic a, repA ~ Rep a (), metaA ~ GDatatypeMetaOf repA, Datatype metaA, 'MetaCons symCtor fix hasSel ~ metaCtor, Constructor metaCtor, GShallow symCtor repA) => GFill# liftedCtor '(metaCtor, '[ '( 'MetaSel f0 u0 ss0 ds0, t0), '( 'MetaSel f1 u1 ss1 ds1, t1), '( 'MetaSel f2 u2 ss2 ds2, t2), '( 'MetaSel f3 u3 ss3 ds3, t3), '( 'MetaSel f4 u4 ss4 ds4, t4), '( 'MetaSel f5 u5 ss5 ds5, t5)]) a where
  gFill# :: Compact# -> MVar# RealWorld () -> Dest# a -> State# RealWorld -> (# State# RealWorld, GDestsOf# specCtor #)
  gFill# compact mvar dest s0 =
    case takeMVar# mvar s0 of
      (# s1, () #) ->
        case compactAddShallow# compact (reflectCtorInfoPtr# @liftedCtor (# #)) s1 of
          (# s2, xInRegion #) -> case affect# dest xInRegion s2 of
            (# s3, addr# #) -> case getSlots6# xInRegion s3 of
              (# s4, res@(# d0#, d1#, d2#, d3#, d4#, d5# #) #) -> case putMVar# mvar () s4 of
                s5 -> (# s5, res #) & putDebugLn# (showFill (Ptr $ unsafeCoerceAddr dest) (Ptr addr#) (ctorName $ getCtorData @metaCtor) [ptrD d0#, ptrD d1#, ptrD d2#, ptrD d3#, ptrD d4#, ptrD d5#])
  {-# INLINE gFill# #-}


-- TODO: add constraints on ds_i variables to ensure no unpacking
instance (Generic a, repA ~ Rep a (), metaA ~ GDatatypeMetaOf repA, Datatype metaA, 'MetaCons symCtor fix hasSel ~ metaCtor, Constructor metaCtor, GShallow symCtor repA) => GFill# liftedCtor '(metaCtor, '[ '( 'MetaSel f0 u0 ss0 ds0, t0), '( 'MetaSel f1 u1 ss1 ds1, t1), '( 'MetaSel f2 u2 ss2 ds2, t2), '( 'MetaSel f3 u3 ss3 ds3, t3), '( 'MetaSel f4 u4 ss4 ds4, t4), '( 'MetaSel f5 u5 ss5 ds5, t5), '( 'MetaSel f6 u6 ss6 ds6, t6)]) a where
  gFill# :: Compact# -> MVar# RealWorld () -> Dest# a -> State# RealWorld -> (# State# RealWorld, GDestsOf# specCtor #)
  gFill# compact mvar dest s0 =
    case takeMVar# mvar s0 of
      (# s1, () #) ->
        case compactAddShallow# compact (reflectCtorInfoPtr# @liftedCtor (# #)) s1 of
          (# s2, xInRegion #) -> case affect# dest xInRegion s2 of
            (# s3, addr# #) -> case getSlots7# xInRegion s3 of
              (# s4, res@(# d0#, d1#, d2#, d3#, d4#, d5#, d6# #) #) -> case putMVar# mvar () s4 of
                s5 -> (# s5, res #) & putDebugLn# (showFill (Ptr $ unsafeCoerceAddr dest) (Ptr addr#) (ctorName $ getCtorData @metaCtor) [ptrD d0#, ptrD d1#, ptrD d2#, ptrD d3#, ptrD d4#, ptrD d5#, ptrD d6#])
  {-# INLINE gFill# #-}

type family Length (a :: [k]) :: Nat where
  Length '[] = 0
  Length (_ : xs) = 1 + Length xs
  Length _ = TypeError ('Text "No match for Length")

type family (a :: [k]) ++ (b :: [k]) :: [k] where
  '[] ++ y = y
  (x : xs) ++ y = x : (xs ++ y)
  _ ++ _ = TypeError ('Text "No match for ++")

type family GDatatypeMetaOf (repA :: Type) :: Meta where
  GDatatypeMetaOf (D1 meta f p) = meta
  GDatatypeMetaOf (M1 _ _ f p) = GDatatypeMetaOf (f p)
  GDatatypeMetaOf _ = TypeError ('Text "No match for GDatatypeMetaOf")

type family GFieldsOf (repA :: Type) :: [(Meta, Type)] where
  GFieldsOf (S1 meta f p) = '[ '(meta, GSlotTypeOf (f p))]
  GFieldsOf (U1 _) = '[]
  GFieldsOf ((f :*: g) p) = GFieldsOf (f p) ++ GFieldsOf (g p)
  GFieldsOf (M1 _ _ f p) = GFieldsOf (f p)
  GFieldsOf _ = TypeError ('Text "No match for GFieldsOf")

type family GSlotTypeOf (repA :: Type) :: Type where
  GSlotTypeOf (K1 _ c _) = c
  GSlotTypeOf (M1 _ _ f p) = GSlotTypeOf (f p)
  GSlotTypeOf _ = TypeError ('Text "No match for GSlotTypeOf")

type family GCtorsOf (repA :: Type) :: [(Meta, [(Meta, Type)])] where
  GCtorsOf (C1 meta f p) = '[ '(meta, GFieldsOf (f p))]
  GCtorsOf (M1 _ _ f p) = GCtorsOf (f p)
  GCtorsOf ((f :+: g) p) = GCtorsOf (f p) ++ GCtorsOf (g p)
  GCtorsOf _ = TypeError ('Text "No match for GCtorsOf")

type family GCtorInfoOf (symCtor :: Symbol) (repA :: Type) :: Maybe (Meta, [(Meta, Type)]) where
  -- GCtorInfoOf "leaf" _ = 'Just '( ('MetaCons "leaf" 'PrefixI 'False), '[])
  -- GCtorInfoOf "comp" _ = 'Just '( ('MetaCons "comp" 'PrefixI 'False), '[])
  GCtorInfoOf symCtor (C1 ('MetaCons symCtor x y) f p) = 'Just '(('MetaCons symCtor x y), GFieldsOf (f p))
  GCtorInfoOf symCtor (C1 ('MetaCons _ _ _) _ _) = 'Nothing
  GCtorInfoOf symCtor ((f :+: g) p) = GCtorInfoOf symCtor (f p) <|> GCtorInfoOf symCtor (g p)
  GCtorInfoOf symCtor (V1 _) = 'Nothing
  GCtorInfoOf symCtor (M1 _ _ f p) = GCtorInfoOf symCtor (f p)
  GCtorInfoOf _ _ = TypeError ('Text "No match for GHasCtor")

type family IsJust (x :: Maybe k) :: Bool where
  IsJust ('Just v) = 'True
  IsJust 'Nothing = 'False

type family FromJust (x :: Maybe k) :: k where
  FromJust ('Just v) = v
  FromJust 'Nothing = TypeError ('Text "FromJust error: got 'Nothing")

type family (x :: Maybe k) <|> (y :: Maybe k) :: Maybe k where
  ('Just v) <|> _ = 'Just v
  'Nothing <|> y = y

type family (a :: Bool) || (b :: Bool) :: Bool where
  'False || b = b
  'True || _ = 'True

type family IfT (a :: Bool) (x :: k) (y :: k) :: k where
  IfT 'True x _ = x
  IfT 'False _ y = y

class KnownBool (b :: Bool) where
  ifV :: ((b ~ 'True) => a) -> ((b ~ 'False) => a) -> a

instance KnownBool 'True where
  ifV t _ = t

instance KnownBool 'False where
  ifV _ f = f

template = """
-- TODO: add constraints on ds_i variables to ensure no unpacking
instance (Generic a, repA ~ Rep a (), metaA ~ GDatatypeMetaOf repA, Datatype metaA, 'MetaCons symCtor fix hasSel ~ metaCtor, Constructor metaCtor, GShallow symCtor repA) => GFill# liftedCtor '(metaCtor, '[ {metaSelList}]) a where
  gFill# :: Compact# -> MVar# RealWorld () -> Dest# a -> State# RealWorld -> (# State# RealWorld, GDestsOf# specCtor #)
  gFill# compact mvar dest s0 =
    case takeMVar# mvar s0 of
      (# s1, () #) ->
        case compactAddShallow# compact (reflectCtorInfoPtr# @liftedCtor (# #)) s1 of
          (# s2, xInRegion #) -> case affect# dest xInRegion s2 of
            (# s3, addr# #) -> case getSlots{n}# xInRegion s3 of
              (# s4, res@(# {destPrimList} #) #) -> case putMVar# mvar () s4 of
                s5 -> (# s5, res #) & putDebugLn# (showFill (Ptr $ unsafeCoerceAddr dest) (Ptr addr#) (ctorName $ getCtorData @metaCtor) [{ptrDList}])
  {{-# INLINE gFill# #-}}"""

for n in range(1, 7+1):
    metaSelList = ", ".join(["'( 'MetaSel f{} u{} ss{} ds{}, t{})".format(i, i, i, i, i) for i in range(n)])
    destPrimList = ", ".join(["d{}#".format(i) for i in range(n)])
    ptrDList = ", ".join(["ptrD d{}#".format(i) for i in range(n)])
    print(template.format(n=n, destPrimList=destPrimList, ptrDList=ptrDList, metaSelList=metaSelList))
    print()

for n in range(1, 7 + 1):
    r = ", ".join("'(mS{}, t{})".format(i, i) for i in range(n))
    print(r)

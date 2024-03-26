{-# LANGUAGE UndecidableInstances #-}
{-# OPTIONS_GHC -Wno-missing-export-lists #-}

module PriceDiscoveryEvent.Utils where

import Data.Text qualified as T
import Plutarch.Api.V1 (AmountGuarantees (Positive), KeyGuarantees (Sorted), PCredential (PPubKeyCredential, PScriptCredential))
import Plutarch.Api.V1.Scripts (PScriptHash)
import Plutarch.Api.V1.Value (padaSymbol, pvalueOf, pnormalize)
import Plutarch.Api.V1.AssocMap qualified as AssocMap

import Plutarch.Api.V2 (
  PAddress,
  PCurrencySymbol,
  PMap (PMap),
  PPubKeyHash,
  PTokenName,
  PTxInInfo,
  PTxOut,
  PTxOutRef,
  PValue (..),
 )
import Plutarch.Bool (pand')
import "liqwid-plutarch-extra" Plutarch.Extra.List (plookupAssoc)
import "liqwid-plutarch-extra" Plutarch.Extra.TermCont (pmatchC)
import Plutarch.Monadic qualified as P
import Plutarch.Prelude
import Plutarch.Api.V1 (AmountGuarantees(..))
import qualified Plutarch.Api.V1.Value as Value
import Plutarch.Api.V2 (PInterval)
import Plutarch.Api.V1 (PPOSIXTime)
import Plutarch.Api.V2 (PExtended(PFinite))
import Plutarch.Internal
data PTriple (a :: PType) (b :: PType) (c :: PType) (s :: S)
  = PTriple (Term s a) (Term s b) (Term s c)
  deriving stock (Generic)
  deriving anyclass (PlutusType, PEq, PShow)

instance DerivePlutusType (PTriple a b c) where type DPTStrat _ = PlutusTypeScott

ppair :: Term s a -> Term s b -> Term s (PPair a b)
ppair a b = pcon (PPair a b)

{- | If the input is True then continue otherwise throw an error message.
   Short trace is a sequence of first letters of long trace words.
-}
passert ::
  forall (s :: S) (a :: PType).
  T.Text -> -- long trace
  Term s PBool ->
  Term s a ->
  Term s a
passert longErrorMsg b inp = pif b inp $ ptraceError (pconstant longErrorMsg)

-- | If the input is True then returns PJust otherwise PNothing
pcheck :: forall (s :: S) (a :: PType). Term s PBool -> Term s a -> Term s (PMaybe a)
pcheck b inp = pif b (pcon $ PJust inp) (pcon PNothing)

{- | Finds the associated Currency symbols that contain token
  names prefixed with the ByteString.
-}
pfindCurrencySymbolsByTokenPrefix ::
  forall
    (anyOrder :: KeyGuarantees)
    (anyAmount :: AmountGuarantees).
  ClosedTerm
    ( PValue anyOrder anyAmount
        :--> PByteString
        :--> PBuiltinList (PAsData PCurrencySymbol)
    )
pfindCurrencySymbolsByTokenPrefix = phoistAcyclic $
  plam $ \value prefix ->
    plet (pisPrefixOf # prefix) $ \prefixCheck ->
      let mapVal = pto (pto value)
          isPrefixed = pfilter # plam (\csPair -> pany # plam (\tk -> prefixCheck # pto (pfromData (pfstBuiltin # tk))) # (pto $ pfromData (psndBuiltin # csPair))) # mapVal
       in pmap # pfstBuiltin # isPrefixed

pcountScriptInputs :: Term s (PBuiltinList PTxInInfo :--> PInteger)
pcountScriptInputs =
  phoistAcyclic $
    let go :: Term s (PInteger :--> PBuiltinList PTxInInfo :--> PInteger)
        go = pfix #$ plam $ \self n -> 
              pelimList 
                (\x xs -> 
                  let cred = pfield @"credential" # (pfield @"address" # (pfield @"resolved" # x))
                   in pmatch cred $ \case 
                        PScriptCredential _ -> self # (n + 1) # xs
                        _ -> self # n # xs
                )
                n
     in go # 0

pfoldl2 ::
  (PListLike listA, PListLike listB, PElemConstraint listA a, PElemConstraint listB b) =>
  Term s ((acc :--> a :--> b :--> acc) :--> acc :--> listA a :--> listB b :--> acc)
pfoldl2 =
  phoistAcyclic $ plam $ \func ->
    pfix #$ plam $ \self acc la lb ->
      pelimList
        ( \a as ->
            pelimList
              (\b bs -> self # (func # acc # a # b) # as # bs)
              perror
              lb
        )
        (pif (pnull # lb) acc perror)
        la

pelemAtWithRest' :: PListLike list => PElemConstraint list a => Term s (PInteger :--> list a :--> PPair a (list a))
pelemAtWithRest' = phoistAcyclic $
  pfix #$ plam $ \self n xs ->
    pif
      (n #== 0)
      (pcon $ PPair (phead # xs) (ptail # xs))
      (self # (n - 1) #$ ptail # xs)

pmapIdxs ::
  (PListLike listB, PElemConstraint listB b) =>
  Term s (PBuiltinList (PAsData PInteger) :--> listB b :--> listB b)
pmapIdxs =
  phoistAcyclic $
    pfix #$ plam $ \self la lb ->
      pelimList
        ( \a as -> P.do
            PPair foundEle xs <- pmatch $ pelemAtWithRest' # pfromData a # lb
            (pcons # foundEle # (self # as # xs))
        )
        pnil
        la

{- | Finds the associated Currency symbols that contain the given token
  name.
-}
pfindCurrencySymbolsByTokenName ::
  forall
    (anyOrder :: KeyGuarantees)
    (anyAmount :: AmountGuarantees).
  ClosedTerm
    ( PValue anyOrder anyAmount
        :--> PTokenName
        :--> PBuiltinList (PAsData PCurrencySymbol)
    )
pfindCurrencySymbolsByTokenName = phoistAcyclic $
  plam $ \value tn ->
      let mapVal = pto (pto value)
          hasTn = pfilter # plam (\csPair -> pany # plam (\tk -> tn #== (pfromData (pfstBuiltin # tk))) # (pto $ pfromData (psndBuiltin # csPair))) # mapVal
       in pmap # pfstBuiltin # hasTn

-- | Checks if a Currency Symbol is held within a Value
phasDataCS ::
  forall
    (anyOrder :: KeyGuarantees)
    (anyAmount :: AmountGuarantees).
  ClosedTerm
    (PAsData PCurrencySymbol :--> PValue anyOrder anyAmount :--> PBool)
phasDataCS = phoistAcyclic $
  plam $ \symbol value ->
    pany # plam (\tkPair -> (pfstBuiltin # tkPair) #== symbol) #$ pto (pto value)

phasCS ::
  forall
    (anyOrder :: KeyGuarantees)
    (anyAmount :: AmountGuarantees).
  ClosedTerm
    (PValue anyOrder anyAmount :--> PCurrencySymbol :--> PBool)
phasCS = phoistAcyclic $
  plam $ \value symbol ->
    pany # plam (\tkPair -> pfromData (pfstBuiltin # tkPair) #== symbol) #$ pto (pto value)

-- | Checks that a Value contains all the given CurrencySymbols.
pcontainsCurrencySymbols ::
  forall
    (anyOrder :: KeyGuarantees)
    (anyAmount :: AmountGuarantees).
  ClosedTerm
    ( PValue anyOrder anyAmount
        :--> PBuiltinList (PAsData PCurrencySymbol)
        :--> PBool
    )
pcontainsCurrencySymbols = phoistAcyclic $
  plam $ \inValue symbols ->
    let value = pmap # pfstBuiltin #$ pto $ pto inValue
        containsCS = plam $ \cs -> pelem # cs # value
     in pall # containsCS # symbols

-- | Checks if a tokenName is prefixed by a certain ByteString
pisPrefixedWith :: ClosedTerm (PTokenName :--> PByteString :--> PBool)
pisPrefixedWith = plam $ \tn prefix ->
  let tnBS = pto tn
   in pisPrefixOf # prefix # tnBS

-- | Checks if the first ByteString is a prefix of the second
pisPrefixOf :: ClosedTerm (PByteString :--> PByteString :--> PBool)
pisPrefixOf = plam $ \prefix src ->
  let prefixLength = plengthBS # prefix
      prefix' = psliceBS # 0 # prefixLength # src
   in prefix' #== prefix

tcexpectJust :: forall r (a :: PType) (s :: S). Term s r -> Term s (PMaybe a) -> TermCont @r s (Term s a)
tcexpectJust escape ma = tcont $ \f -> pmatch ma $ \case
  PJust v -> f v
  PNothing -> escape

paysToAddress :: Term s (PAddress :--> PTxOut :--> PBool)
paysToAddress = phoistAcyclic $ plam $ \adr txOut -> adr #== (pfield @"address" # txOut)

paysValueToAddress ::
  Term s (PValue 'Sorted 'Positive :--> PAddress :--> PTxOut :--> PBool)
paysValueToAddress = phoistAcyclic $
  plam $ \val adr txOut ->
    pletFields @["address", "value"] txOut $ \txoFields ->
      txoFields.address #== adr #&& txoFields.value #== val

paysAtleastValueToAddress ::
  Term s (PValue 'Sorted 'Positive :--> PAddress :--> PTxOut :--> PBool)
paysAtleastValueToAddress = phoistAcyclic $
  plam $ \val adr txOut ->
    pletFields @["address", "value"] txOut $ \txoFields ->
      txoFields.address #== adr #&& txoFields.value #<= val

paysToCredential :: Term s (PScriptHash :--> PTxOut :--> PBool)
paysToCredential = phoistAcyclic $
  plam $ \valHash txOut ->
    let txOutCred = pfield @"credential" # (pfield @"address" # txOut)
     in pmatch txOutCred $ \case
          PScriptCredential txOutValHash -> (pfield @"_0" # txOutValHash) #== valHash
          PPubKeyCredential _ -> (pcon PFalse)

pelemAt' :: PIsListLike l a => Term s (PInteger :--> l a :--> a)
pelemAt' = phoistAcyclic $
  pfix #$ plam $ \self n xs ->
    pif
      (n #== 0)
      (phead # xs)
      (self # (n - 1) #$ ptail # xs)

pelemAtFlipped' :: PIsListLike l a => Term s (l a :--> PInteger :--> a)
pelemAtFlipped' = phoistAcyclic $
  pfix #$ plam $ \self xs n ->
    pif
      (n #== 0)
      (phead # xs)
      (self # (ptail # xs) # (n - 1))

pmapMaybe ::
  forall (list :: PType -> PType) (a :: PType) (b :: PType).
  PListLike list =>
  PElemConstraint list a =>
  PElemConstraint list b =>
  ClosedTerm ((a :--> PMaybe b) :--> list a :--> list b)
pmapMaybe =
  phoistAcyclic $
    plam $ \func ->
      precList
        ( \self x xs ->
            pmatch (func # x) $ \case
              PJust y -> (pcons # y # (self # xs))
              PNothing -> (self # xs)
        )
        (const pnil)

paysToPubKey :: Term s (PPubKeyHash :--> PTxOut :--> PBool)
paysToPubKey = phoistAcyclic $
  plam $ \pkh txOut ->
    let txOutCred = pfield @"credential" # (pfield @"address" # txOut)
     in pmatch txOutCred $ \case
          PScriptCredential _ -> pconstant False
          PPubKeyCredential pkh' -> (pfield @"_0" # pkh') #== pkh

ptryOutputToAddress :: (PIsListLike list PTxOut) => Term s (list PTxOut :--> PAddress :--> PTxOut)
ptryOutputToAddress = phoistAcyclic $
  plam $ \outs target ->
    ( pfix #$ plam $ \self xs ->
        pelimList
          ( \txo txos ->
              pif (target #== (pfield @"address" # txo)) txo (self # txos)
          )
          perror
          xs
    )
      # outs

ptryOwnOutput :: (PIsListLike list PTxOut) => Term s (list PTxOut :--> PScriptHash :--> PTxOut)
ptryOwnOutput = phoistAcyclic $
  plam $ \outs target ->
    ( pfix #$ plam $ \self xs ->
        pelimList
          ( \txo txos ->
              pmatch (pfield @"credential" # (pfield @"address" # txo)) $ \case
                PPubKeyCredential _ -> (self # txos)
                PScriptCredential ((pfield @"_0" #) -> vh) ->
                  pif (target #== vh) txo (self # txos)
          )
          perror
          xs
    )
      # outs

ptryOwnInput :: (PIsListLike list PTxInInfo) => Term s (list PTxInInfo :--> PTxOutRef :--> PTxOut)
ptryOwnInput = phoistAcyclic $
  plam $ \inputs ownRef ->
    precList (\self x xs -> pletFields @'["outRef", "resolved"] x $ \txInFields -> pif (ownRef #== txInFields.outRef) txInFields.resolved (self # xs)) (const perror) # inputs

pmustFind :: PIsListLike l a => Term s ((a :--> PBool) :--> l a :--> a)
pmustFind =
  phoistAcyclic $ plam $ \f -> pfix #$ plam $ \self xs -> pelimList (\y ys -> pif (f # y) y (self # ys)) perror xs

-- Get the head of the list if the list contains exactly one element, otherwise error.
pheadSingleton :: (PListLike list, PElemConstraint list a) => Term s (list a :--> a)
pheadSingleton = phoistAcyclic $
  plam $ \xs ->
    pelimList
      (pelimList (\_ _ -> ptraceError "List contains more than one element."))
      (ptraceError "List is empty.")
      xs

ptxSignedByPkh ::
  Term s (PAsData PPubKeyHash :--> PBuiltinList (PAsData PPubKeyHash) :--> PBool)
ptxSignedByPkh = pelem

psymbolValueOfHelper ::
  forall
    (keys :: KeyGuarantees)
    (amounts :: AmountGuarantees)
    (s :: S).
  Term
    s
    ( (PInteger :--> PBool)
        :--> PCurrencySymbol
        :--> ( PValue keys amounts
                :--> PInteger
             )
    )
psymbolValueOfHelper =
  phoistAcyclic $
    plam $ \cond sym value'' -> unTermCont $ do
      PValue value' <- pmatchC value''
      PMap value <- pmatchC value'
      m' <-
        tcexpectJust
          0
          ( plookupAssoc
              # pfstBuiltin
              # psndBuiltin
              # pdata sym
              # value
          )
      PMap m <- pmatchC (pfromData m')
      pure $
        pfoldr
          # plam
            ( \x v ->
                plet (pfromData $ psndBuiltin # x) $ \q ->
                  pif
                    (cond # q)
                    (q + v)
                    v
            )
          # 0
          # m

-- | Sum of total positive amounts in Value for a given policyId
ppositiveSymbolValueOf ::
  forall
    (keys :: KeyGuarantees)
    (amounts :: AmountGuarantees)
    (s :: S).
  Term s (PCurrencySymbol :--> (PValue keys amounts :--> PInteger))
ppositiveSymbolValueOf = phoistAcyclic $ psymbolValueOfHelper #$ plam (0 #<)

-- | Sum of total negative amounts in Value for a given policyId
pnegativeSymbolValueOf ::
  forall
    (keys :: KeyGuarantees)
    (amounts :: AmountGuarantees)
    (s :: S).
  Term s (PCurrencySymbol :--> (PValue keys amounts :--> PInteger))
pnegativeSymbolValueOf = phoistAcyclic $ psymbolValueOfHelper #$ plam (#< 0)

-- | Probably more effective than `plength . pflattenValue`
pcountOfUniqueTokens ::
  forall
    (keys :: KeyGuarantees)
    (amounts :: AmountGuarantees)
    (s :: S).
  Term s (PValue keys amounts :--> PInteger)
pcountOfUniqueTokens = phoistAcyclic $
  plam $ \val ->
    let tokensLength = plam (\pair -> pmatch (pfromData $ psndBuiltin # pair) $ \(PMap tokens) -> plength # tokens)
     in pmatch val $ \(PValue val') ->
          pmatch val' $ \(PMap csPairs) -> pfoldl # plam (\acc x -> acc + (tokensLength # x)) # 0 # csPairs

-- | Subtracts one Value from another
(#-) ::
  forall
    (amounts :: AmountGuarantees)
    (s :: S).
  Term s (PValue 'Sorted amounts) ->
  Term s (PValue 'Sorted amounts) ->
  Term s (PValue 'Sorted 'NonZero)
a #- b = pnormalize #$ Value.punionWith # plam (-) # a # b

pfindWithRest ::
  forall (list :: PType -> PType) (a :: PType).
  PListLike list =>
  PElemConstraint list a =>
  ClosedTerm
    ( (a :--> PBool)
        :--> list a
        :--> PPair a (list a)
    )
pfindWithRest = phoistAcyclic $
  plam $ \f ys ->
    let mcons self x xs =
          pmatch (f # x) $ \case
            PTrue -> P.do
              acc <- plam
              pcon $ PPair x (pconcat # acc # xs)
            PFalse -> P.do
              acc <- plam
              self # xs #$ pcons # x # acc
        mnil = const (ptraceError "Find")
     in precList mcons mnil # ys # pnil

pcountCS ::
  forall
    (keys :: KeyGuarantees)
    (amounts :: AmountGuarantees)
    (s :: S).
  Term s (PValue keys amounts :--> PInteger)
pcountCS = phoistAcyclic $
  plam $ \val ->
    pmatch val $ \(PValue val') ->
      pmatch val' $ \(PMap csPairs) ->
        plength # csPairs

pcountNonAdaCS ::
  forall
    (keys :: KeyGuarantees)
    (amounts :: AmountGuarantees)
    (s :: S).
  Term s (PValue keys amounts :--> PInteger)
pcountNonAdaCS =
  phoistAcyclic $
    let go :: Term _ (PInteger :--> PBuiltinList (PBuiltinPair (PAsData PCurrencySymbol) (PAsData (PMap keys PTokenName PInteger))) :--> PInteger)
        go = plet (pdata padaSymbol) $ \padaSymbolD ->
          pfix #$ plam $ \self n ->
            pelimList (\x xs -> pif (pfstBuiltin # x #== padaSymbolD) (self # n # xs) (self # (n + 1) # xs)) n
     in plam $ \val ->
          pmatch val $ \(PValue val') ->
            pmatch val' $ \(PMap csPairs) ->
              go # 0 # csPairs

pfirstTokenName ::
  forall
    (keys :: KeyGuarantees)
    (amounts :: AmountGuarantees)
    (s :: S).
  Term s (PValue keys amounts :--> PTokenName)
pfirstTokenName = phoistAcyclic $
  plam $ \val ->
    pmatch val $ \(PValue val') ->
      pmatch val' $ \(PMap csPairs) ->
        pmatch (pfromData (psndBuiltin # (phead # csPairs))) $ \(PMap tokens) ->
          pfromData $ pfstBuiltin # (phead # tokens)

ptryLookupValue ::
  forall
    (keys :: KeyGuarantees)
    (amounts :: AmountGuarantees)
    (s :: S).
  Term
    s
    ( PAsData PCurrencySymbol
        :--> PValue keys amounts
        :--> PBuiltinList (PBuiltinPair (PAsData PTokenName) (PAsData PInteger))
    )
ptryLookupValue = phoistAcyclic $
  plam $ \policyId val ->
    pmatch val $ \(PValue val') ->
      precList
        ( \self x xs ->
            pif
              (pfstBuiltin # x #== policyId)
              ( pmatch (pfromData (psndBuiltin # x)) $ \(PMap tokens) ->
                  tokens
              )
              (self # xs)
        )
        (const perror)
        # pto val'

{- | Removes a currency symbol from a value 
-}
pfilterCSFromValue ::
  forall
    (anyOrder :: KeyGuarantees)
    (anyAmount :: AmountGuarantees).
  ClosedTerm
    ( PValue anyOrder anyAmount
        :--> PAsData PCurrencySymbol
        :--> PValue anyOrder anyAmount
    )
pfilterCSFromValue = phoistAcyclic $
  plam $ \value policyId ->
      let mapVal = pto (pto value)
          go = pfix #$ plam $ \self ys ->
                pelimList (\x xs -> pif (pfstBuiltin # x #== policyId) xs (pcons # x # (self # xs))) pnil ys
       in pcon (PValue $ pcon $ PMap $ go # mapVal)

psingletonOfCS ::
  forall
    (keys :: KeyGuarantees)
    (amounts :: AmountGuarantees)
    (s :: S).
  Term
    s
    ( PAsData PCurrencySymbol
        :--> PValue keys amounts
        :--> PPair PTokenName PInteger
    )
psingletonOfCS = phoistAcyclic $
  plam $ \policyId val ->
    pmatch val $ \(PValue val') ->
      precList
        ( \self x xs ->
            pif
              (pfstBuiltin # x #== policyId)
              ( pmatch (pfromData (psndBuiltin # x)) $ \(PMap tokens) ->
                  let tkPair = pheadSingleton # tokens
                   in (pcon (PPair (pfromData (pfstBuiltin # tkPair)) (pfromData (psndBuiltin # tkPair))))
              )
              (self # xs)
        )
        (const perror)
        # pto val'

pvalueOfOne ::
  forall
    (keys :: KeyGuarantees)
    (amounts :: AmountGuarantees)
    (s :: S).
  Term
    s
    ( PAsData PCurrencySymbol
        :--> PValue keys amounts
        :--> PBool
    )
pvalueOfOne = phoistAcyclic $
  plam $ \policyId val ->
    pmatch val $ \(PValue val') ->
      precList
        ( \self x xs ->
            pif
              (pfstBuiltin # x #== policyId)
              ( pmatch (pfromData (psndBuiltin # x)) $ \(PMap tokens) ->
                  pfromData (psndBuiltin # (pheadSingleton # tokens)) #== 1
              )
              (self # xs)
        )
        (const (pconstant False))
        # pto val'

pvalueOfOneScott ::
  forall
    (keys :: KeyGuarantees)
    (amounts :: AmountGuarantees)
    (s :: S).
  Term
    s
    ( PCurrencySymbol
        :--> PValue keys amounts
        :--> PBool
    )
pvalueOfOneScott = phoistAcyclic $
  plam $ \policyId val ->
    pmatch val $ \(PValue val') ->
      precList
        ( \self x xs ->
            pif
              (pfromData (pfstBuiltin # x) #== policyId)
              ( pmatch (pfromData (psndBuiltin # x)) $ \(PMap tokens) ->
                  pfromData (psndBuiltin # (pheadSingleton # tokens)) #== 1
              )
              (self # xs)
        )
        (const (pconstant False))
        # pto val'

pfirstTokenNameWithCS ::
  forall
    (keys :: KeyGuarantees)
    (amounts :: AmountGuarantees)
    (s :: S).
  Term s (PAsData PCurrencySymbol :--> PValue keys amounts :--> PTokenName)
pfirstTokenNameWithCS = phoistAcyclic $
  plam $ \policyId val ->
    pmatch val $ \(PValue val') ->
      precList
        ( \self x xs ->
            pif
              (pfstBuiltin # x #== policyId)
              ( pmatch (pfromData (psndBuiltin # x)) $ \(PMap tokens) ->
                  pfromData $ pfstBuiltin # (phead # tokens)
              )
              (self # xs)
        )
        (const perror)
        # pto val'

-- | Finds amount of the first asset in a value that doesn't have ownPolicyId as its currency symbol.
ptryFindAmt ::
  forall
    (keys :: KeyGuarantees)
    (amounts :: AmountGuarantees)
    (s :: S).
  Term s (PCurrencySymbol :--> PValue keys amounts :--> PInteger)
ptryFindAmt = phoistAcyclic $
  plam $ \ownPolicyId val ->
    pmatch val $ \(PValue val') ->
      pmatch val' $ \(PMap csPairs) ->
        precList
          ( \self x xs ->
              pif
                (pnot # (pfromData (pfstBuiltin # x) #== ownPolicyId))
                ( pmatch (pfromData (psndBuiltin # x)) $ \(PMap tokens) ->
                    pfoldr
                      # plam
                        ( \x acc ->
                            plet (pfromData $ psndBuiltin # x) $ \q ->
                              pif
                                (0 #< q)
                                (q + acc)
                                acc
                        )
                      # 0
                      # tokens
                )
                (self # xs)
          )
          (const $ ptraceError "ptryFindAmt")
          # csPairs

phasInput :: Term s (PBuiltinList PTxInInfo :--> PTxOutRef :--> PBool)
phasInput = phoistAcyclic $ plam $ \refs oref -> pany # plam (\oref' -> oref #== pfield @"outRef" # oref') # refs

pvalueContains ::
  ClosedTerm
    ( PValue 'Sorted 'Positive
        :--> PValue 'Sorted 'Positive
        :--> PBool
    )
pvalueContains = phoistAcyclic $
  plam $ \superset subset ->
    let forEachTN cs = plam $ \tnPair ->
          let tn = pfromData $ pfstBuiltin # tnPair
              amount = pfromData $ psndBuiltin # tnPair
           in amount #<= pvalueOf # superset # cs # tn
        forEachCS = plam $ \csPair ->
          let cs = pfromData $ pfstBuiltin # csPair
              tnMap = pto $ pfromData $ psndBuiltin # csPair
           in pall # forEachTN cs # tnMap
     in pall # forEachCS #$ pto $ pto subset

{- | Extract the token name and the amount of the given currency symbol.
Throws when the token name is not found or more than one token name is involved
Plutarch level function.
-}
ponlyAsset ::
  forall
    (keys :: KeyGuarantees)
    (amounts :: AmountGuarantees)
    (s :: S).
  Term s (PValue keys amounts :--> PTriple PCurrencySymbol PTokenName PInteger)
ponlyAsset = phoistAcyclic $
  plam $ \val ->
    pmatch val $ \(PValue val') ->
      plet (pheadSingleton # pto val') $ \valuePair ->
        pmatch (pfromData (psndBuiltin # valuePair)) $ \(PMap tokens) ->
          plet (pheadSingleton # tokens) $ \tkPair ->
            pcon (PTriple (pfromData (pfstBuiltin # valuePair)) (pfromData (pfstBuiltin # tkPair)) (pfromData (psndBuiltin # tkPair)))

pand'List :: [Term s PBool] -> Term s PBool
pand'List ts' = 
  case ts' of 
    [] -> pconstant True 
    ts -> foldl1 (\res x -> pand' # res # x) ts

pcond ::  [(Term s PBool, Term s a)] -> Term s a -> Term s a
pcond [] def = def
pcond ((cond, x) : conds) def = pif cond x $ pcond conds def

(#>) :: (POrd t) => Term s t -> Term s t -> Term s PBool
a #> b = b #< a
infix 4 #>

(#>=) :: (POrd t) => Term s t -> Term s t -> Term s PBool
a #>= b = b #<= a
infix 4 #>=

(#/=) :: (PEq t) => Term s t -> Term s t -> Term s PBool
a #/= b = pnot # (a #== b)
infix 4 #/=

pisFinite :: Term s (PInterval PPOSIXTime :--> PBool)
pisFinite = plam $ \i -> 
  let isFiniteFrom = pmatch (pfield @"_0" # (pfield @"from" # i)) $ \case 
        PFinite _ -> pconstant True 
        _ -> pconstant False
      isFiniteTo = pmatch (pfield @"_0" # (pfield @"to" # i)) $ \case 
        PFinite _ -> pconstant True 
        _ -> pconstant False
   in pand' # isFiniteFrom # isFiniteTo

pmapAndConvertList :: (PIsListLike listA a, PIsListLike listB b) => Term s ((a :--> b) :--> listA a :--> listB b)
pmapAndConvertList = phoistAcyclic $
  plam $ \f ->
    pfix #$ plam $ \self xs -> pelimList (\y ys -> pcons # (f # y) # (self # ys)) pnil xs 

{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE OverloadedRecordDot #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE UndecidableInstances #-}
{-# OPTIONS_GHC -Wno-incomplete-uni-patterns #-}
{-# OPTIONS_GHC -Wno-missing-import-lists #-}

module LiquidityEvent.LiquidityTokenHolder where

import GHC.Stack (HasCallStack)
import Plutarch (Config (Config), TracingMode (DoTracing))
import Plutarch.Api.V1 (PCredential (..))
import Plutarch.Api.V1.Value (padaToken, padaSymbol, plovelaceValueOf, pnoAdaValue, pnormalize, pvalueOf, pforgetPositive)
import Plutarch.Api.V1.Value qualified as Value 
import Plutarch.Api.V2 (
  AmountGuarantees (Positive),
  KeyGuarantees (Sorted),
  PAddress (..),
  PCurrencySymbol,
  PMintingPolicy,
  POutputDatum (POutputDatum),
  PPOSIXTime (..),
  PPubKeyHash,
  PScriptContext,
  PScriptHash,
  PScriptPurpose (PMinting, PSpending),
  PTokenName (..),
  PTxInInfo (..),
  PTxInfo (..),
  PTxOut,
  PTxOutRef,
  PValidator,
  PValue (..),
 )
import Plutarch.Bool (pand')
import Plutarch.DataRepr (
  DerivePConstantViaData (..),
  PDataFields,
 )
import Plutarch.Extra.Interval (pbefore)
import Plutarch.Extra.ScriptContext (pfromPDatum, ptryFromInlineDatum)
import "liqwid-plutarch-extra" Plutarch.Extra.TermCont (
  pletC,
  pletFieldsC,
  pmatchC,
  ptraceC,
  ptryFromC,
 )
import Plutarch.Lift (PConstantDecl, PUnsafeLiftDecl (..))
import Plutarch.List (pfoldl')
import Plutarch.Num ((#+))
import Plutarch.Prelude
import Plutarch.Unsafe (punsafeCoerce, punsafeDowncast)
import PlutusLedgerApi.V2
import PlutusTx qualified
import Types.Constants (projectTokenHolderTN, rewardFoldTN, commitFoldTN)
import PriceDiscoveryEvent.Utils (
  pand'List,
  pcond,
  pelemAt',
  phasInput,
  pheadSingleton,
  ptryLookupValue,
  pfindCurrencySymbolsByTokenName,
  ptryOwnInput, pmustFind, ptryOwnOutput, (#>)
 )
import Types.LiquiditySet ( PLiquiditySetNode, PLiquidityHolderDatum(..), PProxyTokenHolderDatum(..) )
import PriceDiscoveryEvent.MultiFoldLiquidity (PLiquidityFoldDatum)
import Plutarch.Builtin (pforgetData)
import qualified Plutarch.Monadic as P
import qualified Plutarch.Api.V1 as V1
import Plutarch.Api.V2.Tx (POutputDatum(POutputDatumHash))

pmustFindDatum ::
  Term s (V1.PDatumHash :--> V1.PMap 'V1.Unsorted V1.PDatumHash V1.PDatum :--> PData)
pmustFindDatum =
  phoistAcyclic $ plam $ \datumHash datums ->
    (pfix #$ plam $ \self datumList ->
      (pelimList
        ( \datumTuple datumTuples ->
            pif
              (datumHash #== (pfromData (pfstBuiltin # datumTuple)))
              (pforgetData $ psndBuiltin # datumTuple) 
              (self # datumTuples)
        )
        perror
        datumList)
    ) 
    # (pto datums) 

data PLiquidityHolderMintAct (s :: S)
  = PMintHolder (Term s (PDataRecord '[]))
  | PBurnHolder (Term s (PDataRecord '[]))
  deriving stock (Generic)
  deriving anyclass (PlutusType, PIsData)

instance DerivePlutusType PLiquidityHolderMintAct where
  type DPTStrat _ = PlutusTypeData

instance PTryFrom PData PLiquidityHolderMintAct 

instance PTryFrom PData (PAsData PLiquidityHolderMintAct)

pmintLiquidityTokenHolder :: Term s (PTxOutRef :--> PMintingPolicy)
pmintLiquidityTokenHolder = phoistAcyclic $ 
  plam $ \oref redm ctx ->
    let red = punsafeCoerce @_ @_ @PLiquidityHolderMintAct redm 
     in pmatch red $ \case 
          PMintHolder _ -> popaque $ pmintTokenHolder # oref # ctx 
          PBurnHolder _ -> popaque $ pburnTokenHolder # ctx 

pburnTokenHolder :: Term s (PScriptContext :--> PUnit)
pburnTokenHolder = phoistAcyclic $ 
  plam $ \ctx -> unTermCont $ do
    contextFields <- pletFieldsC @'["txInfo", "purpose"] ctx
    PMinting policy <- pmatchC contextFields.purpose
    ownPolicyId <- pletC $ pfield @"_0" # policy

    info <- pletFieldsC @'["mint"] contextFields.txInfo
    tkPairs <- pletC $ ptryLookupValue # ownPolicyId # info.mint
    tkPair <- pletC (pheadSingleton # tkPairs)
    let numMinted = psndBuiltin # tkPair 
    pure $
      pif ( pfromData numMinted #== -1 ) (pconstant ()) perror 

pmintTokenHolder :: Term s (PTxOutRef :--> PScriptContext :--> PUnit)
pmintTokenHolder = phoistAcyclic $ 
  plam $ \oref ctx -> unTermCont $ do
    contextFields <- pletFieldsC @'["txInfo", "purpose"] ctx
    PMinting policy <- pmatchC contextFields.purpose
    ownPolicyId <- pletC $ pfield @"_0" # policy

    info <- pletFieldsC @'["inputs", "outputs", "mint"] contextFields.txInfo
    tkPairs <- pletC $ ptryLookupValue # ownPolicyId # (pnormalize # info.mint)
    tkPair <- pletC (pheadSingleton # tkPairs)

    let holderOutput = pmustFind @PBuiltinList # plam(\out -> 1 #<= pvalueOf # (pfield @"value" # out) # pfromData ownPolicyId # projectTokenHolderTN) # info.outputs 
    POutputDatum ((pfield @"outputDatum" #) -> holderOutputDatum) <- pmatchC (pfield @"datum" # holderOutput)

    let numMinted = psndBuiltin # tkPair 
        tkMinted = pfstBuiltin # tkPair 
        expectedDatum = pforgetData $ pdata $ pcon $ PLiquidityHolderDatum $ pdcons @"lpTokenName" # (pconstantData "") #$ pdcons @"totalCommitted" # pconstantData 0 #$ pdcons @"totalLPTokens" # pconstantData 0 # pdnil 
        mintChecks = 
          pand'List
            [ pfromData numMinted #== 1
            , projectTokenHolderTN #== pfromData tkMinted
            , phasInput # info.inputs # oref 
            , expectedDatum #== pfromData (pto holderOutputDatum)
            ] 
    pure $
      pif ( mintChecks ) (pconstant ()) perror 

data PLiquidityHolderAct (s :: S)
  = PAddCollected (Term s (PDataRecord '[]))
  | PForwardToV1 (Term s (PDataRecord '[]))
  | PBeginRewards (Term s (PDataRecord '[]))
  deriving stock (Generic)
  deriving anyclass (PlutusType, PIsData)

instance DerivePlutusType PLiquidityHolderAct where
  type DPTStrat _ = PlutusTypeData

proxyTokenHolderAddress :: Term _ PAddress
proxyTokenHolderAddress = pfromData $ pconstantData (Address (ScriptCredential "a5b38cc78899b452d48205198a5e457b6f92f50866f4abff82bab11a") Nothing)

pliquidityTokenHolder :: Term s (PAsData PAddress :--> PAsData PCurrencySymbol :--> PAsData PCurrencySymbol :--> PData :--> PData :--> PScriptContext :--> POpaque)
pliquidityTokenHolder = phoistAcyclic $ plam $ \proxyTokenHolderAddress rewardsCS commitCS datum redeemer ctx ->
  let red = punsafeCoerce @_ @_ @PLiquidityHolderAct redeemer 
      dat = punsafeCoerce @_ @_ @PLiquidityHolderDatum datum 
   in pmatch red $ \case 
        PAddCollected _ -> paddCollected # pfromData (pfield @"totalCommitted" # dat) # commitCS # ctx 
        PForwardToV1 _ -> pforwardToProxy # pfromData proxyTokenHolderAddress # dat # ctx 
        PBeginRewards _ -> pbeginRewards # rewardsCS # ctx

pforwardToProxy :: Term s (PAddress :--> PLiquidityHolderDatum :--> PScriptContext :--> POpaque)
pforwardToProxy = phoistAcyclic $ plam $ \proxyTokenHolderAddress ownDatum ctx -> P.do 
  ctxF <- pletFields @'["txInfo", "purpose"] ctx 
  infoF <- pletFields @'["inputs", "outputs", "datums"] ctxF.txInfo
  PSpending ((pfield @"_0" #) -> ownRef) <- pmatch ctxF.purpose
  let ownInput = ptryOwnInput # infoF.inputs # ownRef
  ownInputF <- pletFields @'["address", "value"] ownInput

  ownDatF <- pletFields @'["totalCommitted", "totalLPTokens", "lpTokenName"] ownDatum
  let proxyOutput = 
        ( pmustFind @PBuiltinList
            # plam (\out -> pfield @"address" # out #== proxyTokenHolderAddress)
            # infoF.outputs 
        )
  proxyOutputF <- pletFields @["value", "datum"] proxyOutput
  (POutputDatumHash ((pfield @"datumHash" #) -> datumHash)) <- pmatch proxyOutputF.datum 
  let proxyDatum =  punsafeCoerce @_ @_ @PProxyTokenHolderDatum $ pmustFindDatum # datumHash # infoF.datums
  proxyDatumF <- pletFields @["totalCommitted", "returnAddress"] proxyDatum
  let forwardToProxyChecks = 
          pand'List
            [ ptraceIfFalse "cgz" $ pfromData ownDatF.totalCommitted #> pconstant 0
            , ptraceIfFalse "retAddr" $ proxyDatumF.returnAddress #== ownInputF.address
            , ptraceIfFalse "totCom" $ proxyDatumF.totalCommitted #== ownDatF.totalCommitted
            , ptraceIfFalse "totLP" $ pfromData ownDatF.totalLPTokens #== pconstant 0
            , ptraceIfFalse "tn" $ pfromData ownDatF.lpTokenName #== pconstant ""
            , ptraceIfFalse "val" $ proxyOutputF.value #== ownInputF.value 
            ] 
  pif forwardToProxyChecks (popaque $ pconstant ()) perror 

pbeginRewards :: Term s (PAsData PCurrencySymbol :--> PScriptContext :--> POpaque)
pbeginRewards = phoistAcyclic $ plam $ \rewardsCS ctx -> unTermCont $ do 
  ctxF <- pletFieldsC @'["txInfo", "purpose"] ctx 
  infoF <- pletFieldsC @'["inputs", "mint"] ctxF.txInfo

  PSpending ((pfield @"_0" #) -> ownRef) <- pmatchC ctxF.purpose
  let ownInput = ptryOwnInput # infoF.inputs # ownRef
  ownInputF <- pletFieldsC @'["value"] ownInput
  
  mintedValue <- pletC (pnormalize # infoF.mint) 
  let possibleCSs = pfindCurrencySymbolsByTokenName # ownInputF.value # projectTokenHolderTN 
      pthCS = pheadSingleton # possibleCSs
      tkhPairs = ptryLookupValue # pthCS # mintedValue
      tkhPair = (pheadSingleton # tkhPairs)
      thkMinted = psndBuiltin # tkhPair 

  let rewardPair = pheadSingleton #$ ptryLookupValue # rewardsCS # mintedValue
      rewardTkMinted = psndBuiltin # rewardPair 
  
  pure $
    pif ( pfromData rewardTkMinted #== 1 #&& pfromData thkMinted #== -1) (popaque $ pconstant ()) perror 

paddCollected :: Term s (PInteger :--> PAsData PCurrencySymbol :--> PScriptContext :--> POpaque)
paddCollected = phoistAcyclic $ plam $ \ownInputTotalCommitted commitCS ctx -> unTermCont $ do 
  ctxF <- pletFieldsC @'["txInfo", "purpose"] ctx 
  infoF <- pletFieldsC @'["inputs", "outputs", "mint"] ctxF.txInfo
  mintedValue <- pletC (pnormalize # infoF.mint) 
  PSpending ((pfield @"_0" #) -> ownRef) <- pmatchC ctxF.purpose
  txInputs <- pletC infoF.inputs
  let ownInput = ptryOwnInput # txInputs # ownRef
  ownInputF <- pletFieldsC @'["value", "address"] ownInput
  PScriptCredential ((pfield @"_0" #) -> ownValHash) <- pmatchC (pfield @"credential" # ownInputF.address)

  let commitInp = 
        pfield @"resolved" #
          ( pmustFind @PBuiltinList
              # plam (\inp -> pvalueOf # (pfield @"value" # (pfield @"resolved" # inp)) # pfromData commitCS # commitFoldTN #== 1)
              # txInputs 
          )
  commitInputF <- pletFieldsC @'["value", "datum"] commitInp 
  let commitDatum = punsafeCoerce @_ @_ @PLiquidityFoldDatum $ (ptryFromInlineDatum # commitInputF.datum) 
  commitDatF <- pletFieldsC @'["currNode", "committed"] commitDatum
  
  let ownOutput = ptryOwnOutput # infoF.outputs # ownValHash
  ownOutputF <- pletFieldsC @'["value", "datum"] ownOutput  
  
  (POutputDatum ownOutDatum) <- pmatchC ownOutputF.datum
  ownOutDatF <- pletFieldsC @'["totalCommitted", "totalLPTokens", "lpTokenName"] (pfromPDatum @PLiquidityHolderDatum # (pfield @"outputDatum" # ownOutDatum))
  let commitTkPair = (pheadSingleton #$ ptryLookupValue # commitCS # mintedValue)
      commitTkBurned = (pfromData $ psndBuiltin # commitTkPair) #== -1
      collectedAda = Value.psingleton # padaSymbol # padaToken # commitDatF.committed
      addCollectedChecks = 
          pand'List
            [ ptraceIfFalse "acburn" commitTkBurned 
            , ptraceIfFalse "acvalue" $ pforgetPositive ownOutputF.value #== (pforgetPositive ownInputF.value <> collectedAda)
            , ptraceIfFalse "actotcom" $ pfromData ownOutDatF.totalCommitted #== pfromData commitDatF.committed
            , ptraceIfFalse "actotlp" $ pfromData ownOutDatF.totalLPTokens #== 0 
            , ptraceIfFalse "aclpName" $ pfromData ownOutDatF.lpTokenName #== pconstant ""
            , ptraceIfFalse "ac" $ ownInputTotalCommitted #== 0
            ] 
  pure $
    pif addCollectedChecks (popaque $ pconstant ()) perror 
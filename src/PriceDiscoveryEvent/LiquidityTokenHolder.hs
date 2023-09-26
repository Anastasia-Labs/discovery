{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE OverloadedRecordDot #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE UndecidableInstances #-}
{-# OPTIONS_GHC -Wno-incomplete-uni-patterns #-}
{-# OPTIONS_GHC -Wno-missing-import-lists #-}

module PriceDiscoveryEvent.LiquidityTokenHolder where

import GHC.Stack (HasCallStack)
import Plutarch (Config (Config), TracingMode (DoTracing))
import Plutarch.Api.V1 (PCredential (..))
import Plutarch.Api.V1.Value (padaToken, padaSymbol, plovelaceValueOf, pnoAdaValue, pnormalize, pvalueOf)
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
import Plutarch.Unsafe (punsafeCoerce)
import PlutusLedgerApi.V2
import PlutusTx qualified
import Types.Constants (projectTokenHolderTN, rewardFoldTN)
import PriceDiscoveryEvent.Utils (
  pand'List,
  pcond,
  pelemAt',
  phasInput,
  pheadSingleton,
  ptryLookupValue,
  pfindCurrencySymbolsByTokenName,
  ptryOwnInput
 )
import Types.LiquiditySet ( PLiquiditySetNode, PLiquidityHolderDatum )

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
    tkPairs <- pletC $ ptryLookupValue # ownPolicyId # (pnormalize # info.mint)
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

    info <- pletFieldsC @'["inputs","mint"] contextFields.txInfo
    tkPairs <- pletC $ ptryLookupValue # ownPolicyId # (pnormalize # info.mint)
    tkPair <- pletC (pheadSingleton # tkPairs)
    let numMinted = psndBuiltin # tkPair 
        tkMinted = pfstBuiltin # tkPair 
        mintChecks = 
          pand'List
            [ pfromData numMinted #== 1
            , projectTokenHolderTN #== pfromData tkMinted
            , phasInput # info.inputs # oref 
            ] 
    pure $
      pif ( mintChecks ) (pconstant ()) perror 

data PLiquidityHolderAct (s :: S)
  = PAddCollected (Term s (PDataRecord '[]))
  | PCreatePool (Term s (PDataRecord '[]))
  | PBeginRewards (Term s (PDataRecord '[]))
  deriving stock (Generic)
  deriving anyclass (PlutusType, PIsData)

instance DerivePlutusType PLiquidityHolderMintAct where
  type DPTStrat _ = PlutusTypeData


pliquidityTokenHolder :: Term s (PAsData PCurrencySymbol :--> PAsData PCurrencySymbol :--> PValidator)
pliquidityTokenHolder = phoistAcyclic $ plam $ \rewardsCS commitCS _dat redeemer ctx -> unTermCont $ do 
  let red = punsafeCoerce @_ @_ @PLiquidityHolderAct redeemer 
   in pmatch red $ \case 
          PAddCollected _ -> popaque $ paddCollected # commitCS # ctx 
          PCreatePool _ -> perror -- TODO
          PBeginRewards _ -> pbeginRewards # rewardsCS # ctx

pbeginRewards :: Term s (PAsData PCurrencySymbol :--> PValidator)
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

paddCollected :: Term s (PAsData PCurrencySymbol :--> PValidator)
paddCollected = phoistAcyclic $ plam $ \commitCS ctx -> unTermCont $ do 
  ctxF <- pletFieldsC @'["txInfo", "purpose"] ctx 
  infoF <- pletFieldsC @'["inputs", "outputs", "mint"] ctxF.txInfo
  mintedValue <- pletC (pnormalize # infoF.mint) 
  PSpending ((pfield @"_0" #) -> ownRef) <- pmatchC ctxF.purpose
  let ownInput = ptryOwnInput # infoF.inputs # ownRef
  ownInputF <- pletFieldsC @'["value", "address", "datum"] ownInput
  PScriptCredential ((pfield @"_0" #) -> ownValHash) <- pmatchC (pfield @"credential" # ownInputF.address)

  let commitInp = 
        pfield @"resolved" #
          ( pmustFind @PBuiltinList
              # plam (\inp -> pvalueOf # (pfield @"value" # (pfield @"resolved" # inp)) # commitCS # commitFoldTN #== 1)
              # txInputs 
          )
  commitInputF <- pletFields @'["value", "datum"] commitInp 
  let commitDatum = punsafeCoerce @_ @_ @PLiquidityFoldDatum $ (ptryFromInlineDatum # commitInputF.datum) 
  commitDatF <- pletFieldsC @'["currNode", "committed"] commitDatum
  
  let ownOutput = ptryOwnOutput # info.outputs # ownValHash
      ownOutputF <- pletFieldsC @'["value", "datum"] ownOutput  
  
  (POutputDatum ownOutDatum) <- pmatchC ownOutputF.datum
  ownOutDatF <- pletFields @'["currNode", "totalCommitted"] (pfromPDatum @PLiquidityHolderDatum # (pfield @"outputDatum" # ownOutDatum))
 
  let commitTkPair = (pheadSingleton #$ ptryLookupValue # commitCS # mintedValue)
      commitTkBurned = (pfromData psndBuiltin # commitTkPair) #== -1
      collectedAda = Value.psingleton # padaSymbol # padaToken # commitDatF.committed
      addCollectedChecks = 
          pand'List
            [ commitTkBurned 
            , pforgetPositive ownOutputF.value #== (ownInputF.value <> collectedAda)
            , ownOutDatF.currNode #== commitDatF.currNode 
            , ownOutDatF.totalCommitted #== commitDatF.committed 
            ] 
  pure $
    pif addCollectedChecks (popaque $ pconstant ()) perror 
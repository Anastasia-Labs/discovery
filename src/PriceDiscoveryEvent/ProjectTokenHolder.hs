{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE OverloadedRecordDot #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE UndecidableInstances #-}
{-# OPTIONS_GHC -Wno-incomplete-uni-patterns #-}
{-# OPTIONS_GHC -Wno-missing-import-lists #-}

module PriceDiscoveryEvent.ProjectTokenHolder where

import GHC.Stack (HasCallStack)
import Plutarch (Config (Config), TracingMode (DoTracing))
import Plutarch.Api.V1 (PCredential (..))
import Plutarch.Api.V1.Value (padaToken, plovelaceValueOf, pnoAdaValue, pnormalize, pvalueOf)
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
  pfindCurrencySymbolsByTokenName
 )
import PriceDiscoveryEvent.Utils (ptryOwnInput)

data PTokenHolderMintAct (s :: S)
  = PMintHolder (Term s (PDataRecord '[]))
  | PBurnHolder (Term s (PDataRecord '[]))
  deriving stock (Generic)
  deriving anyclass (PlutusType, PIsData)

instance DerivePlutusType PTokenHolderMintAct where
  type DPTStrat _ = PlutusTypeData

instance PTryFrom PData PTokenHolderMintAct 

instance PTryFrom PData (PAsData PTokenHolderMintAct)

pmintProjectTokenHolder :: Term s (PTxOutRef :--> PMintingPolicy)
pmintProjectTokenHolder = phoistAcyclic $ 
  plam $ \oref redm ctx ->
    let red = punsafeCoerce @_ @_ @PTokenHolderMintAct redm 
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


data PTokenHolderConfig (s :: S)
  = PTokenHolderConfig
      ( Term
          s
          ( PDataRecord
              '[ "rewardsCS" ':= PCurrencySymbol
               ]
          )
      )
  deriving stock (Generic)
  deriving anyclass (PlutusType, PIsData, PDataFields)

instance DerivePlutusType PTokenHolderConfig where
  type DPTStrat _ = PlutusTypeData

pprojectTokenHolder :: Term s (PAsData PCurrencySymbol :--> PValidator)
pprojectTokenHolder = phoistAcyclic $ plam $ \rewardsCS _dat _redeemer ctx -> unTermCont $ do 
  ctxF <- pletFieldsC @'["txInfo", "purpose"] ctx 
  infoF <- pletFieldsC @'["inputs", "mint"] ctxF.txInfo

  PSpending ((pfield @"_0" #) -> ownRef) <- pmatchC ctxF.purpose
  let ownInput = ptryOwnInput # infoF.inputs # ownRef
  ownInputF <- pletFieldsC @'["value"] ownInput
  
  mintedValue <- pletC (pnormalize # infoF.mint) 
  let possibleCSs = pfindCurrencySymbolsByTokenName # ownInputF.value # projectTokenHolderTN 
      pthCS = pheadSingleton # possibleCSs
  
  let tkhPairs = ptryLookupValue # pthCS # mintedValue
      tkhPair = (pheadSingleton # tkhPairs)
      thkMinted = psndBuiltin # tkhPair 

  tkPairs <- pletC $ ptryLookupValue # rewardsCS # mintedValue
  tkPair <- pletC (pheadSingleton # tkPairs)
  let rewardTkMinted = psndBuiltin # tkPair 
  
  pure $
    pif ( pfromData rewardTkMinted #== 1 #&& pfromData thkMinted #== -1) (popaque $ pconstant ()) perror 
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE OverloadedRecordDot #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE UndecidableInstances #-}
{-# OPTIONS_GHC -Wno-incomplete-uni-patterns #-}
{-# OPTIONS_GHC -Wno-missing-import-lists #-}

module LiquidityEvent.ProxyTokenHolderV1 where

import GHC.Stack (HasCallStack)
import Plutarch (Config (Config), TracingMode (DoTracing))
import Plutarch.Api.V1 
import Plutarch.Api.V1.Value (padaToken, padaSymbol, plovelaceValueOf, pnoAdaValue, pnormalize, pvalueOf, pforgetPositive)
import Plutarch.Api.V1.Value qualified as Value 
import Plutarch.Bool (pand')
import Plutarch.DataRepr (
  DerivePConstantViaData (..),
  PDataFields,
 )
import Plutarch.Extra.Interval (pbefore)
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
import Types.Constants (projectTokenHolderTN, rewardFoldTN, commitFoldTN)
import Types.LiquiditySet (PLiquidityHolderDatum(..), PProxyTokenHolderDatum)
import PriceDiscoveryEvent.Utils (
  pand'List,
  pheadSingleton,
  ptryLookupValue,
  pfindCurrencySymbolsByTokenName,
  pmustFind,
  pfilterCSFromValue
 )


data PProxyTokenHolderAct (s :: S)
  = PInitPool (Term s (PDataRecord '[]))
  deriving stock (Generic)
  deriving anyclass (PlutusType, PIsData)

instance DerivePlutusType PProxyTokenHolderAct where
  type DPTStrat _ = PlutusTypeData

pmustFindDatum ::
  Term s (PDatumHash :--> PBuiltinList (PAsData (PTuple PDatumHash PDatum)) :--> PData)
pmustFindDatum =
  phoistAcyclic $ plam $ \datumHash ->
    pfix #$ plam $ \self datums ->
      pelimList
        ( \datumTuple datumTuples ->
            pif
              (datumHash #== pfield @"_0" # datumTuple)
              ( let datum :: Term _ PData
                    datum = pto $ pfromData $ pfield @"_1" # pfromData datumTuple
                 in datum 
              )
              (self # datumTuples)
        )
        perror
        datums


pproxyTokenHolderV1 :: Term s (PAsData PCurrencySymbol :--> PData :--> PData :--> PScriptContext :--> POpaque)
pproxyTokenHolderV1 = phoistAcyclic $ plam $ \poolTokenCS datum redeemer ctx ->
  let red = punsafeCoerce @_ @_ @PProxyTokenHolderAct redeemer 
      dat = punsafeCoerce @_ @_ @PProxyTokenHolderDatum datum 
   in pmatch red $ \case 
        PInitPool _ -> popaque $ pinitPool # poolTokenCS # dat # ctx 

pinitPool :: Term s (PAsData PCurrencySymbol :--> PProxyTokenHolderDatum :--> PScriptContext :--> POpaque)
pinitPool = phoistAcyclic $ plam $ \poolTokenCS datum ctx -> unTermCont $ do 
  ctxF <- pletFieldsC @'["txInfo", "purpose"] ctx 
  infoF <- pletFieldsC @'["inputs", "mint", "outputs", "datums"] ctxF.txInfo

  PSpending ((pfield @"_0" #) -> ownRef) <- pmatchC ctxF.purpose
  let ownInput = 
        pfield @"resolved" #
          ( pmustFind @PBuiltinList
              # plam (\inp -> pfield @"outRef" # inp #== ownRef)
              # infoF.inputs 
          )
  ownInputF <- pletFieldsC @'["value"] ownInput
  ownDatumF <- pletFieldsC @'["returnAddress", "totalCommitted"] datum 
  let returnAddress = ownDatumF.returnAddress
      poolPairs = ptryLookupValue # poolTokenCS # infoF.mint
      lpPair = (phead # poolPairs)
      poolPair = (pheadSingleton # (ptail # poolPairs))
      poolTokenName = pfstBuiltin # poolPair
      lpMinted = psndBuiltin # lpPair 
      lpTokenName = pfstBuiltin # lpPair 
      pthCS = pheadSingleton #$ pfindCurrencySymbolsByTokenName # ownInputF.value # projectTokenHolderTN 
      poolOutput =
        ( pmustFind @PBuiltinList
              # plam (\txOut -> pvalueOf # (pfield @"value" # txOut) # pfromData poolTokenCS # pfromData poolTokenName #== 1)
              # infoF.outputs 
        )
      forwardOutput = 
        ( pmustFind @PBuiltinList
              # plam (\txOut -> pfield @"address" # txOut #== returnAddress)
              # infoF.outputs 
        )
      ownInputValueNoPTH = pfilterCSFromValue # ownInputF.value # pthCS
  forwardOutputF <- pletFieldsC @'["value", "datumHash"] forwardOutput
  
  PDJust ((pfield @"_0" #) -> forwardOutputDH) <- pmatchC forwardOutputF.datumHash 
  let forwardDatum = punsafeCoerce @_ @_ @PLiquidityHolderDatum (pmustFindDatum # forwardOutputDH # infoF.datums) 
      expectedDatum = pcon $ PLiquidityHolderDatum $ pdcons @"lpTokenName" # lpTokenName #$ pdcons @"totalCommitted" # ownDatumF.totalCommitted #$ pdcons @"totalLPTokens" # lpMinted # pdnil 
      validatorChecks = 
        pand'List 
          [ ptraceIfFalse "pthd" $ forwardDatum #== expectedDatum
          , ptraceIfFalse "pthlpv" $ pforgetPositive (pnoAdaValue # forwardOutputF.value) 
              #== (Value.psingleton # pfromData pthCS # projectTokenHolderTN # 1 
                <> Value.psingletonData # poolTokenCS # lpTokenName # lpMinted)
          , ptraceIfFalse "pthpv" $ pforgetPositive ( pfield @"value" # poolOutput ) #==
              (pforgetPositive ownInputValueNoPTH) <> Value.psingletonData # poolTokenCS # poolTokenName # pdata 1
          ] 
  pure $
    pif validatorChecks (popaque $ pconstant ()) perror 

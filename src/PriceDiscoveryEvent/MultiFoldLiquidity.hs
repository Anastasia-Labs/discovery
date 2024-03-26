{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE OverloadedRecordDot #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE UndecidableInstances #-}
{-# OPTIONS_GHC -Wno-incomplete-uni-patterns #-}
{-# OPTIONS_GHC -Wno-missing-import-lists #-}

module PriceDiscoveryEvent.MultiFoldLiquidity where

import GHC.Stack (HasCallStack)
import Plutarch (Config (Config), TracingMode (DoTracing))
import Plutarch.Api.V1 (PCredential (..))
import Plutarch.Api.V1.Value (padaToken, plovelaceValueOf, pnoAdaValue, pnormalize, pvalueOf, padaSymbol, pforgetPositive)
import Plutarch.Api.V1.Value qualified as Value 
import Plutarch.Api.V2 (
  AmountGuarantees (Positive),
  KeyGuarantees (Sorted),
  PAddress (..),
  PCurrencySymbol,
  PMintingPolicy,
  POutputDatum (POutputDatum, POutputDatumHash),
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
  pguardC
 )
import Plutarch.Lift (PConstantDecl, PUnsafeLiftDecl (..))
import Plutarch.List (pfoldl')
import Plutarch.Num ((#+))
import Plutarch.Prelude
import Plutarch.Unsafe (punsafeCoerce)
import PlutusLedgerApi.V2
import PlutusTx qualified
import PriceDiscoveryEvent.Utils (
  pand'List,
  pcond,
  pelemAt',
  pelemAtFlipped',
  phasInput,
  pheadSingleton,
  ptryLookupValue,
  ptryOutputToAddress,
  ptryOwnInput,
  ptryOwnOutput,
  pvalueOfOne,
  (#>), ptxSignedByPkh, pfoldl2, pvalueOfOneScott, pcountScriptInputs, pfindCurrencySymbolsByTokenName, pmustFind, (#>=),
 )
import Types.Classes
import Types.Constants (commitFoldTN, minAda, nodeDepositAda, poriginNodeTN, rewardFoldTN, projectTokenHolderTN, foldingFee)
import Types.LiquiditySet ( PLiquiditySetNode, PLiquidityHolderDatum )
import Types.DiscoverySet (PNodeKey(..), PNodeKeyState(..))
import qualified Plutarch.Api.V1 as V1
import Plutarch.Builtin (pforgetData)
import PriceDiscoveryEvent.Utils (pcountOfUniqueTokens)

data PLiquidityFoldMintConfig (s :: S)
  = PLiquidityFoldMintConfig
      ( Term
          s
          ( PDataRecord
              '[ "nodeCS" ':= PCurrencySymbol
               , "foldAddr" ':= PAddress
               , "discoveryDeadline" ':= PPOSIXTime 
               ]
          )
      )
  deriving stock (Generic)
  deriving anyclass (PlutusType, PIsData, PDataFields)

instance DerivePlutusType PLiquidityFoldMintConfig where
  type DPTStrat _ = PlutusTypeData

data PLiquidityFoldMintAct (s :: S)
  = PLiquidityMintFold (Term s (PDataRecord '[]))
  | PLiquidityBurnFold (Term s (PDataRecord '[]))
  deriving stock (Generic)
  deriving anyclass (PlutusType, PIsData)

instance DerivePlutusType PLiquidityFoldMintAct where
  type DPTStrat _ = PlutusTypeData

instance PTryFrom PData PLiquidityFoldMintAct 

instance PTryFrom PData (PAsData PLiquidityFoldMintAct)

data PLiquidityFoldDatum (s :: S)
  = PLiquidityFoldDatum
      ( Term
          s
          ( PDataRecord
              '[ "currNode" ':= PLiquiditySetNode
               , "committed" ':= PInteger
               , "owner" ':= PAddress
               ]
          )
      )
  deriving stock (Generic)
  deriving anyclass (PlutusType, PIsData, PDataFields)

instance DerivePlutusType PLiquidityFoldDatum where
  type DPTStrat _ = PlutusTypeData

instance PTryFrom PData PLiquidityFoldDatum

instance PTryFrom PData (PAsData PLiquidityFoldDatum)

data PLiquidityFoldAct (s :: S)
  = PLiquidityFoldNodes
      ( Term
          s
          ( PDataRecord
              '[ "nodeInpIdxs" ':= PBuiltinList (PAsData PInteger) 
               , "nodeOutIdxs" ':= PBuiltinList (PAsData PInteger) 
               ]
          )
      )
  | PLiquidityReclaim (Term s (PDataRecord '[]))
  deriving stock (Generic)
  deriving anyclass (PlutusType, PIsData)

instance DerivePlutusType PLiquidityFoldAct where
  type DPTStrat _ = PlutusTypeData

deriving anyclass instance
  PTryFrom PData PLiquidityFoldAct

data PCollectionFoldState (s :: S) = PCollectionFoldState
  { key :: Term s PNodeKeyState
  , next :: Term s PNodeKeyState
  , committed :: Term s PInteger
  , num :: Term s PInteger
  }
  deriving stock (Generic)
  deriving anyclass (PlutusType, PEq)

instance DerivePlutusType PCollectionFoldState where
  type DPTStrat _ = PlutusTypeScott

pmintFoldPolicyW :: Term s (PLiquidityFoldMintConfig :--> PMintingPolicy)
pmintFoldPolicyW = phoistAcyclic $ 
  plam $ \fconfig redm ctx ->
    let red = punsafeCoerce @_ @_ @PLiquidityFoldMintAct redm 
     in pmatch red $ \case 
          PLiquidityMintFold _ -> popaque $ pmintCommitFold # fconfig # ctx 
          PLiquidityBurnFold _ -> popaque $ pburnCommitFold # ctx 

pburnCommitFold :: Term s (PScriptContext :--> PUnit)
pburnCommitFold = phoistAcyclic $ 
  plam $ \ ctx -> unTermCont $ do
    contextFields <- pletFieldsC @'["txInfo", "purpose"] ctx
    PMinting policy <- pmatchC contextFields.purpose
    ownPolicyId <- pletC $ pfield @"_0" # policy

    info <- pletFieldsC @'["mint"] contextFields.txInfo
    let tkPairs = ptryLookupValue # ownPolicyId # info.mint
    tkPair <- pletC (pheadSingleton # tkPairs)
    let numMinted = psndBuiltin # tkPair 
    pure $
      pif ( pfromData numMinted #== -1 ) (pconstant ()) perror 

pmintCommitFold :: Term s (PLiquidityFoldMintConfig :--> PScriptContext :--> PUnit)
pmintCommitFold = phoistAcyclic $ 
  plam $ \fconfig ctx -> unTermCont $ do 
    foldConfF <- pletFieldsC @'["nodeCS", "foldAddr", "discoveryDeadline"] fconfig 
    contextFields <- pletFieldsC @'["txInfo", "purpose"] ctx

    PMinting policy <- pmatchC contextFields.purpose
    ownPolicyId <- pletC $ pfield @"_0" # policy

    info <- pletFieldsC @'["referenceInputs", "inputs", "outputs", "mint", "validRange"] contextFields.txInfo

    let tkPairs = ptryLookupValue # ownPolicyId # info.mint
    tkPair <- pletC (pheadSingleton # tkPairs)

    let numMinted = psndBuiltin # tkPair
        foldOutput = ptryOutputToAddress # info.outputs # foldConfF.foldAddr
        refInput = pfield @"resolved" # (pheadSingleton @PBuiltinList # info.referenceInputs)

    refInputF <- pletFieldsC @'["value", "datum"] refInput

    (POutputDatum refInpDatum) <- pmatchC refInputF.datum
    let refInpDat = pfromPDatum @PLiquiditySetNode # (pfield @"outputDatum" # refInpDatum)

    foldOutputF <- pletFieldsC @'["value", "datum"] foldOutput
    (POutputDatum foldOutputDatum) <- pmatchC foldOutputF.datum

    let foldOutDatum = pfromPDatum @PLiquidityFoldDatum # (pfield @"outputDatum" # foldOutputDatum)
    foldOutDatumF <- pletFieldsC @'["currNode", "committed"] foldOutDatum
    let foldInitChecks =
          pand'List
            [ pfromData numMinted #== 1
            , pcountOfUniqueTokens # foldOutputF.value #== 2
            , pvalueOf # foldOutputF.value # pfromData ownPolicyId # commitFoldTN #== pconstant 1
            , foldOutDatumF.currNode #== refInpDat 
            , pfromData foldOutDatumF.committed #== pconstant 0 
            , pvalueOf # refInputF.value # foldConfF.nodeCS # poriginNodeTN #== pconstant 1
            , pbefore # pfromData foldConfF.discoveryDeadline # info.validRange 
            ]
    pure $
        pif foldInitChecks
            ( pconstant () )
            perror 

pfoldValidatorW :: Term s (PAsData PCurrencySymbol :--> PAsData PCurrencySymbol :--> PValidator)
pfoldValidatorW = phoistAcyclic $
  plam $ \nodeCS tokenHolderCS datum redeemer ctx ->
    let dat = punsafeCoerce @_ @_ @PLiquidityFoldDatum datum
        red = punsafeCoerce @_ @_ @PLiquidityFoldAct redeemer
     in pmatch red $ \case
          PLiquidityFoldNodes r -> pletFields @'["nodeInpIdxs", "nodeOutIdxs"] r $ \redF ->
            pfoldNodes # nodeCS # redF.nodeInpIdxs # redF.nodeOutIdxs # dat # ctx
          PLiquidityReclaim _ -> unTermCont $ do 
            -- PPubKeyCredential ((pfield @"_0" #) -> ownerPkh) <- pmatchC (pfield @"credential" # (pfield @"owner" # dat))
            ctxF <- pletFieldsC @'["txInfo", "purpose"] ctx
            infoF <- pletFieldsC @'["inputs", "signatories", "mint"] ctxF.txInfo
            let projectInput = 
                  pany @PBuiltinList
                    # plam (\inp -> pvalueOf # (pfield @"value" # (pfield @"resolved" # inp)) # pfromData tokenHolderCS # projectTokenHolderTN #== 1)
                    # infoF.inputs
            PSpending ((pfield @"_0" #) -> ownRef) <- pmatchC ctxF.purpose
            let ownInput = ptryOwnInput # infoF.inputs # ownRef
            ownInputF <- pletFieldsC @'["address", "value", "datum"] ownInput
            (POutputDatum commitDatum) <- pmatchC ownInputF.datum
            let commitDat = punsafeCoerce @_ @_ @PLiquidityFoldDatum (pfield @"outputDatum" # commitDatum)
            commitDatF <- pletFieldsC @'["currNode", "committed", "owner"] commitDat
            commitFoldNodeF <- pletFieldsC @'["key", "next"] commitDatF.currNode
            let possibleCSs = pfindCurrencySymbolsByTokenName # ownInputF.value # commitFoldTN 
                commitCS = pheadSingleton # possibleCSs
                commitPairs = ptryLookupValue # commitCS # infoF.mint
                commitPair = (pheadSingleton # commitPairs)
                commitMinted = psndBuiltin # commitPair 
                reclaimChecks = 
                  pand'List 
                    [ pmatch
                        commitFoldNodeF.next
                        ( \case
                            PEmpty _ -> pconstant True
                            PKey _ -> pconstant False
                        )
                    , (pfromData commitMinted #== -1)
                    , projectInput
                    ]
            pure $ 
              pif reclaimChecks
                  (popaque $ pconstant ())
                  perror 

pfoldBijectiveUTxOs ::
  (Term s a -> Term s PTxOut -> Term s PTxOut -> Term s a) ->
  Term s a -> 
  Term s (PBuiltinList PTxInInfo) ->
  Term s (PBuiltinList PTxOut) ->   
  Term s (PBuiltinList (PAsData PInteger)) ->
  Term s (PBuiltinList (PAsData PInteger)) ->
  Term s a
pfoldBijectiveUTxOs f acc txInputs txOutputs inputIdxs outputIdxs = 
  plet (pelemAtFlipped' # txInputs) $ \pelemAtInputs ->
    plet (pelemAtFlipped' # txOutputs) $ \pelemAtOutputs ->
      pfoldl2
        # plam
          ( \state inputIdx outputIdx ->
            f state (pfield @"resolved" # (pelemAtInputs # pfromData inputIdx)) (pelemAtOutputs # pfromData outputIdx)
          )
        # acc
        # inputIdxs
        # outputIdxs

pisLiquiditySuccessor :: Term s PCurrencySymbol -> Term s PCollectionFoldState -> Term s PTxOut -> Term s PTxOut -> Term s PCollectionFoldState 
pisLiquiditySuccessor nodeCS accNode inputNode outputNode = unTermCont $ do
  accNodeF <- pmatchC accNode
  inputNodeF <- pletFieldsC @'["address", "value", "datum"] inputNode
  inputNodeValue <- pletC $ pforgetPositive inputNodeF.value
  let inputNodeDatum = punsafeCoerce @_ @_ @PLiquiditySetNode $ (ptryFromInlineDatum # inputNodeF.datum)  
  inputNodeDatumF <- pletFieldsC @'["key", "next", "commitment"] inputNodeDatum
  
  outputNodeF <- pletFieldsC @'["address", "value", "datum"] outputNode
  let outputNodeDatum = punsafeCoerce @_ @_ @PLiquiditySetNode $ (ptryFromInlineDatum # outputNodeF.datum)  
  outputNodeDatumF <- pletFieldsC @'["key", "next", "commitment"] outputNodeDatum

  nodeCommitment <- pletC $ (plovelaceValueOf # inputNodeValue) - nodeDepositAda
  let nodeKey = toScott $ pfromData inputNodeDatumF.key
      owedAdaValue = Value.psingleton # padaSymbol # padaToken # ((-nodeCommitment) - foldingFee) 
      successorChecks = 
        pand'List 
          [ ptraceIfFalse "lsn" (accNodeF.next #== nodeKey)
          , ptraceIfFalse "lsv" $ (inputNodeValue <> owedAdaValue) #== pforgetPositive outputNodeF.value
          , ptraceIfFalse "lsa" $ outputNodeF.address #== inputNodeF.address 
          , ptraceIfFalse "lsk" $ outputNodeDatumF.key #== inputNodeDatumF.key
          , ptraceIfFalse "lsn" $ outputNodeDatumF.next #== inputNodeDatumF.next
          , ptraceIfFalse "lsc" $ pfromData outputNodeDatumF.commitment #== nodeCommitment
          , ptraceIfFalse "lsc2" $ nodeCommitment #> pconstant 0
          , ptraceIfFalse "lsnt" $ pvalueOfOneScott # nodeCS # inputNodeValue
          , ptraceIfFalse "lsnh" $ 
              pmatch 
                inputNodeDatumF.key 
                ( \case
                    PEmpty _ -> pconstant False
                    PKey _ -> pconstant True
                )
          ]
      newAccState =
        pcon @PCollectionFoldState
          accNodeF
            { next = toScott (pfromData inputNodeDatumF.next)
            , committed = accNodeF.committed + nodeCommitment
            , num = accNodeF.num + 1
            }
  pure $ pif successorChecks newAccState perror

pfoldNodes :: Term s (PAsData PCurrencySymbol :--> PBuiltinList (PAsData PInteger) :--> PBuiltinList (PAsData PInteger) :--> PLiquidityFoldDatum :--> PScriptContext :--> POpaque)
pfoldNodes = phoistAcyclic $
  plam $ \nodeCS nodeInputIndices nodeOutIndices dat ctx -> unTermCont $ do
    ctxF <- pletFieldsC @'["txInfo", "purpose"] ctx
    info <- pletFieldsC @'["inputs", "referenceInputs", "outputs", "mint", "validRange"] ctxF.txInfo
    PSpending ((pfield @"_0" #) -> ownRef) <- pmatchC ctxF.purpose
    
    txInputs <- pletC $ info.inputs

    let ownInput = ptryOwnInput # txInputs # ownRef
    ownInputF <- pletFieldsC @'["address", "value"] ownInput
    PScriptCredential ((pfield @"_0" #) -> ownValHash) <- pmatchC (pfield @"credential" # ownInputF.address)
    datF <- pletFieldsC @'["currNode", "committed", "owner"] dat
    currFoldNodeF <- pletFieldsC @'["key", "next"] datF.currNode

    let ownOutput = ptryOwnOutput # info.outputs # ownValHash
    ownOutputF <- pletFieldsC @'["address", "value", "datum"] ownOutput
    (POutputDatum foldOutputDatum) <- pmatchC ownOutputF.datum

    let commitFoldState =
          pcon
            ( PCollectionFoldState
                (toScott $ pfromData currFoldNodeF.key)
                (toScott $ pfromData currFoldNodeF.next)
                0
                1 
            )
        foldOutDatum = pfromPDatum @PLiquidityFoldDatum # (pfield @"outputDatum" # foldOutputDatum)
    newFoldDatumF <- pletFieldsC @'["currNode", "committed", "owner"] foldOutDatum
    newFoldNodeF <- pletFieldsC @'["key", "next"] newFoldDatumF.currNode
    newCommitFoldState <- pmatchC $ pfoldBijectiveUTxOs (pisLiquiditySuccessor $ pfromData nodeCS) commitFoldState txInputs info.outputs nodeInputIndices nodeOutIndices
    let collectedAda = Value.psingleton # padaSymbol # padaToken # newCommitFoldState.committed 
        foldChecks =
          pand'List
            [ ptraceIfFalse "fnk" $ currFoldNodeF.key #== newFoldNodeF.key
            , ptraceIfFalse "fnn" $ newCommitFoldState.next #== (toScott $ pfromData newFoldNodeF.next)
            , ptraceIfFalse "fnc" $ pfromData newFoldDatumF.committed #== (pfromData datF.committed) + newCommitFoldState.committed
            , ptraceIfFalse "fno" $ newFoldDatumF.owner #== datF.owner 
            , ptraceIfFalse "fnv" $ pforgetPositive ownOutputF.value #== (pforgetPositive ownInputF.value <> collectedAda)
            , ptraceIfFalse "fns" $ (pcountScriptInputs # txInputs) #== newCommitFoldState.num 
            ]
    pure $
      pif foldChecks (popaque (pconstant ())) perror

data PDistributionFoldMintConfig (s :: S)
  = PDistributionFoldMintConfig
      ( Term
          s
          ( PDataRecord
              '[ "nodeCS" ':= PCurrencySymbol
               , "tokenHolderCS" ':= PCurrencySymbol
               , "rewardScriptAddr" ':= PAddress
               , "lpCS" ':= PCurrencySymbol
               , "commitFoldCS" ':= PCurrencySymbol
               , "projectAddr" ':= PAddress
               ]
          )
      )
  deriving stock (Generic)
  deriving anyclass (PlutusType, PIsData, PDataFields)

instance DerivePlutusType PDistributionFoldMintConfig where
  type DPTStrat _ = PlutusTypeData

data PDistributionFoldConfig (s :: S)
  = PDistributionFoldConfig
      ( Term
          s
          ( PDataRecord
              '[ "nodeCS" ':= PCurrencySymbol
               , "lpCS" ':= PCurrencySymbol
               ]
          )
      )
  deriving stock (Generic)
  deriving anyclass (PlutusType, PIsData, PDataFields)

instance DerivePlutusType PDistributionFoldConfig where
  type DPTStrat _ = PlutusTypeData

data PDistributionFoldDatum (s :: S)
  = PDistributionFoldDatum
      ( Term
          s
          ( PDataRecord
              '[ "currNode" ':= PLiquiditySetNode
               , "totalProjectTokens" ':= PInteger
               , "totalCommitted" ':= PInteger 
               , "owner" ':= PAddress
               ]
          )
      )
  deriving stock (Generic)
  deriving anyclass (PlutusType, PIsData, PDataFields)

instance DerivePlutusType PDistributionFoldDatum where
  type DPTStrat _ = PlutusTypeData

deriving anyclass instance
  PTryFrom PData PDistributionFoldDatum

data PDistributionFoldAct (s :: S)
  = PDistributionFoldNodes
      ( Term
          s
          ( PDataRecord
              '[ "nodeIdxs" ':= PBuiltinList (PAsData PInteger)
               , "nodeOutIdxs" ':= PBuiltinList (PAsData PInteger)
               ]
          )
      )
  | PDistributionReclaim (Term s (PDataRecord '[]))
  deriving stock (Generic)
  deriving anyclass (PlutusType, PIsData)

instance DerivePlutusType PDistributionFoldAct where
  type DPTStrat _ = PlutusTypeData

deriving anyclass instance
  PTryFrom PData PDistributionFoldAct

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

pmintRewardFoldPolicyW :: Term s (PDistributionFoldMintConfig :--> PMintingPolicy)
pmintRewardFoldPolicyW = phoistAcyclic $
  plam $ \rewardConfig _redm ctx -> unTermCont $ do
    rewardConfigF <- pletFieldsC @'["nodeCS", "tokenHolderCS", "rewardScriptAddr", "lpCS", "commitFoldCS", "projectAddr"] rewardConfig
    contextFields <- pletFieldsC @'["txInfo", "purpose"] ctx

    PMinting policy <- pmatchC contextFields.purpose
    ownPolicyId <- pletC $ pfield @"_0" # policy

    info <- pletFieldsC @'["inputs", "referenceInputs", "outputs", "mint", "datums"] contextFields.txInfo

    mintedValue <- pletC (pnormalize # info.mint)
    let tkPairs = ptryLookupValue # ownPolicyId # mintedValue
    tkPair <- pletC (pheadSingleton # tkPairs)
    
    txInputs <- pletC info.inputs
    tokenHolderCS <- pletC $ rewardConfigF.tokenHolderCS
    let nodeRefInput = pfield @"resolved" #$          
          pmustFind @PBuiltinList 
                  # plam (\inp -> pvalueOf # (pfield @"value" # (pfield @"resolved" # inp)) # rewardConfigF.nodeCS # poriginNodeTN #== 1)
                  # info.referenceInputs
              
        projectInput = pfield @"resolved" #$          
          pmustFind @PBuiltinList 
                  # plam (\inp -> pvalueOf # (pfield @"value" # (pfield @"resolved" # inp)) # tokenHolderCS # projectTokenHolderTN #== 1)
                  # txInputs
        
        projectOutput =         
          pmustFind @PBuiltinList 
                  # plam (\inp -> pfield @"address" # inp #== rewardConfigF.projectAddr)
                  # info.outputs
      
        numMinted = psndBuiltin # tkPair
        foldOutput = ptryOutputToAddress # info.outputs # rewardConfigF.rewardScriptAddr

    projectOutputF <- pletFieldsC @'["value", "datum"] projectOutput
    (POutputDatum ((pfield @"outputDatum" #) -> projOutputDatum)) <- pmatchC projectOutputF.datum
    let projOutDatum = punsafeCoerce @_ @_ @PData projOutputDatum

    projectInpF <- pletFieldsC @'["value", "datum"] projectInput

    (POutputDatumHash ((pfield @"datumHash" #) -> datumHash)) <- pmatchC projectInpF.datum 
    let projectInpDat =  punsafeCoerce @_ @_ @PLiquidityHolderDatum $ pmustFindDatum # datumHash # info.datums
    projectInpDatF <- pletFieldsC @'["totalCommitted", "totalLPTokens", "lpTokenName"] projectInpDat

    refInputF <- pletFieldsC @'["value", "datum"] nodeRefInput

    (POutputDatum refInpDatum) <- pmatchC refInputF.datum
    let refInpDat = punsafeCoerce @_ @_ @PLiquiditySetNode (pfield @"outputDatum" # refInpDatum)

    foldOutputF <- pletFieldsC @'["value", "datum"] foldOutput
    (POutputDatum foldOutputDatum) <- pmatchC foldOutputF.datum
    let foldOutDatum = pfromPDatum @PDistributionFoldDatum # (pfield @"outputDatum" # foldOutputDatum)
    foldOutDatumF <- pletFieldsC @'["currNode", "totalProjectTokens", "totalCommitted"] foldOutDatum
    rewardFoldProjectTk <- pletC foldOutDatumF.totalProjectTokens
    totalLPTokens <- pletC $ projectInpDatF.totalLPTokens 
    raisedTokens <- pletC $ pdiv # totalLPTokens # 2
    rewardFoldExpectedLPTokens <- pletC $ totalLPTokens - raisedTokens
    lpTokenCS <- pletC rewardConfigF.lpCS
    lpTokenName <- pletC projectInpDatF.lpTokenName 
    foldOutputValue <- pletC foldOutputF.value

    let raisedProjectTokens = Value.psingleton # lpTokenCS # lpTokenName # raisedTokens
        foldProjectTokens = Value.psingleton # lpTokenCS # lpTokenName # rewardFoldExpectedLPTokens
        rfoldToken = Value.psingleton # pfromData ownPolicyId # rewardFoldTN # 1
        foldInitChecks =
          pand'List
            [ ptraceIfFalse "rfmint" $ pfromData numMinted #== 1
            , ptraceIfFalse "rfn" $ foldOutDatumF.currNode #== refInpDat
            , ptraceIfFalse "rftpt1" $ rewardFoldProjectTk #== pvalueOf # foldOutputValue # lpTokenCS # lpTokenName
            , ptraceIfFalse "rftpt2" $ foldOutDatumF.totalProjectTokens #== rewardFoldExpectedLPTokens
            , ptraceIfFalse "rfrpo" $ raisedProjectTokens #== pnoAdaValue # pforgetPositive projectOutputF.value
            , ptraceIfFalse "rfrpd" $ projOutDatum #== pforgetData (pconstantData ())
            , ptraceIfFalse "rfv" $ pforgetPositive (pnoAdaValue # foldOutputValue) #== foldProjectTokens <> rfoldToken
            , ptraceIfFalse "rfc" $ projectInpDatF.totalCommitted #== foldOutDatumF.totalCommitted 
            , ptraceIfFalse "rfbpth" $ pvalueOf # mintedValue # tokenHolderCS # projectTokenHolderTN #== -1
            ]
    pure $
      pif
        foldInitChecks
        (popaque $ pconstant ())
        perror

data PDistributionFoldState (s :: S) = PDistributionFoldState
  { next :: Term s PNodeKeyState
  , owedProjectTkns :: Term s PInteger
  , foldCount :: Term s PInteger 
  }
  deriving stock (Generic)
  deriving anyclass (PlutusType, PEq)

instance DerivePlutusType PDistributionFoldState where
  type DPTStrat _ = PlutusTypeScott

prewardSuccessor :: 
  Term s PCurrencySymbol ->
  Term s PCurrencySymbol ->
  Term s PTokenName -> 
  Term s PInteger ->
  Term s PInteger -> 
  Term s PDistributionFoldState -> 
  Term s PTxOut -> 
  Term s PTxOut -> 
  Term s PDistributionFoldState
prewardSuccessor nodeCS projectCS projectTN totalProjectTokens totalCommitted state inputNode outputNode = unTermCont $ do
  accNodeF <- pmatchC state
  nodeInputF <- pletFieldsC @'["address", "value", "datum"] inputNode
  inputValue <- pletC $ pforgetPositive nodeInputF.value
  (POutputDatum nodeInpDatum) <- pmatchC nodeInputF.datum
  let nodeInpDat = punsafeCoerce @_ @_ @PLiquiditySetNode (pfield @"outputDatum" # nodeInpDatum)
  nodeInDatF <- pletFieldsC @'["key", "next", "commitment"] nodeInpDat
  
  let nodeCommitment = nodeInDatF.commitment
  owedProjectTokens <- pletC $ pdiv # (nodeCommitment * totalProjectTokens) # totalCommitted

  nodeOutputF <- pletFieldsC @'["address", "value", "datum"] outputNode
  let owedProjectValue = Value.psingleton # projectCS # projectTN # owedProjectTokens 
      owedAdaValue = Value.psingleton # padaSymbol # padaToken # (-foldingFee) 
      nodeKey = toScott $ pfromData nodeInDatF.key
      successorChecks = 
        pand'List 
          [ ptraceIfFalse "rck" (accNodeF.next #== nodeKey)
          -- To trace the value: <> (pshow ((inputValue <> owedProjectValue <> owedAdaValue)))
          , ptraceIfFalse "rcv" $ (inputValue <> owedProjectValue <> owedAdaValue) #== pforgetPositive nodeOutputF.value 
          , ptraceIfFalse "rca" $ nodeOutputF.address #== nodeInputF.address 
          , ptraceIfFalse "rcd" $ nodeOutputF.datum #== nodeInputF.datum 
          , ptraceIfFalse "rct" $ pvalueOfOneScott # nodeCS # inputValue
          ]
      accState =
        pcon @PDistributionFoldState
          accNodeF
            { next = toScott (pfromData nodeInDatF.next)
            , owedProjectTkns = accNodeF.owedProjectTkns + owedProjectTokens
            , foldCount = accNodeF.foldCount + 1 
            }
  pure $ pif successorChecks accState perror

pfoldCorrespondingUTxOs ::
  Term s PCurrencySymbol ->
  Term s PCurrencySymbol ->
  Term s PTokenName ->
  Term s PInteger ->
  Term s PInteger -> 
  Term s PDistributionFoldState ->    
  Term s (PBuiltinList PTxOut) ->
  Term s (PBuiltinList PTxOut) ->
  Term s PDistributionFoldState 
pfoldCorrespondingUTxOs nodeCS projectCS projectTN totalProjectTokens totalCommitted acc la lb =  
  pfoldl2
    # plam
      ( \state nodeIn nodeOut ->
         prewardSuccessor nodeCS projectCS projectTN totalProjectTokens totalCommitted state nodeIn nodeOut
      )
    # acc
    # la
    # lb

prewardFoldValidatorW :: Term s (PDistributionFoldConfig :--> PValidator)
prewardFoldValidatorW = phoistAcyclic $
  plam $ \rewardConfig datum redeemer ctx ->
    let dat = punsafeCoerce @_ @_ @PDistributionFoldDatum datum
        red = punsafeCoerce @_ @_ @PDistributionFoldAct redeemer
     in pmatch red $ \case
          PDistributionFoldNodes r -> pletFields @'["nodeIdxs", "nodeOutIdxs"] r $ \redF ->
            prewardFoldNodes # rewardConfig # redF.nodeIdxs # redF.nodeOutIdxs # dat # ctx
          PDistributionReclaim _ -> unTermCont $ do 
            PPubKeyCredential ((pfield @"_0" #) -> ownerPkh) <- pmatchC (pfield @"credential" # (pfield @"owner" # dat))
            ctxF <- pletFieldsC @'["txInfo", "purpose"] ctx
            infoF <- pletFieldsC @'["inputs", "signatories", "mint"] ctxF.txInfo
            PSpending ((pfield @"_0" #) -> ownRef) <- pmatchC ctxF.purpose
            let ownInput = ptryOwnInput # infoF.inputs # ownRef
            ownInputF <- pletFieldsC @'["value"] ownInput
            let signedByOwner = (ptxSignedByPkh # ownerPkh # infoF.signatories)
                atEnd = pmatch
                          (pfield @"next" # (pfield @"currNode" # dat))
                          ( \case
                              PEmpty _ -> pconstant True
                              PKey _ -> pconstant False
                          )
                rewardCS = pheadSingleton # (pfindCurrencySymbolsByTokenName # ownInputF.value # rewardFoldTN)
                rewardPair = pheadSingleton # (ptryLookupValue # rewardCS # infoF.mint)
                rewardNFTMinted = psndBuiltin # rewardPair 
                rewardReclaimChecks =
                  pand'List 
                    [ ptraceIfFalse "drc: nsbo" signedByOwner -- not signed by owner 
                    , ptraceIfFalse "drc: nae" atEnd -- reward fold has not processed all nodes
                    , ptraceIfFalse "drc: nrb" $ pfromData rewardNFTMinted #== -1 -- reward fold NFT has not been burned 
                    ]
            pure $ 
              pif rewardReclaimChecks
                  (popaque $ pconstant ())
                  perror 

prewardFoldNodes :: 
  Term s 
    (PDistributionFoldConfig 
      :--> PBuiltinList (PAsData PInteger) 
      :--> PBuiltinList (PAsData PInteger) 
      :--> PDistributionFoldDatum 
      :--> PScriptContext 
      :--> POpaque)    
prewardFoldNodes = phoistAcyclic $ plam $ \rewardConfig inputIdxs outputIdxs dat ctx -> unTermCont $ do 
  rewardConfigF <- pletFieldsC @'["nodeCS", "projectTN", "lpCS"] rewardConfig    
  ctxF <- pletFieldsC @'["txInfo", "purpose"] ctx
  info <- pletFieldsC @'["inputs", "outputs", "referenceInputs", "mint"] ctxF.txInfo
  txIns <- pletC $ pfromData info.inputs 
  txOuts <- pletC $ pfromData info.outputs

  let nodeInputs :: Term _ (PBuiltinList PTxOut)
      nodeInputs = pmap @PBuiltinList # plam (\i -> pfield @"resolved" # (pelemAt' # pfromData i # txIns)) # inputIdxs
      nodeOutputs :: Term _ (PBuiltinList PTxOut)
      nodeOutputs = pmap @PBuiltinList # plam (\i -> (pelemAt' # pfromData i # txOuts)) # outputIdxs

  PSpending ((pfield @"_0" #) -> ownRef) <- pmatchC ctxF.purpose
  
  let ownInput = ptryOwnInput # txIns # ownRef
  ownInputF <- pletFieldsC @'["address", "value"] ownInput
  PScriptCredential ((pfield @"_0" #) -> ownValHash) <- pmatchC (pfield @"credential" # ownInputF.address)
  datF <- pletFieldsC @'["currNode", "totalProjectTokens", "totalCommitted", "owner"] dat
  currFoldNodeF <- pletFieldsC @'["key", "next"] datF.currNode

  let ownOutput = ptryOwnOutput # txOuts # ownValHash
  ownOutputF <- pletFieldsC @'["value", "datum"] ownOutput
  (POutputDatum foldOutputDatum) <- pmatchC ownOutputF.datum

  let foldOutDatum = pfromPDatum @PDistributionFoldDatum # (pfield @"outputDatum" # foldOutputDatum)
  newDatumF <- pletFieldsC @'["currNode", "totalProjectTokens", "totalCommitted", "owner"] foldOutDatum
  newFoldNodeF <- pletFieldsC @'["key", "next"] newDatumF.currNode 

  let rewardsFoldState =
        pcon
          ( PDistributionFoldState
              (toScott $ pfromData currFoldNodeF.next)
              0
              1
          )
  ownInputValue <- pletC ownInputF.value
  projCS <- pletC $ pfromData rewardConfigF.lpCS 
  projTN <- pletC $ pfromData $ pfstBuiltin #$ pheadSingleton #$ ptryLookupValue # pdata projCS # ownInputValue
  totalProjTokens <- pletC datF.totalProjectTokens
  nodeCS <- pletC rewardConfigF.nodeCS
  totalCommitment <- pletC datF.totalCommitted 
  newRewardsFoldState <- pmatchC $ pfoldCorrespondingUTxOs nodeCS projCS projTN totalProjTokens totalCommitment rewardsFoldState nodeInputs nodeOutputs
  let foldChecks = 
        pand'List 
          [ ptraceIfFalse "nodeKey" $ newFoldNodeF.key #== currFoldNodeF.key
          , ptraceIfFalse "ptn" $ newDatumF.totalProjectTokens #== totalProjTokens
          , ptraceIfFalse "tc" $ newDatumF.totalCommitted #== totalCommitment 
          , ptraceIfFalse "own" $ newDatumF.owner #== datF.owner 
          , ptraceIfFalse "rstate" $ newRewardsFoldState.next #== (toScott $ pfromData newFoldNodeF.next)
          , ptraceIfFalse "rval" $ pnormalize # (Value.pforgetPositive ownInputF.value <> Value.psingleton # projCS # projTN # (-newRewardsFoldState.owedProjectTkns)) #== Value.pforgetPositive ownOutputF.value 
          , ptraceIfFalse "rsco" $ (pcountScriptInputs # txIns) #== newRewardsFoldState.foldCount 
          ]
  pure $
      pif foldChecks (popaque (pconstant ())) perror

-- prewardFoldNode :: Term s (PDistributionFoldConfig :--> PDistributionFoldDatum :--> PScriptContext :--> POpaque)
-- prewardFoldNode = phoistAcyclic $
--   plam $ \rewardConfig dat ctx -> unTermCont $ do
--     rewardConfigF <- pletFieldsC @'["nodeCS", "lpCS", "projectAddr"] rewardConfig
--     ctxF <- pletFieldsC @'["txInfo", "purpose"] ctx
--     info <- pletFieldsC @'["inputs", "outputs", "referenceInputs", "mint"] ctxF.txInfo

--     PSpending ((pfield @"_0" #) -> ownRef) <- pmatchC ctxF.purpose
--     let ownInput = ptryOwnInput # info.inputs # ownRef
--     ownInputF <- pletFieldsC @'["address", "value"] ownInput
--     PScriptCredential ((pfield @"_0" #) -> ownValHash) <- pmatchC (pfield @"credential" # ownInputF.address)

--     datF <- pletFieldsC @'["currNode", "totalProjectTokens", "totalCommitted", "owner"] dat
--     currFoldNodeF <- pletFieldsC @'["key", "next"] datF.currNode

--     txOuts <- pletC info.outputs
--     let ownOutput = ptryOwnOutput # txOuts # ownValHash
--     ownOutputF <- pletFieldsC @'["address", "value", "datum"] ownOutput
--     (POutputDatum foldOutputDatum) <- pmatchC ownOutputF.datum

--     let foldOutDatum = pfromPDatum @PDistributionFoldDatum # (pfield @"outputDatum" # foldOutputDatum)
--     foldOutDatumF <- pletFieldsC @'["currNode", "totalProjectTokens", "totalCommitted", "owner"] foldOutDatum

--     oldTotalCommitted <- pletC datF.totalCommitted

--     let nodeInputs =
--           pfilter @PBuiltinList
--             # plam (\inp -> (pvalueOfOne # rewardConfigF.nodeCS # (pfield @"value" # (pfield @"resolved" # inp))))
--             # info.inputs
--     nodeInputF <- pletFieldsC @'["address", "value", "datum"] (pfield @"resolved" # (pheadSingleton # nodeInputs))
--     (POutputDatum nodeInpDatum) <- pmatchC nodeInputF.datum

--     nodeInputValue <- pletC nodeInputF.value
--     nodeCommitment <- pletC $ plovelaceValueOf # nodeInputValue - nodeDepositAda
--     owedProjectTkns <- pletC $ pdiv # (nodeCommitment * datF.totalProjectTokens) # datF.totalCommitted
--     -- doesn't work with no decimal tokens
--     -- nodeOutputValue = nodeOutputValue + rewardFoldProjectTk - nodeInputAda
--     let nodeInpDat = pfromPDatum @PLiquiditySetNode # (pfield @"outputDatum" # nodeInpDatum)
--     nodeInpDatF <- pletFieldsC @'["key", "next"] nodeInpDat

--     let nodeOutput = ptryOutputToAddress # txOuts # nodeInputF.address
--     nodeOutputF <- pletFieldsC @'["value"] nodeOutput

--     mkProjValue <- pletC $ Value.psingleton # rewardConfigF.projectCS # rewardConfigF.projectTN
--     mkAdaValue <- pletC $ Value.psingleton # padaSymbol # padaToken
--     distributedValue <- pletC $ mkProjValue # (-owedProjectTkns)
--     posDistributedValue <- pletC $ mkProjValue # owedProjectTkns
--     collectedAdaValue <- pletC $ mkAdaValue # (-nodeCommitment)
--     posCollectedAdaValue <- pletC $ mkAdaValue # nodeCommitment

--     let correctOwnOutput = (pforgetPositive ownInputF.value) <> distributedValue 
--         correctNodeOutput = (pforgetPositive nodeInputValue <> posDistributedValue) <> collectedAdaValue
--         projectOut = ptryOutputToAddress # txOuts # rewardConfigF.projectAddr
--     let foldChecks =
--           pand'List
--             [ currFoldNodeF.next #== nodeInpDatF.key,
--               foldOutDatumF.currNode #== nodeInpDat,
--               foldOutDatumF.totalCommitted #== oldTotalCommitted,
--               foldOutDatumF.totalProjectTokens #== datF.totalProjectTokens,
--               foldOutDatumF.owner #== datF.owner,
--               (pnoAdaValue # correctOwnOutput ) #== (pnoAdaValue #$ pforgetPositive ownOutputF.value),
--               correctNodeOutput #== (pforgetPositive nodeOutputF.value),
--               pforgetPositive (pfield @"value" # projectOut) #== posCollectedAdaValue
--             ]
--     pure $ pif foldChecks (popaque (pconstant ())) perror
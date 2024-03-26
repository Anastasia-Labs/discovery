{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE OverloadedRecordDot #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE UndecidableInstances #-}
{-# OPTIONS_GHC -Wno-incomplete-uni-patterns #-}
{-# OPTIONS_GHC -Wno-missing-import-lists #-}

module PriceDiscoveryEvent.MultiFold where

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
import PriceDiscoveryEvent.Utils (
  pand'List,
  pcond,
  pelemAt',
  phasInput,
  pheadSingleton,
  ptryLookupValue,
  ptryOutputToAddress,
  ptryOwnInput,
  ptryOwnOutput,
  pvalueOfOne,
  (#>),
  ptxSignedByPkh,
  pfoldl2,
  pvalueOfOneScott,
  pcountScriptInputs,
  pfindCurrencySymbolsByTokenName, pcountOfUniqueTokens,
 )
import Types.Classes
import Types.Constants (commitFoldTN, minAda, nodeDepositAda, poriginNodeTN, rewardFoldTN, projectTokenHolderTN, foldingFee)
import Types.DiscoverySet

data PFoldMintConfig (s :: S)
  = PFoldMintConfig
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

instance DerivePlutusType PFoldMintConfig where
  type DPTStrat _ = PlutusTypeData

data PFoldMintAct (s :: S)
  = PMintFold (Term s (PDataRecord '[]))
  | PBurnFold (Term s (PDataRecord '[]))
  deriving stock (Generic)
  deriving anyclass (PlutusType, PIsData)

instance DerivePlutusType PFoldMintAct where
  type DPTStrat _ = PlutusTypeData

instance PTryFrom PData PFoldMintAct 

instance PTryFrom PData (PAsData PFoldMintAct)

data PFoldDatum (s :: S)
  = PFoldDatum
      ( Term
          s
          ( PDataRecord
              '[ "currNode" ':= PDiscoverySetNode
               , "committed" ':= PInteger
               , "owner" ':= PAddress
               ]
          )
      )
  deriving stock (Generic)
  deriving anyclass (PlutusType, PIsData, PDataFields)

instance DerivePlutusType PFoldDatum where
  type DPTStrat _ = PlutusTypeData

instance PTryFrom PData PFoldDatum

instance PTryFrom PData (PAsData PFoldDatum)

data PFoldAct (s :: S)
  = PFoldNodes
      ( Term
          s
          ( PDataRecord
              '[ "nodeIdxs" ':= PBuiltinList (PAsData PInteger) ]
          )
      )
  | PReclaim (Term s (PDataRecord '[]))
  deriving stock (Generic)
  deriving anyclass (PlutusType, PIsData)

instance DerivePlutusType PFoldAct where
  type DPTStrat _ = PlutusTypeData

deriving anyclass instance
  PTryFrom PData PFoldAct

data PCommitFoldState (s :: S) = PCommitFoldState
  { key :: Term s PNodeKeyState
  , next :: Term s PNodeKeyState
  , committed :: Term s PInteger
  -- , num :: Term s PInteger
  }
  deriving stock (Generic)
  deriving anyclass (PlutusType, PEq)

instance DerivePlutusType PCommitFoldState where
  type DPTStrat _ = PlutusTypeScott

pmintFoldPolicyW :: Term s (PFoldMintConfig :--> PMintingPolicy)
pmintFoldPolicyW = phoistAcyclic $ 
  plam $ \fconfig redm ctx ->
    let red = punsafeCoerce @_ @_ @PFoldMintAct redm 
     in pmatch red $ \case 
          PMintFold _ -> popaque $ pmintCommitFold # fconfig # ctx 
          PBurnFold _ -> popaque $ pburnCommitFold # ctx 

pburnCommitFold :: Term s (PScriptContext :--> PUnit)
pburnCommitFold = phoistAcyclic $ 
  plam $ \ ctx -> unTermCont $ do
    contextFields <- pletFieldsC @'["txInfo", "purpose"] ctx
    PMinting policy <- pmatchC contextFields.purpose
    ownPolicyId <- pletC $ pfield @"_0" # policy

    info <- pletFieldsC @'["mint"] contextFields.txInfo
    tkPairs <- pletC $ ptryLookupValue # ownPolicyId # (pnormalize # info.mint)
    tkPair <- pletC (pheadSingleton # tkPairs)
    let numMinted = psndBuiltin # tkPair 
    pure $
      pif ( pfromData numMinted #== -1 ) (pconstant ()) perror 

pmintCommitFold :: Term s (PFoldMintConfig :--> PScriptContext :--> PUnit)
pmintCommitFold = phoistAcyclic $ 
  plam $ \fconfig ctx -> unTermCont $ do 
    foldConfF <- pletFieldsC @'["nodeCS", "foldAddr", "discoveryDeadline"] fconfig 
    contextFields <- pletFieldsC @'["txInfo", "purpose"] ctx

    PMinting policy <- pmatchC contextFields.purpose
    ownPolicyId <- pletC $ pfield @"_0" # policy

    info <- pletFieldsC @'["referenceInputs", "outputs", "mint", "validRange"] contextFields.txInfo

    tkPairs <- pletC $ ptryLookupValue # ownPolicyId # (pnormalize # info.mint)
    tkPair <- pletC (pheadSingleton # tkPairs)

    let numMinted = psndBuiltin # tkPair
        foldOutput = ptryOutputToAddress # info.outputs # foldConfF.foldAddr
        refInput = pfield @"resolved" # (pheadSingleton @PBuiltinList # info.referenceInputs)

    refInputF <- pletFieldsC @'["value", "datum"] refInput

    (POutputDatum refInpDatum) <- pmatchC refInputF.datum
    let refInpDat = pfromPDatum @PDiscoverySetNode # (pfield @"outputDatum" # refInpDatum)

    foldOutputF <- pletFieldsC @'["value", "datum"] foldOutput
    (POutputDatum foldOutputDatum) <- pmatchC foldOutputF.datum

    let foldOutDatum = pfromPDatum @PFoldDatum # (pfield @"outputDatum" # foldOutputDatum)
    foldOutDatumF <- pletFieldsC @'["currNode", "committed"] foldOutDatum

    let foldInitChecks =
          pand'List
            [ pfromData numMinted #== 1
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

pfoldValidatorW :: Term s (PAsData PCurrencySymbol :--> PAsData PPOSIXTime :--> PValidator)
pfoldValidatorW = phoistAcyclic $
  plam $ \nodeCS discoveryDeadline datum redeemer ctx ->
    let dat = punsafeCoerce @_ @_ @PFoldDatum datum
        red = punsafeCoerce @_ @_ @PFoldAct redeemer
     in pmatch red $ \case
          PFoldNodes r -> pletFields @'["nodeIdxs"] r $ \redF ->
            pfoldNodes # nodeCS # discoveryDeadline # redF.nodeIdxs # dat # ctx
          PReclaim _ -> unTermCont $ do 
            PPubKeyCredential ((pfield @"_0" #) -> ownerPkh) <- pmatchC (pfield @"credential" # (pfield @"owner" # dat))
            ctxF <- pletFieldsC @'["txInfo", "purpose"] ctx
            infoF <- pletFieldsC @'["inputs", "signatories", "mint"] ctxF.txInfo
            PSpending ((pfield @"_0" #) -> ownRef) <- pmatchC ctxF.purpose
            let ownInput = ptryOwnInput # infoF.inputs # ownRef
            ownInputF <- pletFieldsC @'["address", "value"] ownInput
            let possibleCSs = pfindCurrencySymbolsByTokenName # ownInputF.value # commitFoldTN 
                commitCS = pheadSingleton # possibleCSs
                commitPairs = ptryLookupValue # commitCS # infoF.mint
                commitPair = (pheadSingleton # commitPairs)
                commitMinted = psndBuiltin # commitPair 
            pure $ 
              pif (ptxSignedByPkh # ownerPkh # infoF.signatories #&& pfromData commitMinted #== -1)
                  (popaque $ pconstant ())
                  perror  

pisSuccessor :: Term s (PCurrencySymbol :--> PCommitFoldState :--> PTxOut :--> PCommitFoldState)
pisSuccessor = plam $ \nodeCS accNode node -> unTermCont $ do
  accNodeF <- pmatchC accNode
  nodeF <- pletFieldsC @'["value", "datum"] node
  nodeValue <- pletC nodeF.value
  let nodeDatum = punsafeCoerce @_ @_ @PDiscoverySetNode $ (ptryFromInlineDatum # nodeF.datum)
      hasNodeTk = pvalueOfOneScott # nodeCS # nodeValue
  currNodeF <- pletFieldsC @'["key", "next"] nodeDatum

  let nodeKey = toScott $ pfromData currNodeF.key
      accState =
        pcon @PCommitFoldState
          accNodeF
            { next = toScott (pfromData currNodeF.next)
            , committed = accNodeF.committed + (plovelaceValueOf # nodeValue) - nodeDepositAda
            -- , num = accNodeF.num + 1
            }
  pure $ pif (pand' # (accNodeF.next #== nodeKey) # hasNodeTk) accState perror

pfoldNodes :: Term s (PAsData PCurrencySymbol :--> PAsData PPOSIXTime :--> PBuiltinList (PAsData PInteger) :--> PFoldDatum :--> PScriptContext :--> POpaque)
pfoldNodes = phoistAcyclic $
  plam $ \nodeCS discoveryDeadline nodeIndices dat ctx -> unTermCont $ do
    ctxF <- pletFieldsC @'["txInfo", "purpose"] ctx
    -- all reference inputs have node currency symbol
    -- all reference inputs are connected in the linked list
    info <- pletFieldsC @'["inputs", "referenceInputs", "outputs", "mint", "validRange"] ctxF.txInfo
    PSpending ((pfield @"_0" #) -> ownRef) <- pmatchC ctxF.purpose

    let ownInput = ptryOwnInput # info.inputs # ownRef
    ownInputF <- pletFieldsC @'["address", "value"] ownInput
    PScriptCredential ((pfield @"_0" #) -> ownValHash) <- pmatchC (pfield @"credential" # ownInputF.address)
    datF <- pletFieldsC @'["currNode", "committed", "owner"] dat
    currFoldNodeF <- pletFieldsC @'["key", "next"] datF.currNode
    
    let ownOutput = ptryOwnOutput # info.outputs # ownValHash
    ownOutputF <- pletFieldsC @'["address", "value", "datum"] ownOutput
    (POutputDatum foldOutputDatum) <- pmatchC ownOutputF.datum

    let commitFoldState =
          pcon
            ( PCommitFoldState
                (toScott $ pfromData currFoldNodeF.key)
                (toScott $ pfromData currFoldNodeF.next)
                (pfromData datF.committed)
            )
        foldOutDatum = pfromPDatum @PFoldDatum # (pfield @"outputDatum" # foldOutputDatum)
    newFoldDatumF <- pletFieldsC @'["currNode", "committed", "owner"] foldOutDatum
    newFoldNodeF <- pletFieldsC @'["key", "next"] newFoldDatumF.currNode

    let refInputs :: Term _ (PBuiltinList PTxInInfo)
        refInputs = info.referenceInputs

    refIns <- pletC refInputs

    let nodeInputs :: Term _ (PBuiltinList PTxOut)
        nodeInputs = pmap @PBuiltinList # plam (\i -> pfield @"resolved" # (pelemAt' # pfromData i # refIns)) # nodeIndices
        newCommitFoldState' = pfoldl # (pisSuccessor # pfromData nodeCS) # commitFoldState # nodeInputs
        countOwnInputs = plength 
            # ( pfilter @PBuiltinList
                  # plam (\txInp -> (pfield @"address" # (pfield @"resolved" # txInp)) #== ownInputF.address)
                  # info.inputs 
              )
    newCommitFoldState <- pmatchC newCommitFoldState'
    let foldChecks =
          pand'List
            [ countOwnInputs #== 1
            , pfromData info.mint #== mempty
            , currFoldNodeF.key #== newFoldNodeF.key
            , newCommitFoldState.next #== (toScott $ pfromData newFoldNodeF.next)
            , pfromData newFoldDatumF.committed #== newCommitFoldState.committed
            , newFoldDatumF.owner #== datF.owner 
            , pnoAdaValue # ownOutputF.value #== pnoAdaValue # ownInputF.value
            , pbefore # pfromData discoveryDeadline # info.validRange
            ]
    pure $
      pif foldChecks (popaque (pconstant ())) perror

data PRewardMintFoldConfig (s :: S)
  = PRewardMintFoldConfig
      ( Term
          s
          ( PDataRecord
              '[ "nodeCS" ':= PCurrencySymbol
               , "tokenHolderCS" ':= PCurrencySymbol
               , "rewardScriptAddr" ':= PAddress
               , "projectTN" ':= PTokenName
               , "projectCS" ':= PCurrencySymbol
               , "commitFoldCS" ':= PCurrencySymbol
               ]
          )
      )
  deriving stock (Generic)
  deriving anyclass (PlutusType, PIsData, PDataFields)

instance DerivePlutusType PRewardMintFoldConfig where
  type DPTStrat _ = PlutusTypeData

data PRewardFoldConfig (s :: S)
  = PRewardFoldConfig
      ( Term
          s
          ( PDataRecord
              '[ "nodeCS" ':= PCurrencySymbol
               , "projectCS" ':= PCurrencySymbol
               , "projectTN" ':= PTokenName
               , "projectAddr" ':= PAddress
               ]
          )
      )
  deriving stock (Generic)
  deriving anyclass (PlutusType, PIsData, PDataFields)

instance DerivePlutusType PRewardFoldConfig where
  type DPTStrat _ = PlutusTypeData

data PRewardFoldDatum (s :: S)
  = PRewardFoldDatum
      ( Term
          s
          ( PDataRecord
              '[ "currNode" ':= PDiscoverySetNode
               , "totalProjectTokens" ':= PInteger
               , "totalCommitted" ':= PInteger 
               , "owner" ':= PAddress
               ]
          )
      )
  deriving stock (Generic)
  deriving anyclass (PlutusType, PIsData, PDataFields)

instance DerivePlutusType PRewardFoldDatum where
  type DPTStrat _ = PlutusTypeData

deriving anyclass instance
  PTryFrom PData PRewardFoldDatum

data PRewardsFoldAct (s :: S)
  = PRewardsFoldNodes
      ( Term
          s
          ( PDataRecord
              '[ "nodeIdxs" ':= PBuiltinList (PAsData PInteger)
               , "nodeOutIdxs" ':= PBuiltinList (PAsData PInteger)
               ]
          )
      )
  | PRewardsReclaim (Term s (PDataRecord '[]))
  deriving stock (Generic)
  deriving anyclass (PlutusType, PIsData)

instance DerivePlutusType PRewardsFoldAct where
  type DPTStrat _ = PlutusTypeData

deriving anyclass instance
  PTryFrom PData PRewardsFoldAct

pmintRewardFoldPolicyW :: Term s (PRewardMintFoldConfig :--> PMintingPolicy)
pmintRewardFoldPolicyW = phoistAcyclic $
  plam $ \rewardConfig _redm ctx -> unTermCont $ do
    rewardConfigF <- pletFieldsC @'["nodeCS", "tokenHolderCS", "rewardScriptAddr", "projectTN", "projectCS", "commitFoldCS"] rewardConfig
    contextFields <- pletFieldsC @'["txInfo", "purpose"] ctx

    PMinting policy <- pmatchC contextFields.purpose
    ownPolicyId <- pletC $ pfield @"_0" # policy

    info <- pletFieldsC @'["inputs", "referenceInputs", "outputs", "mint"] contextFields.txInfo

    mintedValue <- pletC $ (pnormalize # info.mint)
    tkPairs <- pletC $ ptryLookupValue # ownPolicyId # mintedValue
    tkPair <- pletC (pheadSingleton # tkPairs)

    let commitInp = pfield @"resolved" #$ 
          pheadSingleton
            # ( pfilter @PBuiltinList
                  # plam (\inp -> pvalueOf # (pfield @"value" # (pfield @"resolved" # inp)) # rewardConfigF.commitFoldCS # commitFoldTN #== 1)
                  # info.inputs 
              )
        nodeRefInput = pfield @"resolved" #$          
          pheadSingleton
            # ( pfilter @PBuiltinList
                  # plam (\inp -> pvalueOf # (pfield @"value" # (pfield @"resolved" # inp)) # rewardConfigF.nodeCS # poriginNodeTN #== 1)
                  # info.referenceInputs
              )
        projectInput = pfield @"resolved" #$          
          pheadSingleton
            # ( pfilter @PBuiltinList
                  # plam (\inp -> pvalueOf # (pfield @"value" # (pfield @"resolved" # inp)) # rewardConfigF.tokenHolderCS # projectTokenHolderTN #== 1)
                  # info.inputs
              )
        numMinted = psndBuiltin # tkPair
        foldOutput = ptryOutputToAddress # info.outputs # rewardConfigF.rewardScriptAddr

    commitInpF <- pletFieldsC @'["value", "datum"] commitInp
    (POutputDatum commitDatum) <- pmatchC commitInpF.datum
    let commitDat = punsafeCoerce @_ @_ @PFoldDatum (pfield @"outputDatum" # commitDatum)
    commitDatF <- pletFieldsC @'["currNode", "committed", "owner"] commitDat
    commitFoldNodeF <- pletFieldsC @'["key", "next"] commitDatF.currNode

    refInputF <- pletFieldsC @'["value", "datum"] nodeRefInput

    (POutputDatum refInpDatum) <- pmatchC refInputF.datum
    let refInpDat = pfromPDatum @PDiscoverySetNode # (pfield @"outputDatum" # refInpDatum)

    foldOutputF <- pletFieldsC @'["value", "datum"] foldOutput
    (POutputDatum foldOutputDatum) <- pmatchC foldOutputF.datum

    let foldOutDatum = pfromPDatum @PRewardFoldDatum # (pfield @"outputDatum" # foldOutputDatum)
    foldOutDatumF <- pletFieldsC @'["currNode", "totalProjectTokens", "totalCommitted"] foldOutDatum

    totalProjectTkns <- pletC foldOutDatumF.totalProjectTokens 
    let foldInitChecks =
          pand'List
            [ pfromData numMinted #== 1
            , foldOutDatumF.currNode #== refInpDat
            , totalProjectTkns #== pvalueOf # foldOutputF.value # rewardConfigF.projectCS # rewardConfigF.projectTN
            , totalProjectTkns #== pvalueOf # (pfield @"value" # projectInput) # rewardConfigF.projectCS # rewardConfigF.projectTN
            , pvalueOf # foldOutputF.value # pfromData ownPolicyId # rewardFoldTN #== 1
            , pcountOfUniqueTokens # foldOutputF.value #== 3
            , pmatch
                commitFoldNodeF.next
                ( \case
                    PEmpty _ -> pconstant True
                    PKey _ -> pconstant False
                )
            , commitDatF.committed #== foldOutDatumF.totalCommitted 
            , pvalueOf # mintedValue # rewardConfigF.tokenHolderCS # projectTokenHolderTN #== -1
            ]
    pure $
      pif
        foldInitChecks
        (popaque $ pconstant ())
        perror

data PRewardsFoldState (s :: S) = PRewardsFoldState
  { next :: Term s PNodeKeyState
  , owedProjectTkns :: Term s PInteger
  , receivedCommitment :: Term s PInteger 
  , foldCount :: Term s PInteger 
  }
  deriving stock (Generic)
  deriving anyclass (PlutusType, PEq)

instance DerivePlutusType PRewardsFoldState where
  type DPTStrat _ = PlutusTypeScott

prewardSuccessor :: 
  Term s PCurrencySymbol ->
  Term s PCurrencySymbol ->
  Term s PTokenName -> 
  Term s PInteger ->
  Term s PInteger -> 
  Term s PRewardsFoldState -> 
  Term s PTxOut -> 
  Term s PTxOut -> 
  Term s PRewardsFoldState
prewardSuccessor nodeCS projectCS projectTN totalProjectTokens totalCommitted state inputNode outputNode = unTermCont $ do
  accNodeF <- pmatchC state
  nodeInputF <- pletFieldsC @'["address", "value", "datum"] inputNode
  inputValue <- pletC $ pforgetPositive nodeInputF.value
  (POutputDatum nodeInpDatum) <- pmatchC nodeInputF.datum
  let nodeInpDat = punsafeCoerce @_ @_ @PDiscoverySetNode (pfield @"outputDatum" # nodeInpDatum)
  nodeInDatF <- pletFieldsC @'["key", "next"] nodeInpDat
  
  nodeCommitment <- pletC $ plovelaceValueOf # inputValue - nodeDepositAda
  owedProjectTokens <- pletC $ pdiv # (nodeCommitment * totalProjectTokens) # totalCommitted

  nodeOutputF <- pletFieldsC @'["address", "value", "datum"] outputNode
  nodeOutputValue <- pletC $ nodeOutputF.value 
  let owedProjectValue = Value.psingleton # projectCS # projectTN # owedProjectTokens 
      owedAdaValue = Value.psingleton # padaSymbol # padaToken # ((-nodeCommitment) - (foldingFee * 2) ) 
      nodeKey = toScott $ pfromData nodeInDatF.key
      successorChecks = 
        pand'List 
          [ (accNodeF.next #== nodeKey)
          , (inputValue <> owedProjectValue <> owedAdaValue) #== pforgetPositive nodeOutputValue
          , nodeOutputF.address #== nodeInputF.address 
          , nodeOutputF.datum #== nodeInputF.datum 
          , pvalueOfOneScott # nodeCS # inputValue
          ]
      accState =
        pcon @PRewardsFoldState
          accNodeF
            { next = toScott (pfromData nodeInDatF.next)
            , owedProjectTkns = accNodeF.owedProjectTkns + owedProjectTokens
            , receivedCommitment = accNodeF.receivedCommitment + nodeCommitment
            , foldCount = accNodeF.foldCount + 1 
            }
  pure $ pif successorChecks accState perror

pfoldCorrespondingUTxOs ::
  Term s PCurrencySymbol ->
  Term s PCurrencySymbol ->
  Term s PTokenName ->
  Term s PInteger ->
  Term s PInteger -> 
  Term s PRewardsFoldState ->    
  Term s (PBuiltinList PTxOut) ->
  Term s (PBuiltinList PTxOut) ->
  Term s PRewardsFoldState 
pfoldCorrespondingUTxOs nodeCS projectCS projectTN totalProjectTokens totalCommitted acc la lb =  
  pfoldl2
    # plam
      ( \state nodeIn nodeOut ->
         prewardSuccessor nodeCS projectCS projectTN totalProjectTokens totalCommitted state nodeIn nodeOut
      )
    # acc
    # la
    # lb

prewardFoldValidatorW :: Term s (PRewardFoldConfig :--> PValidator)
prewardFoldValidatorW = phoistAcyclic $
  plam $ \rewardConfig datum redeemer ctx ->
    let dat = punsafeCoerce @_ @_ @PRewardFoldDatum datum
        red = punsafeCoerce @_ @_ @PRewardsFoldAct redeemer
     in pmatch red $ \case
          PRewardsFoldNodes r -> pletFields @'["nodeIdxs", "nodeOutIdxs"] r $ \redF ->
            prewardFoldNodes # rewardConfig # redF.nodeIdxs # redF.nodeOutIdxs # dat # ctx
          PRewardsReclaim _ -> unTermCont $ do 
            PPubKeyCredential ((pfield @"_0" #) -> ownerPkh) <- pmatchC (pfield @"credential" # (pfield @"owner" # dat))
            infoF <- pletFieldsC @'["signatories"] (pfield @"txInfo" # ctx)
            let signedByOwner = (ptxSignedByPkh # ownerPkh # infoF.signatories)
                atEnd = pmatch
                          (pfield @"next" # (pfield @"currNode" # dat))
                          ( \case
                              PEmpty _ -> pconstant True
                              PKey _ -> pconstant False
                          )
            pure $ 
              pif (signedByOwner #&& atEnd)
                  (popaque $ pconstant ())
                  perror 

prewardFoldNodes :: 
  Term s 
    (PRewardFoldConfig 
      :--> PBuiltinList (PAsData PInteger) 
      :--> PBuiltinList (PAsData PInteger) 
      :--> PRewardFoldDatum 
      :--> PScriptContext 
      :--> POpaque)    
prewardFoldNodes = phoistAcyclic $ plam $ \rewardConfig inputIdxs outputIdxs dat ctx -> unTermCont $ do 
  rewardConfigF <- pletFieldsC @'["nodeCS", "projectTN", "projectCS", "projectAddr"] rewardConfig    
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

  let foldOutDatum = pfromPDatum @PRewardFoldDatum # (pfield @"outputDatum" # foldOutputDatum)
  newDatumF <- pletFieldsC @'["currNode", "totalProjectTokens", "totalCommitted", "owner"] foldOutDatum
  newFoldNodeF <- pletFieldsC @'["key", "next"] newDatumF.currNode 

  let rewardsFoldState =
        pcon
          ( PRewardsFoldState
              (toScott $ pfromData currFoldNodeF.next)
              0
              0
              1
          )

  projCS <- pletC rewardConfigF.projectCS 
  projTN <- pletC rewardConfigF.projectTN
  totalProjTokens <- pletC datF.totalProjectTokens
  nodeCS <- pletC rewardConfigF.nodeCS
  totalCommitment <- pletC datF.totalCommitted 
  newRewardsFoldState <- pmatchC $ pfoldCorrespondingUTxOs nodeCS projCS projTN totalProjTokens totalCommitment rewardsFoldState nodeInputs nodeOutputs
  let projectOut = ptryOutputToAddress # txOuts # rewardConfigF.projectAddr      
  let foldChecks = 
        pand'List 
          [ newFoldNodeF.key #== currFoldNodeF.key
          , newDatumF.totalProjectTokens #== totalProjTokens
          , newDatumF.totalCommitted #== totalCommitment 
          , newDatumF.owner #== datF.owner 
          , newRewardsFoldState.next #== (toScott $ pfromData newFoldNodeF.next)
          , pnormalize # (Value.pforgetPositive ownInputF.value <> Value.psingleton # projCS # projTN # (-newRewardsFoldState.owedProjectTkns)) #== Value.pforgetPositive ownOutputF.value 
          , pvalueOf # (pfield @"value" # projectOut) # padaSymbol # padaToken #== newRewardsFoldState.receivedCommitment
          , (pcountScriptInputs # txIns) #== newRewardsFoldState.foldCount 
          ]
  pure $
      pif foldChecks (popaque (pconstant ())) perror

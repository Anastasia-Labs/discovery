{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE UndecidableInstances #-}

module LiquidityEvent.Validator (
  pLiquiditySetValidator,
  pLiquidityGlobalLogicW
) where

import Data.ByteString (ByteString)

import Plutarch (Config)
import Plutarch.Api.V1 (
  PCredential (..),
 )
import Plutarch.Api.V1.AssocMap qualified as AssocMap
import Plutarch.Api.V1.Value (PValue (..), plovelaceValueOf, pnoAdaValue, pvalueOf)
import Plutarch.Api.V2 (
  PPubKeyHash (..),
  PCurrencySymbol (..),
  POutputDatum (..),
  PScriptPurpose (PSpending),
  PValidator,
  PStakeValidator,
 )
import Plutarch.Extra.Interval (pafter, pbefore)
import Plutarch.Extra.ScriptContext (pfromPDatum)
import Plutarch.Monadic qualified as P
import Plutarch.Prelude
import Plutarch.Unsafe (punsafeCoerce)
import PriceDiscoveryEvent.Utils (passert, pcontainsCurrencySymbols, pfindCurrencySymbolsByTokenPrefix, pheadSingleton, ptryOwnInput, ptryOwnOutput, phasCS, pisFinite, pmustFind, pand'List)
import Types.Constants (rewardFoldTN)
import Types.LiquiditySet (PLBELockConfig (..), PLiquiditySetNode (..), PLNodeAction (..))
import PriceDiscoveryEvent.MultiFoldLiquidity (PDistributionFoldDatum (..))
import Types.DiscoverySet (PNodeKey(..))

pLiquidityGlobalLogicW :: Term s (PAsData PCurrencySymbol :--> PStakeValidator)
pLiquidityGlobalLogicW = phoistAcyclic $ plam $ \foldCS' _redeemer ctx -> P.do
  -- let rewardsIdx = punsafeCoerce @_ @_ @(PAsData PInteger) redeemer
  ctxF <- pletFields @'["txInfo"] ctx
  infoF <- pletFields @'["inputs"] ctxF.txInfo
  foldCS <- plet $ pfromData foldCS'
  let hasFoldToken = pany @PBuiltinList # plam (\inp -> phasCS # (pfield @"value" # (pfield @"resolved" # inp)) # foldCS) # infoF.inputs 
  -- let rewardInp = pelemAt @PBuiltinList # pfromData rewardsIdx # infoF.inputs 
  --     hasFoldToken = pvalueOf # (pfield @"value" # (pfield @"resolved" # rewardInp)) # pfromData rewardCS # rewardFoldTN #== 1
  pif hasFoldToken (popaque $ pconstant ()) perror 

pLiquiditySetValidator ::
  Config ->
  ByteString ->
  ClosedTerm (PLBELockConfig :--> PValidator)
pLiquiditySetValidator cfg prefix = plam $ \discConfig dat redmn ctx' ->
  let redeemer = punsafeCoerce @_ @_ @PLNodeAction redmn
      oldDatum = punsafeCoerce @_ @_ @PLiquiditySetNode dat
   in 
    pmatch redeemer $ \case
      PLRewardFoldAct _ ->
        let stakeCerts = pfield @"wdrl" # (pfield @"txInfo" # ctx')
            stakeScript = pfromData $ pfield @"rewardCred" # discConfig 
         in pmatch (AssocMap.plookup # stakeScript # stakeCerts) $ \case 
              PJust _ -> (popaque $ pconstant ()) 
              PNothing -> perror 
      PLCommitFoldAct _ ->
        let stakeCerts = pfield @"wdrl" # (pfield @"txInfo" # ctx')
            stakeScript = pfromData $ pfield @"commitCred" # discConfig 
        in pmatch (AssocMap.plookup # stakeScript # stakeCerts) $ \case 
            PJust _ -> (popaque $ pconstant ()) 
            PNothing -> perror 
      otherRedeemers -> P.do 
        ctx <- pletFields @'["txInfo", "purpose"] ctx'
        info <- pletFields @'["inputs", "outputs", "mint", "validRange", "signatories", "referenceInputs"] ctx.txInfo
        txInputs <- plet info.inputs

        let ownInput = P.do
              PSpending ((pfield @"_0" #) -> ref) <- pmatch ctx.purpose
              ptryOwnInput # txInputs # ref
              
        ownInputF <- pletFields @'["value", "address"] ownInput

        let ownInputValue = pfromData ownInputF.value

        case otherRedeemers of 
          PLLinkedListAct _ -> P.do
            -- all those CSs has tokens that prefixed by Node prefix
            -- any of those can be actual Node CS
            let potentialNodeCSs = pfindCurrencySymbolsByTokenPrefix # ownInputValue # pconstant prefix
            -- TODO: Current launchpad token cannot start with FSN
            passert
              "Must mint/burn for any linked list interaction"
              (pcontainsCurrencySymbols # pfromData info.mint # potentialNodeCSs)
            (popaque $ pconstant ())
          PLModifyCommitment _ -> P.do
            PScriptCredential ((pfield @"_0" #) -> ownValHash) <- pmatch (pfield @"credential" # ownInputF.address)
            configF <- pletFields @'["discoveryDeadline"] discConfig
            let ownOutput = ptryOwnOutput # info.outputs # ownValHash
            ownOutputF <- pletFields @'["value", "datum"] ownOutput
            POutputDatum ((pfield @"outputDatum" #) -> ownOutputDatum) <- pmatch ownOutputF.datum
            let newDatum = pfromPDatum @PLiquiditySetNode # ownOutputDatum
            passert "Cannot modify datum when committing" (newDatum #== oldDatum)
            passert "Cannot modify non-ada value" (pnoAdaValue # ownInputF.value #== pnoAdaValue # ownOutputF.value)
            passert "Cannot reduce ada value" (plovelaceValueOf # ownInputF.value #< plovelaceValueOf # ownOutputF.value + 10_000_000)
            passert "No tokens minted" (pfromData info.mint #== mempty)
            passert "deadline passed" ((pafter # (pfromData configF.discoveryDeadline - 86_400) # info.validRange))
            passert "vrange not finite" (pisFinite # info.validRange)
            (popaque $ pconstant ()) 
          PLClaimAct _ -> P.do
            configF <- pletFields @'["rewardFoldCS", "discoveryDeadline"] discConfig
            vrange <- plet info.validRange
            let commonChecks = 
                  pand'List
                    [ ptraceIfFalse "pclaim missing sig" $ pelem # nodeKey # info.signatories 
                    , ptraceIfFalse "pclaim no minting" $ pfromData info.mint #== mempty
                    , ptraceIfFalse "vrange not bound" $ pisFinite # vrange
                    ] 
                nodeKey = pmatch (pfield @"key" # oldDatum) $ \case
                      PEmpty _ -> perror
                      PKey ((pfield @"_0" #) -> nkey) -> pdata $ pcon $ PPubKeyHash $ pfromData nkey 
            pif commonChecks 
            -- if a day has past since the deadline then user can claim without referencing the fold 
              (pif (pbefore # (pfromData configF.discoveryDeadline + 86_400_000) # vrange)
                (popaque $ pconstant ())
                -- otherwise the user must include the reward fold utxo as a reference input 
                -- and the reward fold must be complete (next is null)
                (P.do
                  let foldRefInput = pfield @"resolved" #$          
                        pmustFind @PBuiltinList 
                          # plam (\inp -> pvalueOf # (pfield @"value" # (pfield @"resolved" # inp)) # configF.rewardFoldCS # rewardFoldTN #== 1)
                          # info.referenceInputs
                  foldRefInputF <- pletFields @'["datum"] foldRefInput
                  POutputDatum ((pfield @"outputDatum" #) -> rFoldD) <- pmatch foldRefInputF.datum
                  let rFoldDatum = punsafeCoerce @_ @_ @PDistributionFoldDatum rFoldD
                  pmatch
                    (pfield @"next" # (pfield @"currNode" # rFoldDatum))
                    ( \case
                        PEmpty _ -> (popaque $ pconstant ())
                        PKey _ -> ptrace "pclaim RFold not complete" perror 
                    )           
                ) 
              )
              perror 
        
-- TODO PlaceHolder # This contribution holds only the minimum amount of Ada + the FoldingFee, it cannot be updated. It cannot be removed until the reward fold has completed.
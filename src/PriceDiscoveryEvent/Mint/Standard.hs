{-# OPTIONS_GHC -Wno-redundant-constraints #-}
{-# OPTIONS_GHC -Wno-unused-imports #-}

module PriceDiscoveryEvent.Mint.Standard (
  mkDiscoveryNodeMP,
  mkDiscoveryNodeMPW,
) where

import Plutarch.Api.V2 (
  PMintingPolicy,
  PScriptContext,
  PTxOutRef,
 )
import Plutarch.Extra.Interval (pafter, pbefore)

--  pRemoveAndDeinit,

import Plutarch.Internal (Config (..))
import Plutarch.Monadic qualified as P
import Plutarch.Unsafe (punsafeCoerce)
import PriceDiscoveryEvent.Mint.Common (
  PPriceDiscoveryCommon (mint, ownCS),
  makeCommon,
  pDeinit,
  pInit,
  pInsert,
  pRemove,
  pClaim
 )
import PriceDiscoveryEvent.Mint.Helpers (
  hasUtxoWithRef,
 )

import Plutarch.Prelude
import PriceDiscoveryEvent.Utils (pand'List, passert, pcond)
import Types.DiscoverySet (PDiscoveryConfig (..), PDiscoveryNodeAction (..))

--------------------------------
-- FinSet Node Minting Policy:
--------------------------------

mkDiscoveryNodeMP ::
  Config ->
  ClosedTerm
    ( PDiscoveryConfig
        :--> PDiscoveryNodeAction
        :--> PScriptContext
        :--> PUnit
    )
mkDiscoveryNodeMP cfg = plam $ \discConfig redm ctx -> P.do
  configF <- pletFields @'["initUTxO"] discConfig

  (common, inputs, outs, sigs, vrange) <-
    runTermCont $
      makeCommon cfg ctx

  pmatch redm $ \case
    PInit _ -> P.do
      passert "Init must consume TxOutRef" $
        hasUtxoWithRef # configF.initUTxO # inputs
      pInit cfg common
    PDeinit _ ->
      -- TODO deinit must check that reward fold has been completed
      pDeinit cfg common
    PInsert action -> P.do
      act <- pletFields @'["keyToInsert", "coveringNode"] action
      let insertChecks =
            pand'List
              [ pafter # (pfield @"discoveryDeadline" # discConfig) # vrange
              , pelem # act.keyToInsert # sigs
              ]
      pif insertChecks (pInsert cfg common # act.keyToInsert # act.coveringNode) perror
    PRemove action -> P.do
      configF <- pletFields @'["discoveryDeadline"] discConfig
      act <- pletFields @'["keyToRemove", "coveringNode"] action
      discDeadline <- plet configF.discoveryDeadline
      pcond 
        [ ((pbefore # discDeadline # vrange), (pClaim cfg common outs sigs # act.keyToRemove))
        , ((pafter # discDeadline # vrange), (pRemove cfg common vrange discConfig outs sigs # act.keyToRemove # act.coveringNode))
        ]
        perror 

mkDiscoveryNodeMPW ::
  Config ->
  ClosedTerm
    ( PDiscoveryConfig
        :--> PMintingPolicy
    )
mkDiscoveryNodeMPW cfg = phoistAcyclic $ plam $ \discConfig redm ctx ->
  let red = punsafeCoerce @_ @_ @PDiscoveryNodeAction redm
   in popaque $ mkDiscoveryNodeMP cfg # discConfig # red # ctx

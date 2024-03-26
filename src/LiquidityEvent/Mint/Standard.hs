{-# OPTIONS_GHC -Wno-redundant-constraints #-}
{-# OPTIONS_GHC -Wno-unused-imports #-}

module LiquidityEvent.Mint.Standard (
  mkLiquidityNodeMP,
  mkLiquidityNodeMPW,
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
import LiquidityEvent.Mint.Common (
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
import PriceDiscoveryEvent.Utils (pand'List, passert, pcond, pisFinite)
import Types.LiquiditySet (PLiquidityConfig (..), PLiquidityNodeAction (..))

--------------------------------
-- FinSet Node Minting Policy:
--------------------------------

mkLiquidityNodeMP ::
  Config ->
  ClosedTerm
    ( PLiquidityConfig
        :--> PLiquidityNodeAction
        :--> PScriptContext
        :--> PUnit
    )
mkLiquidityNodeMP cfg = plam $ \discConfig redm ctx -> P.do
  configF <- pletFields @'["initUTxO"] discConfig

  (common, inputs, outs, sigs, vrange) <-
    runTermCont $
      makeCommon cfg ctx

  pmatch redm $ \case
    PLInit _ -> P.do
      passert "Init must consume TxOutRef" $
        hasUtxoWithRef # configF.initUTxO # inputs
      pInit cfg common
    PLDeinit _ ->
      -- TODO deinit must check that reward fold has been completed
      pDeinit cfg common
    PLInsert action -> P.do
      act <- pletFields @'["keyToInsert", "coveringNode"] action
      let insertChecks =
            pand'List
              [ pisFinite # vrange
              , pafter # (pfield @"discoveryDeadline" # discConfig) # vrange
              , pelem # act.keyToInsert # sigs
              ]
      pif insertChecks (pInsert cfg common # act.keyToInsert # act.coveringNode) perror
    PLRemove action -> P.do
      configF <- pletFields @'["discoveryDeadline"] discConfig
      act <- pletFields @'["keyToRemove", "coveringNode"] action
      discDeadline <- plet (pfromData configF.discoveryDeadline)
      passert "vrange not finite" (pisFinite # vrange)
      pcond 
        [ ((pbefore # (discDeadline + 86_400_000) # vrange), (pClaim cfg common outs sigs # act.keyToRemove))
        , ((pafter # discDeadline # vrange), (pRemove cfg common vrange discConfig outs sigs # act.keyToRemove # act.coveringNode))
        ]
        perror 

mkLiquidityNodeMPW ::
  Config ->
  ClosedTerm
    ( PLiquidityConfig
        :--> PMintingPolicy
    )
mkLiquidityNodeMPW cfg = phoistAcyclic $ plam $ \discConfig redm ctx ->
  let red = punsafeCoerce @_ @_ @PLiquidityNodeAction redm
   in popaque $ mkLiquidityNodeMP cfg # discConfig # red # ctx

module PriceDiscoveryEvent.Mint.Helpers (
  coversSeparators,
  coversKey,
  hasUtxoWithRef,
  pseparatorsMintValue,
  correctNodeTokensMinted,
  correctNodeTokenMinted,
) where

import Plutarch.Api.V1.AssocMap qualified as AssocMap
import Plutarch.Api.V1.Value qualified as V
import Plutarch.Api.V2 (
  AmountGuarantees (NonZero),
  KeyGuarantees (Sorted),
  PCurrencySymbol,
  PPubKeyHash,
  PTokenName,
  PTxInInfo,
  PTxOut,
  PTxOutRef,
  PValue,
 )
import Plutarch.Extra.Traversable (pfoldMap)
import Plutarch.Monadic qualified as P

import Plutarch.Prelude
import PriceDiscoveryEvent.Utils (phasCS)
import Types.Constants (pnodeKeyTN)
import Types.DiscoverySet (PDiscoverySetNode, PNodeKey (PEmpty, PKey))

-- | Checks that key is 'covered' by the Node
coversKey :: ClosedTerm (PAsData PDiscoverySetNode :--> PByteString :--> PBool)
coversKey = phoistAcyclic $
  plam $ \datum keyToCover -> P.do
    nodeDatum <- pletFields @'["key", "next"] datum
    let moreThanKey = pmatch (nodeDatum.key) $ \case
          PEmpty _ -> pcon PTrue
          PKey (pfromData . (pfield @"_0" #) -> key) -> key #< keyToCover
        lessThanNext = pmatch (nodeDatum.next) $ \case
          PEmpty _ -> pcon PTrue
          PKey (pfromData . (pfield @"_0" #) -> next) -> keyToCover #< next
    moreThanKey #&& lessThanNext

-- | Checks that all the separators are covered by the node
coversSeparators :: ClosedTerm (PAsData PDiscoverySetNode :--> PBuiltinList PByteString :--> PBool)
coversSeparators = phoistAcyclic $
  plam $ \datum separators -> P.do
    nodeDatum <- pletFields @'["key", "next"] datum
    let moreThanKey = pmatch (nodeDatum.key) $ \case
          PEmpty _ -> pcon PTrue
          PKey (pfromData . (pfield @"_0" #) -> key) -> pall # plam (key #<) # separators
        lessThanNext = pmatch (nodeDatum.next) $ \case
          PEmpty _ -> pcon PTrue
          PKey (pfromData . (pfield @"_0" #) -> next) -> pall # plam (#< next) # separators
    moreThanKey #&& lessThanNext

{- | @hasUtxoWithRef # oref # inputs@
  ensures that in @inputs@ there is an input having @TxOutRef@ @oref@ .
-}
hasUtxoWithRef ::
  ClosedTerm
    ( PTxOutRef
        :--> PBuiltinList PTxInInfo
        :--> PBool
    )
hasUtxoWithRef = phoistAcyclic $
  plam $ \oref inInputs ->
    pany # plam (\input -> oref #== (pfield @"outRef" # input)) # inInputs

-- | Makes a Value from a list of separators keys
pseparatorsMintValue ::
  ClosedTerm
    ( PInteger
        :--> PCurrencySymbol
        :--> PBuiltinList PByteString
        :--> PValue 'Sorted 'NonZero
    )
pseparatorsMintValue = phoistAcyclic $
  plam $ \amount nodeCS separators ->
    let mkSeparatorToken = plam $ \key -> V.psingleton # nodeCS # (pnodeKeyTN # key) # amount
     in pfoldMap # mkSeparatorToken # separators

{- | Ensures that the minted amount of the FinSet CS is exactly the specified
     list of tokenNames and amount
-}
correctNodeTokensMinted ::
  ClosedTerm
    ( PCurrencySymbol
        :--> PList PTokenName
        :--> PInteger
        :--> PValue 'Sorted 'NonZero
        :--> PBool
    )
correctNodeTokensMinted = phoistAcyclic $
  plam $ \nodeCS tokenNames amount mint -> P.do
    PJust nodeMint <- pmatch $ AssocMap.plookup # nodeCS # pto mint
    let mkToken = plam $ \tn ->
          AssocMap.pinsert # tn # amount
        tokenMap = pfoldr # mkToken # AssocMap.pempty # tokenNames
    tokenMap #== nodeMint

{- | Ensures that the minted amount of the FinSet CS is exactly the specified
     tokenName and amount
-}
correctNodeTokenMinted ::
  ClosedTerm
    ( PCurrencySymbol
        :--> PTokenName
        :--> PInteger
        :--> PValue 'Sorted 'NonZero
        :--> PBool
    )
correctNodeTokenMinted = phoistAcyclic $
  plam $ \nodeCS tokenName amount mint -> P.do
    PJust nodeMint <- pmatch $ AssocMap.plookup # nodeCS # pto mint
    let tokenMap = AssocMap.psingleton # tokenName # amount
    tokenMap #== nodeMint

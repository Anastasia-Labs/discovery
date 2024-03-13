{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeFamilyDependencies #-}
{-# OPTIONS_GHC -Wno-orphans #-}

module Types.LiquiditySet where

import Plutarch.Api.V2 (
  PAddress,
  PScriptHash (..),
  PPOSIXTime,
  PPubKeyHash (PPubKeyHash),
  PTxOutRef,
  PCurrencySymbol,
  PStakingCredential(..),
  PTokenName(..)
 )
import Plutarch.DataRepr (
  DerivePConstantViaData (DerivePConstantViaData),
  PDataFields,
 )
import Plutarch.Lift (PConstantDecl, PUnsafeLiftDecl (PLifted))
import Plutarch.Monadic qualified as P
import GHC.Generics (Generic)
import Plutarch.Prelude
import PlutusLedgerApi.V2 (BuiltinByteString, PubKeyHash)
import PlutusTx qualified
import Types.Classes 
import Types.DiscoverySet (PNodeKey(..), PNodeKeyState(..))

data PProxyTokenHolderDatum (s :: S)
  = PProxyTokenHolderDatum
      ( Term
          s
          ( PDataRecord
              '[ "totalCommitted" ':= PInteger 
               , "returnAddress" ':= PAddress
               ]
          )
      )
  deriving stock (Generic)
  deriving anyclass (PlutusType, PIsData, PDataFields)

instance DerivePlutusType PProxyTokenHolderDatum where
  type DPTStrat _ = PlutusTypeData

deriving anyclass instance
  PTryFrom PData PProxyTokenHolderDatum
  
data NodeKey = Key BuiltinByteString | Empty
  deriving stock (Show, Eq, Ord, Generic)
PlutusTx.unstableMakeIsData ''NodeKey

data LNodeAction
  = LLinkedListAct
  | LModifyCommitment
  | LCommitFoldAct
  | LRewardFoldAct
  deriving stock (Generic, Show)

PlutusTx.unstableMakeIsData ''LNodeAction

data PLNodeAction (s :: S)
  = PLLinkedListAct (Term s (PDataRecord '[]))
  | PLModifyCommitment (Term s (PDataRecord '[]))
  | PLCommitFoldAct (Term s (PDataRecord '["commitIdx" ':= PInteger]))
  | PLRewardFoldAct (Term s (PDataRecord '["rewardsIdx" ':= PInteger]))
  deriving stock (Generic)
  deriving anyclass (PlutusType, PIsData, PShow)

instance DerivePlutusType PLNodeAction where
  type DPTStrat _ = PlutusTypeData

instance PUnsafeLiftDecl PLNodeAction where
  type PLifted PLNodeAction = LNodeAction

deriving via
  (DerivePConstantViaData LNodeAction PLNodeAction)
  instance
    (PConstantDecl LNodeAction)

instance PTryFrom PData (PAsData PLNodeAction)
instance PTryFrom PData PLNodeAction

data PLBELockConfig (s :: S)
  = PLBELockConfig
      ( Term
          s
          ( PDataRecord
              '[ "discoveryDeadline" ':= PPOSIXTime
               , "penaltyAddress" ':= PAddress
               , "commitCred" ':= PStakingCredential
               , "rewardCred" ':= PStakingCredential
               ]
          )
      )
  deriving stock (Generic)
  deriving anyclass (PlutusType, PIsData, PDataFields, PEq)

instance DerivePlutusType PLBELockConfig where type DPTStrat _ = PlutusTypeData

data PLiquidityConfig (s :: S)
  = PLiquidityConfig
      ( Term
          s
          ( PDataRecord
              '[ "initUTxO" ':= PTxOutRef
               , "discoveryDeadline" ':= PPOSIXTime
               , "penaltyAddress" ':= PAddress
               ]
          )
      )
  deriving stock (Generic)
  deriving anyclass (PlutusType, PIsData, PDataFields, PEq)

instance DerivePlutusType PLiquidityConfig where type DPTStrat _ = PlutusTypeData

data LiquiditySetNode = MkLiquiditySetNode
  { key :: NodeKey
  , next :: NodeKey
  , committed :: Integer 
  }
  deriving stock (Show, Eq, Generic)
PlutusTx.unstableMakeIsData ''LiquiditySetNode

data PLiquiditySetNodeState (s :: S) = PLiquiditySetNodeState
  { key :: Term s PNodeKeyState
  , next :: Term s PNodeKeyState
  , committed :: Term s PInteger
  }
  deriving stock (Generic)
  deriving anyclass (PlutusType, PEq)

instance DerivePlutusType PLiquiditySetNodeState where type DPTStrat _ = PlutusTypeScott

data PLiquiditySetNode (s :: S)
  = PLiquiditySetNode
      ( Term
          s
          ( PDataRecord
              '[ "key" ':= PNodeKey
               , "next" ':= PNodeKey
               , "commitment" ':= PInteger 
               ]
          )
      )
  deriving stock (Generic)
  deriving anyclass (PlutusType, PIsData, PDataFields, PEq)

instance DerivePlutusType PLiquiditySetNode where type DPTStrat _ = PlutusTypeData

deriving anyclass instance
  PTryFrom PData PLiquiditySetNode

deriving anyclass instance
  PTryFrom PData (PAsData PLiquiditySetNode)

instance PUnsafeLiftDecl PLiquiditySetNode where
  type PLifted PLiquiditySetNode = LiquiditySetNode

deriving via
  (DerivePConstantViaData LiquiditySetNode PLiquiditySetNode)
  instance
    PConstantDecl LiquiditySetNode


instance ScottConvertible PInteger where
  type ScottOf PInteger = PInteger
  toScott i = i
  fromScott i = i

instance ScottConvertible PLiquiditySetNode where
  type ScottOf PLiquiditySetNode = PLiquiditySetNodeState
  toScott discSetNode' = pmatch discSetNode' $ \(PLiquiditySetNode discSetNode) -> pletFields @'["key", "next", "commitment"] discSetNode $ \discSetNodeF -> 
    pcon (PLiquiditySetNodeState {key = toScott discSetNodeF.key, next = toScott discSetNodeF.next, committed = discSetNodeF.commitment})
  fromScott discSetNode = pmatch discSetNode $
      \( PLiquiditySetNodeState
          { key
          , next
          , committed 
          }
        ) -> 
          (pcon (PLiquiditySetNode 
            (pdcons @"key" # pdata (fromScott key) 
              #$ (pdcons @"next" # pdata (fromScott next))
              #$ (pdcons @"commitment" # pdata committed)
              #$ pdnil)))

data PSeparatorConfig (s :: S)
  = PSeparatorConfig
      ( Term
          s
          ( PDataRecord
              '[ "signer" ':= PPubKeyHash
               , "cutOff" ':= PPOSIXTime
               ]
          )
      )
  deriving stock (Generic)
  deriving anyclass (PlutusType, PIsData, PDataFields, PEq)

instance DerivePlutusType PSeparatorConfig where type DPTStrat _ = PlutusTypeData

mkNode :: Term s (PNodeKey :--> PNodeKey :--> PLiquiditySetNode)
mkNode = phoistAcyclic $
  plam $ \key next ->
    pcon $
      PLiquiditySetNode $
        pdcons @"key" # pdata key
          #$ pdcons @"next" # pdata next
          #$ pdcons @"commitment" # pconstantData 0 
          #$ pdnil

mkNodeWithCommit :: Term s (PNodeKey :--> PNodeKey :--> PInteger :--> PLiquiditySetNode)
mkNodeWithCommit = phoistAcyclic $
  plam $ \key next commitment ->
    pcon $
      PLiquiditySetNode $
        pdcons @"key" # pdata key
          #$ pdcons @"next" # pdata next
          #$ pdcons @"commitment" # pdata commitment
          #$ pdnil

data LiquidityNodeAction
  = Init
  | Deinit
  | -- | first arg is the key to insert, second arg is the covering node
    Insert PubKeyHash LiquiditySetNode
  | -- | first arg is the key to remove, second arg is the covering node
    Remove PubKeyHash LiquiditySetNode
  deriving stock (Show, Eq, Generic)
PlutusTx.unstableMakeIsData ''LiquidityNodeAction

data PLiquidityNodeAction (s :: S)
  = PLInit (Term s (PDataRecord '[]))
  | PLDeinit (Term s (PDataRecord '[]))
  | PLInsert (Term s (PDataRecord '["keyToInsert" ':= PPubKeyHash, "coveringNode" ':= PLiquiditySetNode]))
  | PLRemove (Term s (PDataRecord '["keyToRemove" ':= PPubKeyHash, "coveringNode" ':= PLiquiditySetNode]))
  deriving stock (Generic)
  deriving anyclass (PlutusType, PIsData, PEq)

instance DerivePlutusType PLiquidityNodeAction where type DPTStrat _ = PlutusTypeData

deriving anyclass instance
  PTryFrom PData (PAsData PLiquidityNodeAction)

instance PUnsafeLiftDecl PLiquidityNodeAction where
  type PLifted PLiquidityNodeAction = LiquidityNodeAction
deriving via
  (DerivePConstantViaData LiquidityNodeAction PLiquidityNodeAction)
  instance
    PConstantDecl LiquidityNodeAction

data PLiquidityHolderDatum (s :: S)
  = PLiquidityHolderDatum
      ( Term
          s
          ( PDataRecord
              '[ "lpTokenName" ':= PTokenName
               , "totalCommitted" ':= PInteger 
               , "totalLPTokens" ':= PInteger
               ]
          )
      )
  deriving stock (Generic)
  deriving anyclass (PEq, PlutusType, PIsData, PDataFields)

instance DerivePlutusType PLiquidityHolderDatum where
  type DPTStrat _ = PlutusTypeData

deriving anyclass instance
  PTryFrom PData PLiquidityHolderDatum
  
-----------------------------------------------
-- Helpers:

mkBSNode :: ClosedTerm (PByteString :--> PByteString :--> PAsData PLiquiditySetNode)
mkBSNode = phoistAcyclic $
  plam $ \key' next' ->
    let key = pcon $ PKey $ pdcons @"_0" # pdata key' #$ pdnil
        next = pcon $ PKey $ pdcons @"_0" # pdata next' #$ pdnil
     in pdata $ mkNode # key # next 

-- | Checks that the node is the empty head node and the datum is empty
isEmptySet :: ClosedTerm (PAsData PLiquiditySetNode :--> PBool)
isEmptySet = phoistAcyclic $
  plam $ \head -> P.do
    keys <- pletFields @'["key", "next"] head
    isNothing # pfromData keys.key #&& isNothing # pfromData keys.next

-- | Checks that a PubKeyHash does belong to the first Node in the set.
isFirstNode :: ClosedTerm (PByteString :--> PLiquiditySetNode :--> PBool)
isFirstNode = phoistAcyclic $
  plam $ \key node -> P.do
    keys <- pletFields @'["key", "next"] node
    pmatch (keys.next) $ \case
      PKey n ->
        key #== pfromData (pfield @"_0" # n) #&& isNothing # pfromData keys.key
      _ -> pcon PFalse

-- | Checks that a PubkeyHash does belong to the last Node in a set.
isLastNode :: ClosedTerm (PByteString :--> PLiquiditySetNode :--> PBool)
isLastNode = phoistAcyclic $
  plam $ \key node -> P.do
    keys <- pletFields @'["key", "next"] node
    pmatch (keys.key) $ \case
      PKey ((pfield @"_0" #) -> n) ->
        key #== pfromData n #&& isNothing # pfromData keys.next
      _ -> pcon PFalse

-- | Checks that node key is absent.
isNothing :: Term s (PNodeKey :--> PBool)
isNothing = phoistAcyclic $
  plam $ \md -> pmatch md $ \case
    PKey _ -> pcon PFalse
    PEmpty _ -> pcon PTrue

{- | @
  node `asPredecessorOf` next
  @ makes @node@ to be a predecessor of a node with *key* @next@
  Seen as if the node between them was removed.
  @node.key@ remains the same, @node.next@ changes to @next@.
-}
asPredecessorOf :: ClosedTerm (PAsData PLiquiditySetNode :--> PByteString :--> PLiquiditySetNode)
asPredecessorOf = phoistAcyclic $
  plam $ \node next ->
    let nodeKey = pfromData $ pfield @"key" # node
        nextPK = pcon $ PKey $ pdcons @"_0" # pdata next #$ pdnil
     in mkNode # nodeKey # nextPK

{- | @
    key `asSuccessorOf` node
  @ makes @node@ to be a successor of a node with *next* @key@
  Seen as if the node between them was removed.
  @node.next@ remains the same, @node.key@ changes to @key@.
-}
asSuccessorOf :: ClosedTerm (PByteString :--> PAsData PLiquiditySetNode :--> PLiquiditySetNode)
asSuccessorOf = phoistAcyclic $
  plam $ \key node ->
    let nodeNext = pfromData $ pfield @"next" # node
        keyPK = pcon $ PKey $ pdcons @"_0" # pdata key #$ pdnil
     in mkNode # keyPK # nodeNext

-- | Extracts the next node key
getNextPK :: ClosedTerm (PAsData PLiquiditySetNode :--> PMaybe PPubKeyHash)
getNextPK = phoistAcyclic $
  plam $ \node ->
    let nextNodeKey = pfromData $ pfield @"next" # node
     in pmatch nextNodeKey $ \case
          PEmpty _ -> pcon PNothing
          PKey ((pfield @"_0" #) -> n) -> pcon $ PJust $ pcon $ PPubKeyHash $ pfromData n

-- | Extracts the node key
getCurrentPK :: ClosedTerm (PAsData PLiquiditySetNode :--> PMaybe PPubKeyHash)
getCurrentPK = phoistAcyclic $
  plam $ \node ->
    let nodeKey = pfromData $ pfield @"key" # node
     in pmatch nodeKey $ \case
          PEmpty _ -> pcon PNothing
          PKey ((pfield @"_0" #) -> n) -> pcon $ PJust $ pcon $ PPubKeyHash $ pfromData n

{- | Checks whether @SetNode@ key is less than next node key.
  Any valid sequence of nodes MUST follow this property.
-}
validNode :: ClosedTerm (PAsData PLiquiditySetNode :--> PBool)
validNode = phoistAcyclic $
  plam $ \node -> P.do
    nodeDatum <- pletFields @'["key", "next"] node
    pmatch (nodeDatum.key) $ \case
      PEmpty _ -> pcon PTrue
      PKey ((pfield @"_0" #) -> key) -> pmatch (nodeDatum.next) $ \case
        PEmpty _ -> pcon PTrue
        PKey ((pfield @"_0" #) -> next) ->
          pfromData key #< pfromData next -- nodes ordered incrementally

coversLiquidityKey :: ClosedTerm (PAsData PLiquiditySetNode :--> PByteString :--> PBool)
coversLiquidityKey = phoistAcyclic $
  plam $ \datum keyToCover -> P.do
    nodeDatum <- pletFields @'["key", "next", "commitment"] datum
    let moreThanKey = pmatch (nodeDatum.key) $ \case
          PEmpty _ -> pcon PTrue
          PKey (pfromData . (pfield @"_0" #) -> key) -> key #< keyToCover
        lessThanNext = pmatch (nodeDatum.next) $ \case
          PEmpty _ -> pcon PTrue
          PKey (pfromData . (pfield @"_0" #) -> next) -> keyToCover #< next
    moreThanKey #&& lessThanNext #&& (pfromData nodeDatum.commitment #== 0)
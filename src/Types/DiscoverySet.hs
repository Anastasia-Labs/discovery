{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeFamilyDependencies #-}
{-# LANGUAGE UndecidableInstances #-}
{-# OPTIONS_GHC -Wno-orphans #-}

module Types.DiscoverySet (
  PDiscoveryNodeAction (..),
  PNodeValidatorAction (..),
  PDiscoveryConfig (..),
  PDiscoveryLaunchConfig (..),
  PSepNodeAction (..),
  PSeparatorConfig (..),
  PDiscoverySetNode (..),
  PNodeKey (..),
  PNodeKeyState (..),
  isEmptySet,
  asPredecessorOf,
  asSuccessorOf,
  getNextPK,
  getCurrentPK,
  isFirstNode,
  isLastNode,
  mkNode,
  isNothing,
  validNode,
  mkBSNode,
) where

import GHC.Generics (Generic)
import Plutarch.Api.V2 (
  PAddress,
  PCurrencySymbol,
  PPOSIXTime,
  PPubKeyHash (PPubKeyHash),
  PScriptHash (..),
  PStakingCredential(..),
  PTxOutRef,
 )
import Plutarch.DataRepr (
  DerivePConstantViaData (DerivePConstantViaData),
  PDataFields,
 )
import Plutarch.Lift (PConstantDecl, PUnsafeLiftDecl (PLifted))
import Plutarch.Monadic qualified as P
import Plutarch.Prelude
import PlutusLedgerApi.V2 (BuiltinByteString, PubKeyHash)
import PlutusTx qualified
import Types.Classes

data NodeValidatorAction
  = LinkedListAct
  | ModifyCommitment
  | RewardFoldAct
  deriving stock (Generic, Show)

PlutusTx.unstableMakeIsData ''NodeValidatorAction

data PNodeValidatorAction (s :: S)
  = PLinkedListAct (Term s (PDataRecord '[]))
  | PModifyCommitment (Term s (PDataRecord '[]))
  | PRewardFoldAct (Term s (PDataRecord '[]))
  deriving stock (Generic)
  deriving anyclass (PlutusType, PIsData, PShow)

instance DerivePlutusType PNodeValidatorAction where
  type DPTStrat _ = PlutusTypeData

instance PUnsafeLiftDecl PNodeValidatorAction where
  type PLifted PNodeValidatorAction = NodeValidatorAction

deriving via
  (DerivePConstantViaData NodeValidatorAction PNodeValidatorAction)
  instance
    (PConstantDecl NodeValidatorAction)

instance PTryFrom PData (PAsData PNodeValidatorAction)
instance PTryFrom PData PNodeValidatorAction

data PDiscoveryLaunchConfig (s :: S)
  = PDiscoveryLaunchConfig
      ( Term
          s
          ( PDataRecord
              '[ "discoveryDeadline" ':= PPOSIXTime
               , "penaltyAddress" ':= PAddress
               , "globalCred" ':= PStakingCredential
               ]
          )
      )
  deriving stock (Generic)
  deriving anyclass (PlutusType, PIsData, PDataFields, PEq)

instance DerivePlutusType PDiscoveryLaunchConfig where type DPTStrat _ = PlutusTypeData

data PDiscoveryConfig (s :: S)
  = PDiscoveryConfig
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

instance DerivePlutusType PDiscoveryConfig where type DPTStrat _ = PlutusTypeData

data DiscoveryNodeKey = Key BuiltinByteString | Empty
  deriving stock (Show, Eq, Ord, Generic)
PlutusTx.unstableMakeIsData ''DiscoveryNodeKey

data DiscoverySetNode = MkSetNode
  { key :: DiscoveryNodeKey
  , next :: DiscoveryNodeKey
  }
  deriving stock (Show, Eq, Generic)
PlutusTx.unstableMakeIsData ''DiscoverySetNode

data SepNodeAction
  = SepInit
  | SepDeinit
  | SepInsert PubKeyHash DiscoverySetNode
  | SepRemove PubKeyHash DiscoverySetNode
  | InsertSeps [BuiltinByteString] DiscoverySetNode
  | -- | first arg is the key to insert, second arg is the covering node
    RemoveSeps [BuiltinByteString] DiscoverySetNode
  -- first arg is the key to remove, second arg is the covering node
  deriving stock (Show, Eq, Generic)
PlutusTx.unstableMakeIsData ''SepNodeAction

data DiscoveryNodeAction
  = Init
  | Deinit
  | -- | first arg is the key to insert, second arg is the covering node
    Insert PubKeyHash DiscoverySetNode
  | -- | first arg is the key to remove, second arg is the covering node
    Remove PubKeyHash DiscoverySetNode
  deriving stock (Show, Eq, Generic)
PlutusTx.unstableMakeIsData ''DiscoveryNodeAction

data PNodeKey (s :: S)
  = PKey (Term s (PDataRecord '["_0" ':= PByteString]))
  | PEmpty (Term s (PDataRecord '[]))
  deriving stock (Generic)
  deriving anyclass (PlutusType, PIsData, PEq)

deriving via
  (DerivePConstantViaData DiscoveryNodeKey PNodeKey)
  instance
    PConstantDecl DiscoveryNodeKey

instance PUnsafeLiftDecl PNodeKey where
  type PLifted PNodeKey = DiscoveryNodeKey

deriving anyclass instance
  PTryFrom PData PNodeKey

instance DerivePlutusType PNodeKey where type DPTStrat _ = PlutusTypeData

data PNodeKeyState (s :: S)
  = PKeyScott (Term s PByteString)
  | PEmptyScott
  deriving stock (Generic)
  deriving anyclass (PlutusType, PEq)

instance DerivePlutusType PNodeKeyState where type DPTStrat _ = PlutusTypeScott

instance ScottConvertible PNodeKey where
  type ScottOf PNodeKey = PNodeKeyState
  toScott nodeKey = pmatch nodeKey $ \case
    PKey kname -> pcon (PKeyScott (pfield @"_0" # kname))
    PEmpty _ -> pcon PEmptyScott
  fromScott nodeKeyScott = pmatch nodeKeyScott $ \case
    PKeyScott bs -> pcon (PKey (pdcons # pdata bs # pdnil))
    PEmptyScott -> pcon (PEmpty pdnil)

data PDiscoverySetNodeState (s :: S) = PDiscoverySetNodeState
  { key :: Term s PNodeKeyState
  , next :: Term s PNodeKeyState
  }
  deriving stock (Generic)
  deriving anyclass (PlutusType, PEq)

instance DerivePlutusType PDiscoverySetNodeState where type DPTStrat _ = PlutusTypeScott

data PDiscoverySetNode (s :: S)
  = PDiscoverySetNode
      ( Term
          s
          ( PDataRecord
              '[ "key" ':= PNodeKey
               , "next" ':= PNodeKey
               -- , "commitment" ':= PInteger
               ]
          )
      )
  deriving stock (Generic)
  deriving anyclass (PlutusType, PIsData, PDataFields, PEq)

instance DerivePlutusType PDiscoverySetNode where type DPTStrat _ = PlutusTypeData

deriving anyclass instance
  PTryFrom PData PDiscoverySetNode

deriving anyclass instance
  PTryFrom PData (PAsData PDiscoverySetNode)

instance PUnsafeLiftDecl PDiscoverySetNode where
  type PLifted PDiscoverySetNode = DiscoverySetNode

deriving via
  (DerivePConstantViaData DiscoverySetNode PDiscoverySetNode)
  instance
    PConstantDecl DiscoverySetNode

instance ScottConvertible PDiscoverySetNode where
  type ScottOf PDiscoverySetNode = PDiscoverySetNodeState
  toScott discSetNode' = pmatch discSetNode' $ \(PDiscoverySetNode discSetNode) -> pletFields @'["key", "next"] discSetNode $ \discSetNodeF ->
    pcon (PDiscoverySetNodeState {key = toScott discSetNodeF.key, next = toScott discSetNodeF.next})
  fromScott discSetNode =
    pmatch discSetNode $
      \( PDiscoverySetNodeState
          { key
          , next
          }
        ) ->
          ( pcon
              ( PDiscoverySetNode
                  ( pdcons @"key"
                      # pdata (fromScott key)
                      #$ (pdcons @"next" # pdata (fromScott next))
                      -- #$ (pdcons @"commitment" # pdata 0)
                      #$ pdnil
                  )
              )
          )

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

mkNode :: Term s (PNodeKey :--> PNodeKey :--> PDiscoverySetNode)
mkNode = phoistAcyclic $
  plam $ \key next ->
    pcon $
      PDiscoverySetNode $
        pdcons @"key"
          # pdata key
          #$ pdcons @"next"
          # pdata next
          #$ pdnil

data PDiscoveryNodeAction (s :: S)
  = PInit (Term s (PDataRecord '[]))
  | PDeinit (Term s (PDataRecord '[]))
  | PInsert (Term s (PDataRecord '["keyToInsert" ':= PPubKeyHash, "coveringNode" ':= PDiscoverySetNode]))
  | PRemove (Term s (PDataRecord '["keyToRemove" ':= PPubKeyHash, "coveringNode" ':= PDiscoverySetNode]))
  deriving stock (Generic)
  deriving anyclass (PlutusType, PIsData, PEq)

instance DerivePlutusType PDiscoveryNodeAction where type DPTStrat _ = PlutusTypeData

deriving anyclass instance
  PTryFrom PData (PAsData PDiscoveryNodeAction)

instance PUnsafeLiftDecl PDiscoveryNodeAction where
  type PLifted PDiscoveryNodeAction = DiscoveryNodeAction
deriving via
  (DerivePConstantViaData DiscoveryNodeAction PDiscoveryNodeAction)
  instance
    PConstantDecl DiscoveryNodeAction

data PSepNodeAction (s :: S)
  = PSepInit (Term s (PDataRecord '[]))
  | PSepDeinit (Term s (PDataRecord '[]))
  | PSepInsert (Term s (PDataRecord '["keyToInsert" ':= PPubKeyHash, "coveringNode" ':= PDiscoverySetNode]))
  | PSepRemove (Term s (PDataRecord '["keyToRemove" ':= PPubKeyHash, "coveringNode" ':= PDiscoverySetNode]))
  | -- | separators must be sorted or validation will fail
    PInsertSeps (Term s (PDataRecord '["separators" ':= PBuiltinList (PAsData PByteString), "coveringNode" ':= PDiscoverySetNode]))
  | PRemoveSeps (Term s (PDataRecord '["separators" ':= PBuiltinList (PAsData PByteString), "coveringNode" ':= PDiscoverySetNode]))
  deriving stock (Generic)
  deriving anyclass (PlutusType, PIsData, PEq)

instance DerivePlutusType PSepNodeAction where type DPTStrat _ = PlutusTypeData

deriving anyclass instance
  PTryFrom PData (PAsData PSepNodeAction)

instance PUnsafeLiftDecl PSepNodeAction where
  type PLifted PSepNodeAction = SepNodeAction
deriving via
  (DerivePConstantViaData SepNodeAction PSepNodeAction)
  instance
    PConstantDecl SepNodeAction

-----------------------------------------------
-- Helpers:

mkBSNode :: ClosedTerm (PByteString :--> PByteString :--> PAsData PDiscoverySetNode)
mkBSNode = phoistAcyclic $
  plam $ \key' next' ->
    let key = pcon $ PKey $ pdcons @"_0" # pdata key' #$ pdnil
        next = pcon $ PKey $ pdcons @"_0" # pdata next' #$ pdnil
     in pdata $ mkNode # key # next

-- | Checks that the node is the empty head node and the datum is empty
isEmptySet :: ClosedTerm (PAsData PDiscoverySetNode :--> PBool)
isEmptySet = phoistAcyclic $
  plam $ \head -> P.do
    keys <- pletFields @'["key", "next"] head
    isNothing # pfromData keys.key #&& isNothing # pfromData keys.next

-- | Checks that a PubKeyHash does belong to the first Node in the set.
isFirstNode :: ClosedTerm (PByteString :--> PDiscoverySetNode :--> PBool)
isFirstNode = phoistAcyclic $
  plam $ \key node -> P.do
    keys <- pletFields @'["key", "next"] node
    pmatch (keys.next) $ \case
      PKey n ->
        key #== pfromData (pfield @"_0" # n) #&& isNothing # pfromData keys.key
      _ -> pcon PFalse

-- | Checks that a PubkeyHash does belong to the last Node in a set.
isLastNode :: ClosedTerm (PByteString :--> PDiscoverySetNode :--> PBool)
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
asPredecessorOf :: ClosedTerm (PAsData PDiscoverySetNode :--> PByteString :--> PDiscoverySetNode)
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
asSuccessorOf :: ClosedTerm (PByteString :--> PAsData PDiscoverySetNode :--> PDiscoverySetNode)
asSuccessorOf = phoistAcyclic $
  plam $ \key node ->
    let nodeNext = pfromData $ pfield @"next" # node
        keyPK = pcon $ PKey $ pdcons @"_0" # pdata key #$ pdnil
     in mkNode # keyPK # nodeNext

-- | Extracts the next node key
getNextPK :: ClosedTerm (PAsData PDiscoverySetNode :--> PMaybe PPubKeyHash)
getNextPK = phoistAcyclic $
  plam $ \node ->
    let nextNodeKey = pfromData $ pfield @"next" # node
     in pmatch nextNodeKey $ \case
          PEmpty _ -> pcon PNothing
          PKey ((pfield @"_0" #) -> n) -> pcon $ PJust $ pcon $ PPubKeyHash $ pfromData n

-- | Extracts the node key
getCurrentPK :: ClosedTerm (PAsData PDiscoverySetNode :--> PMaybe PPubKeyHash)
getCurrentPK = phoistAcyclic $
  plam $ \node ->
    let nodeKey = pfromData $ pfield @"key" # node
     in pmatch nodeKey $ \case
          PEmpty _ -> pcon PNothing
          PKey ((pfield @"_0" #) -> n) -> pcon $ PJust $ pcon $ PPubKeyHash $ pfromData n

{- | Checks whether @SetNode@ key is less than next node key.
  Any valid sequence of nodes MUST follow this property.
-}
validNode :: ClosedTerm (PAsData PDiscoverySetNode :--> PBool)
validNode = phoistAcyclic $
  plam $ \node -> P.do
    nodeDatum <- pletFields @'["key", "next"] node
    pmatch (nodeDatum.key) $ \case
      PEmpty _ -> pcon PTrue
      PKey ((pfield @"_0" #) -> key) -> pmatch (nodeDatum.next) $ \case
        PEmpty _ -> pcon PTrue
        PKey ((pfield @"_0" #) -> next) ->
          pfromData key #< pfromData next -- nodes ordered incrementally

{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}

{-# HLINT ignore "Eta reduce" #-}
module PlutarchMain (main) where

import Data.Default (Default (def))
import Plutarch
import Plutarch.Api.V1 
import Plutarch.Builtin
import Plutarch.Context
import Plutarch.Lift
import Plutarch.List
import Plutarch.Unsafe
import Testing.Eval (evalT, evalWithArgsT)
import PlutusLedgerApi.V1.Scripts
import PlutusLedgerApi.V1.Time
import PlutusLedgerApi.V1.Value as Value
import PlutusLedgerApi.V2 (PubKeyHash (..), always, Map, Address(..), fromList)
import PlutusLedgerApi.V2.Contexts
import Vulcan.Common.Types.Auction (Positive)
import Plutarch.Api.V1.AssocMap
import Plutarch.Positive (PPositive, ptryPositive)
import Ledger.Exports.V1 (Credential(..))
import qualified Plutarch.Api.V1.AssocMap as Map
import  Plutarch.Bool
import PlutusTx qualified 
import PlutusTx.Prelude qualified as PlutusTx

-- import Vulcan.Onchain.Collections.BulkMint (pbulkMintPolicyW)
-- import Vulcan.Onchain.Collections.SequentialMint (psequentialNFTMintW, pseqValidatorW, pseqStateMintingPolicy)

-- seqStateToken :: Integer -> Value
-- seqStateToken n = Value.singleton seqStateCurrencySymbol "6c7bfa6b888fb3e600d4d9505b4fbca905df8ac58ed623b7170ab12a" n

-- seqNFTToken :: TokenName -> Integer -> Value
-- seqNFTToken tkname n = Value.singleton seqNFTCurrencySymbol tkname n

-- sequenceStateTxOutRef :: TxOutRef
-- sequenceStateTxOutRef = TxOutRef "abce0f123e" 1

-- bulkMintTxOutRef :: TxOutRef
-- bulkMintTxOutRef = TxOutRef "dbae0f234e" 1

-- testBulkMintCurrencySymbol :: CurrencySymbol
-- testBulkMintCurrencySymbol = bulkMintCurrencySymbolH (Config {tracingMode = NoTracing}) testBulkMintParameters

-- testBulkMintParameters :: BulkMintParametersD
-- testBulkMintParameters = (BulkMintParametersD {uniqueRef = bulkMintTxOutRef, collectionSize = 3})

-- testSeqValidatorParameters :: SequenceParametersD
-- testSeqValidatorParameters =
--   SequenceParametersD
--     { seqStateCS = seqStateCurrencySymbol
--     , sequenceOwner = seqOwner
--     , threshold = 5
--     }

-- seqStateCurrencySymbol :: CurrencySymbol
-- seqStateCurrencySymbol = seqStateTokenCurrencySymbol sequenceStateTxOutRef

-- seqNFTCurrencySymbol :: CurrencySymbol
-- seqNFTCurrencySymbol = sequentialNFTCurrencySymbol seqValidatorValHash

-- seqValidatorValHash :: ValidatorHash
-- seqValidatorValHash = ValidatorHash "6c7bfa6b888fb3e600d4d9505b4fbca905df8ac58ed623b7170ab12a"

-- seqOwner :: PubKeyHash
-- seqOwner = "1a5cea7b8b3e600d45088fd95b4aba9a05df8ac58ee623b7150ab23d"

-- seqStateDatum :: Integer -> SequenceDatum
-- seqStateDatum n = SequenceDatum {mintCount = n}

-- sequenceValidatorCtxBuilder :: SpendingBuilder
-- sequenceValidatorCtxBuilder =
--   mconcat
--     [ withSpendingOutRef ref2
--     , input $
--         pubKey pk
--           <> withValue minAdaVal
--           <> withRef ref1
--     , input $
--         script seqValidatorValHash
--           <> withValue (minAdaVal <> seqStateToken 1)
--           <> withInlineDatum (mkD $ seqStateDatum 0)
--           <> withRef ref2
--     , signedWith seqOwner
--     , timeRange always
--     ]

-- sequenceValidatorFailsCtx :: ScriptContext
-- sequenceValidatorFailsCtx =
--   let builder :: SpendingBuilder
--       builder =
--         mconcat
--           [ sequenceValidatorCtxBuilder
--           , output $
--               script seqValidatorValHash
--                 <> withValue (minAdaVal <> seqStateToken 1)
--                 <> withInlineDatum (mkD $ seqStateDatum 0)
--           , output $
--               pubKey "deadbeefdeadbeefdeadbeef"
--                 <> withValue (minAdaVal <> seqNFTToken "foo" 1)
--           , mint $ seqNFTToken "foo" 1
--           ]
--    in buildSpending [checkSpending] (mkNormalized builder)

-- sequenceValidatorSucceedsCtx :: ScriptContext
-- sequenceValidatorSucceedsCtx =
--   let builder :: SpendingBuilder
--       builder =
--         mconcat
--           [ sequenceValidatorCtxBuilder
--           , output $
--               script seqValidatorValHash
--                 <> withValue (minAdaVal <> seqStateToken 1)
--                 <> withInlineDatum (mkD $ seqStateDatum 1)
--           , output $
--               pubKey "deadbeefdeadbeefdeadbeef"
--                 <> withValue (minAdaVal <> seqNFTToken "foo" 1)
--           , mint $ seqNFTToken "foo" 1
--           ]
--    in buildSpending [checkSpending] (mkNormalized builder)

-- sequenceStateTokenCtxBuilder :: MintingBuilder
-- sequenceStateTokenCtxBuilder =
--   mconcat
--     [ withMinting seqStateCurrencySymbol
--     , input $
--         pubKey pk
--           <> withValue (minAdaVal <> minAdaVal)
--           <> withRef sequenceStateTxOutRef
--     , signedWith pk
--     , timeRange always
--     ]

-- sequenceStateTokenFailsCtx :: ScriptContext
-- sequenceStateTokenFailsCtx =
--   let builder :: MintingBuilder
--       builder =
--         sequenceStateTokenCtxBuilder
--           <> mconcat
--             [ output $
--                 pubKey pk
--                   <> withValue (minAdaVal <> Value.singleton seqStateCurrencySymbol "foo" 1)
--             , mint (Value.singleton seqStateCurrencySymbol "foo" 1)
--             ]
--    in buildMinting [checkMinting] $ mkNormalized builder

-- sequenceStateTokenSucceedCtx :: ScriptContext
-- sequenceStateTokenSucceedCtx =
--   let builder :: MintingBuilder
--       builder =
--         sequenceStateTokenCtxBuilder
--           <> mconcat
--             [ output $
--                 pubKey pk
--                   <> withValue minAdaVal
--             , output $
--                 script seqValidatorValHash
--                   <> withValue (minAdaVal <> Value.singleton seqStateCurrencySymbol "6c7bfa6b888fb3e600d4d9505b4fbca905df8ac58ed623b7170ab12a" 1)
--             , mint (Value.singleton seqStateCurrencySymbol "6c7bfa6b888fb3e600d4d9505b4fbca905df8ac58ed623b7170ab12a" 1)
--             ]
--    in buildMinting [checkMinting] $ mkNormalized builder

-- bulkMintCtxBuilder :: MintingBuilder
-- bulkMintCtxBuilder =
--   mconcat
--     [ withMinting testBulkMintCurrencySymbol
--     , input $
--         pubKey pk
--           <> withValue (minAdaVal <> minAdaVal <> minAdaVal)
--           <> withRef bulkMintTxOutRef
--     , signedWith pk
--     , timeRange always
--     ]

-- bulkMintSucceedCtx :: ScriptContext
-- bulkMintSucceedCtx =
--   let builder :: MintingBuilder
--       builder =
--         bulkMintCtxBuilder
--           <> mconcat
--             [ output $
--                 pubKey pk
--                   <> withValue (minAdaVal <> Value.singleton testBulkMintCurrencySymbol ("BlueToken" :: TokenName) 1)
--             , output $
--                 pubKey pk1
--                   <> withValue (minAdaVal <> Value.singleton testBulkMintCurrencySymbol ("BooToken" :: TokenName) 1)
--             , output $
--                 pubKey pk2
--                   <> withValue (minAdaVal <> Value.singleton testBulkMintCurrencySymbol ("GooToken" :: TokenName) 1)
--             , mint $
--                 Value.singleton testBulkMintCurrencySymbol ("BlueToken" :: TokenName) 1
--                   <> Value.singleton testBulkMintCurrencySymbol ("BooToken" :: TokenName) 1
--                   <> Value.singleton testBulkMintCurrencySymbol ("GooToken" :: TokenName) 1
--             ]
--    in buildMinting [checkMinting] $ mkNormalized builder




scred1 :: ValidatorHash
scred1 = "6c7bfa6b888fb3e600d4d9505b4fbca905df8ac58ed623b7170ab12a"

scred2 :: ValidatorHash
scred2 = "6c7bfa6b888fb3e600d4d9505b4fbca905df8ac58ed623b7170ab12b"

scred3 :: ValidatorHash
scred3 = "6c7bfa6b888fb3e600d4d9505b4fbca905df8ac58ed623b7170ab12c"

scred4 :: ValidatorHash
scred4 = "6c7bfa6b888fb3e600d4d9505b4fbca905df8ac58ed623b7170ab12d"

scred5 :: ValidatorHash
scred5 = "6c7bfa6b888fb3e600d4d9505b4fbca905df8ac58ed623b7170ab13a"

scred6 :: ValidatorHash
scred6 = "6c7bfa6b888fb3e600d4d9505b4fbca905df8ac58ed623b7170ab14a"

scred7 :: ValidatorHash 
scred7 = "6c7bfa6b888fb3e600d4d9505b4fbca905df8ac58ed623b7170ab15a"

plotsOfHashes :: Term s (PBuiltinList PValidatorHash)
plotsOfHashes = pconstant [scred1, scred2, scred3, scred4, scred5, scred6, scred7, scred1, scred2, scred3, scred4, scred5, scred6, scred7, scred1, scred2, scred3, scred4, scred5, scred6, scred7, scred1, scred2, scred3, scred4, scred5, scred6, scred7, scred1, scred2, scred3, scred4, scred5, scred6, scred7, scred1, scred2, scred3, scred4, scred5, scred6, scred7]

canonicalOrdering = pconstant [26, 21, 6, 12, 13, 15]

tail26 :: PIsListLike l a => Term s (l a :--> a)
tail26 = plam (\xs -> ptail #$ ptail #$ ptail #$ ptail #$ ptail #$ ptail #$ ptail #$ ptail #$ ptail #$ ptail #$ ptail #$ ptail #$ ptail #$ ptail #$ ptail #$ ptail #$ ptail #$ ptail #$ ptail #$ ptail #$ ptail #$ ptail #$ ptail #$ ptail #$ ptail #$ ptail # xs)

main :: IO ()
main = do
  putStrLn "elemAt: naive"
  case evalT
    (  ptail #$ ptail #$ ptail #$ ptail #$ ptail #$ ptail #$ ptail #$ ptail #$ ptail #$ ptail #$ ptail #$ ptail #$ ptail #$ ptail #$ ptail #$ ptail #$ ptail #$ ptail #$ ptail #$ ptail #$ ptail #$ ptail #$ ptail #$ ptail #$ ptail #$ ptail # plotsOfHashes
    ) of
    Right (result, budget, trc) -> print (unScript result) >> print trc >> print budget
    Left err -> print err

  putStrLn "\n"
  putStrLn "elemAt: fast "
  case evalT
    (  pelemAtFast # 26 # plotsOfHashes
    ) of
    Right (result, budget, trc) -> print (unScript result) >> print trc >> print budget
    Left err -> print err
  
  putStrLn "elemAt: canonical ordering naive"
  case evalT
    (  Plutarch.List.pmap # plam (\idx -> pelemAt' # idx # plotsOfHashes) # canonicalOrdering
    ) of
    Right (result, budget, trc) -> print (unScript result) >> print trc >> print budget
    Left err -> print err

  putStrLn "\n"
  putStrLn "elemAt: canonical ordering fast "
  case evalT
    (  Plutarch.List.pmap # plam (\idx -> pelemAtFast # idx # plotsOfHashes) # canonicalOrdering
    ) of
    Right (result, budget, trc) -> print (unScript result) >> print trc >> print budget
    Left err -> print err


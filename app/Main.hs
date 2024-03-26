{-# OPTIONS_GHC -Wno-unused-imports #-}
{-# OPTIONS_GHC -Wno-unused-top-binds #-}

module Main (main) where

import Cardano.Binary qualified as CBOR
import Data.Aeson (KeyValue ((.=)), object)
import Data.Aeson.Encode.Pretty (encodePretty)
import Data.Bifunctor (
  first,
 )
import Data.ByteString.Base16 qualified as Base16
import Data.ByteString.Lazy qualified as LBS
import Data.Default (def)
import Data.Text (
  Text,
  pack,
 )
import Data.Text.Encoding qualified as Text
import Plutarch (
  Config (Config),
  TracingMode (DoTracing, NoTracing, DoTracingAndBinds),
  compile,
 )
import Plutarch.Evaluate (
  evalScript,
 )
import "liqwid-plutarch-extra" Plutarch.Extra.Script (
  applyArguments,
 )
import Plutarch.Prelude
import Plutarch.Script (Script, serialiseScript)
import PlutusLedgerApi.V2 (
  Data,
  ExBudget,
 )
import Ply.Plutarch (
  writeTypedScript,
 )
import PriceDiscoveryEvent.Mint.Standard (mkDiscoveryNodeMPW)
import PriceDiscoveryEvent.MultiFold (pfoldValidatorW, pmintFoldPolicyW, pmintRewardFoldPolicyW, prewardFoldValidatorW)
import PriceDiscoveryEvent.Validator (pDiscoverySetValidator, pDiscoverGlobalLogicW)
import PriceDiscoveryEvent.ProjectTokenHolder (pprojectTokenHolder, pmintProjectTokenHolder)
import PriceDiscoveryEvent.MultiFoldLiquidity qualified as LiquidityFold 
import LiquidityEvent.Mint.Standard (mkLiquidityNodeMPW)
import LiquidityEvent.Validator (pLiquiditySetValidator, pLiquidityGlobalLogicW)
import LiquidityEvent.ProxyTokenHolderV1 qualified as ProxyTokenHolderV1
import AlwaysFails (pAlwaysFails, pAuthMint)
import System.IO
import LiquidityEvent.LiquidityTokenHolder (pmintLiquidityTokenHolder, pliquidityTokenHolder)

encodeSerialiseCBOR :: Script -> Text
encodeSerialiseCBOR = Text.decodeUtf8 . Base16.encode . CBOR.serialize' . serialiseScript

evalT :: Config -> ClosedTerm a -> Either Text (Script, ExBudget, [Text])
evalT cfg x = evalWithArgsT cfg x []

evalWithArgsT :: Config -> ClosedTerm a -> [Data] -> Either Text (Script, ExBudget, [Text])
evalWithArgsT cfg x args = do
  cmp <- compile cfg x
  let (escr, budg, trc) = evalScript $ applyArguments cmp args
  scr <- first (pack . show) escr
  pure (scr, budg, trc)

-- writePlutusScript :: String -> FilePath -> ClosedTerm a -> IO ()
-- writePlutusScript title filepath term = do
--   case evalT term of
--     Left e -> putStrLn (show e)
--     Right (script, _, _) -> do
--       let
--         scriptType = "PlutusScriptV2" :: String
--         plutusJson = object ["type" .= scriptType, "description" .= title, "cborHex" .= encodeSerialiseCBOR script]
--         content = encodePretty plutusJson
--       LBS.writeFile filepath content

writePlutusScript :: Config -> String -> FilePath -> ClosedTerm a -> IO ()
writePlutusScript cfg title filepath term = do
  case evalT cfg term of
    Left e -> putStrLn (show e)
    Right (script, _, _) -> do
      let
        scriptType = "PlutusScriptV2" :: String
        plutusJson = object ["type" .= scriptType, "description" .= title, "cborHex" .= encodeSerialiseCBOR script]
        content = encodePretty plutusJson
      LBS.writeFile filepath content

writePlutusScriptTraceBind :: String -> FilePath -> ClosedTerm a -> IO ()
writePlutusScriptTraceBind title filepath term =
  writePlutusScript (Config DoTracingAndBinds) title filepath term

writePlutusScriptTrace :: String -> FilePath -> ClosedTerm a -> IO ()
writePlutusScriptTrace title filepath term =
  writePlutusScript (Config DoTracing) title filepath term

writePlutusScriptNoTrace :: String -> FilePath -> ClosedTerm a -> IO ()
writePlutusScriptNoTrace title filepath term =
  writePlutusScript (Config NoTracing) title filepath term

main :: IO ()
main = do
  putStrLn "Writing Plutus Scripts to files"
  writePlutusScriptNoTrace "Discovery Stake Validator" "./compiled/discoveryStakeValidator.json" pDiscoverGlobalLogicW
  writePlutusScriptNoTrace "Discovery Validator" "./compiled/discoveryValidator.json" $ pDiscoverySetValidator def "FSN"
  writePlutusScriptNoTrace "Discovery Mint" "./compiled/discoveryMinting.json" $ mkDiscoveryNodeMPW def
  writePlutusScriptNoTrace "Commit Fold Validator" "./compiled/foldValidator.json" pfoldValidatorW
  writePlutusScriptNoTrace "Commit Fold Mint" "./compiled/foldMint.json" pmintFoldPolicyW
  writePlutusScriptNoTrace "Reward Fold Validator" "./compiled/rewardFoldValidator.json" prewardFoldValidatorW
  writePlutusScriptNoTrace "Reward Fold Mint" "./compiled/rewardFoldMint.json" pmintRewardFoldPolicyW
  writePlutusScriptNoTrace "Always Fails" "./compiled/alwaysFails.json" pAlwaysFails
  writePlutusScriptNoTrace "Auth Mint" "./compiled/authMint.json" pAuthMint
  writePlutusScriptNoTrace "Token Holder Validator" "./compiled/tokenHolderValidator.json" pprojectTokenHolder
  writePlutusScriptNoTrace "Token Holder Policy" "./compiled/tokenHolderPolicy.json" pmintProjectTokenHolder

  
  writePlutusScriptNoTrace "Liquidity Stake Validator" "./compiledLiquidity/liquidityStakeValidator.json" pLiquidityGlobalLogicW
  writePlutusScriptNoTrace "Liquidity Validator" "./compiledLiquidity/liquidityValidator.json" $ pLiquiditySetValidator def "FSN"
  writePlutusScriptNoTrace "Liquidity Mint" "./compiledLiquidity/liquidityMinting.json" $ mkLiquidityNodeMPW def
  writePlutusScriptNoTrace "Collect Fold Validator" "./compiledLiquidity/liquidityFoldValidator.json" LiquidityFold.pfoldValidatorW
  writePlutusScriptNoTrace "Collect Fold Mint" "./compiledLiquidity/liquidityFoldMint.json" LiquidityFold.pmintFoldPolicyW
  writePlutusScriptNoTrace "Distribute Fold Validator" "./compiledLiquidity/distributionFoldValidator.json" LiquidityFold.prewardFoldValidatorW
  writePlutusScriptNoTrace "Distribute Fold Mint" "./compiledLiquidity/distributionRewardFoldMint.json" LiquidityFold.pmintRewardFoldPolicyW
  writePlutusScriptNoTrace "Proxy Token Holder V1" "./compiledLiquidity/proxyTokenHolderV1.json" ProxyTokenHolderV1.pproxyTokenHolderV1
  writePlutusScriptNoTrace "Liquidity Token Holder Mint" "./compiledLiquidity/liquidityTokenHolderMint.json" pmintLiquidityTokenHolder
  writePlutusScriptNoTrace "Liquidity Token Holder Validator" "./compiledLiquidity/liquidityTokenHolderValidator.json" pliquidityTokenHolder

  writePlutusScriptTraceBind "Liquidity Stake Validator" "./compiledLiquidityBinds/liquidityStakeValidator.json" pLiquidityGlobalLogicW
  writePlutusScriptTraceBind "Liquidity Validator" "./compiledLiquidityBinds/liquidityValidator.json" $ pLiquiditySetValidator def "FSN"
  writePlutusScriptTraceBind "Liquidity Mint" "./compiledLiquidityBinds/liquidityMinting.json" $ mkLiquidityNodeMPW def
  writePlutusScriptTraceBind "Collect Fold Validator" "./compiledLiquidityBinds/liquidityFoldValidator.json" LiquidityFold.pfoldValidatorW
  writePlutusScriptTraceBind "Collect Fold Mint" "./compiledLiquidityBinds/liquidityFoldMint.json" LiquidityFold.pmintFoldPolicyW
  writePlutusScriptTraceBind "Distribute Fold Validator" "./compiledLiquidityBinds/distributionFoldValidator.json" LiquidityFold.prewardFoldValidatorW
  writePlutusScriptTraceBind "Distribute Fold Mint" "./compiledLiquidityBinds/distributionRewardFoldMint.json" LiquidityFold.pmintRewardFoldPolicyW
  writePlutusScriptTraceBind "Proxy Token Holder V1" "./compiledLiquidityBinds/proxyTokenHolderV1.json" ProxyTokenHolderV1.pproxyTokenHolderV1
  writePlutusScriptTraceBind "Liquidity Token Holder Mint" "./compiledLiquidityBinds/liquidityTokenHolderMint.json" pmintLiquidityTokenHolder
  writePlutusScriptTraceBind "Liquidity Token Holder Validator" "./compiledLiquidityBinds/liquidityTokenHolderValidator.json" pliquidityTokenHolder


  writePlutusScriptTrace "Liquidity Stake Validator" "./compiledLiquidityTracing/liquidityStakeValidator.json" pLiquidityGlobalLogicW
  writePlutusScriptTrace "Liquidity Validator" "./compiledLiquidityTracing/liquidityValidator.json" $ pLiquiditySetValidator def "FSN"
  writePlutusScriptTrace "Liquidity Mint" "./compiledLiquidityTracing/liquidityMinting.json" $ mkLiquidityNodeMPW def
  writePlutusScriptTrace "Collect Fold Validator" "./compiledLiquidityTracing/liquidityFoldValidator.json" LiquidityFold.pfoldValidatorW
  writePlutusScriptTrace "Collect Fold Mint" "./compiledLiquidityTracing/liquidityFoldMint.json" LiquidityFold.pmintFoldPolicyW
  writePlutusScriptTrace "Distribute Fold Validator" "./compiledLiquidityTracing/distributionFoldValidator.json" LiquidityFold.prewardFoldValidatorW
  writePlutusScriptTrace "Distribute Fold Mint" "./compiledLiquidityTracing/distributionRewardFoldMint.json" LiquidityFold.pmintRewardFoldPolicyW
  writePlutusScriptTrace "Proxy Token Holder V1" "./compiledLiquidityTracing/proxyTokenHolderV1.json" ProxyTokenHolderV1.pproxyTokenHolderV1
  writePlutusScriptTrace "Liquidity Token Holder Mint" "./compiledLiquidityTracing/liquidityTokenHolderMint.json" pmintLiquidityTokenHolder
  writePlutusScriptTrace "Liquidity Token Holder Validator" "./compiledLiquidityTracing/liquidityTokenHolderValidator.json" pliquidityTokenHolder

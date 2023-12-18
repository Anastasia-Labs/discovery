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
  TracingMode (DoTracing, NoTracing),
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

encodeSerialiseCBOR :: Script -> Text
encodeSerialiseCBOR = Text.decodeUtf8 . Base16.encode . CBOR.serialize' . serialiseScript

evalT :: ClosedTerm a -> Either Text (Script, ExBudget, [Text])
evalT x = evalWithArgsT x []

evalWithArgsT :: ClosedTerm a -> [Data] -> Either Text (Script, ExBudget, [Text])
evalWithArgsT x args = do
  cmp <- compile (Config NoTracing) x
  let (escr, budg, trc) = evalScript $ applyArguments cmp args
  scr <- first (pack . show) escr
  pure (scr, budg, trc)

writePlutusScript :: String -> FilePath -> ClosedTerm a -> IO ()
writePlutusScript title filepath term = do
  case evalT term of
    Left e -> putStrLn (show e)
    Right (script, _, _) -> do
      let
        scriptType = "PlutusScriptV2" :: String
        plutusJson = object ["type" .= scriptType, "description" .= title, "cborHex" .= encodeSerialiseCBOR script]
        content = encodePretty plutusJson
      LBS.writeFile filepath content

main :: IO ()
main = do
  putStrLn "hi"
  writePlutusScript "Discovery Stake Validator" "./compiled/discoveryStakeValidator.json" pDiscoverGlobalLogicW
  writePlutusScript "Discovery Validator" "./compiled/discoveryValidator.json" $ pDiscoverySetValidator def "FSN"
  writePlutusScript "Discovery Mint" "./compiled/discoveryMinting.json" $ mkDiscoveryNodeMPW def
  writePlutusScript "Commit Fold Validator" "./compiled/foldValidator.json" pfoldValidatorW
  writePlutusScript "Commit Fold Mint" "./compiled/foldMint.json" pmintFoldPolicyW
  writePlutusScript "Reward Fold Validator" "./compiled/rewardFoldValidator.json" prewardFoldValidatorW
  writePlutusScript "Reward Fold Mint" "./compiled/rewardFoldMint.json" pmintRewardFoldPolicyW
  writePlutusScript "Always Fails" "./compiled/alwaysFails.json" pAlwaysFails
  writePlutusScript "Auth Mint" "./compiled/authMint.json" pAuthMint
  writePlutusScript "Token Holder Validator" "./compiled/tokenHolderValidator.json" pprojectTokenHolder
  writePlutusScript "Token Holder Policy" "./compiled/tokenHolderPolicy.json" pmintProjectTokenHolder
  writePlutusScript "Liquidity Stake Validator" "./compiledLiquidity/liquidityStakeValidator.json" pLiquidityGlobalLogicW
  writePlutusScript "Liquidity Validator" "./compiledLiquidity/liquidityValidator.json" $ pLiquiditySetValidator def "FSN"
  writePlutusScript "Liquidity Mint" "./compiledLiquidity/liquidityMinting.json" $ mkLiquidityNodeMPW def
  writePlutusScript "Collect Fold Validator" "./compiledLiquidity/liquidityFoldValidator.json" LiquidityFold.pfoldValidatorW
  writePlutusScript "Collect Fold Mint" "./compiledLiquidity/liquidityFoldMint.json" LiquidityFold.pmintFoldPolicyW
  writePlutusScript "Distribute Fold Validator" "./compiledLiquidity/distributionFoldValidator.json" LiquidityFold.prewardFoldValidatorW
  writePlutusScript "Distribute Fold Mint" "./compiledLiquidity/distributionRewardFoldMint.json" LiquidityFold.pmintRewardFoldPolicyW
  writePlutusScript "Proxy Token Holder V1" "./compiledLiquidity/proxyTokenHolderV1.json" ProxyTokenHolderV1.pproxyTokenHolderV1


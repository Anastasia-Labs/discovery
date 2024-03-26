{-# OPTIONS_GHC -Wno-missing-export-lists #-}

module Types.Constants where

import Plutarch
import Plutarch.Api.V1 (PTokenName (..))
import Plutarch.Monadic qualified as P
import Plutarch.Prelude
import PlutusLedgerApi.V1 (TokenName)
import PriceDiscoveryEvent.Utils (passert, pisPrefixOf)

projectTokenHolderTN :: Term s PTokenName
projectTokenHolderTN =
  let tn :: TokenName
      tn = "PTHolder"
   in pconstant tn

commitFoldTN :: Term s PTokenName
commitFoldTN =
  let tn :: TokenName
      tn = "CFold"
   in pconstant tn

rewardFoldTN :: Term s PTokenName
rewardFoldTN =
  let tn :: TokenName
      tn = "RFold"
   in pconstant tn

poriginNodeTN :: Term s PTokenName
poriginNodeTN =
  let tn :: TokenName
      tn = "FSN"
   in pconstant tn

pcorrNodeTN :: Term s PTokenName
pcorrNodeTN =
  let tn :: TokenName
      tn = "FCN"
   in pconstant tn

psetNodePrefix :: ClosedTerm PByteString
psetNodePrefix = pconstant "FSN"

pnodeKeyTN :: ClosedTerm (PByteString :--> PTokenName)
pnodeKeyTN = phoistAcyclic $
  plam $
    \nodeKey -> pcon $ PTokenName $ psetNodePrefix <> nodeKey

pparseNodeKey :: ClosedTerm (PTokenName :--> PMaybe PByteString)
pparseNodeKey = phoistAcyclic $
  plam $ \(pto -> tn) -> P.do
    let prefixLength = 3
        tnLength = plengthBS # tn
        key = psliceBS # prefixLength # (tnLength - prefixLength) # tn
    passert "incorrect node prefix" $ pisPrefixOf # psetNodePrefix # tn
    pif (prefixLength #< tnLength) (pcon $ PJust key) (pcon PNothing)

foldingFee :: Term s PInteger
foldingFee = pconstant 1_000_000

minAda :: Term s PInteger
minAda = pconstant 2_000_000

-- 3 Ada for min UTxO Ada for the node UTxO 
-- 1 Ada for the collection fold fee 
-- 1 Ada for the reward fold fee 
nodeDepositAda :: Term s PInteger 
nodeDepositAda = pconstant 5_000_000

minAdaToCommit :: Term s PInteger 
minAdaToCommit = pconstant 6_000_000
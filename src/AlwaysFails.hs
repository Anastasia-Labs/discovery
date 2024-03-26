{-# OPTIONS_GHC -Wno-incomplete-uni-patterns #-}
{-# OPTIONS_GHC -Wno-missing-import-lists #-}

module AlwaysFails (pAlwaysFails, pAuthMint) where 

import Plutarch.Prelude
import Plutarch.Api.V2 
import PriceDiscoveryEvent.Utils (pvalueOfOne)

pAlwaysFails ::
  ClosedTerm PValidator
pAlwaysFails  = plam $ \_dat _redmn _ctx' -> popaque $ perror

pAuthMint ::
  Term s (PAsData PCurrencySymbol :--> PMintingPolicy)
pAuthMint  = plam $ \multisigCert _redmn ctx ->
  let inputs = pfield @"inputs" # (pfield @"txInfo" # ctx) 
   in pif (pany @PBuiltinList
            # plam (\inp -> (pvalueOfOne # multisigCert # (pfield @"value" # (pfield @"resolved" # inp)))) 
            # inputs)
          (popaque $ pconstant ())
          perror 
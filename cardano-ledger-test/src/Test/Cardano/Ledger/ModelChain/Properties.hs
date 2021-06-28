{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE NumericUnderscores #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Test.Cardano.Ledger.ModelChain.Properties where

import Cardano.Ledger.Alonzo (AlonzoEra)
import Cardano.Ledger.BaseTypes (unitIntervalFromRational)
import Cardano.Ledger.Coin
import qualified Cardano.Ledger.Core as Core
import qualified Cardano.Ledger.Era
import Cardano.Ledger.Shelley (ShelleyEra)
import qualified Cardano.Ledger.Val as Val
import Control.State.Transition.Extended
import Data.Default.Class
import Data.Foldable
import qualified Data.Map as Map
import Data.Ratio ((%))
import qualified Data.Set as Set
import Data.Typeable
import Shelley.Spec.Ledger.API.Genesis
import Test.Cardano.Ledger.Elaborators.Alonzo ()
import Test.Cardano.Ledger.Elaborators.Shelley ()
import Test.Cardano.Ledger.ModelChain
import Test.Cardano.Ledger.ModelChain.Utils
import Test.Shelley.Spec.Ledger.ConcreteCryptoTypes (C_Crypto)
import Test.Tasty
import Test.Tasty.QuickCheck

-- | some hand-written model based unit tests
modelUnitTests ::
  forall era proxy.
  ( ElaborateEraModel era,
    Default (AdditionalGenesisConfig era),
    Eq (PredicateFailure (Core.EraRule "LEDGER" era)),
    Show (PredicateFailure (Core.EraRule "LEDGER" era)),
    Cardano.Ledger.Era.Era era
  ) =>
  proxy era ->
  TestTree
modelUnitTests proxy =
  testGroup
    (show $ typeRep proxy)
    [ testProperty "noop" $ testChainModelInteraction proxy Map.empty [],
      testProperty "noop-2" $
        testChainModelInteraction
          proxy
          ( Map.fromList
              [ ("alice", Coin 1_000_000),
                ("bob", Coin 1_000_000)
              ]
          )
          [ModelEpoch [] mempty],
      let genAct =
            Map.fromList
              [ ("alice", Coin 1_000_000_000_000)
              ]
          checks nes ems =
            let rewards = observeRewards (nes, ems)
             in counterexample (show rewards) $ Coin 0 === fold rewards
       in testProperty "deleg" $
            testChainModelInteractionWith
              proxy
              checks
              genAct
              [ ModelEpoch
                  [ ModelBlock
                      0
                      [ (modelTx 1)
                          { _mtxInputs = Set.fromList [ModelGensisIn "alice"],
                            _mtxOutputs =
                              [ ModelTxOut "alice" (1_000_000_000_000 - (100_000_000_000))
                              ],
                            _mtxFee = 100_000_000_000,
                            _mtxDCert =
                              [ ModelRegisterStake "alice",
                                ModelRegisterPool (ModelPoolParams "pool1" (Coin 0) (Coin 0) (unitIntervalFromRational (0 % 1)) "alice" ["alice"]),
                                ModelDelegate (ModelDelegation "alice" "pool1")
                              ]
                          }
                      ]
                  ]
                  (ModelBlocksMade $ Map.fromList []),
                ModelEpoch [] (ModelBlocksMade $ Map.fromList []),
                ModelEpoch [] (ModelBlocksMade $ Map.fromList [("pool1", 100)]),
                ModelEpoch [] (ModelBlocksMade $ Map.fromList []),
                ModelEpoch
                  [ ModelBlock
                      0
                      [ (modelTx 1)
                          { _mtxInputs = Set.fromList [ModelTxIn 1 0],
                            _mtxOutputs =
                              [ ModelTxOut "alice" (1_000_000_000_000 - (2 * 100_000_000_000)),
                                ModelTxOut "bob" 8999820000000
                              ],
                            _mtxFee = 100_000_000_000,
                            _mtxWdrl = Map.singleton "alice" (Coin 8999820000000)
                          }
                      ]
                  ]
                  (ModelBlocksMade $ Map.fromList [])
              ],
      testProperty "xfer" $
        testChainModelInteraction
          proxy
          ( Map.fromList
              [ ("alice", Coin 1_000_000_000)
              ]
          )
          [ ModelEpoch
              [ ModelBlock
                  1
                  [ (modelTx 1)
                      { _mtxInputs = Set.fromList [ModelGensisIn "alice"],
                        _mtxOutputs =
                          [ ModelTxOut "bob" 100_000_000,
                            ModelTxOut "alice" (1_000_000_000 - (100_000_000 + 1_000_000))
                          ],
                        _mtxFee = 1_000_000
                      }
                  ]
              ]
              mempty
          ],
      testProperty "unbalanced" $
        testChainModelInteractionRejection
          proxy
          (ModelValueNotConservedUTxO (Val.inject $ Coin 1_000_000_000) (Val.inject $ Coin 101_000_000))
          ( Map.fromList
              [ ("alice", Coin 1_000_000_000)
              ]
          )
          [ ModelEpoch
              [ ModelBlock
                  1
                  [ (modelTx 1)
                      { _mtxInputs = (Set.fromList [ModelGensisIn "alice"]),
                        _mtxOutputs = [ModelTxOut "bob" 100_000_000],
                        _mtxFee = 1_000_000
                      }
                  ]
              ]
              mempty
          ],
      testProperty "xfer-2" $
        testChainModelInteraction
          proxy
          ( Map.fromList
              [ ("alice", Coin 1_000_000_000)
              ]
          )
          [ ModelEpoch
              [ ModelBlock
                  1
                  [ (modelTx 1)
                      { _mtxInputs = Set.fromList [ModelGensisIn "alice"],
                        _mtxOutputs =
                          [ ModelTxOut "bob" 100_000_000,
                            ModelTxOut "alice" (1_000_000_000 - (100_000_000 + 1_000_000))
                          ],
                        _mtxFee = 1_000_000
                      }
                  ],
                ModelBlock
                  2
                  [ (modelTx 2)
                      { _mtxInputs = Set.fromList [ModelTxIn 1 1],
                        _mtxOutputs =
                          [ ModelTxOut "bob" 100_000_000,
                            ModelTxOut "alice" (1_000_000_000 - 2 * (100_000_000 + 1_000_000))
                          ],
                        _mtxFee = 1_000_000
                      }
                  ]
              ]
              mempty
          ]
    ]

modelUnitTests_ :: TestTree
modelUnitTests_ =
  testGroup
    "model-unit-tests"
    [ modelUnitTests (Proxy :: Proxy (ShelleyEra C_Crypto)),
      modelUnitTests (Proxy :: Proxy (AlonzoEra C_Crypto))
    ]

defaultTestMain :: IO ()
defaultTestMain = defaultMain modelUnitTests_

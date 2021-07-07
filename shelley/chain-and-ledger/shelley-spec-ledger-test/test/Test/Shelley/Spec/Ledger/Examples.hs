{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}

module Test.Shelley.Spec.Ledger.Examples
  ( CHAINExample (..),
    testCHAINExample,
    testCHAINExample',
    testAndNormalizeCHAINExample,
    complete,
  )
where

import Cardano.Ledger.Shelley ()
import Control.State.Transition.Extended hiding (Assertion)
import Control.State.Transition.Trace (checkTrace, (.-), (.->),runAndCompare)
import Shelley.Spec.Ledger.BlockChain (Block)
import Shelley.Spec.Ledger.PParams (PParams' (..))
import Shelley.Spec.Ledger.STS.Chain (CHAIN, ChainState(..), totalAda)
import Shelley.Spec.Ledger.Scripts ()
import Test.Shelley.Spec.Ledger.ConcreteCryptoTypes (C)
import Test.Shelley.Spec.Ledger.Orphans ()
import Test.Shelley.Spec.Ledger.Utils (applySTSTest, maxLLSupply, runShelleyBase)
import Test.Tasty.HUnit (Assertion, (@?=))

import Shelley.Spec.Ledger.EpochBoundary(SnapShots(..))
import Shelley.Spec.Ledger.LedgerState(EpochState(..),NewEpochState(..))
import GHC.Records(HasField)
import Cardano.Ledger.Address(Addr)
-- import Debug.Trace(trace)
import Cardano.Ledger.Era (Era,Crypto (..))
import qualified Cardano.Ledger.Core as Core
import qualified Shelley.Spec.Ledger.EpochBoundary as EB

-- | Normalizes a ChainState by running the_pstakeMark to completion
complete ::
  ( Era era,
    HasField "address" (Core.TxOut era) (Addr (Crypto era))
  ) => ChainState era -> ChainState era
complete chainstate = chainstate{chainNes=newepochstate{nesEs=epochstate{esSnapshots=snapshots{_pstakeMark=newmark}}}}
   where newepochstate = chainNes chainstate
         epochstate = nesEs newepochstate
         snapshots = esSnapshots epochstate
         mark = _pstakeMark snapshots
         newmark = EB.Completed(EB.runToCompletion mark)


data CHAINExample h = CHAINExample
  { -- | State to start testing with
    startState :: ChainState h,
    -- | Block to run chain state transition system on
    newBlock :: Block h,
    -- | type of fatal error, if failure expected and final chain state if success expected
    intendedResult :: Either [[PredicateFailure (CHAIN h)]] (ChainState h)
  }


-- | Runs example, applies chain state transition system rule (STS),
--   and checks that trace ends with expected state or expected error.
testCHAINExample' :: CHAINExample C -> Assertion
testCHAINExample' (CHAINExample initSt block (Right expectedSt)) = do
  (checkTrace @(CHAIN C) runShelleyBase () $ pure initSt .- block .-> expectedSt)
    >> (totalAda expectedSt @?= maxLLSupply)
testCHAINExample' (CHAINExample initSt block predicateFailure@(Left _)) = do
  let st = runShelleyBase $ applySTSTest @(CHAIN C) (TRC ((), initSt, block))
  st @?= predicateFailure


-- | Runs example, applies chain state transition system rule (STS),
--   checks that trace ends with a state,
--   that is normalized and then compared to expected state or expected error.
testAndNormalizeCHAINExample :: (ChainState C -> ChainState C) -> CHAINExample C -> Assertion
testAndNormalizeCHAINExample normalize (CHAINExample initSt block (Right expectedSt)) = do
  (checkTrace @(CHAIN C) runShelleyBase () $ runAndCompare normalize (pure initSt) block expectedSt)
    >> (totalAda expectedSt @?= maxLLSupply)
testAndNormalizeCHAINExample _normalize (CHAINExample initSt block predicateFailure@(Left _)) = do
  let st = runShelleyBase $ applySTSTest @(CHAIN C) (TRC ((), initSt, block))
  st @?= predicateFailure


testCHAINExample :: CHAINExample C -> Assertion
testCHAINExample x = testAndNormalizeCHAINExample complete x
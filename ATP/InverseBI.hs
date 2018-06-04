--------------------------------------------------------------------------------

--  Copyright 2018 Remy Goldschmidt
--
--  Licensed under the Apache License, Version 2.0 (the "License");
--  you may not use this file except in compliance with the License.
--  You may obtain a copy of the License at
--
--    http://www.apache.org/licenses/LICENSE-2.0
--
--  Unless required by applicable law or agreed to in writing, software
--  distributed under the License is distributed on an "AS IS" BASIS,
--  WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
--  See the License for the specific language governing permissions and
--  limitations under the License.

--------------------------------------------------------------------------------

{-# LANGUAGE DataKinds          #-}
{-# LANGUAGE DeriveAnyClass     #-}
{-# LANGUAGE DeriveGeneric      #-}
{-# LANGUAGE GADTs              #-}
{-# LANGUAGE KindSignatures     #-}
{-# LANGUAGE StandaloneDeriving #-}

--------------------------------------------------------------------------------

-- |
-- Automated theorem proving for the logic of bunched implications using
-- the inverse method, as described in
-- <https://www.cl.cam.ac.uk/~nk480/inverse-method-for-bi.pdf>.
module ATP.InverseBI
  ( module ATP.InverseBI -- FIXME: specific export list
  ) where

--------------------------------------------------------------------------------

import           Control.Monad

import           Control.Monad.ST    (ST, runST)

import           Data.Either
import           Data.Maybe

import           Data.HashSet        (HashSet)
import qualified Data.HashSet        as HashSet

import           Data.HashMap.Strict (HashMap)
import qualified Data.HashMap.Strict as HashMap

import           Data.Hashable       (Hashable)
import           GHC.Generics        (Generic)

import           Flow                ((.>), (|>))

import           ATP.Utils.MHashMap  (MHashMap)
import qualified ATP.Utils.MHashMap  as MHashMap

import           ATP.Utils.MHashSet  (MHashSet)
import qualified ATP.Utils.MHashSet  as MHashSet

import           ATP.Utils.MBitmap   (MBitmap)
import qualified ATP.Utils.MBitmap   as MBitmap

--------------------------------------------------------------------------------

type Variable = Int

--------------------------------------------------------------------------------

data Formula pv where
  Variable :: !pv                            -> Formula pv
  (:∨:)    :: !(Formula pv) -> !(Formula pv) -> Formula pv
  (:∧:)    :: !(Formula pv) -> !(Formula pv) -> Formula pv
  (:⊃:)    :: !(Formula pv) -> !(Formula pv) -> Formula pv
  (:∗:)    :: !(Formula pv) -> !(Formula pv) -> Formula pv
  (:-∗:)   :: !(Formula pv) -> !(Formula pv) -> Formula pv

deriving instance (Generic  pv) => Generic  (Formula pv)
deriving instance (Eq       pv) => Eq       (Formula pv)
deriving instance ( Generic pv, Hashable pv
                  ) => Hashable (Formula pv)

--------------------------------------------------------------------------------

data Bunches pv where
  Assumption :: !(Formula pv)                  -> Bunches pv
  Øₘ         ::                                   Bunches pv
  (:&:)      :: !(Bunches pv) -> !(Bunches pv) -> Bunches pv
  Øₐ         ::                                   Bunches pv
  (:|:)      :: !(Bunches pv) -> !(Bunches pv) -> Bunches pv

deriving instance (Generic  pv) => Generic  (Bunches pv)
deriving instance (Eq       pv) => Eq       (Bunches pv)
deriving instance ( Generic pv, Hashable pv
                  ) => Hashable (Bunches pv)

--------------------------------------------------------------------------------

data CanonicalBunchesKind where
  CBKAny            :: CanonicalBunchesKind
  CBKAdditive       :: CanonicalBunchesKind
  CBKMultiplicative :: CanonicalBunchesKind

data CanonicalBunches (kind :: CanonicalBunchesKind) pv where
  CBAssumption     :: Formula pv
                   -> CanonicalBunches any pv
  CBAdditive       :: HashSet (CanonicalBunches 'CBKMultiplicative pv)
                   -> CanonicalBunches 'CBKAdditive pv
  CBMultiplicative :: HashSet (CanonicalBunches 'CBKAdditive pv)
                   -> CanonicalBunches 'CBKMultiplicative pv
  CBAny            :: CanonicalBunches any pv
                   -> CanonicalBunches 'CBKAny pv

-- |
-- FIXME: doc
canonicalizeBunches :: Bunches pv -> CanonicalBunches 'CBKAny pv
canonicalizeBunches = undefined
--   = convertToSets
--     .> eliminateSingletons
--   where
--     convertToSets :: CanonicalBunches
--
--     eliminateSingletons :: CanonicalBunches 'CBKAny pv
--                         -> CanonicalBunches 'CBKAny pv
--     eliminateSingletons = undefined

--------------------------------------------------------------------------------

-- |
-- @⊑@ is the transitive, reflexive (with respect to @≡@) closure of
-- @Γ(Δ) ⊑ Γ(Δ ; Δ')@.
(⊑) :: Bunches pv -> Bunches pv -> Bool
(⊑) = undefined

-- |
-- The minimal (or least) upper bound set of @Δ@ and @Γ@ is a set of upper
-- bounds for @Δ@ and @Γ@ under the @⊑@ relation:
--
-- @∀ Σ ∈ lubs(Δ)(Γ) . (Δ ⊑ Σ) ∧ (Γ ⊑ Σ)@
--
-- Additionally, for any upper bound @Σ@ of @Δ@ and @Γ@, the minimal upper
-- bound set contains at least one element @Σ'@ such that @Σ' ⊑ Σ@:
--
-- @∀ Σ . ((Δ ⊑ Σ) ∧ (Γ ⊑ Σ)) ⇒ (∃ Σ' ∈ lubs(Δ)(Γ) . Σ' ⊑ Σ)@
lubs :: Bunches pv -> Bunches pv -> HashSet (Bunches pv)
lubs = undefined

--------------------------------------------------------------------------------

data Constraint pv where
  (:≡:)  :: !(Bunches pv)
         -> !(Bunches pv)
         -> Constraint pv
  (:≢:)  :: !(Bunches pv)
         -> !(Bunches pv)
         -> Constraint pv
  InLUBS :: !(Bunches pv)
         -> !(Bunches pv)
         -> !(Bunches pv)
         -> Constraint pv

deriving instance (Generic  pv) => Generic  (Constraint pv)
deriving instance (Eq       pv) => Eq       (Constraint pv)
deriving instance ( Generic pv, Hashable pv
                  ) => Hashable (Constraint pv)

--------------------------------------------------------------------------------

data Judgement pv where
  (:⊢:) :: !(Bunches pv) -> !(Formula pv) -> Judgement pv

deriving instance (Generic  pv) => Generic  (Judgement pv)
deriving instance (Eq       pv) => Eq       (Judgement pv)
deriving instance ( Generic pv, Hashable pv
                  ) => Hashable (Judgement pv)

--------------------------------------------------------------------------------

data ProofTokenᴵ where
  PT_Initᴵ   :: ProofTokenᴵ
  PT_Cᴵ      :: ProofTokenᴵ
  PT_Eᴵ      :: ProofTokenᴵ
  PT_SupLᴵ   :: ProofTokenᴵ
  PT_SupR1ᴵ  :: ProofTokenᴵ
  PT_SupR2ᴵ  :: ProofTokenᴵ
  PT_AndRᴵ   :: ProofTokenᴵ
  PT_AndL1ᴵ  :: ProofTokenᴵ
  PT_AndL2ᴵ  :: ProofTokenᴵ
  PT_OrR1ᴵ   :: ProofTokenᴵ
  PT_OrR2ᴵ   :: ProofTokenᴵ
  PT_OrLᴵ    :: ProofTokenᴵ
  PT_StarLᴵ  :: ProofTokenᴵ
  PT_StarRᴵ  :: ProofTokenᴵ
  PT_MagicLᴵ :: ProofTokenᴵ
  PT_MagicRᴵ :: ProofTokenᴵ

--------------------------------------------------------------------------------

data Proofᴵ pv where

  -- |
  -- FIXME: doc
  --
  -- @
  --   ───────────────────────────────────────── [INITᴵ]
  --   ⟨φ⟩ ⊢ᴵ φ
  -- @
  Initᴵ
    :: !(Formula pv) -- FIXME: may be unnecessary
    -- ^ @φ@
    -> Proofᴵ pv
    -- ^ A proof of @⟨φ⟩ ⊢ᴵ φ@

  -- |
  -- FIXME: doc
  --
  -- @
  --   Γ ⊢ᴵ φ
  --   (Δ₁ ; Δ₂) ⊆ Γ
  --   Δ ∈ lubs(Δ₁)(Δ₂)
  --   Δ ≢ (Δ₁ ; Δ₂)
  --   ───────────────────────────────────────── [Cᴵ]
  --   Γ[(Δ₁ ; Δ₂) ↦ Δ] ⊢ᴵ φ
  -- @
  Cᴵ
    :: !(Bunches pv) -- FIXME: may be unnecessary
    -- ^ @Γ@
    -> !(Bunches pv) -- FIXME: may be unnecessary
    -- ^ @Δ@
    -> !(Bunches pv) -- FIXME: may be unnecessary
    -- ^ @Δ₁@
    -> !(Bunches pv) -- FIXME: may be unnecessary
    -- ^ @Δ₂@
    -> !(Proofᴵ pv)
    -- ^ A proof of @Γ ⊢ᴵ φ@
    -> Proofᴵ pv
    -- ^ A proof of @Γ[(Δ₁ ; Δ₂) ↦ Δ] ⊢ᴵ φ@

  -- |
  -- FIXME: doc
  --
  -- @
  --   Γ ⊢ᴵ φ
  --   Γ ≡ Γ'
  --   ───────────────────────────────────────── [Eᴵ]
  --   Γ' ⊢ᴵ φ
  -- @
  Eᴵ
    :: !(Bunches pv) -- FIXME: may be unnecessary
    -- ^ @Γ@
    -> !(Bunches pv) -- FIXME: may be unnecessary
    -- ^ @Γ'@
    -> !(Proofᴵ pv)
    -- ^ A proof of @Γ ⊢ᴵ φ@
    -> Proofᴵ pv
    -- ^ A proof of @Γ' ⊢ᴵ φ@

  -- |
  -- FIXME: doc
  --
  -- @
  --   (Δ' ; ⟨ψ⟩) ⊆ Δ
  --   Γ ⊢ᴵ φ
  --   Δ ⊢ᴵ χ
  --   ───────────────────────────────────────── [⊃Lᴵ]
  --   Δ[(Δ' ; ⟨ψ⟩) ↦ (Δ' ; Γ ; ⟨φ ⊃ ψ⟩)] ⊢ᴵ χ
  -- @
  SupLᴵ
    :: !(Bunches pv) -- FIXME: may be unnecessary
    -- ^ @Γ@
    -> !(Bunches pv) -- FIXME: may be unnecessary
    -- ^ @Δ@
    -> !(Bunches pv) -- FIXME: may be unnecessary
    -- ^ @Δ'@
    -> !(Formula pv) -- FIXME: may be unnecessary
    -- ^ @ψ@
    -> !(Proofᴵ pv)
    -- ^ A proof of @Γ ⊢ᴵ φ@
    -> !(Proofᴵ pv)
    -- ^ A proof of @Δ ⊢ᴵ χ@
    -> Proofᴵ pv
    -- ^ A proof of @Δ[(Δ' ; ⟨ψ⟩) ↦ (Δ' ; Γ ; ⟨φ ⊃ ψ⟩)] ⊢ᴵ χ@

  -- |
  -- FIXME: doc
  --
  -- @
  --   (Γ ; ⟨φ⟩) ⊢ᴵ ψ
  --   ───────────────────────────────────────── [⊃R₁ᴵ]
  --   Γ ⊢ᴵ (φ ⊃ ψ)
  -- @
  SupR1ᴵ
    :: !(Proofᴵ pv)
    -- ^ A proof of @(Γ ; ⟨φ⟩) ⊢ᴵ ψ@
    -> Proofᴵ pv
    -- ^ A proof of @Γ ⊢ᴵ (φ ⊃ ψ)@

  -- |
  -- FIXME: doc
  --
  -- @
  --   Γ ⊢ᴵ ψ
  --   ───────────────────────────────────────── [⊃R₂ᴵ]
  --   Γ ⊢ᴵ (φ ⊃ ψ)
  -- @
  SupR2ᴵ
    :: !(Formula pv) -- FIXME: may be unnecessary
    -- ^ @φ@
    -> !(Proofᴵ pv)
    -- ^ A proof of @Γ ⊢ᴵ ψ@
    -> Proofᴵ pv
    -- ^ A proof of @Γ ⊢ᴵ (φ ⊃ ψ)@

  -- |
  -- FIXME: doc
  --
  -- @
  --   Γ ⊢ᴵ φ
  --   Δ ⊢ᴵ ψ
  --   ───────────────────────────────────────── [∧Rᴵ]
  --   (Γ ; Δ) ⊢ᴵ (φ ∧ ψ)
  -- @
  AndRᴵ
    :: !(Proofᴵ pv)
    -- ^ A proof of @Γ ⊢ᴵ φ@
    -> !(Proofᴵ pv)
    -- ^ A proof of @Δ ⊢ᴵ ψ@
    -> Proofᴵ pv
    -- ^ A proof of @(Γ ; Δ) ⊢ᴵ (φ ∧ ψ)@

  -- |
  -- FIXME: doc
  --
  -- @
  --   ⟨φ⟩ ⊆ Γ
  --   Γ ⊢ᴵ χ
  --   ───────────────────────────────────────── [∧L₁ᴵ]
  --   Γ[⟨φ⟩ ↦ ⟨φ ∧ ψ⟩] ⊢ᴵ χ
  -- @
  AndL1ᴵ
    :: !(Formula pv) -- FIXME: may be unnecessary
    -- ^ @φ@
    -> !(Formula pv) -- FIXME: may be unnecessary
    -- ^ @ψ@
    -> !(Proofᴵ pv)
    -- ^ A proof of @Γ ⊢ᴵ χ@
    -> Proofᴵ pv
    -- ^ A proof of @Γ[⟨φ⟩ ↦ ⟨φ ∧ ψ⟩] ⊢ᴵ χ@

  -- |
  -- FIXME: doc
  --
  -- @
  --   ⟨ψ⟩ ⊆ Γ
  --   Γ ⊢ᴵ χ
  --   ───────────────────────────────────────── [∧L₂ᴵ]
  --   Γ[⟨φ⟩ ↦ ⟨φ ∧ ψ⟩] ⊢ᴵ χ
  -- @
  AndL2ᴵ
    :: !(Formula pv) -- FIXME: may be unnecessary
    -- ^ @φ@
    -> !(Formula pv) -- FIXME: may be unnecessary
    -- ^ @ψ@
    -> !(Proofᴵ pv)
    -- ^ A proof of @Γ ⊢ᴵ χ@
    -> Proofᴵ pv
    -- ^ A proof of @Γ[⟨φ⟩ ↦ ⟨φ ∧ ψ⟩] ⊢ᴵ χ@

  -- |
  -- FIXME: doc
  --
  -- @
  --   Γ ⊢ᴵ φ
  --   ───────────────────────────────────────── [∨R₁ᴵ]
  --   Γ ⊢ᴵ (φ ∨ ψ)
  -- @
  OrR1ᴵ
    :: !(Proofᴵ pv)
    -- ^ A proof of @Γ ⊢ᴵ φ@
    -> Proofᴵ pv
    -- ^ A proof of @Γ ⊢ᴵ (φ ∨ ψ)@
  -- |
  -- FIXME: doc
  --
  -- @
  --   Γ ⊢ᴵ ψ
  --   ───────────────────────────────────────── [∨R₂ᴵ]
  --   Γ ⊢ᴵ (φ ∨ ψ)
  -- @
  OrR2ᴵ
    :: !(Proofᴵ pv)
    -- ^ A proof of @Γ ⊢ᴵ φ@
    -> Proofᴵ pv
    -- ^ A proof of @Γ ⊢ᴵ (φ ∨ ψ)@

  -- |
  -- FIXME: doc
  --
  -- @
  --   ⟨φ⟩ ⊆ Γ
  --   ⟨ψ⟩ ⊆ Δ
  --   fresh(p)
  --   Σ ∈ lubs(Γ[⟨φ⟩ ↦ ⟨p⟩])(Δ[⟨ψ⟩ ↦ ⟨p⟩])
  --   Γ ⊢ᴵ χ
  --   Δ ⊢ᴵ χ
  --   ───────────────────────────────────────── [∨Lᴵ]
  --   Σ[⟨p⟩ ↦ ⟨φ ∨ ψ⟩] ⊢ᴵ χ
  -- @
  OrLᴵ
    :: !(Formula pv) -- FIXME: may be unnecessary
    -- ^ @φ@
    -> !(Formula pv) -- FIXME: may be unnecessary
    -- ^ @ψ@
    -> !(Bunches pv) -- FIXME: may be unnecessary
    -- ^ @Γ@
    -> !(Bunches pv) -- FIXME: may be unnecessary
    -- ^ @Δ@
    -> !(Bunches (Maybe pv)) -- FIXME: may be unnecessary
    -- ^ @Σ(□)@
    -> !(Proofᴵ pv)
    -- ^ A proof of @Γ ⊢ᴵ χ@
    -> !(Proofᴵ pv)
    -- ^ A proof of @Δ ⊢ᴵ χ@
    -> Proofᴵ pv
    -- ^ A proof of @Σ[⟨p⟩ ↦ ⟨φ ∨ ψ⟩] ⊢ᴵ χ@

  -- |
  -- FIXME: doc
  --
  -- @
  --   (⟨φ⟩ , ⟨ψ⟩) ⊆ Γ
  --   Γ ⊢ᴵ χ
  --   ───────────────────────────────────────── [∗Lᴵ]
  --   Γ[(⟨φ⟩ , ⟨ψ⟩) ↦ ⟨φ ∗ ψ⟩] ⊢ᴵ χ
  -- @
  StarLᴵ
    :: !(Formula pv) -- FIXME: may be unnecessary
    -- ^ @φ@
    -> !(Formula pv) -- FIXME: may be unnecessary
    -- ^ @ψ@
    -> !(Bunches pv) -- FIXME: may be unnecessary
    -- ^ @Γ@
    -> !(Proofᴵ pv)
    -- ^ A proof of @Γ ⊢ᴵ χ@
    -> Proofᴵ pv
    -- ^ A proof of @Γ[(⟨φ⟩ , ⟨ψ⟩) ↦ ⟨φ ∗ ψ⟩] ⊢ᴵ χ@

  -- |
  -- FIXME: doc
  --
  -- @
  --   Γ ⊢ᴵ φ
  --   Δ ⊢ᴵ ψ
  --   ───────────────────────────────────────── [∗Rᴵ]
  --   (Γ , Δ) ⊢ᴵ (φ ∗ ψ)
  -- @
  StarRᴵ
    :: !(Proofᴵ pv)
    -- ^ A proof of @Γ ⊢ᴵ φ@
    -> !(Proofᴵ pv)
    -- ^ A proof of @Δ ⊢ᴵ ψ@
    -> Proofᴵ pv
    -- ^ A proof of @(Γ , Δ) ⊢ᴵ (φ ∗ ψ)@

  -- |
  -- FIXME: doc
  --
  -- @
  --   (Δ' , ⟨ψ⟩) ⊆ Δ
  --   Γ ⊢ᴵ φ
  --   Δ ⊢ᴵ χ
  --   ───────────────────────────────────────── [─∗Lᴵ]
  --   Δ[(Δ' , ⟨ψ⟩) ↦ (Δ' , Γ , ⟨φ ─∗ ψ⟩)] ⊢ᴵ χ
  -- @
  MagicLᴵ
    :: !(Formula pv) -- FIXME: may be unnecessary
    -- ^ @φ@
    -> !(Formula pv) -- FIXME: may be unnecessary
    -- ^ @ψ@
    -> !(Bunches pv) -- FIXME: may be unnecessary
    -- ^ @Γ@
    -> !(Bunches pv) -- FIXME: may be unnecessary
    -- ^ @Δ@
    -> !(Bunches pv) -- FIXME: may be unnecessary
    -- ^ @Δ'@
    -> !(Proofᴵ pv)
    -- ^ A proof of @Γ ⊢ᴵ φ@
    -> !(Proofᴵ pv)
    -- ^ A proof of @Δ ⊢ᴵ χ@
    -> Proofᴵ pv
    -- ^ A proof of @Δ[(Δ' , ⟨ψ⟩) ↦ (Δ' , Γ , ⟨φ ─∗ ψ⟩)] ⊢ᴵ χ@

  -- |
  -- FIXME: doc
  --
  -- @
  --   (Γ , ⟨φ⟩) ⊢ᴵ ψ
  --   ───────────────────────────────────────── [─∗Rᴵ]
  --   Γ ⊢ᴵ (φ ─∗ ψ)
  -- @
  MagicRᴵ
    :: !(Proofᴵ pv)
    -- ^ A proof of @(Γ , ⟨φ⟩) ⊢ᴵ ψ@
    -> Proofᴵ pv
    -- ^ A proof of @Γ ⊢ᴵ (φ ─∗ ψ)@

--------------------------------------------------------------------------------

subbunches :: Bunches pv -> [Bunches pv]
subbunches = undefined

replaceBunches
  :: HashMap (Bunches pv) (Bunches pv)
  -> Bunches pv
  -> Bunches pv
replaceBunches = undefined

--------------------------------------------------------------------------------

newtype MDatabase s pv
  = MDatabase (MHashSet s (Judgement pv))
  deriving ()

insertDatabase
  :: (Eq pv, Hashable pv, Generic pv)
  => MDatabase s pv
  -> Judgement pv
  -> ST s ()
insertDatabase (MDatabase mdb) = MHashSet.insert mdb

forDatabase
  :: (Eq pv, Hashable pv, Generic pv)
  => MDatabase s pv
  -> (Judgement pv -> ST s ())
  -> ST s ()
forDatabase (MDatabase mdb) = MHashSet.forM_ mdb

--------------------------------------------------------------------------------

applyInit :: (Eq pv, Hashable pv, Generic pv) => MDatabase s pv -> ST s ()
applyInit mdb = do
  undefined

applyC
  :: (Eq pv, Hashable pv, Generic pv)
  => MDatabase s pv -> ST s ()
applyC mdb = do
  mdb' <- MDatabase <$> MHashSet.new
  forDatabase mdb $ \(γ :⊢: φ) -> do
    let getAdditive (x :|: y) = Just (x, y)
        getAdditive _         = Nothing
    forM_ (mapMaybe getAdditive (subbunches γ)) $ \(δ1, δ2) -> do
      forM_ (HashSet.toList (lubs δ1 δ2)) $ \δ -> do
        let γ' = replaceBunches (HashMap.fromList [(δ1 :|: δ2, δ)]) γ
        insertDatabase mdb' (γ' :⊢: φ)
  forDatabase mdb' (insertDatabase mdb)

applyE
  :: (Eq pv, Hashable pv, Generic pv)
  => MDatabase s pv -> ST s ()
applyE mdb = do
  undefined

applySupL
  :: (Eq pv, Hashable pv, Generic pv)
  => MDatabase s pv -> ST s ()
applySupL mdb = do
  undefined

applySupR1
  :: (Eq pv, Hashable pv, Generic pv)
  => MDatabase s pv -> ST s ()
applySupR1 mdb = do
  undefined

applySupR2
  :: (Eq pv, Hashable pv, Generic pv)
  => MDatabase s pv -> ST s ()
applySupR2 mdb = do
  undefined

applyAndR
  :: (Eq pv, Hashable pv, Generic pv)
  => MDatabase s pv -> ST s ()
applyAndR mdb = do
  undefined

applyAndL1
  :: (Eq pv, Hashable pv, Generic pv)
  => MDatabase s pv -> ST s ()
applyAndL1 mdb = do
  undefined

applyAndL2
  :: (Eq pv, Hashable pv, Generic pv)
  => MDatabase s pv -> ST s ()
applyAndL2 mdb = do
  undefined

applyOrR1
  :: (Eq pv, Hashable pv, Generic pv)
  => MDatabase s pv -> ST s ()
applyOrR1 mdb = do
  undefined

applyOrR2
  :: (Eq pv, Hashable pv, Generic pv)
  => MDatabase s pv -> ST s ()
applyOrR2 mdb = do
  undefined

applyOrL
  :: (Eq pv, Hashable pv, Generic pv)
  => MDatabase s pv -> ST s ()
applyOrL mdb = do
  undefined

applyStarL
  :: (Eq pv, Hashable pv, Generic pv)
  => MDatabase s pv -> ST s ()
applyStarL mdb = do
  undefined

applyStarR
  :: (Eq pv, Hashable pv, Generic pv)
  => MDatabase s pv -> ST s ()
applyStarR mdb = do
  undefined

applyMagicL
  :: (Eq pv, Hashable pv, Generic pv)
  => MDatabase s pv -> ST s ()
applyMagicL mdb = do
  undefined

applyMagicR
  :: (Eq pv, Hashable pv, Generic pv)
  => MDatabase s pv -> ST s ()
applyMagicR mdb = do
  undefined

growDatabase
  :: (Eq pv, Hashable pv, Generic pv)
  => MDatabase s pv -> ST s ()
growDatabase mdb = do
  undefined

databaseContains
  :: (Eq pv, Hashable pv)
  => MDatabase s pv
  -> Judgement pv
  -> ST s Bool
databaseContains = undefined

--------------------------------------------------------------------------------

checkProof :: Proofᴵ pv -> Judgement pv -> Maybe (HashSet (Constraint pv))
checkProof = undefined

--------------------------------------------------------------------------------

proveTheorem :: Judgement pv -> Maybe (Proofᴵ pv)
proveTheorem = undefined

--------------------------------------------------------------------------------

exampleJudgement :: Judgement Variable
exampleJudgement
  = let (p, q, r) = (Variable 0, Variable 1, Variable 2)
    in Øₘ :⊢: ((p :∗: (q :∧: r)) :-∗: ((p :∧: q) :∗: (p :∧: r)))

--------------------------------------------------------------------------------

main :: IO ()
main = do
  pure ()

--------------------------------------------------------------------------------

{-#LANGUAGE FlexibleContexts, FlexibleInstances, MultiParamTypeClasses #-}
module Carnap.Languages.PurePropositional.Logic.Equivalence () where

import Data.Map as M (lookup, Map)
import Text.Parsec
import Carnap.Core.Data.Types (Form)
import Carnap.Languages.PurePropositional.Syntax
import Carnap.Languages.PurePropositional.Parser
import Carnap.Languages.PurePropositional.Util (dropOuterParens)
import Carnap.Calculi.NaturalDeduction.Syntax
import Carnap.Calculi.NaturalDeduction.Parser
import Carnap.Calculi.NaturalDeduction.Checker
import Carnap.Languages.ClassicalSequent.Syntax
import Carnap.Languages.ClassicalSequent.Parser
import Carnap.Languages.PurePropositional.Logic.Rules
import Carnap.Languages.Util.LanguageClasses

{-| A system for propositional logic resembling the basic proof system TFL
from the Calgary Remix of Forall x book
-}

data PropEquivalence = AndComm      | CommAnd 
                     | OrComm       | CommOr
                     | IffComm      | CommIff
                     | DNRep        | RepDN
                     | MCRep        | RepMC
                     | MCRep2       | RepMC2
                     | BiExRep      | RepBiEx
                     | AndAssoc     | AssocAnd
                     | OrAssoc      | AssocOr
                     | AndIdem      | IdemAnd
                     | OrIdem       | IdemOr
                     | OrDist       | DistOr
                     | AndDist      | DistAnd
                     | AndAbsorb    | AbsorbAnd
                     | OrAbsorb     | AbsorbOr
                     | NCRep        | RepNC
                     | DM1 | DM2 | DM3 | DM4
                     | Pr (Maybe [(ClassicalSequentOver PurePropLexicon (Sequent (Form Bool)))])
    deriving (Eq)

instance Inference PropEquivalence PurePropLexicon (Form Bool) where
        ruleOf AndComm = andCommutativity !! 0
        ruleOf CommAnd = andCommutativity !! 1
        ruleOf OrComm  = orCommutativity !! 0
        ruleOf CommOr  = orCommutativity !! 1
        ruleOf IffComm = iffCommutativity !! 0 
        ruleOf CommIff = iffCommutativity !! 1
        ruleOf DNRep = doubleNegation !! 0
        ruleOf RepDN = doubleNegation !! 1
        ruleOf MCRep = materialConditional !! 0
        ruleOf RepMC = materialConditional !! 1
        ruleOf MCRep2  = materialConditional !! 2
        ruleOf RepMC2  = materialConditional !! 3
        ruleOf BiExRep = biconditionalExchange !! 0
        ruleOf AndAssoc = andAssociativity !! 0
        ruleOf AssocAnd = andAssociativity !! 1
        ruleOf OrAssoc = orAssociativity !! 0 
        ruleOf AssocOr = orAssociativity !! 1
        ruleOf AndIdem = andIdempotence !! 0
        ruleOf IdemAnd = andIdempotence !! 1
        ruleOf OrIdem = orIdempotence !! 0
        ruleOf IdemOr = orIdempotence !! 1
        ruleOf OrDist = orDistributivity !! 0
        ruleOf DistOr = orDistributivity !! 1
        ruleOf AndDist = andDistributivity !! 0
        ruleOf DistAnd = andDistributivity !! 1
        ruleOf AndAbsorb = andAbsorption !! 0
        ruleOf AbsorbAnd = andAbsorption !! 1
        ruleOf OrAbsorb = orAbsorption !! 0
        ruleOf AbsorbOr = orAbsorption !! 1
        ruleOf NCRep = negatedConditional !! 0
        ruleOf RepNC = negatedConditional !! 1
        ruleOf RepBiEx = biconditionalExchange !! 1
        ruleOf DM1 = deMorgansLaws !! 0
        ruleOf DM2 = deMorgansLaws !! 1
        ruleOf DM3 = deMorgansLaws !! 2
        ruleOf DM4 = deMorgansLaws !! 3
        ruleOf (Pr _) = axiom

        globalRestriction _ _ _ = Nothing

        indirectInference _ = Nothing

        isPremise (Pr _) = True
        isPremise _ = False

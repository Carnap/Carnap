{-#LANGUAGE FlexibleContexts, FlexibleInstances, MultiParamTypeClasses #-}
module Carnap.Languages.PurePropositional.Logic.Equivalence (zachPropEqCalc, parseZachPropEq, ZachPropEq(..)) where

import Data.Char (toLower,toUpper)
import Text.Parsec
import Carnap.Core.Data.Types (Form)
import Carnap.Languages.PurePropositional.Syntax
import Carnap.Languages.PurePropositional.Parser
import Carnap.Languages.PurePropositional.Util (dropOuterParens)
import Carnap.Calculi.Util
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

data ZachPropEq = AndComm      | CommAnd 
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
                | OrDistL      | DistOrL
                | OrDistR      | DistOrR
                | AndDistL     | DistAndL
                | AndDistR     | DistAndR
                | AndAbsorb1   | AbsorbAnd1
                | AndAbsorb2   | AbsorbAnd2
                | AndAbsorb3   | AbsorbAnd3
                | AndAbsorb4   | AbsorbAnd4
                | OrAbsorb1    | AbsorbOr1
                | OrAbsorb2    | AbsorbOr2
                | OrAbsorb3    | AbsorbOr3
                | OrAbsorb4    | AbsorbOr4
                | NCRep        | RepNC
                | Simp1  | Simp2  | Simp3  | Simp4  | Simp5  | Simp6  | Simp7  | Simp8  | Simp9  | Simp10 
                | Simp11 | Simp12 | Simp13 | Simp14 | Simp15 | Simp16 | Simp17 | Simp18 | Simp19 | Simp20 
                | Simp21 | Simp22 | Simp23 | Simp24 | Simp25 | Simp26 | Simp27 | Simp28 | Simp29 | Simp30 
                | Simp31 | Simp32
                | DM1 | DM2 | DM3 | DM4
                | Pr (Maybe [(ClassicalSequentOver PurePropLexicon (Sequent (Form Bool)))])
    deriving (Eq)

instance Show ZachPropEq where
        show AndComm = "Comm"
        show CommAnd = "Comm"
        show OrComm  = "Comm"
        show CommOr  = "Comm"
        show IffComm = "Comm"
        show CommIff = "Comm"
        show DNRep   = "DN"
        show RepDN   = "DN"
        show MCRep   = "Cond"
        show RepMC   = "Cond"
        show MCRep2  = "Cond"
        show RepMC2  = "Cond"
        show NCRep = "Cond"
        show RepNC = "Cond"
        show BiExRep = "Bicond"
        show RepBiEx = "Bicond"
        show DM1     = "DeM"
        show DM2     = "DeM"
        show DM3     = "DeM"
        show DM4     = "DeM"
        show AndAssoc = "Assoc"
        show AssocAnd = "Assoc"
        show OrAssoc  = "Assoc"
        show AssocOr = "Assoc"
        show AndIdem = "Id"
        show IdemAnd = "Id"
        show OrIdem = "Id"
        show IdemOr = "Id"
        show OrDistL = "Dist"
        show DistOrL = "Dist"
        show AndDistL = "Dist"
        show DistAndL = "Dist"
        show OrDistR = "Dist"
        show DistOrR = "Dist"
        show AndDistR = "Dist"
        show DistAndR = "Dist"
        show AndAbsorb1 = "Abs"
        show AbsorbAnd1 = "Abs"
        show AndAbsorb2 = "Abs"
        show AbsorbAnd2 = "Abs"
        show AndAbsorb3 = "Abs"
        show AbsorbAnd3 = "Abs"
        show AndAbsorb4 = "Abs"
        show AbsorbAnd4 = "Abs"
        show OrAbsorb1 = "Abs"
        show AbsorbOr1 = "Abs"
        show OrAbsorb2 = "Abs"
        show AbsorbOr2 = "Abs"
        show OrAbsorb3 = "Abs"
        show AbsorbOr3 = "Abs"
        show OrAbsorb4 = "Abs"
        show AbsorbOr4 = "Abs"
        show Simp1 = "Simp"
        show Simp2 = "Simp"
        show Simp3 = "Simp"
        show Simp4 = "Simp"
        show Simp5 = "Simp"
        show Simp6 = "Simp"
        show Simp7 = "Simp"
        show Simp8 = "Simp"
        show Simp9 = "Simp"
        show Simp10 = "Simp"
        show Simp11 = "Simp"
        show Simp12 = "Simp"
        show Simp13 = "Simp"
        show Simp14 = "Simp"
        show Simp15 = "Simp"
        show Simp16 = "Simp"
        show Simp17 = "Simp"
        show Simp18 = "Simp"
        show Simp19 = "Simp"
        show Simp20 = "Simp"
        show Simp21 = "Simp"
        show Simp22 = "Simp"
        show Simp23 = "Simp"
        show Simp24 = "Simp"
        show Simp25 = "Simp"
        show Simp26 = "Simp"
        show Simp27 = "Simp"
        show Simp28 = "Simp"
        show Simp29 = "Simp"
        show Simp30 = "Simp"
        show Simp31 = "Simp"
        show Simp32 = "Simp"
        show (Pr _) = "Pr"

instance Inference ZachPropEq PurePropLexicon (Form Bool) where
        ruleOf AndComm = andCommutativity !! 0
        ruleOf CommAnd = andCommutativity !! 1
        ruleOf OrComm = orCommutativity !! 0
        ruleOf CommOr = orCommutativity !! 1
        ruleOf IffComm = iffCommutativity !! 0 
        ruleOf CommIff = iffCommutativity !! 1
        ruleOf DNRep = doubleNegation !! 0
        ruleOf RepDN = doubleNegation !! 1
        ruleOf MCRep = materialConditional !! 0
        ruleOf RepMC = materialConditional !! 1
        ruleOf MCRep2 = materialConditional !! 2
        ruleOf RepMC2 = materialConditional !! 3
        ruleOf BiExRep = biconditionalExchange !! 0
        ruleOf AndAssoc = andAssociativity !! 0
        ruleOf AssocAnd = andAssociativity !! 1
        ruleOf OrAssoc = orAssociativity !! 0 
        ruleOf AssocOr = orAssociativity !! 1
        ruleOf AndIdem = andIdempotence !! 0
        ruleOf IdemAnd = andIdempotence !! 1
        ruleOf OrIdem = orIdempotence !! 0
        ruleOf IdemOr = orIdempotence !! 1
        ruleOf OrDistL = orDistributivity !! 0
        ruleOf DistOrL = orDistributivity !! 1
        ruleOf OrDistR = orDistributivity !! 2
        ruleOf DistOrR = orDistributivity !! 3
        ruleOf AndDistL = andDistributivity !! 0
        ruleOf DistAndL = andDistributivity !! 1
        ruleOf AndDistR = andDistributivity !! 2
        ruleOf DistAndR = andDistributivity !! 3
        ruleOf AndAbsorb1 = andAbsorption !! 0
        ruleOf AbsorbAnd1 = andAbsorption !! 1
        ruleOf AndAbsorb2 = andAbsorption !! 2
        ruleOf AbsorbAnd2 = andAbsorption !! 3
        ruleOf AndAbsorb3 = andAbsorption !! 4
        ruleOf AbsorbAnd3 = andAbsorption !! 5
        ruleOf AndAbsorb4 = andAbsorption !! 6
        ruleOf AbsorbAnd4 = andAbsorption !! 7
        ruleOf OrAbsorb1 = orAbsorption !! 0
        ruleOf AbsorbOr1 = orAbsorption !! 1
        ruleOf OrAbsorb2 = orAbsorption !! 2
        ruleOf AbsorbOr2 = orAbsorption !! 3
        ruleOf OrAbsorb3 = orAbsorption !! 4
        ruleOf AbsorbOr3 = orAbsorption !! 5
        ruleOf OrAbsorb4 = orAbsorption !! 6
        ruleOf AbsorbOr4 = orAbsorption !! 7
        ruleOf NCRep = negatedConditional !! 0
        ruleOf RepNC = negatedConditional !! 1
        ruleOf RepBiEx = biconditionalExchange !! 1
        ruleOf DM1 = deMorgansLaws !! 0
        ruleOf DM2 = deMorgansLaws !! 1
        ruleOf DM3 = deMorgansLaws !! 2
        ruleOf DM4 = deMorgansLaws !! 3
        ruleOf Simp1 = andTautCancellation !! 0
        ruleOf Simp2 = andTautCancellation !! 1 
        ruleOf Simp3 = andTautCancellation !! 2 
        ruleOf Simp4 = andTautCancellation !! 3 
        ruleOf Simp5 = andTautCancellation !! 4 
        ruleOf Simp6 = andTautCancellation !! 5 
        ruleOf Simp7 = andTautCancellation !! 6 
        ruleOf Simp8 = andTautCancellation !! 7 
        ruleOf Simp9 = orTautCancellation !! 0
        ruleOf Simp10 = orTautCancellation !! 1
        ruleOf Simp11 = orTautCancellation !! 2
        ruleOf Simp12 = orTautCancellation !! 3
        ruleOf Simp13 = orTautCancellation !! 4
        ruleOf Simp14 = orTautCancellation !! 5
        ruleOf Simp15 = orTautCancellation !! 6
        ruleOf Simp16 = orTautCancellation !! 7
        ruleOf Simp17 = andContCancellation !! 0
        ruleOf Simp18 = andContCancellation !! 1
        ruleOf Simp19 = andContCancellation !! 2
        ruleOf Simp20 = andContCancellation !! 3
        ruleOf Simp21 = andContCancellation !! 4
        ruleOf Simp22 = andContCancellation !! 5
        ruleOf Simp23 = andContCancellation !! 6
        ruleOf Simp24 = andContCancellation !! 7
        ruleOf Simp25 = orContCancellation !! 0
        ruleOf Simp26 = orContCancellation !! 1
        ruleOf Simp27 = orContCancellation !! 2
        ruleOf Simp28 = orContCancellation !! 3
        ruleOf Simp29 = orContCancellation !! 4
        ruleOf Simp30 = orContCancellation !! 5
        ruleOf Simp31 = orContCancellation !! 6
        ruleOf Simp32 = orContCancellation !! 7
        ruleOf (Pr _) = axiom

        restriction (Pr prems) = Just (premConstraint prems)
        restriction _ = Nothing

        isPremise (Pr _) = True
        isPremise _ = False

parseZachPropEq :: RuntimeDeductionConfig PurePropLexicon (Form Bool) -> Parsec String u [ZachPropEq]
parseZachPropEq rtc = do 
        r <- choice (map (try . caseInsensitiveString) ["Comm", "DN", "Cond", "Bicond", "DeM", "Assoc", "Abs", "Id","Dist","PR", "Simp"])
        return $ case map toLower r of
            "comm"-> [AndComm,CommAnd,OrComm,CommOr,IffComm,CommIff]
            "dn" -> [DNRep,RepDN]
            "cond" -> [MCRep,MCRep2,RepMC,RepMC2, NCRep, RepNC]
            "bicond" -> [BiExRep,RepBiEx]
            "assoc" -> [AndAssoc, AssocAnd, OrAssoc, AssocOr]
            "id" -> [AndIdem,IdemAnd,OrIdem,IdemOr]
            "abs" -> [AndAbsorb1,AbsorbAnd1,OrAbsorb1,AbsorbOr1
                     ,AndAbsorb2,AbsorbAnd2,OrAbsorb2,AbsorbOr2
                     ,AndAbsorb3,AbsorbAnd3,OrAbsorb3,AbsorbOr3
                     ,AndAbsorb4,AbsorbAnd4,OrAbsorb4,AbsorbOr4
                     ]
            "simp" -> [Simp1, Simp2, Simp3, Simp4, Simp5, Simp6, Simp7, Simp8, Simp9, Simp10
                      , Simp11, Simp12, Simp13, Simp14, Simp15, Simp16, Simp17, Simp18, Simp19, Simp20
                      , Simp21, Simp22, Simp23, Simp24, Simp25, Simp26, Simp27, Simp28, Simp29, Simp30
                      , Simp31, Simp32 ]
            "dist" -> [OrDistR, DistOrR, AndDistR, DistAndR, OrDistL,DistOrL,AndDistL,DistAndL]
            "dem" -> [DM1,DM2,DM3,DM4]
            "pr" -> [Pr (problemPremises rtc)]
    where caseInsensitiveChar c = char (toLower c) <|> char (toUpper c)
          caseInsensitiveString s = try (mapM caseInsensitiveChar s) <?> "\"" ++ s ++ "\""

parseZachPropEqProof :: RuntimeDeductionConfig PurePropLexicon (Form Bool) -> String -> [DeductionLine ZachPropEq PurePropLexicon (Form Bool)]
parseZachPropEqProof rtc = toDeductionHilbertImplicit (parseZachPropEq rtc) (purePropFormulaParser thomasBolducZachOpts)

zachPropEqCalc = mkNDCalc 
    { ndRenderer = NoRender
    , ndParseProof = parseZachPropEqProof
    , ndProcessLine = hoProcessLineHilbertImplicit
    , ndProcessLineMemo = Just hoProcessLineHilbertImplicitMemo
    , ndParseSeq = parseSeqOver (purePropFormulaParser thomasBolducZachOpts)
    , ndParseForm = (purePropFormulaParser thomasBolducZachOpts)
    , ndNotation = dropBotRight . dropOuterParens 
    }

dropBotRight s = case (break (== '⊢') s) of
      (a,"⊢ ⊥") -> a ++ "⊢ ?"
      _ -> s

{-# LANGUAGE TemplateHaskell #-}

module ParlorGame where

import Control.Lens.TH
import Data.Function ((&))
import Data.Functor ((<&>))
import GHC.Generics (Generic)
import Kanren.Core
import Kanren.Goal
import Kanren.LogicalBase (LogicMaybe (..))
import Kanren.Match
import Kanren.TH
import Prettyprinter
import Prelude hiding (pred)

data Color = Blue | White | Black
  deriving stock (Generic, Show, Eq)

makeLogicals [''Color]
makePrisms ''LogicColor

deriving instance Show LogicColor

data Box = Box
  { color :: Color,
    -- | Whether the box says something true, false or nothing at all
    veracity :: Maybe Bool,
    -- | Whether the box has the gems or is empty
    gems :: Bool
  }
  deriving stock (Generic, Show, Eq)

makeLogicals [''Box]
makePrisms ''LogicBox

deriving instance Show LogicBox

type Boxes = (Box, Box, Box)

type LogicBoxes = (Term Box, Term Box, Term Box)

prettySolutions :: [LogicBoxes] -> Doc ()
prettySolutions solutions = vsep $ prettySolution <$> zip solutions [1 ..]
  where
    prettySolution (boxes, i :: Int) = pretty i <> pretty ":" <> nest 4 (line <> prettyBoxes boxes)

prettyBoxes :: LogicBoxes -> Doc ()
prettyBoxes (b1, b2, b3) = vsep $ prettyBox <$> [b1, b2, b3]

prettyBox :: Term Box -> Doc ()
prettyBox (Var varId) = fill 10 $ pretty "?BOX" <> angles (unsafeViaShow varId)
prettyBox (Value (LogicBox color veracity hasGems)) =
  fill 10 (pretty "BOX" <+> prettyColor color)
    <+> hsep
      ( fill 12
          <$> [ prettyVeracity veracity,
                prettyGems hasGems
              ]
      )
  where
    prettyGems :: Term Bool -> Doc ()
    prettyGems (Var varId) = pretty "?HASGEMS" <> angles (unsafeViaShow varId)
    prettyGems (Value True) = pretty "HAS GEMS"
    prettyGems (Value False) = pretty "HAS NO GEMS"
    prettyVeracity :: Term (Maybe Bool) -> Doc ()
    prettyVeracity (Var varId) = pretty "?SAYS" <> angles (unsafeViaShow varId)
    prettyVeracity (Value LogicNothing) = pretty "SAYS NOTHING"
    prettyVeracity (Value (LogicJust (Var varId))) = pretty "?ISTRUE" <> angles (unsafeViaShow varId)
    prettyVeracity (Value (LogicJust (Value True))) = pretty "IS TRUE"
    prettyVeracity (Value (LogicJust (Value False))) = pretty "IS FALSE"

prettyColor :: Term Color -> Doc ()
prettyColor (Var varId) = pretty "?COLOR" <> angles (unsafeViaShow varId)
prettyColor (Value LogicBlue) = pretty "BLUE"
prettyColor (Value LogicWhite) = pretty "WHITE"
prettyColor (Value LogicBlack) = pretty "BLACK"

data Sentence
  = -- | A sentence saying something about a box
    MkSentence Noun Verb
  deriving stock (Show)

data Noun
  = -- Boxes by Proximity
    ThisBox
  | BoxNextToThisOne
  | BothBoxesNextToThisOne
  | -- Boxes by color
    TheBoxWithColor Color
  | -- Boxes by truth value
    ATrueBox
  | AFalseBox
  | ASilentBox
  deriving stock (Show)

data Verb
  = IsTrue
  | IsFalse
  | ContainsGems
  deriving stock (Show)

type NegatableGoal = Term Bool -> Goal ()

-- Utility predicates

boxTuple :: Term Box -> (Term Color, Term (Maybe Bool), Term Bool) -> Goal ()
boxTuple b (color, veracity, hasGems) = b & (matche & on _LogicBox (\(color', veracity', hasGems') -> do color === color'; veracity === veracity'; hasGems === hasGems'))

boxColor :: Term Box -> Term Color -> Goal ()
boxColor b color = do
  (veracity, hasGems) <- fresh
  boxTuple b (color, veracity, hasGems)

boxColor' :: Term Box -> Color -> Goal ()
boxColor' b color = boxColor b (inject' color)

boxVeracity :: Term Box -> Term (Maybe Bool) -> Goal ()
boxVeracity b veracity = do
  (color, hasGems) <- fresh
  boxTuple b (color, veracity, hasGems)

boxVeracity' :: Term Box -> Maybe Bool -> Goal ()
boxVeracity' b veracity = boxVeracity b (inject' veracity)

boxGems :: Term Box -> Term Bool -> Goal ()
boxGems b gems = do
  (color, veracity) <- fresh
  boxTuple b (color, veracity, gems)

boxGems' :: Term Box -> Bool -> Goal ()
boxGems' b gems = boxGems b (inject' gems)

-- Rules

{-- | At least one box tells the truth and at least one lies.
      This gets more complicated because some boxes may not say anything at all.
      If: all boxes say something, then
      * One box lies/says the truth alone and the other two lie/say the
        truth together.
      If: one box says nothing, then
      * The other two boxes say the truth and lie
--}
veracityRule :: LogicBoxes -> Goal ()
veracityRule bs =
  disj
    do
      disjMany $
        cycle3 bs <&> \(b1, b2, b3) -> do
          (alone, together) <- fresh
          alone =/= together
          boxVeracity b1 (Value $ LogicJust alone)
          boxVeracity b2 (Value $ LogicJust together)
          boxVeracity b3 (Value $ LogicJust together)
    do
      disjMany $
        perms3 bs <&> \(b1, b2, b3) -> do
          boxVeracity' b1 (Just True)
          boxVeracity' b2 (Just False)
          boxVeracity' b3 Nothing

cycle3, perms3 :: (a, a, a) -> [(a, a, a)]
cycle3 (a, b, c) = [(a, b, c), (b, c, a), (c, a, b)]
perms3 (a, b, c) = [(a, b, c), (a, c, b), (b, a, c), (b, c, a), (c, a, b), (c, b, a)]

-- | Only one box has the gems, the others do not.
gemsRule :: LogicBoxes -> Goal ()
gemsRule bs =
  disjMany $
    cycle3 bs <&> \(b1, b2, b3) -> do
      boxGems' b1 True
      boxGems' b2 False
      boxGems' b3 False

-- We test if the game rules work as expected.
-- We count the configurations:

-- * Choose which box is true (3 choices)

-- * Choose if the other two boxes are: False-False, False-Nothing or Nothing-False (3 choices)

-- * Choose which box has the gems (3 choices)

-- Total: 3 * 3 * 3 = 27 configurations
-- >>> length (run \bs -> veracityRule bs >> gemsRule bs)
-- 27

{-- | Given a box, it generates a predicate involving the 3 boxes.

      When the box is truthful, the predicate will hold if the sentence holds.
      When the box is deceiving, the predicate holds if the sentence DOES NOT hold.
--}
translateSentence :: Color -> Sentence -> LogicBoxes -> Goal ()
translateSentence color sentence boxes = do
  case sentence of
    MkSentence ThisBox verb -> boxVeracityPredicate thisBox (verbRule verb thisBox)
    MkSentence BoxNextToThisOne verb -> boxVeracityPredicate thisBox (forAtLeastOne (verbRule verb) neighbors)
    MkSentence BothBoxesNextToThisOne verb -> boxVeracityPredicate thisBox (forAll (verbRule verb) others)
    MkSentence (TheBoxWithColor c) verb -> boxVeracityPredicate thisBox (verbRule verb (box c))
    MkSentence ATrueBox verb -> boxVeracityPredicate thisBox (forAtLeastOne (trueBoxPredicate (verbRule verb)) allBoxes)
    MkSentence AFalseBox verb -> boxVeracityPredicate thisBox (forAtLeastOne (falseBoxPredicate (verbRule verb)) allBoxes)
    MkSentence ASilentBox verb -> boxVeracityPredicate thisBox (forAtLeastOne (silentBoxPredicate (verbRule verb)) allBoxes)
  where
    -- The box showing this sentence
    thisBox = box color
    -- The box with the given colour
    box :: Color -> Term Box
    box = \case
      Blue -> b1
      White -> b2
      Black -> b3
    -- The boxes immediately next to this one
    neighbors = case color of
      Blue -> box <$> [White]
      White -> box <$> [Blue, Black]
      Black -> box <$> [White]
    -- The other boxes
    others = case color of
      Blue -> box <$> [White, Black]
      White -> box <$> [Blue, Black]
      Black -> box <$> [Blue, White]
    allBoxes = [b1, b2, b3]
    (b1, b2, b3) = boxes

-- It's true if the veracity of the predicate matches the veracity of the box
boxVeracityPredicate :: Term Box -> NegatableGoal -> Goal ()
boxVeracityPredicate b p = do
  boxVer <- fresh
  boxVeracity b (Value $ LogicJust boxVer)
  p boxVer

-- It's true if the box is true/false/silent and the predicate holds
trueBoxPredicate, falseBoxPredicate, silentBoxPredicate :: (Term Box -> NegatableGoal) -> Term Box -> NegatableGoal
trueBoxPredicate pred b veracity =
  disj
    do
      veracity === Value True
      boxVeracity b (inject' $ Just True)
      pred b (Value True)
    do
      veracity === Value False
      disj
        do
          -- either the box is false/silent
          boxVer <- fresh
          boxVer =/= inject' (Just True)
          boxVeracity b boxVer
        do
          -- or the predicate is false
          pred b (Value False)
falseBoxPredicate pred b veracity =
  disj
    do
      veracity === Value True
      boxVeracity b (inject' $ Just False)
      pred b (Value True)
    do
      veracity === Value False
      disj
        do
          -- either the box is true/silent
          boxVer <- fresh
          boxVer =/= inject' (Just False)
          boxVeracity b boxVer
        do
          -- or the predicate is false
          pred b (Value False)
silentBoxPredicate pred b veracity =
  disj
    do
      veracity === Value True
      boxVeracity b (inject' Nothing)
      pred b (Value True)
    do
      veracity === Value False
      disj
        do
          -- either the box is true/false
          boxVer <- fresh
          boxVer =/= inject' Nothing
          boxVeracity b boxVer
        do
          -- or the predicate is false
          pred b (Value False)

translateSentence' :: Color -> Maybe Sentence -> LogicBoxes -> Goal ()
translateSentence' c sentence' boxes@(b1, b2, b3) =
  let getBox Blue = b1
      getBox White = b2
      getBox Black = b3
   in case sentence' of
        Just sentence -> translateSentence c sentence boxes
        Nothing -> boxVeracity' (getBox c) Nothing

-- We test the translations:
-- ThisBox
-- >>> let bs = (inject' $ Box Blue (Just True) True, inject' $ Box White (Just False) False, inject' $ Box Black Nothing False)
-- >>> run $ \() -> translateSentence Blue (MkSentence ThisBox IsTrue) bs
-- [()]
-- >>> run $ \() -> translateSentence Blue (MkSentence ThisBox IsFalse) bs
-- []

-- BoxNextToThisOne
-- >>> let bs = (inject' $ Box Blue (Just False) True, inject' $ Box White (Just True) False, inject' $ Box Black (Just False) False)
-- >>> run $ \() -> translateSentence White (MkSentence BoxNextToThisOne IsFalse) bs
-- [(),()]

-- Helpers for writing predicates that hold existentially or universally.
-- We apply Morgan's laws to be able to negate the entire predicate and still have
-- a constructive proof.
-- This is equivalent to converting the whole predicate into a _NNF_ (Negated Normal Form).
forAtLeastOne :: forall a. (a -> NegatableGoal) -> [a] -> NegatableGoal
forAtLeastOne p as veracity =
  disj
    (veracity === Value True >> disjMany (flip p veracity <$> as))
    (veracity === Value False >> conjMany (flip p veracity <$> as))

-- We test forAtLeastOne
-- >>> let i = inject'
-- >>> let eq3 n ver = disj (ver === i True >> n === i 3) (ver =/= i True >> n =/= 3)
-- >>> run $ \() -> forAtLeastOne eq3 (i <$> [1, 2, 3 :: Int]) (inject' True)
-- [()]
-- >>> run $ \() -> forAtLeastOne eq3 (i <$> [3, 2, 3 :: Int]) (inject' True)
-- [(),()]
-- >>> run $ \() -> forAtLeastOne eq3 (i <$> [1, 1, 1 :: Int]) (inject' True)
-- []
-- >>> run $ \() -> forAtLeastOne eq3 (i <$> [1, 1, 1 :: Int]) (inject' False)
-- [()]
-- >>> run $ \() -> forAtLeastOne eq3 (i <$> [3, 1, 1 :: Int]) (inject' False)
-- []
-- >>> run $ \() -> forAtLeastOne eq3 (i <$> [3, 3, 3 :: Int]) (inject' False)
-- []

forAll :: forall a. (a -> NegatableGoal) -> [a] -> NegatableGoal
forAll p as veracity =
  disj
    (veracity === Value True >> conjMany (flip p veracity <$> as))
    (veracity === Value False >> disjMany (flip p veracity <$> as))

-- | Generates a predicate involving the box based on the verb and the truth
--   value of the verb.
verbRule :: Verb -> Term Box -> NegatableGoal
verbRule verb box sentenceVeracity = do
  case verb of
    IsTrue ->
      disj
        do
          sentenceVeracity === Value True
          boxVeracity' box (Just True)
        do
          sentenceVeracity === Value False
          boxFalseOrSilent box
    IsFalse -> do
      disj
        do
          sentenceVeracity === Value True
          boxVeracity' box (Just False)
        do
          sentenceVeracity === Value False
          boxTrueOrSilent box
    ContainsGems -> do
      boxGems box sentenceVeracity
  where
    boxFalseOrSilent, boxTrueOrSilent :: Term Box -> Goal ()
    boxFalseOrSilent b =
      disj
        do boxVeracity' b (Just False)
        do boxVeracity' b Nothing
    boxTrueOrSilent b =
      disj
        do boxVeracity' b (Just True)
        do boxVeracity' b Nothing

-- We test the verb rule
-- >>> let b = inject' $ Box Blue (Just True) False
-- >>> run $ \() -> verbRule IsTrue b (inject' True)
-- [()]
-- >>> run $ \() -> verbRule IsTrue b (inject' False)
-- []
-- >>> run $ \() -> verbRule IsFalse b (inject' True)
-- []
-- >>> run $ \() -> verbRule IsFalse b (inject' False)
-- [()]
-- >>> run $ \() -> verbRule ContainsGems b (inject' True)
-- []
-- >>> run $ \() -> verbRule ContainsGems b (inject' False)
-- [()]

-- We test again, but in the opposite direction: we see if the sentence is true based on the box
-- >>> run $ \sentenceVer -> do; b <- fresh; boxColor' b Blue; boxVeracity' b (Just True); verbRule IsTrue b sentenceVer
-- [True]

-- | Not really a rule, just assigns colors by order
colorRule :: LogicBoxes -> Goal ()
colorRule (b1, b2, b3) = do
  boxColor b1 $ inject' Blue
  boxColor b2 $ inject' White
  boxColor b3 $ inject' Black

-- | All the game rules
gameRules :: LogicBoxes -> Goal ()
gameRules boxes = conjMany $ ($ boxes) <$> [colorRule, gemsRule, veracityRule]

solve :: Maybe Sentence -> Maybe Sentence -> Maybe Sentence -> LogicBoxes -> Goal ()
solve s1 s2 s3 boxes = do
  colorRule boxes
  gemsRule boxes
  veracityRule boxes
  translateSentence' Blue s1 boxes
  translateSentence' White s2 boxes
  translateSentence' Black s3 boxes

solve' :: Maybe Sentence -> Maybe Sentence -> Maybe Sentence -> [LogicBoxes]
solve' s1 s2 s3 = run $ \boxes -> solve s1 s2 s3 boxes

s11, s12, s13 :: Maybe Sentence
s11 = Just $ MkSentence BoxNextToThisOne ContainsGems
s12 = Just $ MkSentence BothBoxesNextToThisOne ContainsGems
s13 = Just $ MkSentence BoxNextToThisOne IsTrue

-- >>> prettySolutions $ solve' s11 s12 s13
-- 1:
--     BOX BLUE   IS TRUE      HAS NO GEMS
--     BOX WHITE  IS FALSE     HAS GEMS
--     BOX BLACK  IS FALSE     HAS NO GEMS
-- 2:
--     BOX BLUE   IS TRUE      HAS NO GEMS
--     BOX WHITE  IS FALSE     HAS GEMS
--     BOX BLACK  IS FALSE     HAS NO GEMS

s21, s22, s23 :: Maybe Sentence
s21 = Just $ MkSentence BoxNextToThisOne ContainsGems
s22 = Nothing
s23 = Just $ MkSentence BoxNextToThisOne IsFalse

-- >>> prettySolutions $ solve' s21 s22 s23
-- 1:
--     BOX BLUE   IS TRUE      HAS NO GEMS
--     BOX WHITE  SAYS NOTHING HAS GEMS
--     BOX BLACK  IS FALSE     HAS NO GEMS

s31, s32, s33 :: Maybe Sentence
s31 = Just $ MkSentence AFalseBox ContainsGems
s32 = Just $ MkSentence (TheBoxWithColor Blue) IsTrue
s33 = Just $ MkSentence (TheBoxWithColor Blue) ContainsGems

-- We try the third puzzle:
-- >>> prettySolutions $ solve' s31 s32 s33
-- 1:
--     BOX BLUE   IS TRUE      HAS NO GEMS
--     BOX WHITE  IS TRUE      HAS NO GEMS
--     BOX BLACK  IS FALSE     HAS GEMS
--

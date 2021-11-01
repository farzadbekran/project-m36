{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE RecordWildCards #-}

module ProjectM36.AtomFunctions.ConstraintFunctions where

import           ProjectM36.AtomFunctionError
import           ProjectM36.Base
import           System.IO.Unsafe
import qualified Data.Map.Strict as Map
import qualified Data.Text as T
import qualified Data.List as L
import qualified Text.Fuzzy as FZ
import qualified Data.HashSet as HS

-- | Maybe Int -> Maybe Int -> Int -> Either AtomFunctionError Bool
-- min -> max -> value -> result
checkIntConstraint :: [Atom] -> Either AtomFunctionError Atom
checkIntConstraint (mMin:mMax:val:_) = case val of
  IntAtom v -> case (mMin, mMax) of
    ( ConstructedAtom "Just" _ [IntAtom mn]
      , ConstructedAtom "Just" _ [IntAtom mx])
      -> pure $ BoolAtom $ v >= mn && v <= mx
    ( ConstructedAtom "Just" _ [IntAtom mm]
      , ConstructedAtom "Nothing" _ []) -> pure $ BoolAtom $ v >= mm
    ( ConstructedAtom "Nothing" _ []
      , ConstructedAtom "Just" _ [IntAtom mx]) -> pure $ BoolAtom $ v <= mx
    ( ConstructedAtom "Nothing" _ []
      , ConstructedAtom "Nothing" _ []) -> pure $ BoolAtom True
    (_, _) -> Left AtomFunctionTypeMismatchError
  _         -> Left AtomFunctionTypeMismatchError
checkIntConstraint _ = Left AtomFunctionTypeMismatchError

-- | Maybe Integer -> Maybe Integer -> Integer -> Either AtomFunctionError Bool
-- min -> max -> value -> result
checkIntegerConstraint :: [Atom] -> Either AtomFunctionError Atom
checkIntegerConstraint (mMin:mMax:val:_) = case val of
  IntegerAtom v -> case (mMin, mMax) of
    ( ConstructedAtom "Just" _ [IntegerAtom mn]
      , ConstructedAtom "Just" _ [IntegerAtom mx])
      -> pure $ BoolAtom $ v >= mn && v <= mx
    ( ConstructedAtom "Just" _ [IntegerAtom mm]
      , ConstructedAtom "Nothing" _ []) -> pure $ BoolAtom $ v >= mm
    ( ConstructedAtom "Nothing" _ []
      , ConstructedAtom "Just" _ [IntegerAtom mx]) -> pure $ BoolAtom $ v <= mx
    ( ConstructedAtom "Nothing" _ []
      , ConstructedAtom "Nothing" _ []) -> pure $ BoolAtom True
    (_, _) -> Left AtomFunctionTypeMismatchError
  _ -> Left AtomFunctionTypeMismatchError
checkIntegerConstraint _ = Left AtomFunctionTypeMismatchError

-- | Maybe Double -> Maybe Double -> Double -> Either AtomFunctionError Bool
-- min -> max -> value -> result
checkDoubleConstraint :: [Atom] -> Either AtomFunctionError Atom
checkDoubleConstraint (mMin:mMax:val:_) = case val of
  DoubleAtom v -> case (mMin, mMax) of
    ( ConstructedAtom "Just" _ [DoubleAtom mn]
      , ConstructedAtom "Just" _ [DoubleAtom mx])
      -> pure $ BoolAtom $ v >= mn && v <= mx
    ( ConstructedAtom "Just" _ [DoubleAtom mm]
      , ConstructedAtom "Nothing" _ []) -> pure $ BoolAtom $ v >= mm
    ( ConstructedAtom "Nothing" _ []
      , ConstructedAtom "Just" _ [DoubleAtom mx]) -> pure $ BoolAtom $ v <= mx
    ( ConstructedAtom "Nothing" _ []
      , ConstructedAtom "Nothing" _ []) -> pure $ BoolAtom True
    (_, _) -> Left AtomFunctionTypeMismatchError
  _ -> Left AtomFunctionTypeMismatchError
checkDoubleConstraint _ = Left AtomFunctionTypeMismatchError

-- | Maybe Day -> Maybe Day -> Day -> Either AtomFunctionError Bool
-- min -> max -> value -> result
checkDayConstraint :: [Atom] -> Either AtomFunctionError Atom
checkDayConstraint (mMin:mMax:val:_) = case val of
  DayAtom v -> case (mMin, mMax) of
    ( ConstructedAtom "Just" _ [DayAtom mn]
      , ConstructedAtom "Just" _ [DayAtom mx])
      -> pure $ BoolAtom $ v >= mn && v <= mx
    ( ConstructedAtom "Just" _ [DayAtom mm]
      , ConstructedAtom "Nothing" _ []) -> pure $ BoolAtom $ v >= mm
    ( ConstructedAtom "Nothing" _ []
      , ConstructedAtom "Just" _ [DayAtom mx]) -> pure $ BoolAtom $ v <= mx
    ( ConstructedAtom "Nothing" _ []
      , ConstructedAtom "Nothing" _ []) -> pure $ BoolAtom True
    (_, _) -> Left AtomFunctionTypeMismatchError
  _         -> Left AtomFunctionTypeMismatchError
checkDayConstraint _ = Left AtomFunctionTypeMismatchError

-- | Maybe UTCTime -> Maybe UTCTime -> UTCTime -> Either AtomFunctionError Bool
-- min -> max -> value -> result
checkUTCTimeConstraint :: [Atom] -> Either AtomFunctionError Atom
checkUTCTimeConstraint (mMin:mMax:val:_) = case val of
  DateTimeAtom v -> case (mMin, mMax) of
    ( ConstructedAtom "Just" _ [DateTimeAtom mn]
      , ConstructedAtom "Just" _ [DateTimeAtom mx])
      -> pure $ BoolAtom $ v >= mn && v <= mx
    ( ConstructedAtom "Just" _ [DateTimeAtom mm]
      , ConstructedAtom "Nothing" _ []) -> pure $ BoolAtom $ v >= mm
    ( ConstructedAtom "Nothing" _ []
      , ConstructedAtom "Just" _ [DateTimeAtom mx])
      -> pure $ BoolAtom $ v <= mx
    ( ConstructedAtom "Nothing" _ []
      , ConstructedAtom "Nothing" _ []) -> pure $ BoolAtom True
    (_, _) -> Left AtomFunctionTypeMismatchError
  _ -> Left AtomFunctionTypeMismatchError
checkUTCTimeConstraint _ = Left AtomFunctionTypeMismatchError

-- | Bool -> Maybe Integer -> Maybe Integer -> Text -> Either AtomFunctionError Bool
-- isMultiline -> min -> max -> value -> result
checkTextConstraint :: [Atom] -> Either AtomFunctionError Atom
checkTextConstraint ((BoolAtom isMulti):mMin:mMax:val:_) = case val of
  TextAtom v
    -> let lineCount = length $ T.lines v
           charCount = T.length v
           comparable = fromIntegral
             $ if isMulti
               then lineCount
               else charCount
       in case (mMin, mMax) of
            ( ConstructedAtom "Just" _ [IntegerAtom mn]
              , ConstructedAtom "Just" _ [IntegerAtom mx])
              -> pure $ BoolAtom $ comparable >= mn && comparable <= mx
            ( ConstructedAtom "Just" _ [IntegerAtom mm]
              , ConstructedAtom "Nothing" _ [])
              -> pure $ BoolAtom $ comparable >= mm
            ( ConstructedAtom "Nothing" _ []
              , ConstructedAtom "Just" _ [IntegerAtom mx])
              -> pure $ BoolAtom $ comparable <= mx
            ( ConstructedAtom "Nothing" _ []
              , ConstructedAtom "Nothing" _ []) -> pure $ BoolAtom True
            (_, _) -> Left AtomFunctionTypeMismatchError
  _          -> Left AtomFunctionTypeMismatchError
checkTextConstraint _ = Left AtomFunctionTypeMismatchError

-- | Maybe Integer -> Maybe Integer -> DBConstraint -> [Atom] -> Either AtomFunctionError Bool
-- min -> max -> constraint -> value -> result
checkArrayConstraint :: [Atom] -> Either AtomFunctionError Atom
checkArrayConstraint (mMin:mMax:constraint:val:_) = case val of
  ConstructedAtom "List" _ as
    -> let allTrue = all
             (\case
                BoolAtom True -> True
                _ -> False)
           checkContents =
             (\x -> case mapM (\a -> checkConstraint $ constraint:[a]) x of
                Right rs -> allTrue rs
                Left _   -> False)
           listLen = fromIntegral $ length as
       in case (mMin, mMax) of
            ( ConstructedAtom "Just" _ [IntegerAtom mn]
              , ConstructedAtom "Just" _ [IntegerAtom mx]) -> pure
              $ BoolAtom
              $ listLen >= mn && listLen <= mx && checkContents as
            ( ConstructedAtom "Just" _ [IntegerAtom mm]
              , ConstructedAtom "Nothing" _ [])
              -> pure $ BoolAtom $ listLen >= mm && checkContents as
            ( ConstructedAtom "Nothing" _ []
              , ConstructedAtom "Just" _ [IntegerAtom mx])
              -> pure $ BoolAtom $ listLen <= mx && checkContents as
            ( ConstructedAtom "Nothing" _ []
              , ConstructedAtom "Nothing" _ []) -> pure $ BoolAtom True
            (_, _) -> Left AtomFunctionTypeMismatchError
  _ -> Left AtomFunctionTypeMismatchError
checkArrayConstraint _ = Left AtomFunctionTypeMismatchError

-- | DBConstraint -> Atom -> Either AtomFunctionError Bool
-- constraint -> value -> result
checkMaybeConstraint :: [Atom] -> Either AtomFunctionError Atom
checkMaybeConstraint (constraint:val:_) = case val of
  ConstructedAtom "Maybe" _ ((ConstructedAtom "Just" _ as):_)
    -> checkConstraint $ constraint:as
  ConstructedAtom "Maybe" _ ((ConstructedAtom "Nothing" _ _):_)
    -> Right $ BoolAtom True
  _ -> Left AtomFunctionTypeMismatchError
checkMaybeConstraint _ = Left AtomFunctionTypeMismatchError

-- | DBConstraint -> DBConstraint -> Atom -> Either AtomFunctionError Bool
-- constraint -> constraint -> value -> result
checkEitherConstraint :: [Atom] -> Either AtomFunctionError Atom
checkEitherConstraint (constraint1:constraint2:val:_) = case val of
  ConstructedAtom "Either" _ ((ConstructedAtom "Right" _ as):_)
    -> checkConstraint $ constraint2:as
  ConstructedAtom "Either" _ ((ConstructedAtom "Left" _ as):_)
    -> checkConstraint $ constraint1:as
  _ -> Left AtomFunctionTypeMismatchError
checkEitherConstraint _ = Left AtomFunctionTypeMismatchError

-- | DBConstraint -> Value -> Either AtomFunctionError Bool
-- constraint -> value -> Either AtomFunctionError Bool
checkConstraint :: [Atom] -> Either AtomFunctionError Atom
checkConstraint (constraint:valueAtom:_) = case constraint of
  ConstructedAtom constraintType _ as
    -> let atoms = as ++ [valueAtom]
           _ = unsafePerformIO $ print atoms
       in case constraintType of
            "ConsInt" -> checkIntConstraint atoms
            "ConsInteger" -> checkIntegerConstraint atoms
            "ConsDouble" -> checkDoubleConstraint atoms
            "ConsDay" -> checkDayConstraint atoms
            "ConsUTCTime" -> checkUTCTimeConstraint atoms
            "ConsText" -> checkTextConstraint atoms
            "ConsArray" -> checkArrayConstraint atoms
            "ConsMaybe" -> checkMaybeConstraint atoms
            "ConsEither" -> checkEitherConstraint atoms
            _ -> Left AtomFunctionTypeMismatchError
  _ -> Left AtomFunctionTypeMismatchError
checkConstraint _ = Left AtomFunctionTypeMismatchError

-- | Atom -> Either AtomFunctionError TextAtom
-- converts atom to a string representation
toString :: [Atom] -> Either AtomFunctionError Atom
toString ((IntegerAtom i):_) = Right $ TextAtom $ T.pack $ show i
toString ((IntAtom i):_) = Right $ TextAtom $ T.pack $ show i
toString ((DoubleAtom d):_) = Right $ TextAtom $ T.pack $ show d
toString (a@(TextAtom _):_) = Right a
toString ((DayAtom d):_) = Right $ TextAtom $ T.pack $ show d
toString ((DateTimeAtom u):_) = Right $ TextAtom $ T.pack $ show u
toString ((ByteStringAtom _):_) =
  Left $ AtomFunctionUserError "toString: ByteStringAtom not supported!"
toString ((BoolAtom b):_) = Right $ TextAtom $ T.pack $ show b
toString ((UUIDAtom u):_) = Right $ TextAtom $ T.pack $ show u
toString ((RelationAtom _):_) =
  Left $ AtomFunctionUserError "toString: RelationAtom not supported!"
toString ((RelationalExprAtom _):_) =
  Left $ AtomFunctionUserError "toString: RelationalExprAtom not supported!"
toString ((ConstructedAtom "Just" _ as):_) = toString as
toString ((ConstructedAtom "Nothing" _ _):_) = Right $ TextAtom ""
toString ((ConstructedAtom "Left" _ as):_) = toString as
toString ((ConstructedAtom "Right" _ as):_) = toString as
toString ((ConstructedAtom "Cons" _ as):_) = do
  texts <- mapM (toString . (:[])) as
  concatTextAtoms texts
toString a =
  Left $ AtomFunctionUserError $ "toString: Unmatched atom type: " ++ show a

-- | Takes any number of TextAtoms as input, returns a single TextAtom
concatTextAtoms :: [Atom] -> Either AtomFunctionError Atom
concatTextAtoms [] = Right $ TextAtom ""
concatTextAtoms ((TextAtom t):as) =
  let textRest = concatTextAtoms as
  in case textRest of
       Right (TextAtom t') -> Right $ TextAtom $ T.append t t'
       Left e -> Left $ AtomFunctionUserError $ "concatTextAtoms: " ++ show e
       a -> Left
         $ AtomFunctionUserError
         $ "concatTextAtoms: invalid case: " ++ show a
concatTextAtoms a = Left
  $ AtomFunctionUserError
  $ "concatTextAtoms: invalid input type: " ++ show a

-- | searchTerm -> value -> Either AtomFunctionError Int
fuzzySearch :: [Atom] -> Either AtomFunctionError Atom
fuzzySearch [] = Right $ IntAtom 0
fuzzySearch ((TextAtom searchTerm):v:_) =
  case (toString [v]) of
    Right (TextAtom t) ->
      case FZ.match searchTerm t "" "" id False of
        Just FZ.Fuzzy { .. } -> Right $ IntAtom score
        _ -> Right $ IntAtom 0
    Left e -> Left e
fuzzySearch
  a = Left $ AtomFunctionUserError $ "fuzzySearch: invalid case: " ++ show a

constraintAtomFunctions :: AtomFunctions
constraintAtomFunctions = HS.fromList
  [ AtomFunction { atomFuncName = "checkIntConstraint"
                 , atomFuncType = [ ConstructedAtomType
                                      "Maybe"
                                      (Map.fromList [("a", IntAtomType)])
                                  , ConstructedAtomType
                                      "Maybe"
                                      (Map.fromList [("a", IntAtomType)])
                                  , IntAtomType
                                  , BoolAtomType]
                 , atomFuncBody = AtomFunctionBody Nothing checkIntConstraint
                 }
  , AtomFunction { atomFuncName = "checkIntegerConstraint"
                 , atomFuncType = [ ConstructedAtomType
                                      "Maybe"
                                      (Map.fromList [("a", IntegerAtomType)])
                                  , ConstructedAtomType
                                      "Maybe"
                                      (Map.fromList [("a", IntegerAtomType)])
                                  , IntegerAtomType
                                  , BoolAtomType]
                 , atomFuncBody =
                     AtomFunctionBody Nothing checkIntegerConstraint
                 }
  , AtomFunction { atomFuncName = "checkDoubleConstraint"
                 , atomFuncType = [ ConstructedAtomType
                                      "Maybe"
                                      (Map.fromList [("a", DoubleAtomType)])
                                  , ConstructedAtomType
                                      "Maybe"
                                      (Map.fromList [("a", DoubleAtomType)])
                                  , DoubleAtomType
                                  , BoolAtomType]
                 , atomFuncBody =
                     AtomFunctionBody Nothing checkDoubleConstraint
                 }
  , AtomFunction { atomFuncName = "checkDayConstraint"
                 , atomFuncType = [ ConstructedAtomType
                                      "Maybe"
                                      (Map.fromList [("a", DayAtomType)])
                                  , ConstructedAtomType
                                      "Maybe"
                                      (Map.fromList [("a", DayAtomType)])
                                  , DayAtomType
                                  , BoolAtomType]
                 , atomFuncBody = AtomFunctionBody Nothing checkDayConstraint
                 }
  , AtomFunction { atomFuncName = "checkUTCTimeConstraint"
                 , atomFuncType = [ ConstructedAtomType
                                      "Maybe"
                                      (Map.fromList [("a", DateTimeAtomType)])
                                  , ConstructedAtomType
                                      "Maybe"
                                      (Map.fromList [("a", DateTimeAtomType)])
                                  , DateTimeAtomType
                                  , BoolAtomType]
                 , atomFuncBody =
                     AtomFunctionBody Nothing checkUTCTimeConstraint
                 }
  , AtomFunction { atomFuncName = "checkTextConstraint"
                 , atomFuncType = [ ConstructedAtomType
                                      "Maybe"
                                      (Map.fromList [("a", TextAtomType)])
                                  , ConstructedAtomType
                                      "Maybe"
                                      (Map.fromList [("a", TextAtomType)])
                                  , TextAtomType
                                  , BoolAtomType]
                 , atomFuncBody = AtomFunctionBody Nothing checkTextConstraint
                 }
  , AtomFunction { atomFuncName = "checkArrayConstraint"
                 , atomFuncType =
                     [ ConstructedAtomType
                         "Maybe"
                         (Map.fromList [("a", IntegerAtomType)])
                     , ConstructedAtomType
                         "Maybe"
                         (Map.fromList [("a", IntegerAtomType)])
                     , ConstructedAtomType "DBConstraint" Map.empty
                     , ConstructedAtomType
                         "List"
                         (Map.fromList [("a", TypeVariableType "a")])
                     , BoolAtomType]
                 , atomFuncBody = AtomFunctionBody Nothing checkTextConstraint
                 }
  , AtomFunction { atomFuncName = "checkMaybeConstraint"
                 , atomFuncType =
                     [ ConstructedAtomType "DBConstraint" Map.empty
                     , ConstructedAtomType
                         "Maybe"
                         (Map.fromList [("a", TypeVariableType "a")])
                     , BoolAtomType]
                 , atomFuncBody = AtomFunctionBody Nothing checkMaybeConstraint
                 }
  , AtomFunction { atomFuncName = "checkEitherConstraint"
                 , atomFuncType =
                     [ ConstructedAtomType "DBConstraint" Map.empty
                     , ConstructedAtomType "DBConstraint" Map.empty
                     , ConstructedAtomType
                         "Either"
                         (Map.fromList
                            [ ("a", TypeVariableType "a")
                            , ("b", TypeVariableType "b")])
                     , BoolAtomType]
                 , atomFuncBody =
                     AtomFunctionBody Nothing checkEitherConstraint
                 }
  , AtomFunction { atomFuncName = "checkConstraint"
                 , atomFuncType =
                     [ ConstructedAtomType "DBConstraint" Map.empty
                     , TypeVariableType "a"
                     , BoolAtomType]
                 , atomFuncBody = AtomFunctionBody Nothing checkConstraint
                 }
  , AtomFunction { atomFuncName = "toString"
                 , atomFuncType = [TypeVariableType "a", TextAtomType]
                 , atomFuncBody = AtomFunctionBody Nothing toString
                 }
  , AtomFunction { atomFuncName = "fuzzySearch"
                 , atomFuncType = [TextAtomType, TypeVariableType "a", IntAtomType]
                 , atomFuncBody = AtomFunctionBody Nothing fuzzySearch
                 }]

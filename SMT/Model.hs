module SMT.Model (readModel) where

import Text.ParserCombinators.Parsek.Position
import Data.Char (isSpace)

type P a = Parser a

tok :: String -> P ()
tok s = spaces >> string s >> return ()

many1 p = (:) <$> p <*> many p

parseDouble :: P Double
parseDouble = do
  spaces
  x <- many1 digit
  string "."
  y <- many1 digit
  return $ read $ x ++ "." ++ y
parseValue = parseDouble <|> parens (parseDiv <|> parseNeg)

parseDiv = do
  tok "/"
  x <- parseValue
  y <- parseValue
  return (x/y)

parseNeg = do
  tok "-"
  x <- parseValue
  return (negate x)

parseAssoc :: P (String,Double)
parseAssoc = parens $ do
  tok "define-fun"
  spaces
  v <- many1 (satisfy (not . isSpace))
  parens (return ())
  tok "Real"
  x <- parseValue
  return (v,x)

parens :: Parser a -> Parser a
parens = between (tok "(") (tok")")

parseModel :: Parser [(String, Double)]
parseModel = parens $ do
  _ <- optional (tok "model")
    -- z3 <= 4.8.8   outputs the word "model"
    -- z3 >= 4.8.10  does not
  many parseAssoc

readModel :: String -> ParseResult SourcePos [(String, Double)]
readModel = parse "<model>" parseModel longestResult

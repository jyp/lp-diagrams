module SMT.Model (readModel) where

import Text.ParserCombinators.Parsek.Position

data SExpr = Atom String | S [SExpr]

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

parseAssoc :: P (Int,Double)
parseAssoc = parens $ do
  tok "define-fun"
  spaces
  char 'x'
  v <- many1 digit
  parens (return ())
  tok "Real"
  x <- parseValue
  return (read v,x)

parens = between (tok "(") (tok")")
parseModel = parens $ do
  tok "model"
  many parseAssoc

readModel :: String -> ParseResult SourcePos [(Int, Double)]
readModel = parse "<model>" parseModel longestResult

{-
 - ----------------------------------------------------------------------------
 - "THE BEER-WARE LICENSE" (Revision 42):
 - <code@gregorkopf.de> wrote this file. As long as you retain this notice you
 - can do whatever you want with this stuff. If we meet some day, and you
 - think this stuff is worth it, you can buy me a beer in return. Gregor Kopf
 - ----------------------------------------------------------------------------
 -}

{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE ScopedTypeVariables #-}

{-|
Module      : Data.IxSet.Queryable
Description : Query Language for IxSet
Copyright   : (c) Gregor Kopf, 2016
License     : BEER-WARE-LICENSE
Maintainer  : code@gregorkopf.de
Stability   : experimental
Portability : POSIX

This module provides a query language for 'IxSet's. Regular 'IxSet's can be 
queried by using functions like '@='. However, one cannot directly turn a
(human readable) 'String' into such a query. 

The 'IxQueryable' class allows to do this. Instead of creating an 'Indexable'
instance for some type, an 'IxQueryable' instance can be provided. This works
mostly analog to how 'Indexable' instances are built (using 'ixFun'). Instead of
'ixFun' or 'ixGen', you can use the functions 'public' and 'private' to build
'IxQueryable' instances.

Once you provided an 'IxQueryable' instance for your type @x@, you can use the 
function 'parensQuery' to parse a 'String' into an 'IxQuery'. The 'IxQuery' can
then be run on any 'IxSet'@ x@ object. Parsing and running an 'IxQuery' might fail
at runtime and return an error message.

All 'IxQueryable' instances are automatically also 'Indexable' instances. You 
can therefore use all functions from 'IxSet' as you are used to.
-}
module Data.IxSet.Queryable (IxQueryable(..), IxQuery(..), runQuery, parseQuery,
   Qr, public, private) 
where

import           Data.IxSet
import           Data.IxSet.Ix
import           Data.Typeable
import           Data.List
import           Text.ParserCombinators.Parsec

-- | A query index. It is required for each field that shall be queryable
-- or indexable. The 'public' and 'private' functions can be used to generate
-- 'Qr' objects.
data Qr a = forall x. (Ord x, Typeable x) => Qr (Maybe String) (a -> [x]) 
                                                (String -> x)

-- | Generates a queryable index and returns a 'Qr'. If you generate a public
-- index named @foo@, you can later run queries like @foo = myValue@. 
public :: (Ord x, Typeable x) => 
             String -- ^ Name of the queryable field (can be arbitrary)
          -> (a -> [x]) -- ^ Function for generating 'IxSet' indices (see 'ixFun')
          -> (String -> x)  -- ^ Function for turning Strings into query keys
          -> Qr a 
public s k r = Qr (Just s) k r

-- | Generates an indexable, but not queryable index and returns a 'Qr'. This
-- means that you will be able to use functions like '@=' to issue queries, but
-- you will not be able to build 'IxQuery's for the respective field of your
-- type.
private :: (Ord x, Typeable x) => 
              (a -> [x]) -- ^ Function for generating 'IxSet' indices (see 'ixFun')
           -> Qr a
private k = Qr Nothing k undefined

mkfun :: Qr t -> Data.IxSet.Ix.Ix t
mkfun (Qr _ a _) = ixFun $ a

findQ :: [Qr a] -> String -> Maybe (Qr a)
findQ [] _ = Nothing
findQ ((Qr (Just s) a b):rest) x | x == s    = Just (Qr (Just s) a b)
                                 | otherwise = findQ rest x
findQ _ _ = Nothing

mkQ :: forall a y. Qr a -> String -> (forall x. (Ord x, Typeable x) => x -> y) -> y
mkQ (Qr _ _ rd) v f = f $ rd v

-- | The IxQueryable class is similar to the 'Indexable' class. You must supply
-- a list of index generator functions (see 'public' and 'private') in your
-- instances of this class. This will automatically make your type 'Indexable'
-- and queryable.
class IxQueryable a where
   queryTypes :: [Qr a]
   getqt :: IxSet a -> [Qr a]
   getqt _ = queryTypes

instance IxQueryable a => Indexable a where
   empty = ixSet $ map mkfun queryTypes

runQ :: (IxQueryable a, Typeable a, Ord a) => String -> (forall b. (Ord b, Typeable b) => b -> IxSet a -> IxSet a) -> String -> IxSet a -> Either String (IxSet a)
runQ field fun value ixs =
   case findQ (getqt ixs) field of
      Nothing -> Left $ "No such field: " ++ field
      Just qr -> Right $ (mkQ qr value) fun ixs

-- | A query that can be issued over an 'IxSet'. This is done by the 'runQuery'
-- function.
data IxQuery = QrEquals      String String -- ^ Field equals value
             | QrLessThan    String String -- ^ Field less than value
             | QrLessEq      String String -- ^ Field less or equal value
             | QrGreater     String String -- ^ Field greater value
             | QrGreaterEq   String String -- ^ Field greater or equal value
             | QrDisjunction IxQuery IxQuery -- ^ Query1 AND Query2
             | QrConjunction IxQuery IxQuery -- ^ Query1 OR Query2
             | QrNegate      IxQuery -- ^ Query negation
             deriving (Show)

-- | Runs an 'IxQuery' on an 'IxSet' and returns either an error message or a
-- resulting 'IxSet'.
runQuery :: (IxQueryable a, Typeable a, Ord a) => IxSet a -> IxQuery -> Either String (IxSet a)
runQuery ixs (QrEquals      field value) = runQ field (flip (@=))  value ixs
runQuery ixs (QrLessThan    field value) = runQ field (flip (@<))  value ixs
runQuery ixs (QrLessEq      field value) = runQ field (flip (@<=)) value ixs
runQuery ixs (QrGreater     field value) = runQ field (flip (@>))  value ixs
runQuery ixs (QrGreaterEq   field value) = runQ field (flip (@>=)) value ixs
runQuery ixs (QrDisjunction q1    q2   ) = do
   set1 <- runQuery ixs q1
   set2 <- runQuery ixs q2
   return $ set1 ||| set2
runQuery ixs (QrConjunction q1    q2   ) = do
   set1 <- runQuery ixs  q1 
   set2 <- runQuery set1 q2 
   return $ set2
runQuery ixs (QrNegate (QrEquals a b)) = runQuery ixs
                                                  (QrDisjunction (QrLessThan a b) 
                                                                 (QrGreater  a b))
                                                  
runQuery ixs (QrNegate (QrLessThan  a b))   = runQuery ixs (QrGreaterEq a b)
runQuery ixs (QrNegate (QrLessEq    a b))   = runQuery ixs (QrGreater   a b)
runQuery ixs (QrNegate (QrGreater   a b))   = runQuery ixs (QrLessEq    a b)
runQuery ixs (QrNegate (QrGreaterEq a b))   = runQuery ixs (QrLessThan  a b)
runQuery ixs (QrNegate (QrConjunction a b)) = runQuery ixs 
                                                       (QrDisjunction (QrNegate a) 
                                                                      (QrNegate b)) 
                                                       
runQuery ixs (QrNegate (QrDisjunction a b)) = runQuery ixs
                                                       (QrConjunction (QrNegate a) 
                                                                      (QrNegate b)) 

-- | Parses a string into an 'IxQuery'. The following syntax is recognized:
--
-- * Comparisons: @field = value@, @field > value@, @field < value@, @field >= value@, @field <= value@
-- * Conjunction and disjunction: @field1 = value1 and field2 = value2@, @field1 = value1 or field2 = value2@
-- * Parentheses: @(field1 = value1 and field2 = value2) or (field3 = value3)@
-- * Negation: @not (field1 = value1 or field1 = value2)@
--
parseQuery ::    String -- ^ The query string
              -> Either String IxQuery -- ^ Resulting 'IxQuery' or error message
parseQuery input = 
   case parse (do q <- ixQuery; eof; return q) "(query)" input of
      Left  pe  -> Left  $ show pe
      Right ixq -> Right $ ixq

type MyParser a = forall st. GenParser Char st a

ixQuery :: MyParser IxQuery
ixQuery = atomicIxQuery >>= continueQuery

continueQuery :: IxQuery -> MyParser IxQuery
continueQuery q1 = do
   q <- (Just <$> try (try (andClause q1) <|> (orClause q1))) <|> (return Nothing)
   case q of
      Just q2 -> (try $ continueQuery q2) <|> (return q2)
      Nothing -> return $ q1

reserved :: String -> MyParser ()
reserved s = spaces >> string s >> spaces

andClause :: IxQuery -> MyParser IxQuery
andClause q1 = reserved "and" >> (QrConjunction q1 <$> atomicIxQuery)

orClause :: IxQuery -> MyParser IxQuery
orClause q1 = reserved "or" >> (QrDisjunction q1 <$> atomicIxQuery)

atomicIxQuery :: MyParser IxQuery
atomicIxQuery = 
       try notQuery
   <|> try parensQuery
   <|> try queryEq
   <|> try queryLTE
   <|> try queryLT
   <|> try queryGTE
   <|> queryGT

parensQuery :: MyParser IxQuery
parensQuery = between (char '(' >> spaces) (spaces >> char ')') $ ixQuery

notQuery :: MyParser IxQuery
notQuery = reserved "not" >> (QrNegate <$> ixQuery)

queryEq :: MyParser IxQuery
queryEq = QrEquals <$> fieldName <*> (reserved "=" >> quotedString)

queryLT :: MyParser IxQuery
queryLT = QrLessThan <$> fieldName <*> (reserved "<" >> quotedString)

queryLTE :: MyParser IxQuery
queryLTE = QrLessEq <$> fieldName <*> (reserved "<=" >> quotedString)

queryGT :: MyParser IxQuery
queryGT = QrGreater <$> fieldName <*> (reserved ">" >> quotedString)

queryGTE :: MyParser IxQuery
queryGTE = QrGreaterEq <$> fieldName <*> (reserved ">=" >> quotedString)

fieldName :: MyParser String
fieldName = many1 $ noneOf " =()"

quotedString :: MyParser String
quotedString = do
       (do char '"'; s <- many qs; char '"'; return s)
   <|> (many1 $ noneOf " ()")
   where qs =     try (string "\\\"" >> return '"')
              <|> try (string "\\\\" >> return '\\')
              <|> noneOf "\""

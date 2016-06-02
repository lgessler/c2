module Read where

import AST

import Control.Monad
import Control.Applicative
import Data.List
import Control.Monad.State


formatcontent::[String] -> AST
formatcontent = (.) fst $ runState $ do maps <- formatClassMap 
                                        methods <- formatImpMap
                                        pMap <- formatParentMap
                                        clsses <- formatInput
                                        -- we're not using the AST, are we?
                                        return $ AST (Maps maps methods pMap, [])

formatInput::State [String] [Class]
formatInput = do text <- get
                 case text of
                   [] -> return []
                   _ -> liftM2 (:) formatClass formatInput

formatClassMap :: State [String] ClassMap
formatClassMap = modify tail >> ClassMap <$> formatUnnumberedList formatMapClass 

formatMapClass :: State [String] MapClass
formatMapClass = do (name:_) <- get
                    modify tail
                    return . MapClass name =<< formatUnnumberedList formatMPAttr

formatMPAttr :: State [String] Attr
formatMPAttr = do 
  text <- get
  let attributeName = text !! 1
      typeName      = text !! 2 in
      put (drop 3 text) >> case head text of 
     "initializer"          -> return . Attr attributeName typeName =<< formatExpr
     "no_initializer"       -> return $ Attr_NI attributeName typeName

formatImpMap :: State [String] ImpMap
formatImpMap = modify tail >> ImpMap <$> formatUnnumberedList formatClassImp

formatClassImp :: State [String] ClassImp
formatClassImp = do (clssName:text) <- get
                    put text
                    return . ClassImp clssName =<< formatUnnumberedList formatMethodImp

formatMethodImp :: State [String] MethodImp
formatMethodImp = do (name:num_args:text) <- get
                     let (attrs, inter) = splitAt (read num_args :: Int) text in
                       put (tail inter) >> liftM (MethodImp name attrs (head inter)) formatExpr

formatParentMap :: State [String] ParentMap
formatParentMap = modify tail >> ParentMap <$> formatUnnumberedList formatParentRel

formatParentRel :: State [String] (String, String)
formatParentRel = do text <- get
                     put $ drop 2 text
                     return (head text, text !! 1)

formatClass:: State [String] Class
formatClass = liftM3 Class formatType formatInheritance (formatUnnumberedList formatFeature)

formatUnnumberedList:: State [String] a -> State [String] [a]
formatUnnumberedList f = do text <- get 
                            put (tail text) >> formatList f (read $ head text :: Int)

formatList::State [String] a -> Int -> State [String] [a]
formatList _ 0 =  return []
formatList f n =  do hd <- f
                     tl <- formatList f (n-1)
                     return (hd:tl)

formatFeature:: State [String] Feature
formatFeature = do text <- get
                   case head text of
                     "method" -> put (tail text) >> formatMethod
                     _ -> formatAttr

formatAttr:: State [String] Feature
formatAttr = do text <- get
                put $ tail text
                case head text of
                  "attribute_no_init" -> liftM2 AttributeNoInit formatIdentifier formatType
                  _ -> liftM3 AttributeInit formatIdentifier formatType formatExpr

formatMethod:: State [String] Feature
formatMethod = liftM4 Method formatIdentifier (formatUnnumberedList formatFormal) formatType formatExpr

formatFormal:: State [String] (Identifier, Type)
formatFormal = liftM2 (,) formatIdentifier formatType

formatInheritance::State [String] (Maybe Type)
formatInheritance = do text <- get
                       put $ tail text
                       case head text of
                         "no_inherits" -> return Nothing
                         _ -> return . Just =<< formatType

formatType:: State [String] Type
formatType = do (a:b:_) <- get
                modify (drop 2)
                return $ Type (read a::Integer) b

formatIdentifier:: State [String] Identifier
formatIdentifier = do (a:b:_) <- get
                      modify $ drop 2
                      return $ Ident (read a::Integer) b

formatExpr:: State [String] Expr
formatExpr = do (n:t:xs) <- get
                put xs
                TypedExpr <$> (TyEx (read n::Integer) t) <$> formatAnExpr

formatAnExpr:: State [String] AnExpr
formatAnExpr = do (x:_) <- get
                  modify tail
                  f x where
  f x
    | x == "assign"                                  = liftM2 AssignmentEx formatIdentifier formatExpr
    | x `elem` ["integer", "string", "identifier", "true", "false"]     = formatConstant x
    | x == "if"                                      = liftM3 IfEx formatExpr formatExpr formatExpr
    | x == "while"                                   = liftM2 LoopEx formatExpr formatExpr
    | x == "block"                                   = liftM  BlockEx $ formatUnnumberedList formatExpr
    | x == "new"                                     = liftM  NewTypeEx formatType
    | x == "isvoid"                                  = liftM  IsVdEx formatExpr
    | x `elem` ["plus", "minus", "times", "divide"]  = liftM2 (BinOpEx (formatBinOp x)) formatExpr formatExpr
    | x `elem` ["lt", "le", "eq"]                    = liftM2 (CmpOpEx (formatCmpOp x)) formatExpr formatExpr
    | x `elem` ["not", "negate"]                     = liftM  (UnOpEx (formatUnOp x)) formatExpr
    | x == "let"                                     = liftM2 LetEx formatLet formatExpr
    | x == "case"                                    = liftM2 CaseEx formatExpr formatCaseList
    | x `elem` ["self_dispatch", "dynamic_dispatch", "static_dispatch"]     = formatDispatch x
    | x == "internal" = do (x:xs) <- get
                           put xs
                           return$ Interna x

formatDispatch::String -> State [String] AnExpr
formatDispatch x 
        | x == "self_dispatch"       = liftM2 (DispatchEx Nothing Nothing) formatIdentifier $ formatUnnumberedList formatExpr
        | x == "dynamic_dispatch"    = do mthd_expr2 <- formatExpr
                                          method_identifier2 <- formatIdentifier
                                          expr_list2 <- formatUnnumberedList formatExpr
                                          return$ DispatchEx (Just mthd_expr2) Nothing method_identifier2 expr_list2
        | x == "static_dispatch"     = do mthd_expr2 <- formatExpr
                                          method_type <- formatType
                                          method_identifier3 <- formatIdentifier
                                          expr_list3 <- formatUnnumberedList formatExpr
                                          return$ DispatchEx (Just mthd_expr2) (Just method_type) method_identifier3 expr_list3

triple :: a -> b -> c -> (a,b,c)
triple a b c = (a,b,c)

formatCaseList:: State [String] [(Identifier, Type, Expr)]
formatCaseList = formatUnnumberedList (liftM3 triple formatIdentifier formatType formatExpr)

formatLet:: State [String] [(Identifier, Type, Maybe Expr)]
formatLet = formatUnnumberedList$ do
   (a:_) <- get
   modify tail
   liftM3 triple formatIdentifier formatType $ case a of
                                                "let_binding_init"      -> liftM Just formatExpr
                                                "let_binding_no_init"   -> return Nothing

formatUnOp::String -> UnOp
formatUnOp "not" = Not
formatUnOp _     = Neg

formatBinOp::String -> BinOp
formatBinOp opType = case opType of
                              "plus"        -> Add
                              "minus"       -> Sub
                              "times"       -> Mul
                              "divide"      -> Div

formatCmpOp::String -> CmpOp
formatCmpOp opType = case opType of
                         "le"               -> Le
                         "lt"               -> Lt
                         "eq"               -> Eq

formatConstant::String -> State [String] AnExpr
formatConstant constantType = do text <- get
                                 case constantType of
                                       "integer"            -> put (tail text) >> return (ConstantEx (INTS (read (head text)::Integer)))
                                       "string"             -> put (tail text) >> return (ConstantEx (S $ head text))
                                       "true"               -> return $ ConstantEx T
                                       "false"              -> return $ ConstantEx F
                                       "identifier"         -> liftM (ConstantEx . Id) formatIdentifier

-- Printing


printSemanticMaps :: SemanticMaps -> [String]
printSemanticMaps (Maps classMap impMap parentMap) = printClassMap classMap ++ printImpMap impMap ++ printParentMap parentMap

printList:: (a->[String]) -> [a] -> [String]
printList f list = show (length list) : concatMap f list

printClassMap :: ClassMap -> [String]
printClassMap (ClassMap list) = "class_map" : printList printMapClass list
  where printMapClass (MapClass str l) = str : printList printAttr l

printAttr :: Attr -> [ String ]
printAttr (Attr x t e) = "initializer":x:t:printExpr e
printAttr (Attr_NI x t) = ["no_initializer", x, t]

printFeature :: Feature -> [String]
printFeature (AttributeNoInit x t) = "attribute_no_init" : printId x ++ printType t
printFeature (AttributeInit x t e) = "attribute_init" : printId x ++ printType t ++ printExpr e
printFeature (Method name formals t e) = ("method" : printId name ++ printList printFormal formals) ++ (printType t ++ printExpr e)

printFormal :: (Identifier,Type) -> [String]
printFormal (x,t) = printId x ++ printType t


printInheritance :: Maybe Type -> [String]
printInheritance Nothing = ["no_inherits"]
printInheritance (Just t) = printType t

printType :: Type -> [String]
printType (Type n t) = [show n, t]

printId :: Identifier -> [String]
printId (Ident n x) = [show n, x]

printExpr :: Expr -> [String]
printExpr (Ex i e) = show i:printAnExpr e
printExpr (TypedExpr (TyEx i t e)) = show i:t:printAnExpr e
printExpr (Internal _ b) = ["internal", b]

printAnExpr :: AnExpr -> [String]
printAnExpr (AssignmentEx x e) = ("assign":printId x) ++ (printExpr e)
printAnExpr (DispatchEx Nothing Nothing x args) = ("self_dispatch":printId x) ++ (printList printExpr args)
printAnExpr (DispatchEx (Just e) Nothing x args) = ("dynamic_dispatch":printExpr e )++ (printId x) ++ (printList printExpr args)
printAnExpr (DispatchEx (Just e) (Just t) x args) = ("static_dispatch":printExpr e) ++ (printType t) ++ (printId x) ++ (printList printExpr args)
printAnExpr (ConstantEx c) = printConstant c
printAnExpr (IfEx predicate thn els) = "if":(concatMap printExpr [predicate,thn,els])
printAnExpr (LoopEx predicate body) = "while":(concatMap printExpr [predicate,body])
printAnExpr (BlockEx body) = "block":(printList printExpr body)
printAnExpr (NewTypeEx t) = "new":(printType t)
printAnExpr (IsVdEx e) = "isvoid":(printExpr e)
printAnExpr (BinOpEx o r l) = (printBin o) ++ (printExpr r) ++ (printExpr l)
printAnExpr (CmpOpEx o r l) = (printCmp o) ++ (printExpr r) ++ (printExpr l)
printAnExpr (UnOpEx o e) = (printUn o) ++ (printExpr e)
printAnExpr (LetEx bindings e) = "let":(printList printBindings bindings ++ printExpr e)
printAnExpr (CaseEx e elems) = "case":(printExpr e)++(printList printCaseElem elems)
printAnExpr (Interna b) = "internal":b:[]

printConstant :: Constant -> [String]
printConstant (INTS i) = "integer":(show i):[]
printConstant (S s) = "string":s:[]
printConstant (Id i) = "identifier":(printId i)
printConstant T = ["true"]
printConstant F = ["false"]

printBin :: BinOp -> [String]
printBin Add = ["plus"]
printBin Sub = ["minus"]
printBin Mul = ["times"]
printBin Div = ["divide"]

printCmp :: CmpOp -> [String]
printCmp Le = ["le"]
printCmp Lt = ["lt"]
printCmp Eq = ["eq"]

printUn :: UnOp -> [String]
printUn Not = ["not"]
printUn Neg = ["negate"]

printBindings :: (Identifier,Type,Maybe Expr) -> [String]
printBindings (x,t,Nothing) = "let_binding_no_init":(printId x ++ printType t)
printBindings (x,t,Just e) = "let_binding_init":(printId x ++ printType t ++ printExpr e)

printCaseElem :: (Identifier, Type, Expr) -> [String]
printCaseElem (x,t,e) = printId x ++ printType t ++ printExpr e


printImpMap::ImpMap->[String]
printImpMap (ImpMap classes) = "implementation_map": printList printClassImp classes
        where printClassImp (ClassImp name methods) = name : printList printM methods
              printM (MethodImp name formals cls e) = (name : printList return formals)++(cls:printExpr e)

printParentMap::ParentMap->[String]
printParentMap (ParentMap x) = "parent_map":show (length x):concatMap (\(a,b)->[a,b]) (sortBy (\(a,_) (b,_) -> a `compare` b) x)

printAST::AST -> [String]
printAST (AST (maps, classes)) = printSemanticMaps maps -- ++ printList printClass classes


printClass :: Class -> [String]
printClass (Class t Nothing features) = printType t ++ "no_inherits":printList printFeature features
printClass (Class t (Just t') features) = printType t ++ "inherits":printType t' ++ printList printFeature features

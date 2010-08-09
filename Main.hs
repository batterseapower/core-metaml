{-# LANGUAGE FlexibleInstances #-}
import Control.Monad
import Data.Maybe
import System.IO


instance Monad (Either String) where
    return = Right
    Left s  >>= _    = Left s
    Right x >>= fxmy = fxmy x
    fail = Left

instance MonadPlus (Either String) where
    mzero = Left "mzero"
    Left _  `mplus` mx = mx
    Right x `mplus` _  = Right x

markError :: a -> Either a b -> Either a b
markError x (Left _)  = Left x
markError _ (Right y) = Right y


data Nat = Z | S Nat

gtNat :: Nat -> Nat -> Bool
gtNat Z     _     = False
gtNat (S _) Z     = True
gtNat (S x) (S y) = gtNat x y


type Stage = Nat

data BaseType = IntTy
              deriving (Show, Eq)
data Type = BaseTy BaseType | FunTy Type Type | OpenCodeTy Type | ClosedCodeTy Type
          deriving (Show, Eq)

intTy :: Type
intTy = BaseTy IntTy

type Var = String

data Constant = Int Integer | Sub Term Term | Mul Term Term | IfZero Term Term Term
              deriving (Show)
data Term = Constant Constant | Var Var | App Term Term | Lam (Var, Type) Term | Quote Term | Splice Term | RunWith Term [(Var, Term)] | BoxWith Term [(Var, Term)] | Unbox Term | Compile Term | ValRec [((Var, Type), Value)] Term
          deriving (Show)

int :: Integer -> Term
int i = Constant (Int i)

sub :: Term -> Term -> Term
sub e1 e2 = Constant (Sub e1 e2)

mul :: Term -> Term -> Term
mul e1 e2 = Constant (Mul e1 e2)

ifZero :: Term -> Term -> Term -> Term
ifZero e1 e2 e3 = Constant (IfZero e1 e2 e3)

valRec :: (Var, Type) -> Term -> Term -> Term
valRec a b e = ValRec [(a, b)] e

run :: Term -> Term
run = flip RunWith []

box :: Term -> Term
box = flip BoxWith []


constantType :: Stage -> [(Var, (Stage, Type))] -> Constant -> Either String Type
constantType stage env c = case c of
    Int _           -> return (BaseTy IntTy)
    Sub e1 e2       -> do
        typeCheck stage env e1 >>= assertIntTy "constantType: subtracting non-integer"
        typeCheck stage env e2 >>= assertIntTy "constantType: subtracting non-integer"
        return (BaseTy IntTy)
    Mul e1 e2       -> do
        typeCheck stage env e1 >>= assertIntTy "constantType: multiplying non-integer"
        typeCheck stage env e2 >>= assertIntTy "constantType: multiplying non-integer"
        return (BaseTy IntTy)
    IfZero e1 e2 e3 -> do
        typeCheck stage env e1 >>= assertIntTy "constantType: if on non-integer"
        ty2 <- typeCheck stage env e2
        ty3 <- typeCheck stage env e3
        markError "constantType: types of branches do not match" $ guard (ty2 == ty3)
        return ty2
  where
    assertIntTy msg ty = markError (msg ++ " (instead we got " ++ show ty ++ ")") $ do
        BaseTy IntTy <- return ty
        return ()

typeCheck :: Stage -> [(Var, (Stage, Type))] -> Term -> Either String Type
typeCheck stage env e = case e of
    Constant c     -> constantType stage env c
    Var x          -> do
        (stage_x, ty) <- markError ("typeCheck: " ++ x ++ " not in scope") $ do
            Just ty <- return (lookup x env)
            return ty
        if stage_x `gtNat` stage then fail ("typeCheck: staging error for " ++ x) else return ty
    App e1 e2      -> do
        ty_fun <- typeCheck stage env e1
        (ty1, ty_res) <- markError ("typeCheck: application to non-arrow type") $ do
            ty1 `FunTy` ty2 <- return ty_fun
            return (ty1, ty2)
        ty2 <- typeCheck stage env e2
        if ty1 /= ty2 then fail "typeCheck: argument type does not match expected type"
                      else return ty_res
    Lam (x, ty) e  -> liftM (ty `FunTy`) $ typeCheck stage ((x, (stage, ty)):env) e
    Quote e        -> liftM OpenCodeTy $ typeCheck (S stage) env e
    Splice e       -> case stage of Z       -> fail "typeCheck: spliced at level 0"
                                    S stage -> do
                                        ty_open <- typeCheck stage env e
                                        markError "typeCheck: splicing non-open code type" $ do
                                            OpenCodeTy ty <- return ty_open
                                            return ty
    RunWith e with -> do
        with_env <- forM with $ \(x, e) -> do
            ty_closed <- typeCheck stage env e
            ty <- markError ("typeCheck: ran " ++ x ++ " with non-closed code type") $ do
                    ClosedCodeTy ty <- return ty_closed
                    return ty
            return (x, (stage, ClosedCodeTy ty))
        ty_open <- typeCheck stage (with_env ++ [(x, (S stage, e)) | (x, (stage, e)) <- env]) e
        markError "typeCheck: run resulted in non-open code type" $ do
            OpenCodeTy ty <- return ty_open
            return ty
    BoxWith e with -> do
        with_env <- forM with $ \(x, e) -> do
            ty_closed <- typeCheck stage env e
            ty <- markError ("typeCheck: boxed " ++ x ++ " with non-closed code type") $ do
                ClosedCodeTy ty <- return ty_closed
                return ty
            return (x, (Z, ClosedCodeTy ty))
        liftM ClosedCodeTy (typeCheck Z with_env e)
    Unbox e        -> do
        ty_closed <- typeCheck stage env e
        markError "typeCheck: unboxed non-closed code type" $ do
            ClosedCodeTy ty <- return ty_closed
            return ty
    Compile e      -> do
        ty_closed_open <- typeCheck stage env e
        markError "typeCheck: compiled something of the wrong type" $ do
            ClosedCodeTy (OpenCodeTy ty) <- return ty_closed_open
            return (ClosedCodeTy ty)
    ValRec bes e -> do
        let env' = [(x, (stage, ty)) | ((x, ty), _) <- bes] ++ env
        forM_ bes $ \((x, tyb), eb) -> do
            tyb_inferred <- typeCheck stage env' eb
            markError ("Inferred type for " ++ x ++ " valrec " ++ show tyb_inferred ++ " does not match declared type " ++ show tyb) $ guard (tyb == tyb_inferred)
        typeCheck stage env' e


demote :: Stage -> Term -> Term
demote stage e = case e of
    Constant c     -> Constant c
    Var x          -> Var x
    App e1 e2      -> App (demote stage e1) (demote stage e2)
    Lam (x, ty) e  -> Lam (x, ty) (demote stage e)
    Quote e        -> Quote (demote (S stage) e)
    Splice e       -> case stage of Z -> RunWith e []; S stage -> Splice (demote stage e)
    RunWith e with -> RunWith (demote stage e) [(x, demote stage e) | (x, e) <- with]
    BoxWith e with -> BoxWith e                [(x, demote stage e) | (x, e) <- with]
    Unbox e        -> Unbox (demote stage e)
    Compile e      -> Compile (demote stage e)
    ValRec bes e   -> ValRec [((x, ty), demote stage e) | ((x, ty), e) <- bes] (demote stage e)


type Value = Term

evaluateConstant :: Stage -> [(Var, Value)] -> Constant -> Value
evaluateConstant Z env c = case c of
    Int i -> Constant (Int i)
    Sub e1 e2 -> Constant (Int (i1 - i2))
      where Constant (Int i1) = evaluate Z env e1
            Constant (Int i2) = evaluate Z env e2
    Mul e1 e2 -> Constant (Int (i1 * i2))
      where Constant (Int i1) = evaluate Z env e1
            Constant (Int i2) = evaluate Z env e2
    IfZero e1 e2 e3 -> if i1 == 0 then evaluate Z env e2 else evaluate Z env e3
      where Constant (Int i1) = evaluate Z env e1
evaluateConstant (S stage) env c = Constant $ case c of
    Int i           -> Int i
    Sub e1 e2       -> Sub (evaluate (S stage) env e1) (evaluate (S stage) env e2)
    Mul e1 e2       -> Mul (evaluate (S stage) env e1) (evaluate (S stage) env e2)
    IfZero e1 e2 e3 -> IfZero (evaluate (S stage) env e1) (evaluate (S stage) env e2) (evaluate (S stage) env e3)

evaluate :: Stage -> [(Var, Value)] -> Term -> Value
evaluate Z env e = case e of
    Constant c     -> evaluateConstant Z env c
    Var x          -> fromMaybe (error $ "evaluate: free variable " ++ x ++ " at level 0") $ lookup x env
    App e1 e2      -> evaluate Z ((x, evaluate Z env e2) : env) e1_body
      where Lam (x, _) e1_body = evaluate Z env e1
    Lam (x, ty) e  -> Lam (x, ty) (ValRec [((y, undefined "FIXME: type goes here"), v) | (y, v) <- env, x /= y] e) -- NB: this should capture its free variables. What I'm using to do that is a bit of a hack...!
    Quote e        -> Quote (evaluate (S Z) env e)
    Splice e       -> error "evaluate: splice at level 0"
    RunWith e with -> evaluate Z (with_env ++ env) (demote Z v')
      where Quote v' = evaluate Z (with_env ++ env) e
            with_env = [(x, evaluate Z env e) | (x, e) <- with]
    BoxWith e with -> BoxWith e [(x, evaluate Z env e) | (x, e) <- with]
    Unbox e        -> evaluate Z with_env e'
      where BoxWith e' with_env = evaluate Z env e
    Compile e      -> BoxWith (demote Z v') []
      where BoxWith e' with_env = evaluate Z env      e
            Quote v'            = evaluate Z with_env e'
    ValRec bes e   -> evaluate Z env' e
      where env' = [(x, evaluate Z env' v) | ((x, _), v) <- bes] ++ env -- NB: v1 being a syntactic value is sufficient for this to be well-defined. Just don't try to 'show' the resulting Values!

evaluate (S stage) env e = case e of
    Constant c     -> evaluateConstant (S stage) env c
    Var x          -> fromMaybe (error "evaluate: free variable at non-base level") $ lookup x env -- I think we could just say Var x here if there was no cross-stage persistence?
    App e1 e2      -> App (evaluate (S stage) env e1) (evaluate (S stage) env e2)
    Lam (x, ty) e  -> Lam (x, ty) (evaluate (S stage) ((x, Var x) : env) e)
    Quote e        -> Quote (evaluate (S (S stage)) env e)
    Splice e       -> case stage of Z       -> let Quote v = evaluate stage env e in v
                                    S stage -> Splice (evaluate (S stage) env e)
    RunWith e with -> RunWith (evaluate (S stage) ([(x, Var x) | (x, _) <- with] ++ env) e) [(x, evaluate (S stage) env e) | (x, e) <- with]
    BoxWith e with -> BoxWith e                                                             [(x, evaluate (S stage) env e) | (x, e) <- with]
    Unbox e        -> Unbox (evaluate (S stage) env e)
    Compile e      -> Compile (evaluate (S stage) env e)
    ValRec bes e   -> ValRec [((x, ty), evaluate (S stage) env' v) | ((x, ty), v) <- bes] (evaluate (S stage) env' e)
      where env' = [(x, Var x) | ((x, _), _) <- bes] ++ env


test :: Term -> IO ()
test e = do
    testType e
    print (evaluate Z [] e)

testType :: Term -> IO ()
testType e = do
    putStrLn "---"
    print (typeCheck Z [] e)

main :: IO ()
main = do
    hSetBuffering stdout NoBuffering
    
    let x = "x" :: Var
        n = "n" :: Var
        a = "a" :: Var
    
    -- unbox :: [t] -> t
    test $ Lam (x, ClosedCodeTy intTy) (Unbox (Var x))
    -- up :: t -> <t>
    test $ Lam (x, intTy) (Quote (Var x))
    -- weaken :: [t] -> <t>
    test $ Lam (x, ClosedCodeTy intTy) (Quote (Unbox (Var x)))
    -- execute :: [<t>] -> t
    -- Error in the paper -- this proposed definition (p202) is not actually well typed:
    test $ Lam (x, ClosedCodeTy (OpenCodeTy intTy)) (RunWith (Unbox (Var x)) [(x, Var x)])
    test $ Lam (x, ClosedCodeTy (OpenCodeTy intTy)) (Unbox (Compile (Var x)))
    -- exp :: [int -> <int> -> <int>]
    let exp = "exp" :: Var
        exp_ty = ClosedCodeTy (intTy `FunTy` (OpenCodeTy intTy `FunTy` OpenCodeTy intTy))
        exp_def = flip BoxWith [(exp, Var exp)] $ Lam (n, intTy) $ Lam (x, OpenCodeTy intTy) $ ifZero (Var n) (Quote (int 1)) (Quote (mul (Splice (Var x)) (Splice ((Unbox (Var exp)) `App` sub (Var n) (int 1) `App` Var x))))
        mk_exp = valRec (exp, exp_ty) exp_def
    testType $ mk_exp (Var exp)
    -- exponent :: [int -> <int -> int>]
    let exponent = "exponent" :: Var
        exponent_ty = ClosedCodeTy (intTy `FunTy` OpenCodeTy (intTy `FunTy` intTy))
        exponent_def = flip BoxWith [(exp, Var exp)] $ Lam (n, intTy) $ Quote (Lam (a, intTy) (Splice ((Unbox (Var exp)) `App` Var n `App` Quote (Var a))))
        mk_exponent = valRec (exponent, exponent_ty) exponent_def
    testType $ mk_exp $ mk_exponent (Var exponent)
    -- cube :: [int -> int]
    let cube = "cube" :: Var
        cube_ty = ClosedCodeTy (intTy `FunTy` intTy)
        cube_def = Compile (flip BoxWith [(exponent, Var exponent)] (Unbox (Var exponent) `App` int 3))
        mk_cube = valRec (cube, cube_ty) cube_def
    testType $ mk_exp $ mk_exponent $ mk_cube (Var cube)
    -- -- program :: [int]
    let program = "program" :: Var
        program_ty = ClosedCodeTy intTy
        program_def = Compile (flip BoxWith [(cube, Var cube)] (Quote (Unbox (Var cube) `App` int 2)))
        mk_program = valRec (program, program_ty) program_def
    testType $ mk_exp $ mk_exponent $ mk_cube $ mk_program (Var program)
    -- -- it :: Int
    test $ mk_exp $ mk_exponent $ mk_cube $ mk_program (Unbox (Var program))

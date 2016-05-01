-- ========================================================
-- I413 report

-- name: 望月 聡
-- id  : 1310709
-- acknowledgements:
--  (1) Web:'Lambda Calculus'
--       http://www.cse.iitk.ac.in/users/ppk/teaching/cs653/
--         notes/lectures/Lambda-calculus.lhs.html
--  (2) id: 1310753 , name: 鈴木 隆元
--
-- [memo]
-- Answer1 : "nf e" として実装
-- Answer2 : "sub n" として実装
-- Answer3 : "mysum n" として実装
-- Answer4 : "fac n" として実装
-- ========================================================
import Prelude hiding (succ)

-- [data type] 
data Term =  Var Int
           | Lam Int Term
           | App Term Term deriving Show

-----------------------------------------------------------
-- [free variables] 
-- fv' (Var x)     = [x]
fv' (Var x)     = x:[]
fv' (App e1 e2) = fv e1 ++ fv e2
fv' (Lam v w)   = [ x | x <- fv' w, x /= v]

uniq [] = []
uniq (x :xs) | elem x xs     = uniq xs
             | otherwise     = x : uniq xs

fv (e) = uniq (fv' e)

--fv (Lam x e)   = remove x (fv e)
-- remove :: Eq a => a -> [a] -> [a]
-- remove x = filter (/=x)

-----------------------------------------------------------
-- [substitution] : subst n x e == [n/x]e
--                 -subst e x n
--                        n x nt 
-- Definition 1.2:
-- (a) [N/x]x   = N
-- (b) [N/x]a   = a
-- (c) [N/x](PQ)   = ([N/x]P[N/x]Q)
-- (d) [N/x](\x.P) = \x.P  
-- (e) [N/x](\y.P) = \y.P         if x != FV(P)
-- (f) [N/x](\y.P) = \y.[N/x]P    if x == FV(P) and y != FV(N)
-- (g) [N/x](\y.P) = \z.[N/x][z/y]P 
subst' n (Var x) (Var e) a | x==e      = n
                           | otherwise = (Var e)
subst' n (Var x) (App e1 e2) a         = App (subst n (Var x) e1) (subst n (Var x) e2)
subst' nt (Var x) (Lam y p) a
       | y == x                                    = (Lam y p)
       | not (elem x (fv p))                       = (Lam y p)
       | (elem x (fv p)) && (not (elem y (fv nt))) = (Lam y (subst nt (Var x) p))
       | (elem x (fv p)) && (     elem y (fv nt))  =  Lam a (subst nt (Var x) 
                                                       (subst' (Var a) (Var y) p (a + 1)))

subst t1 t2 t3  = subst' t1 t2 t3 (maximum ((fv t1) ++ (fv t2) ++ fv(t3)) + 1)


--- 以下のコードだと Y-combinatorが正しく求められず断念
-- ---------------------------------
-- subst (Var e) (Var x) n  | x==e      = n
-- subst n (Var x) (Var e)  | x==e      = n
--                          | otherwise = (Var e)
-- 
-- subst n (Var x) (App e1 e2)          = App (subst n (Var x) e1) (subst n (Var x) e2)
-- subst nt (Var x) (Lam y p) 
--        | y == x                                    = (Lam y p)
--        | not (elem x (fv p))                       = (Lam y p)
--        | ((elem x (fv p)) && (elem y (fv nt)))     =  Lam e (subst nt (Var x) (subst (Var e) (Var y) p))
--                                                       where e = (maximum ( fv (Lam y p) ++ (fv nt)) +1)

-- -- subst n (Var x) (Lam w e1) | w==x                = (Lam w e1)
-- --                     | not (w `elem` fv n) = Lam w (subst n (Var x) e1) 
-- --                     | True                = Lam z (subst n (Var x) (subst (Var z) (Var w) e1))
-- --                                              where z = (maximum ( fv (Lam w e1) ++ (fv n)) +1)
-- ---------------------------------


-----------------------------------------------------------
-- [Generate Church num]
cn' 0 = (Var 2)
cn' n = (App (Var 1) (cn' (n-1)))
cn  n = (Lam 1 (Lam 2 (cn' n)))

-----------------------------------------------------------
-- [combinator]

-- successor
-- nf (App suc (nn 0))  --> Lam 4 (Lam 4 (App (Var 4) (Var 5)))
succ = (Lam (_var _x) (Lam (_var _y) (Lam (_var _z) (App (App _x _y) (App _y _z)))))

-- ff = lx. D (suc (x 0)) (x 0)
ff  = (Lam (_var _x) (App (App _D (App succ (App _x (cn 0)))) (App _x (cn 0))))

-- predessor 
-- nf (App pred' (cn 1))   --> Lam 1 (Lam 2 (Var 2))
pred'  = (Lam (_var _x) (App (App (App _x ff) (App (App _D (cn 0)) (cn 0))) (cn 1)))


-- U 
-- = \ux.x(uux)
_U = (Lam (_var _u) (Lam (_var _x) (App _x (App (App _u _u) _x))))

-- Y = UU
_Y = (App _U _U)

-- K = \xy.x
_K = (Lam (_var _x) (Lam (_var _y) _x))


-- _D
--   - nf (App (App (App _D _x) _y) n0)
--     Var 3 (=_x)
--   - nf (App (App (App _D _x) _y) n1)	
--     Var 4 (=_y)
_D = (Lam (_var _x) (Lam (_var _y) (Lam (_var _z) (App (App _z (App _K _y)) _x))))

-- S
_S = (Lam (_var _x) (Lam (_var _y) (Lam (_var _z) (App (App _x _z) (App _y _z)))))

-- I
_I = (Lam (_var _x) _x)

-- ////////////////////////////////////////////////////////////////////////////
-- [test code]

-- [variable define] 

n0 = (Lam (_var _x) (Lam (_var _y) _y))
n1 = (Lam (_var _x) (Lam (_var _y) (App _x _y)))

_var (Var q)  = q

_u   = (Var 0)
_v   = (Var 1)
_w   = (Var 2)
_x   = (Var 3)
_y   = (Var 4)
_z   = (Var 5)
_f   = (Var 10)

-- --------------------------------------------------------
-- [combinators test]
-- Ix  -> x
--  => Var 3
_COMB1 = (App _I _x)

-- Kxy -> x
--   => Var 3
_COMB2 = (App (App _K _x) _y)

-- Sxyz -> xz(yz)
--   => App (App (Var 3) (Var 5)) (App (Var 4) (Var 5))
_COMB3 = (App (App (App _S _x) _y) _z)

-- KISSxyz -> ISxyz -> Sxyz -> xz(yz)
--   => App (App (Var 3) (Var 5)) (App (Var 4) (Var 5))
_COMB4 = (App (App (App (App (App (App _K _I) _S) _S) _x) _y) _z)  

-- (ly.vyy)(Iz) -> vzz
--   => App (App (Var 1) (Var 5)) (Var 5)
_COMB5 = (App (Lam (_var _y) (App (App _v _y) _y) ) (App _I _z))

-- SSxyz -> Sy(xy)z -> yz(xy)z
--   => App (App (Var 4) (Var 5)) (App (App (Var 3) (Var 4)) (Var 5))
_COMB6 = (App (App (App (App _S _S) _x) _y) _z)

-- --------------------------------------------------------------------
-- [free variable test]

a1  = App _v _w
--    -> "fv a1" = [1,2]

a2  = App _y _z
--    -> "fv a2" = [4,5]

-- y,z = [4,5]
a3  = App (App _v _w) (App _x _y)
--    -> "fv a3" = [1,2,3,4]

a4  = App (App (App _v _w) (App _x _y)) (App _z _z)
--    -> "fv a4" = [1,2,3,4,5]

l1  = Lam (_var _x) (App _x _x)
--    -> "fv l1" = []

l2  = Lam (_var _x) (App _x _y)
--    -> "fv l2" = [4]

l3  = Lam (_var _x) (App _y _z)
--    -> "fv l3" = [4,5]

l4  = Lam (_var _y) (App _y _x)
--    -> "fv l4" = [3]

l5 = (Lam (_var _x) (Lam (_var _y) (App (App _x _z) _y)))
--    -> "fv l5" = [5]


--      ((vw)(Lx.(xy) z)
ll1 = (App (App _v _w) (App (Lam (_var _x) (App _x _y)) _z)) 
--    -> "fv ll1" = [1,2,4,5]

ll2 = (App (App _v _w) (App (Lam (_var _x) (App _x _y)) (App (Lam (_var _y) (App _z _y)) _z) ))
--    -> "fv ll2" = [1,2,4,5]

ll3 = (App (App _x _z) (App (Lam (_var _x) (App _x _y)) (App (Lam (_var _y) (App _z _y)) _z) ))
--    -> "fv ll3 = [3,4,5]

ll4 = (App (App _v _w) (App (Lam (_var _x) (App _x _y)) (App (Lam (_var _y) (App _z _y)) _z) ))
--    -> "fv ll3 = [1,2,4,5]

-- --------------------------------------------------------------------
-- [subst test]
--
-- 1. [N/x] Var x       = N
-- 2. [N/x] a           = a
-- 3. [N/x] (App P Q)   = ([N/x]P [N/x]Q)
-- 4. [N/x] (Lam x P)   = Lam x P
-- 5. [N/x] (Lam y P)   = Lam y P               ; if x /= FV(P)
-- 6. [N/x] (Lam y P)   = Lam y [N/x]P          ; if x <= FV(P) && y /= FV(N)
-- 7. [N/x] (Lam y P)   = Lam z [N/x][z]y]P     ; if x <= FV(P) && y <= FV(N) 

-- 1. [y/x] x y -> y
--          subst _y _x _y = Var 4
-- 2. [y/x] y y -> y
--          subst _y _y _y = Var 4
-- 3. [y/v] v w --> y w
--          subst _y _v a1 = App (Var 4) (Var 2)
-- 4. [y/x] Lam x.x --> Lam x.x
--          subst _y _x l1 = Lam 3 (App (Var 3) (Var 3))
-- 5. [y/x] Lam x.y --> Lam x.y
--          subst _y _x l2 = Lam 3 (App (Var 3) (Var 4))
-- 6. [y/z] Lam x.x --> Lam x.x
--          subst _y _x l1 = Lam 3 (App (Var 3) (Var 3))
-- 7. [z/y] Lam x.y --> Lam x.z
--          subst _z _y l2 = Lam 3 (App (Var 3) (Var 5))
-- 8. [y/x] Lam y.x --> [y/x] Lam z.x --> Lam z.y
--          subst _y _x l4 = Lam 5 (App (Var 5) (Var 4))

-- --------------------------------------------------------------------
-- test set for nf
--
-- (lx.xx)v -> vv
--   -> App (Var 1) (Var 1)
r1 = (App (Lam (_var _x) (App _x _x)) _v)

-- Omega (lx.xx)(ly.yy) -> (ly.yy)(ly.yy)
-- ** "nf r2" => 終了せず。。
r2 = (App (Lam (_var _x) (App _x _x)) (Lam (_var _y) (App _y _y)))

-- (lx.x)(ly.y)v -> (ly.y)v -> v
--   -> Var 1
r3 = (App (App (Lam (_var _x) _x) (Lam (_var _y) _y)) _v)

-- I Omega 
-- (lx.z)((ly.yy)(ly.yy)) -> z
--   -> Var 5
r4 = (App (Lam (_var _x) _z) (App (Lam (_var _y) (App _y _y)) (Lam (_var _y) (App _y _y))))

-- ((lx.(ly.xxy))z)w -> (ly.zzy)w -> zzw
--    -> App (App (Var 5) (Var 5)) (Var 2)
r5 = (App (App (Lam (_var _x) (Lam (_var _y) (App (App _x _x) _y))) _z) _w)

-- (lx.((ly.y) z)) -> (lx.z)
--   -> Lam 3 (Var 5)
r6 = (Lam (_var _x) (App (Lam (_var _y) _y) _z))

-- (lx.xxx)(lx.xxx) -> (lx.xxx)(lx.xxx)(lx.xxx) -> ...
--    -> ** 終了しない
r7 = (App (Lam (_var _x) (App (App _x _x) _x)) (Lam (_var _x) (App (App _x _x) _x)))

-- (v w) ((lx.x) y) -> (v w) y
--    -> App (App (Var 1) (Var 2)) (Var 4)
r8 = (App (App _v _w) (App (Lam (_var _x) _x) _y))

-- ========================================================
-- [1. Answer]
-- [beta reduction]
nf :: Term -> Term
-- // 以下のコードだとY-combが正しく求められず断念
-- ---------------------------------
-- -- nf (Var v)    = Var v
-- nf (Lam x m)  = Lam x (nf m)
-- nf (App (Lam x m) n)     = nf (subst n (Var x) m)
-- 
-- nf (App m n) | isLam m'  = nf (App m' n')
--              | otherwise = App m' n' where (m',n') = (nf m,nf n)
-- 
-- nf v@(Var _) = v
-- 
-- -- [is lambda]
-- isLam (Lam _ _) = True
-- isLam _         = False
-- ---------------------------------

-- ack.(2)より
nf' (Var v)    t = App (Var v) (nf t)
nf' (Lam x m)  t = subst t (Var x) m
nf' (App m n)  t = let
                      t' = nf' m n
                   in 
                     if ( has_brex t' ) then
                       nf' t' t
                     else
                       App t' (nf t)

_nf  (Var n)            = Var n
_nf  (Lam x t1)         = Lam x (nf t1)
_nf  (App t1 t2)        = nf' t1 t2

nf t  
    | has_brex t = nf (_nf t)
    | otherwise  = t

has_brex' (Var x)   t           = has_brex t
has_brex' (Lam x m) t           = True
has_brex' (App m n) t           = (has_brex' m n) || (has_brex t)

has_brex (Var x)                = False
has_brex (Lam x m)              = has_brex  m
has_brex (App m n)              = has_brex' m n



-- ========================================================
-- [2. answer]
-- sub = yy (\f x y -> d 0 (D x (f (pp x) (pp y)) y ) x)
-- sub = yy (\f x y -> (((d 0) (((D x) ((f (pp x)) (pp y))) y )) x))
-- f = 0, x = 1, y = 2

sub' = (App _Y (Lam (_var _f) (Lam (_var _x) (Lam (_var _y)
                (App (App (App _D (cn 0))
                          (App (App (App _D _x) (App (App _f (App pred' _x)) (App pred' _y))) _y)) _x)))))

sub n m = nf (App (App sub' (cn n)) (cn m))
-- --> "sub 3 1" = Lam 4 (Lam 5 (App (Var 4) (App (Var 4) (Var 5))))

-- ========================================================
-- [3. answer]
-- msum = yy (\f m -> d Z (add  m (f (pp m)) ) m)
-- msum = yy (\f m -> (((d Z) ((add  m) (f (pp m))) ) m))
add' = (App _Y (Lam (_var _f) (Lam (_var _x) (Lam (_var _y)
                (App (App (App _D _y) (App succ (App (App _f (App pred' _x)) _y))) _x)))))

sum' = (App _Y (Lam (_var _f) (Lam (_var _z)
                 (App (App (App _D (cn 0))
                            (App (App add' _z) (App _f (App pred' _z)))
                       ) _z))))

_add n m = nf (App (App add' (cn n)) (cn m))
mysum n   = nf (App sum' (cn n))
-- -> "mysum 2" = Lam 4 (Lam 5 (App (Var 4) (App (Var 4) (App (Var 4) (Var 5)))))

-- ========================================================
-- [4. answer]

-- mul = yy (\f x y -> d 0 (add (f (pp x) y) y) x)
-- mul = yy (\f x y -> (((d 0) ((add (f (pp x) y) y))) x))
mul' = (App _Y (Lam (_var _f) (Lam (_var _x) (Lam (_var _y)
                (App (App (App _D (cn 0))
                        (App (App add' (App (App _f (App pred' _x)) _y)) _y)) _x)))))

-- 
fac' = (App _Y (Lam (_var _f) (Lam (_var _z)
        (App (App (App _D (cn 0))
              (App (App (App _D (cn 1) ) 
                (App (App mul' (App _f (App pred' _z))) _z ))
              (App pred' _z))) _z))))

fac n = nf (App fac' (cn n))
-- -> "fac 2" = Lam 1 (Lam 2 (App (Var 1) (App (Var 1) (Var 2))))


-- ========================================================

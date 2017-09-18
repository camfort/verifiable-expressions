module Language.Expression.Util where

infixr 9 ...

(...) :: (c -> d) -> (a -> b -> c) -> (a -> b -> d)
(f ... g) x y = f (g x y)

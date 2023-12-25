module Prelude where

infix 4 =

class Copy a where
    copy : a -> a -> Prop

subst : Copy a => (a -> a) -> a -> a -> Prop
subst f x y :- forall x'. copy x x' => copy y (f x')
-- @subst (a: *) (copyInst: Copy a) (f: a -> a) (x: a) (y: a) :- forall x': a. copyInst.copy x x' => copyInst.copy y (f x')

(=) : a -> a -> Prop
x = x :- true
-- @(=) (a: *) (x: a) (y: a) :- x ~ y

instance (Copy a, Copy b) => Copy (a -> b) where
    copy f1 f2 :- forall x. copy x x => copy (f1 x) (f2 x)

register (=) as Equal

register Copy as Copy

register copy as copy

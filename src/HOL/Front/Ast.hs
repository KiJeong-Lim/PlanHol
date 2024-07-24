module HOL.Front.Ast where

import Control.Monad.IO.Class
import Control.Monad.Trans.Class
import Control.Monad.Trans.Except
import Control.Monad.Trans.State.Strict
import Control.Monad.Trans.Reader
import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import Z.Utils

data CoreTerm var atom annot
    = CtVar (annot) (var)
    | CtCon (annot) (atom)
    | CtApp (annot) (CoreTerm var atom annot) (CoreTerm var atom annot)
    | CtLam (annot) (var) (CoreTerm var atom annot)
    deriving (Eq, Ord, Show, Functor)

mapCtVar :: (var -> var') -> (CoreTerm var atom annot -> CoreTerm var' atom annot)
mapCtVar f (CtVar annot v) = CtVar annot $! f v
mapCtVar f (CtCon annot c) = CtCon annot c
mapCtVar f (CtApp annot t1 t2) = (CtApp annot $! mapCtVar f t1) $! mapCtVar f t2
mapCtVar f (CtLam annot v t1) = (CtLam annot $! f v) $! mapCtVar f t1

mapCtCon :: (atom -> atom') -> (CoreTerm var atom annot -> CoreTerm var atom' annot)
mapCtCon f (CtVar annot v) = CtVar annot v
mapCtCon f (CtCon annot c) = CtCon annot $! f c
mapCtCon f (CtApp annot t1 t2) = (CtApp annot $! mapCtCon f t1) $! mapCtCon f t2
mapCtCon f (CtLam annot v t1) = CtLam annot v $! mapCtCon f t1

instance HasAnnot (CoreTerm var atom) where
    getAnnot (CtVar annot _) = annot
    getAnnot (CtCon annot _) = annot
    getAnnot (CtApp annot _ _) = annot
    getAnnot (CtLam annot _ _) = annot
    setAnnot annot (CtVar _ v) = CtVar annot v
    setAnnot annot (CtCon _ c) = CtCon annot c
    setAnnot annot (CtApp _ t1 t2) = CtApp annot t1 t2
    setAnnot annot (CtLam _ x t1) = CtLam annot x t1

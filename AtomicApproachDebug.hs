module AtomicApproachDebug where

import AtomicApproachSearch2
import Text.Pretty.Simple (pPrint)

defConst = CONSTANTS {bot = "bot",
                      op_and = "^",
                      op_or = "v",
                      op_impl = "->"}

runDef :: VarState String t -> t
runDef vs = evalState vs (map (("x"++).show) [1,..]) 

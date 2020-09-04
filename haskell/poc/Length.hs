import Control.Monad.Trans.Writer
import Data.Monoid

tick :: Writer (Sum Int) ()
tick = tell (Sum 1)

length :: Traversable t => t a -> Int
length = getSum
       . execWriter
       . traverse (const tick)


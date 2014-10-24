{-# LANGUAGE Safe #-}
-- | Miscellaneous utilities.
module Utils where

-- | Mark something that shouldn't happen.
panic :: String -> a
panic msg = error ("[BUG] " ++ msg)



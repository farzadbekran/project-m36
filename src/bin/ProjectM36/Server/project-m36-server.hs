import ProjectM36.Server
import ProjectM36.Server.ParseArgs
import System.Exit (exitSuccess, exitFailure)
import Text.Fuzzy

main :: IO ()
main = do
  putStrLn "Fuzzy Included!"
  serverConfig <- parseConfig
  ret <- launchServer serverConfig Nothing
  if ret then exitSuccess else exitFailure

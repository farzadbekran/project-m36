import ProjectM36.Server
import ProjectM36.Server.ParseArgs
import System.Exit (exitSuccess, exitFailure)

main :: IO ()
main = do
  putStrLn "Now With Batteries Included!"
  serverConfig <- parseConfig
  ret <- launchServer serverConfig Nothing
  if ret then exitSuccess else exitFailure

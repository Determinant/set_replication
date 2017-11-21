{-# LANGUAGE DeriveGeneric #-}
module Main where

import System.Environment (getArgs)
import Network.Transport.TCP (createTransport, defaultTCPParameters)
import Network.Transport (EndPointAddress(..))
import Control.Distributed.Process
import Control.Distributed.Process.Node (initRemoteTable, runProcess, localNodeId, newLocalNode)
--import Control.Distributed.Process.Backend.SimpleLocalnet
import Control.Distributed.Process.Extras.Timer
import Control.Distributed.Process.Extras.Time
import Control.Concurrent (threadDelay)
import Control.Monad (forever, filterM, forM_)

import Data.Binary
import Data.Typeable
import Data.ByteString.Char8 (pack)
import Text.Printf
import GHC.Generics (Generic)
import qualified SetReplicationCore as SR


convert_list :: SR.List a -> [a]
convert_list SR.Nil = []
convert_list (SR.Cons h t) = h:(convert_list t)

convert_nat :: SR.Nat -> Int
convert_nat SR.O = 0
convert_nat (SR.S x) = 1 + convert_nat x

convert_state :: SR.State -> [Int]
convert_state s = map convert_nat $ convert_list s

data Msg = MsgAdd Int | MsgAck deriving (Typeable, Generic, Show)
data In = ReqAdd Int | ReqRead deriving (Typeable, Generic, Show)
data Out = AddResp | ReadResp [Int] deriving Show
data Node = P | B deriving Show

instance Binary Msg
instance Binary In

convert_node :: SR.Node -> Node
convert_node SR.Primary = P
convert_node SR.Backup = B

convert_packet :: SR.Packet SR.Node SR.Msg -> (Node, Msg)
convert_packet (SR.Build_packet node msg) = (convert_node node, convert_msg msg)

convert_packets :: SR.List (SR.Packet SR.Node SR.Msg) -> [(Node, Msg)]
convert_packets l = map convert_packet $ convert_list l

convert_msg :: SR.Msg -> Msg
convert_msg SR.Ack = MsgAck
convert_msg (SR.Add x) = MsgAdd $ convert_nat x

convert_input :: SR.Input -> In
convert_input (SR.Request_add x) = ReqAdd (convert_nat x)
convert_input SR.Request_read = ReqRead

convert_output :: SR.Output -> Out
convert_output SR.Add_response = AddResp
convert_output (SR.Read_response s) = ReadResp (convert_state s)

convert_outputs :: SR.List SR.Output -> [Out]
convert_outputs l = map convert_output $ convert_list l

build_nat :: Int -> SR.Nat
build_nat x
    | x == 0 = SR.O
    | otherwise = SR.S (build_nat (x - 1))

build_state :: [Int] -> SR.State
build_state [] = SR.Nil
build_state (x:xs) = SR.Cons (build_nat x) $ build_state xs

replyBack :: (ProcessId, String) -> Process ()
replyBack (sender, msg) = do send sender msg
                             say $ "handling " ++ msg

logMessage :: String -> Process ()
logMessage msg = say $ "handling " ++ msg

printResult :: SR.Prod (SR.Prod SR.State (SR.List SR.Packet0)) (SR.List SR.Output) -> IO ()
printResult (SR.Pair (SR.Pair s msgs) outs) =
    printf "s%s msgs%s outs%s\n" (show $ convert_state s) (show $ convert_packets msgs)
                               (show $ convert_outputs outs)

backups = map (\addr -> NodeId (EndPointAddress (pack addr))) ["127.0.0.1:2001:0"]
primary = NodeId (EndPointAddress (pack "127.0.0.1:2000:0"))

inputHandler :: In -> Process ()
inputHandler input = liftIO . putStrLn $ "got input: " ++ (show input)

msgHandler :: Msg -> Process ()
msgHandler msg = liftIO . putStrLn $ "got msg" ++ (show msg)

master_loop = do
    mapM_ (\p -> do nsendRemote p "backup" "msg from p") backups
    receiveWait [match inputHandler, match msgHandler]
    master_loop

backup_loop = do
    --nsendRemote primary "primary" "msg from b"
    msg <- expect :: Process String
    liftIO . putStrLn $ "got " ++ msg
    backup_loop


input = do
    nsendRemote primary "primary" (ReqAdd 0)
    liftIO . threadDelay $ 1000000
    input

main :: IO ()
main = do [id, host, port] <- getArgs
          printf "%s %s %s\n" id host port
          let SR.Pair (SR.Pair s msgs) outs = SR.processInput SR.Primary (SR.Request_add $ build_nat 4) (build_state [1, 3, 5])
          let SR.Pair (SR.Pair s' msgs') outs' = SR.processInput SR.Primary (SR.Request_add $ build_nat 6) s
          putStrLn $ "s" ++ (show $ convert_state s') ++ " msgs" ++ (show $ convert_packets msgs') ++ " outs" ++ (show $ convert_outputs outs')
          printResult $ SR.processMsg SR.Primary SR.Ack s'
          Right t <- createTransport host port defaultTCPParameters
          node <- newLocalNode t initRemoteTable
          runProcess node $ do
            pid <- getSelfPid
            register id pid
            case id of
                "primary" -> master_loop
                "backup" -> backup_loop
                "input" -> input

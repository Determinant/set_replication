{-# LANGUAGE DeriveGeneric #-}
module Main where

import Data.Binary
import Data.Typeable
import Data.ByteString.Char8 (pack)
import Text.Printf
import System.Random
import Control.Concurrent.MVar
import GHC.Generics (Generic)

import System.Environment (getArgs)
import Network.Transport.TCP (createTransport, defaultTCPParameters)
import Network.Transport (EndPointAddress(..))
import Control.Distributed.Process
import Control.Distributed.Process.Node (initRemoteTable, runProcess, newLocalNode)
import Control.Distributed.Process.Extras.Timer
import Control.Distributed.Process.Extras.Time
import Control.Concurrent (threadDelay)
import Control.Monad (forM_)

-- import the generated code by Coq
import qualified SetReplicationCore as SR

type State = [Int]

convert_list :: SR.List a -> [a]
convert_list SR.Nil = []
convert_list (SR.Cons h t) = h:(convert_list t)

convert_nat :: SR.Nat -> Int
convert_nat SR.O = 0
convert_nat (SR.S x) = 1 + convert_nat x

convert_state :: SR.State -> State
convert_state s = map convert_nat $ convert_list s

data Msg = MsgAdd Int | MsgAck deriving (Typeable, Generic, Show)
data In = ReqAdd Int | ReqRead deriving (Typeable, Generic, Show)
data Out = AddResp | ReadResp State deriving Show
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

build_input :: In -> SR.Input
build_input (ReqAdd x) = SR.Request_add (build_nat x)
build_input ReqRead = SR.Request_read

build_msg :: Msg -> SR.Msg
build_msg MsgAck = SR.Ack
build_msg (MsgAdd x) = SR.Add $ build_nat x


build_nat :: Int -> SR.Nat
build_nat x
    | x == 0 = SR.O
    | otherwise = SR.S (build_nat (x - 1))

build_state :: State -> SR.State
build_state [] = SR.Nil
build_state (x:xs) = SR.Cons (build_nat x) $ build_state xs

build_node :: Node -> SR.Node
build_node P = SR.Primary
build_node B = SR.Backup

backups_rawaddr = [("127.0.0.1", "2001")]
primary_rawaddr = ("127.0.0.1", "2000")
input_rawaddr = ("127.0.0.1", "2002")

to_nid (host, port) = host ++ ":" ++ port ++ ":0"

backups_addr = map (\addr -> NodeId (EndPointAddress (pack $ to_nid addr))) backups_rawaddr
primary_addr = NodeId (EndPointAddress (pack $ to_nid primary_rawaddr))
input_addr = NodeId (EndPointAddress (pack $ to_nid input_rawaddr))

pname = "default"

handlerWrapper :: (Show a) => Node -> MVar State ->
                                (SR.Node -> b -> SR.Handler) -> (a -> b) ->
                                a -> Process [(Node, Msg)]
handlerWrapper node state handler builder feed = liftIO $ do
    s <- takeMVar state
    let SR.Pair (SR.Pair s' msgs') outs' = handler (build_node node) (builder feed) (build_state s)
    let ss' = convert_state s'
    let nmsgs = convert_packets msgs'
    putMVar state ss'
    printf "got: %s\n" $ show feed
    printf "new state: %s\n" $ show ss'
    printf "send: %s\n" $ show nmsgs
    printf "output: %s\n" $ show (convert_outputs outs')
    return nmsgs

step :: Node -> MVar State -> Process ()
step node state = do
    outgoing <- receiveWait [match $ handlerWrapper node state SR.processInput build_input,
                             match $ handlerWrapper node state SR.processMsg build_msg]
    forM_ outgoing $ \packet -> do
        let (node, msg) = packet
        case node of
            P -> nsendRemote primary_addr pname msg
            B -> mapM_ (\b -> do nsendRemote b pname msg) backups_addr

primary_loop state = do step P state; primary_loop state
backup_loop state = do step B state; backup_loop state


input_loop (x:xs) = do
    nsendRemote primary_addr pname (ReqAdd (x `mod` 100))
    liftIO . threadDelay $ 1000000
    input_loop xs

main :: IO ()
main = do [id, num] <- getArgs
          printf "%s %s\n" id num
          state <- newMVar $ []
          rng <- newStdGen
          let ((host, port), main_loop) = case id of
                "primary" -> (primary_rawaddr, primary_loop state)
                "backup" -> (backups_rawaddr !! read num, backup_loop state)
                "input" -> (input_rawaddr, input_loop (randoms rng :: [Int]))
          Right t <- createTransport host port defaultTCPParameters
          node <- newLocalNode t initRemoteTable
          runProcess node $ do
            pid <- getSelfPid
            register pname pid
            main_loop

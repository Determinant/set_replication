module Main where

import Network.Transport.TCP (createTransport, defaultTCPParameters)
import Control.Distributed.Process
import Control.Distributed.Process.Node

import Lib
import Set_replication_core

convert_list :: List a -> [a]
convert_list Nil = []
convert_list (Cons h t) = h:(convert_list t)

convert_nat :: Nat -> Int
convert_nat O = 0
convert_nat (S x) = 1 + convert_nat x

convert_state :: State -> [Int]
convert_state s = map convert_nat $ convert_list s

data Mesg = MesgAdd Int | MesgAck deriving Show
data In = ReqAdd Int | ReqRead deriving Show
data Out = AddResp | ReadResp [Int] deriving Show
data Id = P | B deriving Show

convert_node :: Node -> Id
convert_node Primary = P
convert_node Backup = B

convert_packet :: Packet Node Msg -> (Id, Mesg)
convert_packet (Build_packet node msg) = (convert_node node, convert_msg msg)

convert_packets :: List (Packet Node Msg) -> [(Id, Mesg)]
convert_packets l = map convert_packet $ convert_list l

convert_msg :: Msg -> Mesg
convert_msg Ack = MesgAck
convert_msg (Add x) = MesgAdd $ convert_nat x

convert_input :: Input -> In
convert_input (Request_add x) = ReqAdd (convert_nat x)
convert_input Request_read = ReqRead

convert_output :: Output -> Out
convert_output Add_response = AddResp
convert_output (Read_response s) = ReadResp (convert_state s)

convert_outputs :: List Output -> [Out]
convert_outputs l = map convert_output $ convert_list l

build_nat :: Int -> Nat
build_nat x
    | x == 0 = O
    | otherwise = S (build_nat (x - 1))

build_state :: [Int] -> State
build_state [] = Nil
build_state (x:xs) = Cons (build_nat x) $ build_state xs

main :: IO ()
main = do Right t <- createTransport "127.0.0.1" "10501" defaultTCPParameters
          node <- newLocalNode t initRemoteTable
          let Pair (Pair s msgs) outs = processInput Primary (Request_add $ build_nat 4) (build_state [1, 3, 5])
          let Pair (Pair s' msgs') outs' = processInput Primary (Request_add $ build_nat 6) s
          let Pair (Pair s'' msgs'') outs'' = processMsg Primary Ack s'
          putStrLn $ "s" ++ (show $ convert_state s) ++ " msgs" ++ (show $ convert_packets msgs) ++ " outs" ++ (show $ convert_outputs outs)
          putStrLn $ "s" ++ (show $ convert_state s') ++ " msgs" ++ (show $ convert_packets msgs') ++ " outs" ++ (show $ convert_outputs outs')
          putStrLn $ "s" ++ (show $ convert_state s'') ++ " msgs" ++ (show $ convert_packets msgs'') ++ " outs" ++ (show $ convert_outputs outs'')
          return ()

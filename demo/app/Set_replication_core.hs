module Set_replication_core where

import qualified Prelude

data Unit =
   Tt

data Nat =
   O
 | S Nat

data Prod a b =
   Pair a b

data List a =
   Nil
 | Cons a (List a)

app :: (List a1) -> (List a1) -> List a1
app l m =
  case l of {
   Nil -> m;
   Cons a l1 -> Cons a (app l1 m)}

data Packet node msg =
   Build_packet node msg

data Node =
   Primary
 | Backup

data Msg =
   Add Nat
 | Ack

type State = List Nat

data Input =
   Request_add Nat
 | Request_read

data Output =
   Add_response
 | Read_response State

type Packet0 = Packet Node Msg

type Handler_monad a =
  State -> Prod (Prod (Prod a State) (List Packet0)) (List Output)

type Handler = State -> Prod (Prod State (List Packet0)) (List Output)

do0 :: (Handler_monad a1) -> Handler
do0 m s =
  case m s of {
   Pair p os ->
    case p of {
     Pair p0 ps -> case p0 of {
                    Pair _ s' -> Pair (Pair s' ps) os}}}

ret :: a1 -> Handler_monad a1
ret x s =
  Pair (Pair (Pair x s) Nil) Nil

bind :: (Handler_monad a1) -> (a1 -> Handler_monad a2) -> Handler_monad a2
bind ma f s =
  case ma s of {
   Pair p os ->
    case p of {
     Pair p0 ps ->
      case p0 of {
       Pair a s' ->
        case f a s' of {
         Pair p1 os' ->
          case p1 of {
           Pair p2 ps' -> Pair (Pair p2 (app ps ps')) (app os os')}}}}}

nop :: Handler_monad Unit
nop =
  ret Tt

send :: Node -> Msg -> Handler_monad Unit
send to msg s =
  Pair (Pair (Pair Tt s) (Cons (Build_packet to msg) Nil)) Nil

out :: Output -> Handler_monad Unit
out o s =
  Pair (Pair (Pair Tt s) Nil) (Cons o Nil)

get :: Handler_monad State
get s =
  Pair (Pair (Pair s s) Nil) Nil

set :: State -> Handler_monad Unit
set s _ =
  Pair (Pair (Pair Tt s) Nil) Nil

do_add :: Nat -> Handler_monad Unit
do_add h =
  bind get (\x -> set (Cons h x))

do_read :: Handler_monad Unit
do_read =
  bind get (\x -> out (Read_response x))

processInput :: Node -> Input -> Handler
processInput h i =
  do0
    (case h of {
      Primary ->
       case i of {
        Request_add h0 -> bind (do_add h0) (\_ -> send Backup (Add h0));
        Request_read -> do_read};
      Backup -> case i of {
                 Request_add _ -> nop;
                 Request_read -> do_read}})

processMsg :: Node -> Msg -> Handler
processMsg h m =
  do0
    (case h of {
      Primary -> case m of {
                  Add _ -> nop;
                  Ack -> out Add_response};
      Backup ->
       case m of {
        Add h0 -> bind (do_add h0) (\_ -> send Primary Ack);
        Ack -> nop}})


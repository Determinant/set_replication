Require Import List.
Require Import Bool.
Import ListNotations.
Require Import Sumbool.
Require Import Relations.

Module model.
(* simple etwork semantics from Verdi *)
Set Implicit Arguments.
Section Verdi.
  Variable node : Type.
  Variable state : Type.
  Variable msg : Type.
  Variable input : Type.
  Variable output : Type.
  Definition externalEvent : Type := node * (input + output).
  Record packet : Type := { dest : node; payload : msg }.
  Record world : Type :=
    { localState : node -> state;
      inFlightMsgs : list packet;
      trace : list externalEvent }.
  Variable initState    : node -> state.
  Variable processMsg   : node -> msg -> state ->
                          (state * list packet * list output).
  Variable processInput : node -> input -> state ->
                          (state * list packet * list output).
  Hypothesis msg_eq_dec : forall x y : msg, {x = y} + {x <> y}.
  Hypothesis node_eq_dec : forall x y : node, {x = y} + {x <> y}.
  Definition update (f : node -> state) (n : node) (st : state) : node -> state :=
    fun m => if node_eq_dec n m then st else f m.

  Lemma packet_eq_dec : forall x y : packet, {x = y} + {x <> y}.
    decide equality.
  Qed.

  Fixpoint remove_one (x : packet) (l : list packet) : list packet :=
    match l with
      | [] => []
      | y :: l' => if packet_eq_dec x y
                   then l'
                   else y :: remove_one x l'
    end.

  Definition record_outputs (n : node) (outs : list output) : list externalEvent :=
    map (fun o => (n, inr o)) outs.

(*begin code*)
  Inductive reliable_step : world -> world -> Prop :=
  | step_input :
      forall w i n st' ms outs,
        processInput n i (localState w n) = (st', ms, outs) ->
        reliable_step w
          (Build_world
             (update (localState w) n st')
             (ms ++ inFlightMsgs w)
             (trace w ++ [(n, inl i)] ++ record_outputs n outs))
  | step_msg :
      forall w p st' ms outs,
        In p (inFlightMsgs w) ->
        processMsg (dest p) (payload p)
                   (localState w (dest p)) = (st', ms, outs) ->
        reliable_step w
          (Build_world
             (update (localState w) (dest p) st')
             (ms ++ remove_one p (inFlightMsgs w))
             (trace w ++ record_outputs (dest p) outs)).
  Definition reliable_step_star := clos_refl_trans_n1 _ reliable_step.
  Definition initWorld : world := Build_world initState [] [].
  Definition reachable (w : world) : Prop := reliable_step_star initWorld w.
End Verdi.
End model.

Inductive node := primary | backup.
Inductive msg := add: nat -> msg | ack.
Definition state := list nat.
Inductive input := request_add: nat -> input | request_read.
Inductive output := add_response | read_response: state -> output.

Definition initState (_ : node) : state := [].
Definition packet := (model.packet node msg).

Definition handler_monad A :=
  state -> A * state * list packet * list output.
Definition handler :=
  state -> state * list packet * list output.
Definition do {A : Type} (m : handler_monad A) : handler :=
  fun s => let '(a, s', ps, os) := m s in (s', ps, os).
Definition ret {A : Type} (x : A) : handler_monad A :=
  fun s => (x, s, [], []).
Definition bind {A B : Type} (ma : handler_monad A)
           (f : A -> handler_monad B) : handler_monad B :=
  fun s => let '(a, s', ps, os) := ma s in
        let '(b, s'', ps', os') := f a s' in
        (b, s'', ps ++ ps', os ++ os').

Notation "x <- c1 ;; c2" :=
  (@bind _ _ c1 (fun x => c2))
    (at level 100, c1 at next level, right associativity).

Notation "e1 ;; e2" :=
  (_ <- e1 ;; e2)
    (at level 100, right associativity).

Definition nop :=
  ret tt.
Definition send to msg : handler_monad unit :=
  fun s => (tt, s, [model.Build_packet to msg], []).
Definition out o : handler_monad unit :=
  fun s => (tt, s, [], [o]).
Definition get : handler_monad state :=
  fun s => (s, s, [], []).
Definition set s : handler_monad unit :=
  fun _ => (tt, s, [], []).

Definition do_add (h : nat): handler_monad unit :=
  x <- get ;; set (h::x).
Definition do_read: handler_monad unit :=
  x <- get ;; out (read_response x).

Definition processInput (h : node) (i : input) : handler :=
  do
    match h with
    | primary => match i with
                | request_add h => do_add h;; send backup (add h)
                | request_read => do_read
                end
    | backup => match i with
                | request_read => do_read
                | _ => nop
                end
    end.

Definition processMsg (h : node) (m : msg) : handler :=
  do
    match h with
    | backup => match m with
               | add h => do_add h;; send primary ack
               | _ => nop
               end

    | primary => match m with
                | ack => out add_response
                | _ => nop
                end
    end.

Definition data_eq_dec: forall x y : nat, {x = y} + {x <> y}.
Proof. decide equality. Defined.
Definition node_eq_dec : forall x y : node, {x = y} + {x <> y}.
Proof. decide equality. Defined.
Definition node_eqb (x y : node) : bool :=
  if node_eq_dec x y then true else false.
Definition msg_eq_dec : forall x y : msg, {x = y} + {x <> y}.
Proof. decide equality. apply data_eq_dec. Defined.
Definition msg_eqb (x y : msg) : bool :=
  if msg_eq_dec x y then true else false.

Notation reliable_step :=
  (model.reliable_step processMsg processInput msg_eq_dec node_eq_dec).
Notation world :=
  (model.world node state msg input output).
Notation reliable_step_star :=
  (model.reliable_step_star processMsg processInput msg_eq_dec node_eq_dec).
Notation reachable :=
  (model.reachable initState processMsg processInput msg_eq_dec node_eq_dec).
Notation update :=
  (@model.update node (list nat) node_eq_dec).
Notation remove_one :=
  (@model.remove_one node msg msg_eq_dec node_eq_dec).
Notation initWorld := (model.initWorld msg input output initState).


(* begin proofs *)

(* utility lemmas about the properties of sets represented by lists with possibly duplicate values *)
Definition subset (l1 l2: list nat) : Prop := forall (x: nat), In x l1 -> In x l2.
Definition eqset (l1 l2: list nat) : Prop := (subset l1 l2) /\ (subset l2 l1).

Fixpoint new_elems (l : list packet) : list nat :=
  match l with
  | nil => nil
  | p :: t => match (model.dest p) with
              | backup => match (model.payload p) with
                          | add h => h :: (new_elems t)
                          | _ => new_elems t
                          end
              | _ => new_elems t
              end
  end.

Lemma eqset_comm: forall l1 l2, eqset l1 l2 <-> eqset l2 l1.
Proof.
  intros.
  unfold eqset.
  unfold iff.
  split; intros; apply and_comm; congruence.
Qed.

Lemma eqset_trans: forall l1 l2 l3, eqset l1 l2 -> eqset l2 l3 -> eqset l1 l3.
Proof.
  intros.
  unfold eqset in *.
  destruct H, H0.
  split; unfold subset in *.
  induction l1, l2; auto.
  induction l2, l3; auto.
Qed.

Lemma subset_refl: forall l, subset l l.
  unfold subset.
  induction l.
  auto.
  intros.
  auto.
Qed.

Lemma eqset_refl: forall l, eqset l l.
Proof.
  intros.
  unfold eqset; split.
  apply subset_refl.
  apply subset_refl.
Qed.

Lemma in_empty: forall (l: list nat) x, In x (l ++ []) <-> In x l.
Proof.
  induction l; intros; simpl; unfold iff in *; split; auto.
  intros.
  - destruct H; auto; destruct (IHl x); pose (p := H0 H); auto.
  - destruct (IHl x); intros; destruct H1; auto.
Qed.

Lemma in_split: forall (l1 l2: list nat) x, In x (l1 ++ l2) <-> (In x l1 \/ In x l2).
Proof.
  unfold iff. split; intros; induction l1; simpl; simpl in H; auto; destruct H; auto.
  pose (p := IHl1 H). inversion p; auto.
  inversion H. destruct H; auto.
Qed.

Lemma in_shuffle: forall (l1 l2: list nat) x h, In x ((h :: l1) ++ l2) <-> In x (l1 ++ h :: l2).
Proof.
  intros.
  split; unfold iff in *; intros;
  rewrite in_split in H;
  rewrite in_split; destruct H;
  simpl in *; auto; destruct H; auto.
Qed.

Lemma eqset_shuffle: forall l1 l2 l3 h, eqset ((h :: l1) ++ l2) l3 -> eqset (l1 ++ h :: l2) l3.
Proof.
  intros.
  rewrite (eqset_comm ((h :: l1) ++ l2) l3) in H.
  rewrite (eqset_comm (l1 ++ h :: l2) l3).
  induction l3; intros; unfold eqset in *; unfold subset in *;
  split; destruct H; intros; simpl; auto.
  rewrite <- in_shuffle.
  - exact (H x H1).
  - rewrite <- in_shuffle in H1.
    apply (H0 x H1).
  - rewrite <- in_shuffle.
    exact (H x H1).
  - rewrite <- in_shuffle in H1.
    apply (H0 x H1).
Qed.

Lemma subset_part0: forall l1 l2 a, subset (a :: l1) l2 -> subset l1 l2.
Proof.
  intros.
  unfold subset in H; simpl in H; unfold subset.
  intros. apply (H x (or_intror H0)).
Qed.
  
Lemma subset_part: forall l1 l2 l3, subset (l1 ++ l2) l3 -> subset l2 l3.
Proof.
  intros.
  induction l1; auto.
  rewrite <- app_comm_cons in H.
  exact (IHl1 (subset_part0 (l1 ++ l2) l3 a H)).
Qed.

Lemma subset_add: forall l1 l2 x, subset l1 l2 -> subset (x :: l1) (x :: l2).
Proof.
  intros.
  induction l1; unfold subset in *; simpl; auto; intros; destruct H0; auto.
Qed.

Lemma eqset_add: forall l1 l2 x, eqset l1 l2 -> eqset (x :: l1) (x :: l2).
Proof.
  intros; unfold eqset in *; split; destruct H; apply subset_add; auto.
Qed.

Lemma eqset_subst0: forall l1 l2 l3, eqset l1 l2 -> eqset (l1 ++ l3) (l2 ++ l3).
Proof.
  induction l3; unfold eqset in *; unfold subset in *; split; destruct H; intros;
  match goal with
  | H:_ |- In _ (_ ++ []) =>
    rewrite in_empty in *; eauto
  | H:_ |- In _ (_ ++ _ :: _) =>
    pose (p := IHl3 (conj H  H0)); destruct p;
    rewrite <- in_shuffle in *; simpl; simpl in H1; destruct H1; eauto
  end.
Qed.

Lemma eqset_subst: forall l1 l2 l3 l4, eqset l1 l2 -> eqset (l1 ++ l3) l4 -> eqset (l2 ++ l3) l4.
Proof.
  intros.
  pose (p := eqset_subst0 l1 l2 l3 H).
  rewrite eqset_comm.
  rewrite eqset_comm in H0.
  apply (eqset_trans l4 (l1 ++ l3)); eauto.
Qed.

Lemma subset_lswap: forall l1 l2 a b, subset (a :: b :: l1) l2 -> subset (b :: a :: l1) l2.
Proof.
  intros.
  unfold eqset in *; unfold subset in *; simpl.
  intros; destruct H0; apply H; simpl; destruct H0; auto.
Qed.

Lemma subset_rswap: forall l1 l2 a b, subset l2 (a :: b :: l1) -> subset l2 (b :: a :: l1).
Proof.
  intros.
  unfold eqset in *; unfold subset in *; simpl. intros.
  pose (p := (H x H0)). destruct p; destruct H1; eauto.
Qed.

Lemma eqset_swap: forall l1 l2 a b, eqset (a :: b :: l1) l2 -> eqset (b :: a :: l1) l2.
Proof.
  unfold eqset in *; split; intros; destruct H.
  apply subset_lswap; auto.
  apply subset_rswap; auto.
Qed.

Lemma new_elems_cons_backup_add :
  forall l h,
   eqset (new_elems (model.Build_packet backup (add h) :: l)) (h :: (new_elems l)).
Proof.
  intros.
  unfold eqset.
  unfold subset in *.
  split; unfold new_elems; simpl; intros; congruence.
Qed.

Lemma new_elems_cons_primary :
  forall l m,
    eqset (new_elems (model.Build_packet primary m :: l)) (new_elems l).
Proof.
  intros.
  unfold eqset.
  unfold subset in *.
  split; unfold new_elems; simpl; apply subset_refl.
Qed.

Lemma new_elems_cons_ack :
  forall l h,
    eqset (new_elems (model.Build_packet h ack :: l)) (new_elems l).
Proof.
  intros.
  unfold eqset.
  unfold subset in *.
  split; unfold new_elems; simpl; destruct h; apply subset_refl.
Qed.

Ltac break_if :=
  match goal with
    | [ |- context [ if ?X then _ else _ ] ] =>
      match type of X with
        | sumbool _ _ => destruct X
        | _ => destruct X eqn:?
      end
    | [ H : context [ if ?X then _ else _ ] |- _] =>
      match type of X with
        | sumbool _ _ => destruct X
        | _ => destruct X eqn:?
      end
  end.

Lemma new_elems_remove_backup_add :
  forall l h,
    In (model.Build_packet backup (add h)) l ->
    eqset (h :: (new_elems (remove_one (model.Build_packet backup (add h)) l))) (new_elems l).
Proof.
  induction l; simpl; intuition.
  - subst. break_if; try congruence.
    pose (p := new_elems_cons_backup_add l h).
    rewrite eqset_comm in p.
    refine (eqset_trans _ _ _ _ _).
    + eapply p.
    + simpl. destruct dest.
      * unfold eqset; unfold subset; unfold new_elems; simpl; intros; congruence.
      * destruct payload; inversion H0; rewrite <- H1; unfold eqset; split; apply subset_refl.
  - break_if.
    + inversion e; subst.
      pose (p := new_elems_cons_backup_add l h).
      rewrite eqset_comm in p.
      refine (eqset_trans _ _ _ _ _).
      eapply p.
      rewrite eqset_comm in p.
      eauto.
    + destruct dest, payload; simpl; pose (t := IHl h H0); auto.
      pose (p := new_elems_cons_primary l (add h)).
      apply eqset_swap.
      apply eqset_add.
      auto.
Qed.

Lemma new_elems_remove_ack:
  forall l h,
    eqset (new_elems (remove_one (model.Build_packet h ack) l)) (new_elems l).
Proof.
  induction l; simpl; intuition.
  unfold eqset; split; apply (subset_refl []).
  break_if.
  + inversion e; subst.
    destruct dest; remember (model.payload {| model.dest := primary;
                                                         model.payload := ack |}); destruct m; simpl;
    apply (eqset_refl (new_elems l)).
  + destruct dest; destruct payload; simpl;
    try apply eqset_add; try apply IHl.
Qed.

Lemma new_elems_remove_primary :
  forall l m,
    eqset (new_elems (remove_one (model.Build_packet primary m) l)) (new_elems l).
Proof. 
  induction l; simpl; intuition.
  unfold eqset; split; apply subset_refl.
  break_if.
  - inversion e; subst.
    remember (model.dest {| model.dest := primary;
                                       model.payload := payload |}).
    destruct n. 
    apply eqset_refl.
    destruct payload.
    inversion Heqn.
    apply eqset_refl.
  - destruct dest, payload; simpl;
    try apply eqset_add; try apply IHl.
Qed.

Lemma update_same : forall f x v, update f x v x = v.
Proof.
  intros. unfold update. break_if; congruence.
Qed.

Lemma update_diff : forall f x v y, x <> y -> update f x v y = f y.
Proof.
  intros. unfold update. break_if; congruence.
Qed.

Definition backup_union_new_elems_eq_primary (w : world) : Prop :=
  eqset ((new_elems (model.inFlightMsgs w)) ++ model.localState w backup)
        (model.localState w primary).

Definition backup_subset_primary (w : world) : Prop :=
  subset (model.localState w backup) (model.localState w primary).

Lemma backup_union_new_elems_eq_primary_true :
  forall w, reachable w ->
       backup_union_new_elems_eq_primary w.
Proof.
  intros w Hreach.
  induction Hreach as [|w1 w2 Hstep _ IH].
  - unfold backup_union_new_elems_eq_primary.
    unfold initWorld; unfold initState; simpl; unfold eqset; split; apply subset_refl.
  - inversion Hstep; subst.
    * unfold processInput in *.
      destruct i, n; inversion H; subst;
      unfold backup_union_new_elems_eq_primary, state in *; simpl;
      rewrite update_same, update_diff by congruence;
      unfold eqset in *; split; destruct IH;
      try apply subset_add; auto.
    * unfold processMsg in *.
      destruct p. simpl in *.
      destruct dest, payload;
      inversion H0; subst; unfold backup_union_new_elems_eq_primary, state in *; simpl;
      rewrite update_same, update_diff by congruence.
      + pose (p := new_elems_remove_primary (model.inFlightMsgs w1) (add n)).
        apply (eqset_subst (new_elems (model.inFlightMsgs w1)));
        rewrite eqset_comm in p; auto.
      + pose (p := new_elems_remove_ack (model.inFlightMsgs w1) primary).
        apply (eqset_subst (new_elems (model.inFlightMsgs w1)));
        rewrite eqset_comm in p; auto.
      + pose (p := new_elems_remove_backup_add (model.inFlightMsgs w1) n H).
        apply (eqset_shuffle (new_elems (remove_one {| model.dest := backup;
                                                       model.payload := add n |}
                                        (model.inFlightMsgs w1))));
        rewrite eqset_comm in p;
        apply (eqset_subst (new_elems (model.inFlightMsgs w1))); auto.
      + pose (p := new_elems_remove_ack (model.inFlightMsgs w1) backup);
        apply (eqset_subst (new_elems (model.inFlightMsgs w1)));
        rewrite eqset_comm in p; auto.
Qed.


Theorem backup_subset_primary_true :
  forall w,
    reachable w ->
    backup_subset_primary w.
Proof.
  intros.
  apply backup_union_new_elems_eq_primary_true in H.
  unfold backup_union_new_elems_eq_primary, backup_subset_primary in *.
  unfold eqset in H.
  destruct H.
  apply (subset_part (new_elems (model.inFlightMsgs w))); auto.
Qed.

Require Extraction.
Extraction Language Haskell.
Extraction "set_replication_core.hs" processMsg processInput.

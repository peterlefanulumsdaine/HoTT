(* -*- mode: coq; mode: visual-line -*- *)

(** * The Freudenthal Suspension Theorem, and related results. *)

Require Import Overture PathGroupoids Fibrations Equivalences Trunc EquivalenceVarieties Forall Sigma Paths Unit Universe Arrow Connectedness Suspension Truncations HoTT.
Local Open Scope path_scope.
Local Open Scope equiv_scope.
Generalizable Variables X A B f g n.

(** ** Auxiliary lemmas *)

(* TODO: move! *)
Definition ap10_path_forall `{Funext} {A B : Type} (f g : A -> B) (h : f == g)
  : ap10 (path_forall f g h) == h
:= apD10_path_forall f g h.

(** Infrastructure for handling axioms at a second universe level *)
Inductive Large (X : Type) := to_large (x : X) : Large X.

Definition from_large {X:Type} (l : Large X) : X
  := match l with to_large x => x end.
 
Definition with_large {X : Type} {A : Type} : (X -> A) -> (Large X) -> A
  := fun f l => f (from_large l).

Definition with_large_D {X : Type} {P : X -> Type} : (forall x, P x) -> (forall l, P (from_large l))
  := fun f l => f (from_large l).

(** TODO: move the following few lemmas. *)
Lemma transport_as_ap {A} (P : A -> Type) {x y} (p : x = y)
  : transport P p == transport idmap (ap P p).
Proof.
  intros ?; destruct p; exact 1.
Defined.

(** A sequence of transport lemmas about the kind of transport that occurs in Freudenthal. *)
(* TODO: move! *)
Definition pathD_fib `{Funext} `{Univalence}
  {A : Type} (B : A -> Type)
  {a1 a2 : A} (q : a1 = a2)
  (P1 : B a1 -> Type) (P2 : B a2 -> Type)
  (F : forall z : B a1, P1 z <~> P2 (q # z))
: (transport (fun a => (B a -> Type)) q P1 = P2).
Proof.
  destruct q; simpl in *.
  apply path_arrow. intros z.
  apply path_universe_uncurried, F.
Defined.

Definition pathD_fib_inv
  {A : Type} (B : A -> Type)
  {a1 a2 : A} (q : a1 = a2)
  (P1 : B a1 -> Type) (P2 : B a2 -> Type)
  (Q : transport (fun a => (B a -> Type)) q P1 = P2)
: forall z : B a1, P1 z <~> P2 (q # z).
Proof.
  destruct q; simpl in *.
  intros z. apply equiv_path, ap10, Q.
Defined.

Instance isequiv_pathD_fib `{Funext} `{Univalence}
  {A : Type} (B : A -> Type)
  {a1 a2 : A} (q : a1 = a2)
  (P1 : B a1 -> Type) (P2 : B a2 -> Type)
: IsEquiv (pathD_fib B q P1 P2).
Proof.
  refine (isequiv_adjointify _ (pathD_fib_inv _ _ _ _) _ _).
    intros Q. destruct q; simpl in *.
    path_via (path_arrow P1 P2 (fun z : B a1 => ap10 Q z)).
      apply ap, path_forall. intros z. apply eissect.
    apply eta_path_arrow.
  intros F. destruct q; simpl in *.
  apply path_forall; intros z.
  path_via (equiv_path _ _ (path_universe_uncurried (F z))).
    apply ap. refine (ap10_path_arrow _ _ _ _).
  apply eisretr.
Defined.

Lemma pathD_fib_inv_apD `{Funext} `{Univalence}
  {A : Type} {B : A -> Type} (C : forall a, B a -> Type)
  {a1 a2 : A} (q : a1 = a2)
  (b : B a1) (c : C a1 b)
: (pathD_fib B q (C a1) (C a2)) ^-1 (apD C q) b c
  = transportD B C q b c.
Proof.
  destruct q; simpl in *. exact 1.
Defined.


Lemma transportD'
  {A : Type} (B : A -> Type) (C : forall a : A, B a -> Type)
  {x1 x2 : A} (p : x1 = x2) (y : B x1)
: C x1 y -> C x2 (transport B p y).
Proof.
  refine (transport idmap _).
  refine (_ @ ap10 (apD C p) _).
  apply inverse.
  refine (transport_arrow _ _ _ @ _).
  refine (transport_const _ _ @ _).
  apply ap, transport_Vp.
Defined.

Arguments transportD' / [_] _ _ [_ _] _ _ _.

Lemma transportD_as_apD
  {A : Type} (B : A -> Type) (C : forall a : A, B a -> Type)
  {x1 x2 : A} (p : x1 = x2) (y : B x1)
: transportD B C p y == transportD' B C p y.
Proof.
  intros ?; destruct p; simpl. exact 1.
Defined.

(* ** Connectedness of the suspension *)

Instance isconn_susp {n : trunc_index} {X : Type} `{IsConnected n X}
  : IsConnected (trunc_S n) (Susp X).
Proof.
  intros C ? f. exists (f North).
  assert ({ p0 : f North = f South & forall x:X, ap f (merid x) = p0 })
    as [p0 allpath_p0] by auto.
  apply (Susp_rect (fun a => f a = f North) 1 p0^).
  intros x. 
  apply (concat (transport_paths_Fl _ _)).
  apply (concat (concat_p1 _)).
  apply ap, allpath_p0.
Defined.

(** ** The Freudenthal Suspension Theorem *)
Section Freudenthal.

(** We assume funext and univalence.  In fact, since we will use funext at two different levels and local assumptions are monomorphic, we need to assume funext twice; we give the second assumption of it a name (so we can use it explicitly when we want it), and a different type (so it doesn’t get used when we don’t want it). TODO: perhaps this could be handled in a more uniform way?? *)
Context `{Funext} (funext_large : Large Funext) `{Univalence}
        {n : trunc_index} {Hn : ~ n = minus_two}
        (X : Type) (x0:X) `{IsConnMap n _ _ (unit_name x0)}.

(* TODO: eventually, change these to the weaker assumptions:
Context {n : trunc_index} (X : Type) `{IsConnected (trunc_S n) X}.
*)

(** For convenience, we add some local abbreviations. *)
Notation No := (@North X).
Notation So := (@South X).
Notation mer := (@merid X).
Definition mer' := (fun x => mer x @ (mer x0)^).

(** The eventual theorem we want is: *)
Instance Freudenthal
  : IsConnMap (n -2+ n) (mer').
Proof.
  intros p. apply @isconnected_from_iscontr_truncation.
(** We are not ready to prove this yet.  For the remainder of the section, we will generalize this goal a bit, and prove some auxiliary lemmas; then we will return to the theorem. *)
Abort.

(** The goal we require for the FST is: *)
Definition FST_Codes_No (p : No = No)
  := (Truncation (n -2+ n) (hfiber mer' p)).

(** To prove it, we generalise it over [Susp X], by [Susp_rect].  This requires three components, which we construct (the main parts of) as lemmas in advance. *)
Definition FST_Codes_So (q : No = So)
  := (Truncation (n -2+ n) (hfiber mer q)).

(* TODO: move! *)
Definition hfiber_pair {A B} {f: A -> B} {b} (a:A) (p:f a = b) : hfiber f b
  := (a;p).

Definition FST_Codes_cross (x1 : X) (p : No = No)
  : FST_Codes_No p -> FST_Codes_So (p @ mer x1).
Proof.
  unfold FST_Codes_No, FST_Codes_So, mer'.
  apply Truncation_rect_nondep.
  intros [x2 r]. revert x1 x2 r.
  refine (@wedge_incl_elim_uncurried _ _ n n X x0 _ X x0 _
    (fun x1 x2 => (mer x2 @ (mer x0) ^ = p
           -> Truncation (n -2+ n) (hfiber mer (p @ mer x1)))) _ _).
  apply (conn_pointed_type x0). apply (conn_pointed_type x0).  
  intros; apply trunc_arrow.
  exists (fun b s => truncation_incl (hfiber_pair b
                              ((concat_pV_p _ _)^ @ whiskerR s _))).
  exists (fun a r => truncation_incl (hfiber_pair a
      ((concat_1p _)^ @ whiskerR (concat_pV _)^ _ @ whiskerR r _))).
  apply path_forall; intros s. apply ap, ap, whiskerR. clear p s.
  generalize (mer x0). intros p; destruct p; exact 1.
Defined.

(** Obsolete? *)
Definition FST_Codes_cross' (x1 : X) (q : No = So)
  : FST_Codes_No (q @ (mer x1) ^) -> FST_Codes_So q.
Proof.
  unfold FST_Codes_No, FST_Codes_So, mer'.
  apply Truncation_rect_nondep.
  intros [x2 p]. revert x1 x2 p.
  refine (@wedge_incl_elim_uncurried _ _ n n X x0 _ X x0 _
    (fun x1 x2 => (mer x2 @ (mer x0) ^ = q @ (mer x1) ^)
                    -> Truncation (n -2+ n) (hfiber mer q)) _ _).
  apply (conn_pointed_type x0). apply (conn_pointed_type x0).  
  intros; apply trunc_arrow.
  exists (fun b s => truncation_incl (hfiber_pair b (cancelR _ _ _ s))).
  exists (fun a r => truncation_incl (hfiber_pair a
                 (cancelR _ _ _ ((concat_pV _) @ (concat_pV _)^ @ r)))).
  apply path_forall; intros s. apply ap, ap, ap.
  exact ((concat_1p _)^ @ whiskerR (concat_pV _)^ _).
Defined.

(** We will need to show that [FST_Codes_cross] is an equivalence, for each [x1, q]. By connectedness of [X], it will be enough to show this for the case [x1 = x0]; to show this, we first write that case in a tidier form. *)
Definition FST_Codes_cross_x0 (p : No = No)
  : FST_Codes_No p -> FST_Codes_So (p @ mer x0).
Proof.
  unfold FST_Codes_No, FST_Codes_So.
  apply functor_Truncation, (functor_sigma idmap).
  unfold mer'; intros x1. apply moveL_pM.
Defined.

Definition isequiv_FST_Codes_cross (x : X) (p : No = No)
  : IsEquiv (FST_Codes_cross x p).
Proof.
  revert x. 
  apply (@conn_map_elim _ _ _ (unit_name x0) _
    (fun x => IsEquiv (FST_Codes_cross x p))).
    intros x; generalize dependent n. intros [ | n'] imposs.
      destruct (imposs 1).
      intros ?. apply (@trunc_leq minus_one). exact tt. apply hprop_isequiv.
  intros []. unfold FST_Codes_cross.
  apply (isequiv_homotopic (FST_Codes_cross_x0 p)). Focus 2.
    apply Truncation_rect. intros ?; apply trunc_succ.
    intros [x r]; simpl.
    unfold functor_sigma; simpl.
    apply symmetry.
    apply @concat with (y := @truncation_incl (n -2+ n) _ (hfiber_pair x
           ((concat_pV_p (mer x) (mer x0)) ^ @ whiskerR r (mer x0)))).
    refine ((ap10 (wedge_incl_comp1 x0 x0 _ _ _ _ x) r)).
    apply ap, ap. destruct r; simpl. unfold mer'.
    assert (lem : forall (A : Type) (a b c : A) (p : a = b) (q : c = b),
      (concat_pV_p p q) ^ @ 1 = moveL_pM q p (p @ q^) 1).
    intros A a b c p q. destruct p, q. exact 1.
    apply lem.
  unfold FST_Codes_cross_x0.
  apply isequiv_functor_Truncation, @isequiv_functor_sigma. refine _.
  intros a. apply isequiv_moveL_pM.
Qed.

(** Obsolete? *)
Definition FST_Codes_cross_x0' (q : No = So)
  : FST_Codes_No (q @ (mer x0)^) -> FST_Codes_So q.
Proof.
  unfold FST_Codes_No, FST_Codes_So.
  apply functor_Truncation, (functor_sigma idmap).
  unfold mer'; intros x1. apply cancelR.
Defined.

(** Obsolete? *)
Definition isequiv_FST_Codes_cross' (x : X) (q : No = So)
  : IsEquiv (FST_Codes_cross' x q).
Proof.
  revert x. 
  apply (@conn_map_elim _ _ _ (unit_name x0) _
    (fun x => IsEquiv (FST_Codes_cross' x q))).
    intros x; generalize dependent n. intros [ | n'] imposs.
      destruct (imposs 1).
      intros ?. apply (@trunc_leq minus_one). exact tt. apply hprop_isequiv.
  intros []. unfold FST_Codes_cross.
  apply (isequiv_homotopic (FST_Codes_cross_x0' q)). Focus 2.
    apply Truncation_rect. intros ?; apply trunc_succ.
    intros [x r]; simpl.
    unfold functor_sigma; simpl.
    apply symmetry. refine (ap10 (wedge_incl_comp1 x0 x0 _ _ _ _ x) r).
  unfold FST_Codes_cross_x0.
  apply isequiv_functor_Truncation, @isequiv_functor_sigma. refine _.
  intros a. apply isequiv_cancelR.
Defined.

Definition FST_Codes 
  : forall (y : Susp X), (No = y) -> Type.
Proof.
  apply (Susp_rect (fun y => (No = y -> Type)) FST_Codes_No FST_Codes_So).
  intros x. apply (with_large (@pathD_fib) funext_large). refine _.
  intros p. equiv_via (FST_Codes_So (p @ (mer x))).
  exists (FST_Codes_cross x p). apply isequiv_FST_Codes_cross.
  refine (equiv_transport _ _ _ _). apply symmetry, transport_paths_r.
Defined.

Definition FST_Codes'
  : forall (y : Susp X), (No = y) -> Type.
Proof.
  apply (Susp_rect (fun y => (No = y -> Type)) FST_Codes_No FST_Codes_So).
  intros x. apply (with_large (@path_forall) funext_large); intros p.
  refine (transport_arrow _ _ _ @ _).
  refine (transport_const _ _ @ _).
  path_via (FST_Codes_No (p @ (mer x)^)).
    apply ap, transport_paths_r.
  apply path_universe_uncurried.
  exists (FST_Codes_cross' x p).
  apply isequiv_FST_Codes_cross'.
Defined.

(** It now remains to show that each [FST_Codes y p] is contractible. It is easy to provide a canonical inhabitant, by transport. (More directly, we could use path-induction, but we will later need to use transport lemmas to reason about this.) *)
Definition FST_Codes_center (y : Susp X) (p : No = y)
  : FST_Codes y p.
Proof.
  assert (goal' : FST_Codes y (transport _ p 1)).
    apply transportD. simpl; unfold FST_Codes_No.
    apply truncation_incl. exists x0; unfold mer'. apply concat_pV.
  refine (transport _ _ goal'). refine (transport_paths_r _ _ @ _).
  apply concat_1p.
Defined.

(** A transport lemma. *)
Definition FST_Codes_transportD_concrete (x1 : X) (p : No = No)
  : FST_Codes No p <~> FST_Codes So (transport (paths No) (mer x1) p).
Proof.
  equiv_via (FST_Codes So (p @ mer x1)).
  exists (FST_Codes_cross _ _). apply isequiv_FST_Codes_cross.
  refine (equiv_transport FST_Codes_So _ _ _).
  apply inverse, transport_paths_r.
Defined.

(** TODO: move! *)
Definition transportD_pp {A} {B : A -> Type} {C : forall a : A, B a -> Type}
  (x1 x2 x3 : A) (p : x1 = x2) (q : x2 = x3) (y : B x1) (z : C x1 y)
: transportD B C (p @ q) y z
  = transport _ (transport_pp B p q y)^
      (transportD B C q _ (transportD B C p y z)).
Proof.
  destruct p, q. simpl. exact 1.
Defined.

(* TODO: streamline?? *)
Definition transportD_FST_Codes (x1 : X) (p : No = No) (rr : FST_Codes No p)
  : transportD (paths No) FST_Codes (mer x1) p rr 
  = FST_Codes_transportD_concrete x1 p rr.
Proof.
  refine ((@pathD_fib_inv_apD (from_large funext_large) _ _ _ _ _ _ _ _ _)^
           @ _).
  path_via ((@pathD_fib (from_large funext_large) _ _ (paths No) _ _ (mer x1) (FST_Codes No) (FST_Codes So))^-1
    (@pathD_fib (from_large funext_large) _ _ (paths No) _ _ (mer x1) (FST_Codes No) (FST_Codes So)
      (fun p0 : No = No =>
          equiv_composeR'
            {|
            equiv_fun := FST_Codes_cross x1 p0;
            equiv_isequiv := isequiv_FST_Codes_cross x1 p0 |}
            (equiv_transport FST_Codes_So (p0 @ mer x1)
               (transport (paths No) (mer x1) p0)
               (symmetry (transport (paths No) (mer x1) p0) 
                  (p0 @ mer x1) (transport_paths_r (mer x1) p0))))) p rr).
    unfold FST_Codes. rewrite Susp_comp_merid; simpl. exact 1.
  unfold with_large. rewrite eissect. simpl; exact 1.
Defined.

(* TODO: eliminate! *)
Definition transportD_inverse {A} {B : A -> Type} {C : forall a : A, B a -> Type}
  (x1 x2 : A) (p : x1 = x2) (y : B x1)
: C x2 (transport B p y) -> C x1 y.
Proof.
  intros z. refine (_ (transportD B C p^ _ z)).
  refine (transport (C x1) (transport_Vp _ _ _)).
Defined.

(* TODO: move! *)
Definition isequiv_transportD {A} {B : A -> Type} {C : forall a : A, B a -> Type}
  (x1 x2 : A) (p : x1 = x2) (y : B x1)
: IsEquiv (transportD B C p y).
Proof.
  refine (isequiv_adjointify _ (fun z =>
    transport (C x1) (transport_Vp _ _ _) (transportD B C p^ _ z)) _ _).
  intros z. destruct p; simpl. exact 1.
  intros z. destruct p; simpl. exact 1.
Defined.

Existing Instance isequiv_transportD.

Definition FST_Codes_contr (y : Susp X) (p : No = y) (rr : FST_Codes y p)
  : rr = FST_Codes_center y p.
Proof.
  destruct p. revert rr. generalize (idpath No); simpl. intros p.
  apply Truncation_rect. intros rr; apply trunc_succ.
  intros [x1 r]. destruct r. unfold mer', FST_Codes_center.
  rewrite transportD_pp.
  set (HH := (FST_Codes_transportD_concrete x1 1)
             (FST_Codes_transportD_concrete x0 1)^-1
             (truncation_incl (x0; concat_pV (mer x0)))).
  refine (_ @ @ap _ _ _ _ _ _).
  path_via (transport (FST_Codes No)
    (transport_paths_r (mer x1 @ (mer x0) ^) 1 @ concat_1p (mer x1 @ (mer x0) ^))
  (hfiber_pair x1
    (transport_paths_r (mer x1 @ (mer x0) ^) 1 @ concat_1p (mer x1 @ (mer x0) ^)))).
  rewrite transportD_FST_Codes.
Defined.


Definition FST_Codes_transportD (x1 : X) (p : No = No) (rr : FST_Codes No p)
  : transportD (paths No) FST_Codes (mer x1) p rr 
  = FST_Codes_transportD_concrete x1 p rr.
Proof.
  refine (transportD_as_apD _ _ _ _ _ @ _).
  unfold transportD'. 
  unfold FST_Codes. rewrite (Susp_comp_merid _ _ _ _ x1); simpl.
    rewrite (with_large ap10_path_forall funext_large).
  unfold FST_Codes_transportD_concrete.
  rewrite ! transport_pp.
  refine (transport_path_universe _ _ @ _).
  rewrite (transport_paths_r.
  rewrite transport_as_ap.
Admitted.


(** Showing it is contractible, we will again need the universal property of the suspension. We will prove the components as separate lemmas first; to see the required types of these, we temporarily set up the theorem. *)
Definition FST_Codes_contr (y : Susp X) (p : No = y) (rr : FST_Codes y p)
  : rr = FST_Codes_center y p.
Proof.
  revert y p rr.
  Check (Susp_rect (fun y => forall p rr, rr = FST_Codes_center y p)).
Abort.

Definition FST_Codes_contr_No (p : No = No) (rr : FST_Codes No p)
  : (rr = FST_Codes_center No p).
Proof.
  revert rr. apply Truncation_rect. intros ?; apply trunc_succ.
  intros [x1 r]. destruct r. unfold FST_Codes_center. simpl.
  path_via (truncation_incl
    (transport (fun p => hfiber mer' p) (transport_paths_r p 1 @ concat_1p p)
    (transportD (paths No) 
simpl in *.

Instance Freudenthal
  : IsConnMap (n -2+ n) (@merid X).
Proof.
  intros p C ? f.
Admitted.

End Freudenthal.
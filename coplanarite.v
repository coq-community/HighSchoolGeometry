(* This program is free software; you can redistribute it and/or      *)
(* modify it under the terms of the GNU Lesser General Public License *)
(* as published by the Free Software Foundation; either version 2.1   *)
(* of the License, or (at your option) any later version.             *)
(*                                                                    *)
(* This program is distributed in the hope that it will be useful,    *)
(* but WITHOUT ANY WARRANTY; without even the implied warranty of     *)
(* MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the      *)
(* GNU General Public License for more details.                       *)
(*                                                                    *)
(* You should have received a copy of the GNU Lesser General Public   *)
(* License along with this program; if not, write to the Free         *)
(* Software Foundation, Inc., 51 Franklin St, Fifth Floor, Boston, MA *)
(* 02110-1301 USA                                                     *)


Require Export alignement.
Set Implicit Arguments.
Unset Strict Implicit.
 
Definition coplanaires1 (A B C D : PO) :=
  exists a : R,
    (exists b : R,
       cons 1 D =
       add_PP (cons a A) (add_PP (cons b B) (cons (1 + - (a + b)) C))).
 
Lemma vecteur_def_coplanaires1 :
 forall (k k' : R) (A B C D : PO),
 vec A D = add_PP (mult_PP k (vec A B)) (mult_PP k' (vec A C)) ->
 coplanaires1 A B C D.
unfold coplanaires1, vec in |- *; intros.
exists (1 + - (k + k')); auto.
exists k; auto.
RingPP2 H.
RingPP.
Qed.
 
Lemma coplanaires1_vecteur_def :
 forall A B C D : PO,
 coplanaires1 A B C D ->
 exists k : R,
   (exists k' : R,
      vec A D = add_PP (mult_PP k (vec A B)) (mult_PP k' (vec A C))).
unfold coplanaires1, vec in |- *; intros.
elim H; intros a H0; elim H0; intros b H1; try clear H0 H; try exact H1.
exists b; auto.
exists (1 + - (a + b)); auto.
rewrite H1.
RingPP.
Qed.
 
Definition coplanaires (A B C D : PO) :=
  alignes A B C \/ coplanaires1 A B C D.
 
Lemma coplanaires_trivial : forall A B C : PO, coplanaires A B C A.
unfold coplanaires, coplanaires1 in |- *; intros.
right; try assumption.
exists 1; exists 0.
RingPP.
Qed.
 
Lemma coplanaires_trivial2 : forall A B C : PO, coplanaires A B C B.
unfold coplanaires, coplanaires1 in |- *; intros.
right; try assumption.
exists 0; exists 1.
RingPP.
Qed.
 
Lemma coplanaires_trivial3 : forall A B C : PO, coplanaires A B C C.
unfold coplanaires, coplanaires1 in |- *; intros.
right; try assumption.
exists 0; exists 0.
RingPP.
Qed.
Hint Resolve coplanaires_trivial coplanaires_trivial2 coplanaires_trivial3:
  geo.
 
Ltac hcoplanaires H x y :=
  elim H; clear H; intros H;
   [ tauto || idtac
   | elim (coplanaires1_vecteur_def H); clear H; intros x H; elim H; clear H;
      intros y H ].
 
Ltac hPPcoplanaires H x y :=
  elim H; clear H; intros H;
   [ tauto || idtac
   | elim H; clear H; intros x H; elim H; clear H; intros y H ].
 
Lemma non_coplanaires_expl :
 forall A B C D : PO,
 ~ coplanaires A B C D -> ~ alignes A B C /\ ~ coplanaires1 A B C D.
unfold coplanaires in |- *; intros.
intuition.
Qed.
 
Axiom
  repere_espace :
    forall A B C D E : PO,
    ~ coplanaires A B C D ->
    exists a : R,
      (exists b : R,
         (exists c : R,
            cons 1 E =
            add_PP (add_PP (cons a A) (cons b B))
              (add_PP (cons c C) (cons (1 + - (a + b + c)) D)))).
Hint Unfold coplanaires: geo.
 
Lemma vecteur_def_coplanaires :
 forall (k k' : R) (A B C D : PO),
 vec A D = add_PP (mult_PP k (vec A B)) (mult_PP k' (vec A C)) ->
 coplanaires A B C D.
intros; unfold coplanaires in |- *.
right; try assumption.
apply vecteur_def_coplanaires1 with (k := k) (k' := k'); try assumption.
Qed.
 
Lemma alignes_coplanaires :
 forall A B C D : PO, alignes A B C -> coplanaires A B D C.
intros.
halignes H ipattern:a.
apply vecteur_def_coplanaires with (k := a) (k' := 0).
rewrite H0.
Ringvec.
Qed.
Hint Resolve alignes_coplanaires: geo.
 
Lemma coplanaire_ordre_permute :
 forall A B C D : PO, coplanaires A B C D -> coplanaires A B D C.
intros.
elim H; clear H; intros; auto with geo.
elim (coplanaires1_vecteur_def H); intros.
elim H0; [ intros y H1; try clear H0; try exact H1 ].
elim (classic (y = 0)); intros.
assert (alignes A B D); auto with geo.
apply colineaire_alignes with x.
rewrite H1; rewrite H0; Ringvec.
apply vecteur_def_coplanaires with (k := / y * - x) (k' := / y).
rewrite H1.
Fieldvec y.
Qed.
 
Lemma coplanaire_ordre_cycle :
 forall A B C D : PO, coplanaires A B C D -> coplanaires B C D A.
intros.
elim H; clear H; intros; auto with geo.
elim coplanaires1_vecteur_def with (A := A) (B := B) (C := C) (D := D);
 [ intros x H0; elim H0;
    [ intros y H1; try clear H0 coplanaires1_vecteur_def; try exact H1 ]
 | auto ].
elim (classic (y = 1 + - x)); intros.
rewrite H2 in H1.
assert (alignes B C D); auto with geo.
apply colineaire_alignes with (1 + - x).
VReplace (vec B D) (add_PP (vec B A) (vec A D)).
rewrite H1.
Ringvec.
assert (1 + - x + - y <> 0).
contrapose H0.
RReplace y (y + 0).
rewrite <- H3; ring.
apply
 vecteur_def_coplanaires
  with (k := / (1 + - x + - y) * - y) (k' := / (1 + - x + - y)).
VReplace (vec B D) (add_PP (vec B A) (vec A D)).
rewrite H1.
Fieldvec (1 + - x + - y).
Qed.
Hint Resolve coplanaire_ordre_cycle coplanaire_ordre_permute: geo.
 
Lemma coplanaire_trans :
 forall A B C D E : PO,
 ~ alignes A B C ->
 coplanaires A B C D -> coplanaires A B C E -> coplanaires B C D E.
intros.
elim H1; clear H1; intros.
tauto.
elim H0; clear H0; intros.
tauto.
elim coplanaires1_vecteur_def with (A := A) (B := B) (C := C) (D := D);
 [ intros x H2; elim H2; [ intros y H3; try clear H2; try exact H3 ] | auto ].
elim coplanaires1_vecteur_def with (A := A) (B := B) (C := C) (D := E);
 [ intros k H4; elim H4; [ intros k' H5; try clear H4; try exact H5 ]
 | auto ].
elim (classic (y = 1 + - x)); intros.
rewrite H2 in H3.
assert (alignes B C D); auto with geo.
apply colineaire_alignes with (1 + - x).
VReplace (vec B D) (add_PP (vec B A) (vec A D)).
rewrite H3.
Ringvec.
assert (1 + - x + - y <> 0).
contrapose H0.
RReplace y (y + 0).
rewrite <- H4; ring.
assert
 (vec B A =
  add_PP (mult_PP (/ (1 + - x + - y) * - y) (vec B C))
    (mult_PP (/ (1 + - x + - y)) (vec B D))).
VReplace (vec B D) (add_PP (vec B A) (vec A D)).
rewrite H3.
Fieldvec (1 + - x + - y).
assert
 (vec B E =
  add_PP (mult_PP (1 + - k + - k') (vec B A)) (mult_PP k' (vec B C))).
VReplace (vec B E) (add_PP (vec B A) (vec A E)).
rewrite H5.
Ringvec.
apply
 vecteur_def_coplanaires
  with
    (k := k' + / (1 + - x + - y) * - y * (1 + - k + - k'))
    (k' := / (1 + - x + - y) * (1 + - k + - k')).
rewrite H7; rewrite H6.
Fieldvec (1 + - x + - y).
Qed.
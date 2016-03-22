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


Require Export complexes_similitudes.
Set Implicit Arguments.
Unset Strict Implicit.
 
Definition isocele_rectangle_direct (A B C : PO) :=
  A <> B /\
  isocele A B C /\ cons_AV (vec A B) (vec A C) = image_angle pisurdeux.
 
Lemma iso_rec_dir_distinct :
 forall A B C : PO, isocele_rectangle_direct A B C -> A <> C.
unfold isocele_rectangle_direct, isocele in |- *; intros.
elim H;
 [ intros H0 H1; elim H1; [ intros H2 H3; try clear H1 H; try exact H2 ] ].
apply isometrie_distinct with (2 := H2); auto.
Qed.
Hint Resolve iso_rec_dir_distinct: geo.
 
Lemma iso_rec_dir_complexe :
 forall (a b c : C) (A B C : PO),
 a = affixe A ->
 b = affixe B ->
 c = affixe C ->
 isocele_rectangle_direct A B C ->
 Cplus c (Copp a) = Cmult i (Cplus b (Copp a)).
unfold isocele_rectangle_direct, isocele in |- *; intros.
elim H2;
 [ intros H3 H4; elim H4; [ intros H5 H6; try clear H4 H2; try exact H6 ] ].
rewrite forme_polaire_i.
apply rotation_complexe with (J := A) (M := B) (M' := C); auto.
apply rotation_def2; auto.
Qed.
 
Lemma complexe_iso_rec_dir :
 forall (a b c : C) (A B C : PO),
 a = affixe A ->
 b = affixe B ->
 c = affixe C ->
 A <> B ->
 Cplus c (Copp a) = Cmult i (Cplus b (Copp a)) ->
 isocele_rectangle_direct A B C.
unfold isocele_rectangle_direct, isocele in |- *; intros.
cut (distance A B = distance A C); intros.
cut (A <> C); intros.
split; [ try assumption | idtac ].
split; [ try assumption | idtac ].
cut (Cplus b (Copp a) <> zeroC); intros.
cut (Cplus c (Copp a) <> zeroC); intros.
rewrite
 (angle_vecteurs_arguments (A:=A) (B:=B) (A':=A) (B':=C)
    (z:=Cplus b (Copp a)) (z':=Cplus c (Copp a))); 
 auto with geo.
rewrite H3; rewrite forme_polaire_i; rewrite Cmult_argument; auto.
rewrite argument_module_un.
elim existence_argument with (z := Cplus b (Copp a));
 [ intros; try clear existence_argument | auto ].
rewrite H8; repeat rewrite <- mes_opp.
repeat rewrite <- add_mes_compatible.
replace (pisurdeux + x + - x) with pisurdeux; [ auto | ring ].
auto with geo.
apply diff_nonzero with (3 := H5); auto.
apply diff_nonzero with (3 := H2); auto.
apply isometrie_distinct with (2 := H4); auto.
rewrite <- (module_difference H H0).
rewrite <- (module_difference H H1).
rewrite H3; rewrite forme_polaire_i; rewrite Cmult_module;
 rewrite complexe_polaire_module; ring.
Qed.
 
Lemma deux_iso_rec_dir_complexe :
 forall (a b c d e : C) (A B C D E : PO),
 a = affixe A ->
 b = affixe B ->
 c = affixe C ->
 d = affixe D ->
 e = affixe E ->
 isocele_rectangle_direct A B C ->
 isocele_rectangle_direct A D E ->
 Cplus e (Copp c) = Cmult i (Cplus d (Copp b)).
intros.
generalize (iso_rec_dir_complexe (a:=a) (b:=b) (c:=c) (A:=A) (B:=B) (C0:=C));
 intros H11.
generalize (iso_rec_dir_complexe (a:=a) (b:=d) (c:=e) (A:=A) (B:=D) (C0:=E));
 intros H12.
replace (Cplus e (Copp c)) with
 (Cplus (Cplus e (Copp a)) (Copp (Cplus c (Copp a)))); 
 [ idtac | ring ].
rewrite H12; auto.
rewrite H11; auto.
replace (Cplus d (Copp b)) with
 (Cplus (Cplus d (Copp a)) (Copp (Cplus b (Copp a)))); 
 ring.
Qed.
 
Theorem deux_isocele_rectangle_direct :
 forall A B C D E : PO,
 B <> D :>PO ->
 isocele_rectangle_direct A B C ->
 isocele_rectangle_direct A D E ->
 distance B D = distance C E /\
 cons_AV (vec B D) (vec C E) = image_angle pisurdeux.
intros.
elim existence_affixe_point with (M := A); intros a; intros.
elim existence_affixe_point with (M := B); intros b; intros.
elim existence_affixe_point with (M := C); intros c; intros.
elim existence_affixe_point with (M := D); intros d; intros.
elim existence_affixe_point with (M := E); intros e; intros.
cut (Cplus e (Copp c) = Cmult i (Cplus d (Copp b))); intros.
cut (distance B D = distance C E); intros.
cut (C <> E); intros.
split; [ try assumption | idtac ].
cut (Cplus d (Copp b) <> zeroC); intros.
cut (Cplus e (Copp c) <> zeroC); intros.
rewrite
 (angle_vecteurs_arguments (A:=B) (B:=D) (A':=C) (B':=E)
    (z:=Cplus d (Copp b)) (z':=Cplus e (Copp c))); 
 auto with geo.
rewrite H7; rewrite forme_polaire_i; rewrite Cmult_argument; auto.
rewrite argument_module_un.
elim existence_argument with (z := Cplus d (Copp b));
 [ intros; try clear existence_argument | auto ].
rewrite H12; repeat rewrite <- mes_opp.
repeat rewrite <- add_mes_compatible.
replace (pisurdeux + x + - x) with pisurdeux; [ auto | ring ].
auto with geo.
apply diff_nonzero with (3 := H9); auto.
apply diff_nonzero with (3 := H); auto.
apply isometrie_distinct with (2 := H8); auto.
rewrite <- (module_difference H3 H5).
rewrite <- (module_difference H4 H6).
rewrite H7; rewrite forme_polaire_i; rewrite Cmult_module;
 rewrite complexe_polaire_module; ring.
apply
 (deux_iso_rec_dir_complexe (a:=a) (b:=b) (c:=c) (d:=d) (e:=e) (A:=A) (B:=B)
    (C0:=C) (D:=D) (E:=E)); auto.
Qed.
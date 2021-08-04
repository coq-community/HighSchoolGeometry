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


Require Export metrique_triangle.
Set Implicit Arguments.
Unset Strict Implicit.
Parameter rotation : PO -> R -> PO -> PO.
 
Axiom
  rotation_def :
    forall (I A B : PO) (a : R),
    I <> A ->
    B = rotation I a A ->
    distance I A = distance I B /\
    image_angle a = cons_AV (vec I A) (vec I B).
 
Axiom rotation_def_centre : forall (I : PO) (a : R), I = rotation I a I.
 
Axiom
  rotation_def2 :
    forall (I A B : PO) (a : R),
    I <> A ->
    distance I A = distance I B ->
    image_angle a = cons_AV (vec I A) (vec I B) -> B = rotation I a A.
 
Lemma rotation_angle_nul : forall I A : PO, A = rotation I 0 A.
intros.
elim (classic (I = A)); intros.
rewrite <- H.
apply rotation_def_centre.
apply rotation_def2; auto.
apply angle_nul; auto.
Qed.
 
Lemma image_distinct_centre :
 forall (I A B : PO) (a : R),
 I <> A :>PO -> B = rotation I a A :>PO -> I <> B :>PO.
intros; red in |- *; intros.
apply H.
elim rotation_def with (I := I) (A := A) (B := B) (a := a);
 [ unfold distance in |- *; intros | auto | auto ].
rewrite <- H1 in H2.
apply distance_nulle.
rewrite <- (def_sqrt (scalaire (vec I A) (vec I A))); auto with geo.
rewrite H2.
replace (scalaire (vec I I) (vec I I)) with 0.
rewrite sqrt_0; ring.
replace (vec I I) with (mult_PP 0 (vec I B)).
Simplscal.
Ringvec.
Qed.
 
Lemma rotation_inverse :
 forall (I A B : PO) (a : R),
 B = rotation I a A :>PO -> A = rotation I (- a) B :>PO.
intros.
elim (classic (I = A)); intros.
rewrite <- H0.
rewrite <- H0 in H.
rewrite H; rewrite <- rotation_def_centre; auto.
apply rotation_def_centre.
elim rotation_def with (I := I) (A := A) (B := B) (a := a);
 [ try clear rotation_def; intros | auto | auto ].
apply rotation_def2; auto.
apply image_distinct_centre with (2 := H); auto.
rewrite <- (mes_oppx (A:=I) (B:=A) (C:=I) (D:=B) (x:=a)); auto.
apply image_distinct_centre with (2 := H); auto.
Qed.
 
Lemma composee_rotations_meme_centre :
 forall (I A B C : PO) (a b : R),
 B = rotation I a A -> C = rotation I b B -> C = rotation I (a + b) A.
intros.
elim (classic (I = A)); intros.
rewrite H0.
rewrite H.
rewrite <- H1.
repeat rewrite <- rotation_def_centre; auto.
generalize (image_distinct_centre (I:=I) (A:=A) (B:=B) (a:=a)); intros H5.
generalize (image_distinct_centre (I:=I) (A:=B) (B:=C) (a:=b)); intros.
elim rotation_def with (I := I) (A := A) (B := B) (a := a);
 [ try clear rotation_def; intros | auto | auto ].
elim rotation_def with (I := I) (A := B) (B := C) (a := b);
 [ try clear rotation_def; intros | auto | auto ].
apply rotation_def2; auto.
rewrite H3; auto.
rewrite add_mes_compatible.
rewrite H7; rewrite H4; rewrite Chasles; auto.
Qed.
 
Theorem rotation_isometrie :
 forall (I A B A' B' : PO) (a : R),
 A' = rotation I a A -> B' = rotation I a B -> distance A' B' = distance A B.
intros I A B A' B' a H H0; try assumption.
apply distance_carre; auto.
elim (classic (I = A)); intros.
rewrite <- H1 in H.
rewrite <- H1; rewrite H; repeat rewrite <- rotation_def_centre; auto.
elim (classic (I = B)); intros.
rewrite <- H2 in H0.
rewrite H0; rewrite <- H2; repeat rewrite <- rotation_def_centre; auto.
elim rotation_def with (I := I) (A := B) (B := B') (a := a);
 [ try clear rotation_def; intros | auto | auto ].
rewrite H3; auto.
elim (classic (I = B)); intros.
rewrite <- H2 in H0.
rewrite H0; rewrite <- H2; repeat rewrite <- rotation_def_centre; auto.
elim rotation_def with (I := I) (A := A) (B := A') (a := a);
 [ try clear rotation_def; intros | auto | auto ].
rewrite (distance_sym A I); auto.
rewrite H3; rewrite distance_sym; auto.
generalize (image_distinct_centre (I:=I) (A:=A) (B:=A') (a:=a)); intros H11.
generalize (image_distinct_centre (I:=I) (A:=B) (B:=B') (a:=a)); intros H12.
elim rotation_def with (I := I) (A := B) (B := B') (a := a);
 [ try clear rotation_def; intros | auto | auto ].
elim rotation_def with (I := I) (A := A) (B := A') (a := a);
 [ try clear rotation_def; intros | auto | auto ].
mesure I A I B.
rewrite (Al_Kashi (A:=I) (B:=A) (C:=B) (a:=x)); auto.
rewrite (Al_Kashi (A:=I) (B:=A') (C:=B') (a:=x)); auto.
rewrite H5; rewrite H3; auto.
rewrite H7.
replace (cons_AV (vec I A') (vec I B')) with
 (plus (cons_AV (vec I A') (vec I A))
    (plus (cons_AV (vec I A) (vec I B)) (cons_AV (vec I B) (vec I B')))).
rewrite <- (mes_oppx (A:=I) (B:=A) (C:=I) (D:=A') (x:=a)); auto.
rewrite <- H7; rewrite <- H4.
rewrite <- add_mes_compatible; rewrite <- add_mes_compatible.
replace (- a + (x + a)) with x; try ring; auto.
rewrite Chasles; auto.
rewrite Chasles; auto.
Qed.
 
Lemma rotation_IAB :
 forall (I A B A' B' : PO) (a : R),
 I <> A ->
 I <> B ->
 A' = rotation I a A ->
 B' = rotation I a B ->
 cons_AV (vec I A) (vec I B) = cons_AV (vec I A') (vec I B') :>AV.
intros.
generalize (isometrie_distinct (A:=I) (B:=B) (A':=I) (B':=B')); intros.
generalize (isometrie_distinct (A:=I) (B:=A) (A':=I) (B':=A')); intros.
elim rotation_def with (I := I) (A := B) (B := B') (a := a);
 [ try clear rotation_def; intros | auto | auto ].
elim rotation_def with (I := I) (A := A) (B := A') (a := a);
 [ try clear rotation_def; intros | auto | auto ].
replace (cons_AV (vec I A') (vec I B')) with
 (plus (cons_AV (vec I A') (vec I A))
    (plus (cons_AV (vec I A) (vec I B)) (cons_AV (vec I B) (vec I B')))).
rewrite <- H6.
rewrite <- (mes_oppx (A:=I) (B:=A) (C:=I) (D:=A') (x:=a)); auto.
mesure I A I B.
replace (- a + (x + a)) with x; try ring; auto.
rewrite Chasles; auto.
rewrite Chasles; auto.
Qed.
 
Lemma image_bipoint_distinct :
 forall (I A B A' B' : PO) (a : R),
 A <> B :>PO -> A' = rotation I a A -> B' = rotation I a B -> A' <> B' :>PO.
intros.
generalize (rotation_isometrie (I:=I) (A:=A) (B:=B) (A':=A') (B':=B') (a:=a));
 intros H7.
apply (isometrie_distinct (A:=A) (B:=B)); auto.
symmetry  in |- *; auto.
Qed.
 
Theorem rotation_conserve_angle :
 forall (I A B C A' B' C' : PO) (a : R),
 A <> B :>PO ->
 A <> C :>PO ->
 A' = rotation I a A ->
 B' = rotation I a B ->
 C' = rotation I a C ->
 cons_AV (vec A B) (vec A C) = cons_AV (vec A' B') (vec A' C') :>AV.
intros.
generalize
 (image_bipoint_distinct (I:=I) (A:=A) (B:=C) (A':=A') (B':=C') (a:=a));
 intros.
generalize
 (image_bipoint_distinct (I:=I) (A:=A) (B:=B) (A':=A') (B':=B') (a:=a));
 intros H11.
elim (classic (I = A)); intros.
rewrite <- H5 in H1; rewrite <- H5 in H; rewrite <- H5 in H0.
rewrite H1; repeat rewrite <- rotation_def_centre; rewrite <- H5; auto.
elim rotation_def with (I := I) (A := B) (B := B') (a := a);
 [ try clear rotation_def; intros | auto | auto ].
elim rotation_def with (I := I) (A := C) (B := C') (a := a);
 [ try clear rotation_def; intros | auto | auto ].
generalize (isometrie_distinct (A:=I) (B:=B) (A':=I) (B':=B')); intros H30.
generalize (isometrie_distinct (A:=I) (B:=C) (A':=I) (B':=C')); intros H31.
apply rotation_IAB with a; auto.
elim (classic (I = B)); intros.
rewrite <- H6 in H2; rewrite <- H6 in H.
rewrite H2; repeat rewrite <- rotation_def_centre; rewrite <- H6; auto.
elim rotation_def with (I := I) (A := A) (B := A') (a := a);
 [ try clear rotation_def; intros | auto | auto ].
elim (classic (I = C)); intros.
rewrite <- H9 in H3; rewrite <- H9 in H0.
rewrite H3; repeat rewrite <- rotation_def_centre; rewrite <- H9; auto.
rewrite <- angle_nul; auto.
rewrite <- angle_nul; auto.
apply dist_non_nulle; rewrite distance_sym; rewrite <- H7; auto with geo.
elim rotation_def with (I := I) (A := C) (B := C') (a := a);
 [ try clear rotation_def; intros | auto | auto ].
generalize (isometrie_distinct (A:=I) (B:=C) (A':=I) (B':=C')); intros H31.
elim
 cas_egalite_triangle
  with (A := I) (B := A) (C := C) (A' := I) (B' := A') (C' := C');
 (auto with geo; intros).
elim H14; intros H15 H16; try clear H14; try exact H16.
mesure A C A I.
rewrite <- (mes_oppx (A:=A) (B:=C) (C:=A) (D:=I) (x:=x)); auto.
rewrite <- (mes_oppx (A:=A') (B:=C') (C:=A') (D:=I) (x:=x)); auto.
apply dist_non_nulle; rewrite distance_sym; rewrite <- H7; auto with geo.
rewrite H14; rewrite H15; auto.
generalize (isometrie_distinct (A:=I) (B:=A) (A':=I) (B':=A')); intros H30.
apply rotation_IAB with a; auto.
generalize (isometrie_distinct (A:=I) (B:=A) (A':=I) (B':=A')); intros H30.
generalize (isometrie_distinct (A:=I) (B:=B) (A':=I) (B':=B')); intros H31.
elim (classic (I = C)); intros.
rewrite <- H7 in H3.
rewrite H3; repeat rewrite <- rotation_def_centre; rewrite <- H7; auto.
elim rotation_def with (I := I) (A := A) (B := A') (a := a);
 [ try clear rotation_def; intros | auto | auto ].
elim rotation_def with (I := I) (A := B) (B := B') (a := a);
 [ try clear rotation_def; intros | auto | auto ].
elim
 cas_egalite_triangle
  with (A := I) (B := A) (C := B) (A' := I) (B' := A') (C' := B');
 (auto; intros).
elim H14; intros H15 H16; try clear H14; try exact H15.
apply rotation_IAB with a; auto.
generalize (isometrie_distinct (A:=I) (B:=C) (A':=I) (B':=C')); intros H32.
elim rotation_def with (I := I) (A := A) (B := A') (a := a);
 [ try clear rotation_def; intros | auto | auto ].
elim rotation_def with (I := I) (A := B) (B := B') (a := a);
 [ try clear rotation_def; intros | auto | auto ].
elim rotation_def with (I := I) (A := C) (B := C') (a := a);
 [ try clear rotation_def; intros | auto | auto ].
elim
 cas_egalite_triangle
  with (A := I) (B := A) (C := B) (A' := I) (B' := A') (C' := B');
 (auto; intros).
elim
 cas_egalite_triangle
  with (A := I) (B := A) (C := C) (A' := I) (B' := A') (C' := C');
 (auto; intros).
elim H18; intros H19 H20; try clear H18; try exact H20.
elim H16; intros H18 H21; try clear H16; try exact H21.
replace (cons_AV (vec A B) (vec A C)) with
 (plus (cons_AV (vec A B) (vec A I)) (cons_AV (vec A I) (vec A C))).
mesure A C A I.
rewrite <- (mes_oppx (A:=A) (B:=C) (C:=A) (D:=I) (x:=x)); auto with geo.
rewrite (mes_oppx (A:=A') (B:=C') (C:=A') (D:=I) (x:=x)); auto with geo.
rewrite H18; rewrite Chasles; auto with geo.
apply dist_non_nulle; rewrite distance_sym; rewrite <- H8; auto with geo.
apply dist_non_nulle; rewrite distance_sym; rewrite <- H8; auto with geo.
rewrite H16; rewrite H19; auto.
rewrite Chasles; auto.
apply rotation_IAB with a; auto.
apply rotation_IAB with a; auto.
Qed.
 
Theorem rotation_image_bipoint :
 forall (I A B C A' B' C' : PO) (a : R),
 A <> B :>PO ->
 A' = rotation I a A ->
 B' = rotation I a B ->
 distance A' B' = distance A B /\
 image_angle a = cons_AV (vec A B) (vec A' B') :>AV.
intros.
generalize
 (image_bipoint_distinct (I:=I) (A:=A) (B:=B) (A':=A') (B':=B') (a:=a));
 intros H11.
split; [ try assumption | idtac ].
apply rotation_isometrie with (1 := H0); auto.
elim (classic (I = A)); intros.
rewrite <- H2; rewrite <- H2 in H0; rewrite <- H2 in H.
elim rotation_def with (I := I) (A := B) (B := B') (a := a);
 [ try clear rotation_def; intros | auto | auto ].
rewrite H0; repeat rewrite <- rotation_def_centre; auto.
elim (classic (I = B)); intros.
rewrite <- H3; rewrite <- H3 in H1; rewrite <- H3 in H.
generalize (isometrie_distinct (A:=I) (B:=A) (A':=I) (B':=A')); intros H30.
elim rotation_def with (I := I) (A := A) (B := A') (a := a);
 [ try clear rotation_def; intros | auto | auto ].
rewrite H1; repeat rewrite <- rotation_def_centre; auto.
rewrite angle_oppu_oppv; auto.
elim rotation_def with (I := I) (A := B) (B := B') (a := a);
 [ try clear rotation_def; intros | auto | auto ].
elim rotation_def with (I := I) (A := A) (B := A') (a := a);
 [ try clear rotation_def; intros | auto | auto ].
generalize (isometrie_distinct (A:=I) (B:=A) (A':=I) (B':=A')); intros H30.
generalize (isometrie_distinct (A:=I) (B:=B) (A':=I) (B':=B')); intros.
elim
 cas_egalite_triangle
  with (A := I) (B := A) (C := B) (A' := I) (B' := A') (C' := B');
 (auto; intros).
elim H10; intros H12 H13; try clear H10; try exact H13.
replace (cons_AV (vec A B) (vec A' B')) with
 (plus (cons_AV (vec A B) (vec A I))
    (plus (cons_AV (vec A I) (vec A' I)) (cons_AV (vec A' I) (vec A' B')))).
mesure A B A I.
rewrite <- (mes_oppx (A:=A') (B:=B') (C:=A') (D:=I) (x:=x)).
rewrite angle_oppu_oppv; auto.
rewrite <- H7.
rewrite <- add_mes_compatible; rewrite <- add_mes_compatible.
replace (x + (a + - x)) with a; try ring; auto.
apply H11; auto.
apply dist_non_nulle; rewrite distance_sym; rewrite <- H6; auto with geo.
rewrite H10; rewrite H12; auto.
rewrite Chasles; auto.
rewrite Chasles; auto.
apply dist_non_nulle; rewrite distance_sym; rewrite <- H6; auto with geo.
apply rotation_IAB with a; auto.
Qed.
 
Lemma existence_rotation_Ia :
 forall (I M : PO) (a : R), exists M' : PO, M' = rotation I a M.
intros.
elim (classic (M = I)); intros.
exists I.
rewrite H; rewrite <- rotation_def_centre; auto.
elim existence_representant_unitaire with (A := I) (B := M);
 [ intros; try clear existence_representant_unitaire | auto ].
cut (I <> x); intros.
generalize (existence_representant_angle (A:=I) (B:=x) I a); intros.
elim H2;
 [ intros C H3; elim H3; intros H4 H5; try clear H3 H2; try exact H5
 | idtac ].
cut (I <> C); intros.
generalize (distance_vecteur (A:=I) (B:=M)); intros.
elim
 existence_representant_mult_vecteur
  with (A := I) (B := I) (C := C) (k := distance I M); 
 intros D H6; try clear existence_representant_mult_vecteur; 
 try exact H6.
cut (I <> D); intros.
exists D.
apply rotation_def2; auto.
apply resolution; auto with geo.
repeat rewrite <- carre_scalaire_distance.
rewrite H6; rewrite H3; auto.
rewrite <- H0.
Simplscal.
elim def_representant_unitaire2 with (A := I) (B := M) (C := x);
 [ intros; elim H9; intros H22 H23; rewrite H22; try discrR | auto | auto ].
rewrite carre_scalaire_distance.
rewrite H4.
ring.
rewrite angles_representants_unitaires; auto.
replace (representant_unitaire (vec I D)) with (vec I C).
rewrite <- H0; auto.
apply def_representant_unitaire; auto with geo.
cut (distance I M <> 0); intros; auto with geo.
apply colineaire_alignes with (/ distance I M); auto.
rewrite H6.
Fieldvec (distance I M).
rewrite H6.
replace (scalaire (mult_PP (distance I M) (vec I C)) (vec I C)) with
 (distance I M * scalaire (vec I C) (vec I C)).
apply Rmult_pos; auto with geo.
Simplscal.
apply distinct_produit_vecteur with (3 := H6); auto with geo.
auto with geo.
elim def_representant_unitaire2 with (A := I) (B := M) (C := x);
 [ intros; elim H4; intros H22 H23; try discrR | auto | auto ].
auto with geo.
apply distance_non_nulle.
elim def_representant_unitaire2 with (A := I) (B := M) (C := x);
 [ intros; elim H2; intros H22 H23; rewrite H22; try discrR | auto | auto ].
Qed.
 
Lemma deux_mes_angle_rotation :
 forall (I M : PO) (a b : R),
 image_angle a = image_angle b -> rotation I a M = rotation I b M.
intros.
elim (classic (I = M)); intros.
rewrite <- H0; repeat rewrite <- rotation_def_centre; auto.
elim (existence_rotation_Ia I M a); intros.
rewrite <- H1.
generalize (rotation_def (I:=I) (A:=M) (B:=x) (a:=a)); intros.
elim H2; auto; intros.
apply rotation_def2; auto.
rewrite <- H4; rewrite <- H; auto.
Qed.
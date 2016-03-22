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


Require Export angles_vecteurs.
Set Implicit Arguments.
Unset Strict Implicit.
(* Le plan est orienté et on utilise le cercle trigonométrique*)
 
Definition repere_orthonormal_direct (O I J : PO) :=
  image_angle pisurdeux = cons_AV (vec O I) (vec O J) /\
  scalaire (vec O I) (vec O I) = 1 /\ scalaire (vec O J) (vec O J) = 1.
Parameter cos : R -> R.
Parameter sin : R -> R.
Parameter Cos : AV -> R.
Parameter Sin : AV -> R.
(* cosinus et sinus d'un angle (ou d'un réel) sont obtenus par projections
   du point image du cercle trigonométrique sur les axes de coordonnées*)
 
Axiom
  def_cos :
    forall (A B C : PO) (x : R),
    distance A B = 1 ->
    distance A C = 1 ->
    image_angle x = cons_AV (vec A B) (vec A C) ->
    cos x = scalaire (vec A B) (vec A C).
 
Axiom
  def_sin :
    forall (A B C D : PO) (x : R),
    distance A B = 1 ->
    distance A C = 1 ->
    image_angle x = cons_AV (vec A B) (vec A C) ->
    repere_orthonormal_direct A B D -> sin x = scalaire (vec A C) (vec A D).
 
Axiom
  def_Cos :
    forall A B C : PO,
    distance A B = 1 ->
    distance A C = 1 ->
    Cos (cons_AV (vec A B) (vec A C)) = scalaire (vec A B) (vec A C).
 
Axiom
  def_Sin :
    forall A B C D : PO,
    distance A B = 1 ->
    distance A C = 1 ->
    repere_orthonormal_direct A B D ->
    Sin (cons_AV (vec A B) (vec A C)) = scalaire (vec A C) (vec A D).
 
Lemma ROND_RON :
 forall O I J : PO,
 repere_orthonormal_direct O I J -> repere_orthonormal O I J.
unfold repere_orthonormal_direct, repere_orthonormal in |- *; intros.
elim H; intros H0 H1; try clear H; try exact H1.
split; [ auto with geo | try assumption ].
Qed.
Hint Resolve ROND_RON: geo.
 
Definition repere_orthonormal_indirect (O I J : PO) :=
  image_angle pisurdeux = cons_AV (vec O J) (vec O I) /\
  scalaire (vec O I) (vec O I) = 1 /\ scalaire (vec O J) (vec O J) = 1.
 
Lemma ROND_RONI :
 forall O I J : PO,
 repere_orthonormal_direct O I J -> repere_orthonormal_indirect O J I.
unfold repere_orthonormal_indirect, repere_orthonormal_direct in |- *.
intros O I J H; try assumption.
elim H; intros H0 H1; try clear H; try exact H1.
elim H1; intros H H2; try clear H1; try exact H2.
split; [ auto | split; [ auto | try assumption ] ].
Qed.
 
Lemma ROND_new :
 forall O I J K : PO,
 repere_orthonormal_direct O I J ->
 vec O K = mult_PP (-1) (vec O I) -> repere_orthonormal_direct O J K.
unfold repere_orthonormal_indirect, repere_orthonormal_direct in |- *.
intros O I J K H H0; try assumption.
elim H; intros H1 H2; elim H2; intros H3 H4; try clear H2 H; try exact H4.
cut (scalaire (vec O K) (vec O K) = 1); intros.
split; [ auto | split; [ auto | try assumption ] ].
replace pisurdeux with (- pisurdeux + pi).
cut (image_angle (- pisurdeux) = cons_AV (vec O J) (vec O I)); intros.
cut (image_angle pi = cons_AV (vec O I) (vec O K)); intros.
rewrite add_mes_compatible.
rewrite H5; rewrite H2; rewrite Chasles; auto with geo.
replace (vec O K) with (vec I O).
rewrite <- angle_plat; auto with geo.
rewrite H0.
unfold vec in |- *; RingPP.
apply mes_oppx; auto with geo.
unfold pi in |- *; ring.
rewrite H0.
Simplscal; rewrite H3; ring.
Qed.
 
Lemma existence_ROND_AB :
 forall A B : PO,
 distance A B = 1 -> exists C : PO, repere_orthonormal_direct A B C.
intros.
elim
 existence_representant_angle
  with (A := A) (B := B) (C := A) (x := pisurdeux);
 [ intros C H0; elim H0; intros H1 H2; try clear H0; try exact H2 | auto ].
exists C; unfold repere_orthonormal_direct in |- *.
split; [ try assumption | idtac ].
split; auto with geo.
Qed.
 
Lemma cos_deux_mes :
 forall x y : R, image_angle x = image_angle y -> cos x = cos y.
intros.
elim existence_AB_unitaire; intros A H1; elim H1; intros B H0; try clear H1.
elim existence_representant_angle with (A := A) (B := B) (C := A) (x := x);
 [ intros C H1; elim H1; intros; try clear H1 | auto ].
rewrite (def_cos (A:=A) (B:=B) (C:=C) (x:=x)); auto.
rewrite (def_cos (A:=A) (B:=B) (C:=C) (x:=y)); auto.
rewrite <- H3; auto.
Qed.
 
Lemma cos_paire : forall x : R, cos (- x) = cos x.
intros.
elim existence_AB_unitaire; intros A H; elim H; intros B H0; try clear H;
 try exact H0.
elim existence_representant_angle with (A := A) (B := B) (C := A) (x := x);
 [ intros C H; elim H; intros H1 H2; try clear H; try exact H2 | auto ].
rewrite (def_cos (A:=A) (B:=B) (C:=C) (x:=x)); auto.
cut (image_angle (- x) = cons_AV (vec A C) (vec A B)); intros.
rewrite (def_cos (A:=A) (B:=C) (C:=B) (x:=- x)); auto.
rewrite scalaire_sym; auto.
apply mes_oppx; auto with geo.
Qed.
 
Lemma cos_periodique : forall x : R, cos (x + deuxpi) = cos x.
intros.
elim existence_AB_unitaire; intros A H; elim H; intros B H0; try clear H;
 try exact H0.
elim existence_representant_angle with (A := A) (B := B) (C := A) (x := x);
 [ intros C H; elim H; intros H1 H2; try clear H; try exact H2 | auto ].
rewrite (def_cos (A:=A) (B:=B) (C:=C) (x:=x)); auto.
cut (image_angle (x + deuxpi) = cons_AV (vec A B) (vec A C)); intros.
rewrite (def_cos (A:=A) (B:=B) (C:=C) (x:=x + deuxpi)); auto.
apply mesure_mod_deuxpi; auto with geo.
Qed.
 
Lemma sin_deux_mes :
 forall x y : R, image_angle x = image_angle y -> sin x = sin y.
intros.
elim existence_AB_unitaire; intros A H1; elim H1; clear H1; intros B H0.
elim existence_ROND_AB with (A := A) (B := B); [ intros D H10 | auto ].
elim existence_representant_angle with (A := A) (B := B) (C := A) (x := x);
 [ intros C H1; elim H1; intros; try clear H1 | auto ].
rewrite (def_sin (A:=A) (B:=B) (C:=C) (D:=D) (x:=x)); auto.
rewrite (def_sin (A:=A) (B:=B) (C:=C) (D:=D) (x:=y)); auto.
rewrite <- H3; auto.
Qed.
 
Lemma sin_periodique : forall x : R, sin (x + deuxpi) = sin x.
intros.
elim existence_AB_unitaire; intros A H; elim H; intros B H0; try clear H;
 try exact H0.
elim existence_ROND_AB with (A := A) (B := B); [ intros D H10 | auto ].
elim existence_representant_angle with (A := A) (B := B) (C := A) (x := x);
 [ intros C H; elim H; intros H1 H2; try clear H; try exact H2 | auto ].
rewrite (def_sin (A:=A) (B:=B) (C:=C) (D:=D) (x:=x)); auto.
cut (image_angle (x + deuxpi) = cons_AV (vec A B) (vec A C)); intros.
rewrite (def_sin (A:=A) (B:=B) (C:=C) (D:=D) (x:=x + deuxpi)); auto.
apply mesure_mod_deuxpi; auto with geo.
Qed.
 
Lemma sin_cos_pisurdeux_moins_x : forall x : R, sin x = cos (pisurdeux + - x).
intros.
elim existence_AB_unitaire; intros A H; elim H; intros B H0; try clear H;
 try exact H0.
elim existence_representant_angle with (A := A) (B := B) (C := A) (x := x);
 [ intros C H; elim H; intros H1 H2; try clear H; try exact H2 | auto ].
elim existence_ROND_AB with (A := A) (B := B);
 [ intros D H; try exact H | auto ].
rewrite (def_sin (A:=A) (B:=B) (C:=C) (D:=D) (x:=x)); auto.
cut (image_angle (- x) = cons_AV (vec A C) (vec A B)); intros.
replace (pisurdeux + - x) with (- x + pisurdeux); try ring.
elim H; intros.
elim H5; intros H6 H7; try clear H5; try exact H7.
rewrite (def_cos (A:=A) (B:=C) (C:=D) (x:=- x + pisurdeux)); auto with geo.
rewrite add_mes_compatible.
rewrite H3; rewrite H4; rewrite Chasles; auto with geo.
apply mes_oppx; auto with geo.
Qed.
 
Lemma cos_sin_pisurdeux_moins_x : forall x : R, cos x = sin (pisurdeux + - x).
intros.
rewrite sin_cos_pisurdeux_moins_x.
replace (pisurdeux + - (pisurdeux + - x)) with x; try ring.
Qed.
 
Lemma cos_zero : cos 0 = 1.
elim existence_AB_unitaire; intros A H; elim H; intros B H0; try clear H;
 try exact H0.
rewrite (def_cos (A:=A) (B:=B) (C:=B) (x:=0)); auto with geo.
rewrite <- angle_nul; auto with geo.
Qed.
 
Lemma sin_zero : sin 0 = 0.
elim existence_AB_unitaire; intros A H; elim H; intros B H0; try clear H;
 try exact H0.
elim existence_ROND_AB with (A := A) (B := B); [ intros D H | auto ].
elim H; intros.
rewrite (def_sin (A:=A) (B:=B) (C:=B) (D:=D) (x:=0)); auto with geo.
rewrite <- angle_nul; auto with geo.
Qed.
 
Lemma cos_pisurdeux : cos pisurdeux = 0.
elim existence_AB_unitaire; intros A H; elim H; intros B H0; try clear H;
 try exact H0.
elim existence_ROND_AB with (A := A) (B := B); [ intros D H | auto ].
elim H; intros.
elim H2; intros H3 H4; try clear H2; try exact H4.
rewrite (def_cos (A:=A) (B:=B) (C:=D) (x:=pisurdeux)); auto with geo.
Qed.
 
Lemma sin_pisurdeux : sin pisurdeux = 1.
elim existence_AB_unitaire; intros A H; elim H; intros B H0; try clear H;
 try exact H0.
elim existence_ROND_AB with (A := A) (B := B); [ intros D H | auto ].
elim H; intros.
elim H2; intros H3 H4; try clear H2; try exact H4.
rewrite (def_sin (A:=A) (B:=B) (C:=D) (D:=D) (x:=pisurdeux)); auto with geo.
Qed.
 
Lemma cos_pi : cos pi = -1.
elim existence_AB_unitaire; intros A H; elim H; intros B H0; try clear H;
 try exact H0.
elim
 existence_representant_mult_vecteur
  with (A := A) (B := A) (C := B) (k := -1); intros D H1.
cut (scalaire (vec A D) (vec A D) = 1); intros.
rewrite (def_cos (A:=A) (B:=B) (C:=D) (x:=pi)); auto with geo.
rewrite H1.
Simplscal; rewrite carre_scalaire_distance; rewrite H0; ring.
replace (vec A D) with (vec B A).
rewrite <- angle_plat; auto with geo.
rewrite H1.
Ringvec.
rewrite H1.
Simplscal; rewrite carre_scalaire_distance; rewrite H0; ring.
Qed.
 
Lemma sin_pi : sin pi = 0.
elim existence_AB_unitaire; intros A H; elim H; intros B H0; try clear H;
 try exact H0.
elim existence_ROND_AB with (A := A) (B := B); [ intros D H | auto ].
elim H; intros.
elim H2; intros H4 H5; try clear H2; try exact H4.
elim
 existence_representant_mult_vecteur
  with (A := A) (B := A) (C := B) (k := -1); intros E H3.
rewrite (def_sin (A:=A) (B:=B) (C:=E) (D:=D) (x:=pi)); auto.
rewrite H3.
cut (scalaire (vec A B) (vec A D) = 0); auto with geo; intros.
Simplscal; rewrite H2; ring.
cut (scalaire (vec A E) (vec A E) = 1); auto with geo; intros.
rewrite H3.
Simplscal; rewrite H4; ring.
replace (vec A E) with (vec B A).
rewrite <- angle_plat; auto with geo.
rewrite H3.
Ringvec.
Qed.
 
Lemma coordonnees_cos_sin :
 forall (x : R) (O I J M : PO),
 repere_orthonormal_direct O I J ->
 image_angle x = cons_AV (vec O I) (vec O M) ->
 distance O M = 1 ->
 vec O M = add_PP (mult_PP (cos x) (vec O I)) (mult_PP (sin x) (vec O J))
 :>PP.
intros.
elim H; intros.
elim H3; intros H4 H5; try clear H3; try exact H5.
rewrite (def_sin (A:=O) (B:=I) (C:=M) (D:=J) (x:=x)); auto with geo.
rewrite (def_cos (A:=O) (B:=I) (C:=M) (x:=x)); auto with geo.
pattern (vec O M) at 1 in |- *.
rewrite (coordonnees_scalaire_base (O:=O) (I:=I) (J:=J) M); auto with geo.
rewrite scalaire_sym; auto.
Qed.
 
Lemma calcul_cos_sin :
 forall (x a b : R) (O I J M : PO),
 repere_orthonormal_direct O I J ->
 image_angle x = cons_AV (vec O I) (vec O M) ->
 distance O M = 1 ->
 vec O M = add_PP (mult_PP a (vec O I)) (mult_PP b (vec O J)) :>PP ->
 a = cos x /\ b = sin x.
intros.
apply unicite_coordonnees with (2 := H2); auto with geo.
apply coordonnees_cos_sin; auto.
Qed.
 
Lemma trigo_Pythagore : forall x : R, Rsqr (cos x) + Rsqr (sin x) = 1.
unfold Rsqr in |- *; intros.
elim existence_AB_unitaire; intros A H; elim H; intros B H0; try clear H;
 try exact H0.
elim existence_representant_angle with (A := A) (B := B) (C := A) (x := x);
 [ intros C H; elim H; intros H1 H2; try clear H; try exact H2 | auto ].
elim existence_ROND_AB with (A := A) (B := B); [ intros D H | auto ].
elim H; intros.
cut
 (vec A C = add_PP (mult_PP (cos x) (vec A B)) (mult_PP (sin x) (vec A D)));
 intros.
replace 1 with (scalaire (vec A C) (vec A C)); auto with geo.
rewrite H5.
Simplscal.
elim H4; intros H6 H7; try clear H4; try exact H7.
rewrite H7; rewrite H6.
rewrite (pisurdeux_scalaire_nul (A:=A) (B:=B) (C:=D)); auto.
rewrite scalaire_sym.
rewrite (pisurdeux_scalaire_nul (A:=A) (B:=B) (C:=D)); auto.
ring.
apply coordonnees_cos_sin; auto.
Qed.
 
Lemma pisurdeux_plus_x :
 forall x : R, cos (pisurdeux + x) = - sin x /\ sin (pisurdeux + x) = cos x.
intros.
elim existence_AB_unitaire; intros A H; elim H; intros B H0; try clear H;
 try exact H0.
elim existence_ROND_AB with (A := A) (B := B); [ intros D H10 | auto ].
elim
 existence_representant_angle
  with (A := A) (B := B) (C := A) (x := pisurdeux + x);
 [ intros C H; elim H; intros H1 H2; try clear H; try exact H2 | auto ].
elim H10; intros.
elim H3; intros H6 H7; try clear H3; try exact H7.
elim
 existence_representant_mult_vecteur
  with (A := A) (B := A) (C := B) (k := -1); intros E H4.
cut (image_angle x = cons_AV (vec A D) (vec A C)); intros.
generalize
 (coordonnees_cos_sin (x:=pisurdeux + x) (O:=A) (I:=B) (J:=D) (M:=C)); 
 intros.
generalize (coordonnees_cos_sin (x:=x) (O:=A) (I:=D) (J:=E) (M:=C)); intros.
cut
 (vec A C = add_PP (mult_PP (- sin x) (vec A B)) (mult_PP (cos x) (vec A D)));
 intros.
apply unicite_coordonnees with (3 := H9); auto with geo.
rewrite H8; auto.
rewrite H4.
unfold vec in |- *; RingPP.
apply ROND_new with B; auto.
replace x with (- pisurdeux + (pisurdeux + x)); try ring.
replace (cons_AV (vec A D) (vec A C)) with
 (plus (cons_AV (vec A D) (vec A B)) (cons_AV (vec A B) (vec A C))).
replace (cons_AV (vec A D) (vec A B)) with (image_angle (- pisurdeux)).
rewrite <- H2.
apply add_mes_compatible.
apply mes_oppx; auto with geo.
apply Chasles; auto with geo.
Qed.
 
Lemma sin_impaire : forall x : R, sin (- x) = - sin x.
intros.
elim pisurdeux_plus_x with (x := - x); intros H H0;
 try clear pisurdeux_plus_x; try exact H.
replace (sin (- x)) with (-1 * - sin (- x)).
rewrite <- H.
replace (- x + pisurdeux) with (pisurdeux + - x).
rewrite <- sin_cos_pisurdeux_moins_x.
ring.
ring.
ring.
Qed.
 
Lemma pi_moins_x :
 forall x : R, cos (pi + - x) = - cos x /\ sin (pi + - x) = sin x.
intros.
unfold pi in |- *.
replace (pisurdeux + pisurdeux + - x) with (pisurdeux + (pisurdeux + - x)).
elim pisurdeux_plus_x with (x := pisurdeux + - x); intros H H0;
 try clear pisurdeux_plus_x; try exact H0.
rewrite H0; rewrite H.
split; [ try assumption | idtac ].
rewrite cos_sin_pisurdeux_moins_x; auto.
rewrite sin_cos_pisurdeux_moins_x; auto.
ring.
Qed.
 
Lemma pi_plus_x :
 forall x : R, cos (pi + x) = - cos x /\ sin (pi + x) = - sin x.
intros.
elim pi_moins_x with (x := - x); intros H H0; try clear pi_moins_x;
 try exact H0.
replace (pi + x) with (pi + - - x).
rewrite H0; rewrite H.
split; [ try assumption | idtac ].
rewrite cos_paire; auto.
rewrite sin_impaire; auto.
ring.
Qed.
 
Theorem cos_diff :
 forall a b : R, cos (a + - b) = cos a * cos b + sin a * sin b.
intros.
elim existence_AB_unitaire; intros A H; elim H; intros B H0; try clear H;
 try exact H0.
elim existence_ROND_AB with (A := A) (B := B); [ intros D H10 | auto ].
elim existence_representant_angle with (A := A) (B := B) (C := A) (x := a);
 [ intros C H; elim H; intros H1 H2; try clear H; try exact H2 | auto ].
elim existence_representant_angle with (A := A) (B := B) (C := A) (x := b);
 [ intros E H; elim H; intros H3 H4; try clear H; try exact H4 | auto ].
generalize (coordonnees_cos_sin (x:=a) (O:=A) (I:=B) (J:=D) (M:=C)); intros H.
generalize (coordonnees_cos_sin (x:=b) (O:=A) (I:=B) (J:=D) (M:=E)); intros.
replace (cos a * cos b + sin a * sin b) with (scalaire (vec A C) (vec A E)).
cut (image_angle (a + - b) = cons_AV (vec A E) (vec A C)); intros.
rewrite (def_cos (A:=A) (B:=E) (C:=C) (x:=a + - b)); auto.
rewrite scalaire_sym; auto.
replace (cons_AV (vec A E) (vec A C)) with
 (plus (cons_AV (vec A E) (vec A B)) (cons_AV (vec A B) (vec A C))).
replace (cons_AV (vec A E) (vec A B)) with (image_angle (- b)).
rewrite <- H2.
replace (a + - b) with (- b + a).
apply add_mes_compatible.
ring.
apply mes_oppx; auto with geo.
apply Chasles; auto with geo.
rewrite H5; auto.
rewrite H; auto.
Simplscal.
elim H10; intros.
elim H7; intros H8 H9; try clear H7; try exact H9.
cut (scalaire (vec A B) (vec A D) = 0); auto with geo; intros.
rewrite H9; rewrite H8; rewrite H7.
rewrite scalaire_sym; rewrite H7.
ring.
Qed.
 
Lemma cos_som :
 forall a b : R, cos (a + b) = cos a * cos b + - (sin a * sin b).
intros.
replace (a + b) with (a + - - b).
rewrite (cos_diff a (- b)).
rewrite cos_paire.
rewrite sin_impaire.
ring.
ring.
Qed.
 
Lemma sin_som : forall a b : R, sin (a + b) = sin a * cos b + sin b * cos a.
intros.
replace (sin (a + b)) with (cos (pisurdeux + - (a + b))).
replace (pisurdeux + - (a + b)) with (pisurdeux + - a + - b).
rewrite cos_diff.
rewrite <- sin_cos_pisurdeux_moins_x.
rewrite <- cos_sin_pisurdeux_moins_x.
ring.
ring.
rewrite <- sin_cos_pisurdeux_moins_x; auto.
Qed.
 
Lemma sin_diff :
 forall a b : R, sin (a + - b) = sin a * cos b + - (sin b * cos a).
intros.
rewrite sin_som.
rewrite cos_paire.
rewrite sin_impaire.
ring.
Qed.
 
Lemma duplication_cos : forall a : R, cos (2 * a) = 2 * Rsqr (cos a) + -1.
intros.
repeat rewrite double.
rewrite cos_som.
rewrite <- (trigo_Pythagore a).
unfold Rsqr; ring.
Qed.
 
Lemma duplication_cos2 : forall a : R, cos (2 * a) = 1 + - (2 * Rsqr (sin a)).
intros.
repeat rewrite double.
rewrite cos_som.
rewrite <- (trigo_Pythagore a).
unfold Rsqr; ring.
Qed.
 
Lemma duplication_sin : forall a : R, sin (2 * a) = 2 * (sin a * cos a).
intros.
repeat rewrite double.
rewrite sin_som; auto.
Qed.
 
Lemma coordonnees_polaires_cartesiennes :
 forall (x y a r : R) (O I J M : PO),
 repere_orthonormal_direct O I J ->
 O <> M ->
 r = distance O M ->
 image_angle a = cons_AV (vec O I) (vec O M) ->
 vec O M = add_PP (mult_PP x (vec O I)) (mult_PP y (vec O J)) :>PP ->
 x = r * cos a /\ y = r * sin a.
intros.
apply unicite_coordonnees with (2 := H3); auto with geo.
elim existence_representant_unitaire with (A := O) (B := M);
 [ intros C H4; try clear existence_unitaire; try exact H4 | auto ].
rewrite (distance_vecteur (A:=O) (B:=M)); auto.
rewrite <- H4.
rewrite (coordonnees_cos_sin (x:=a) (O:=O) (I:=I) (J:=J) (M:=C)); auto.
rewrite <- H1.
unfold vec in |- *; RingPP.
rewrite H2.
rewrite H4.
inversion H.
elim H6; intros H7 H8; try clear H6; try exact H7.
rewrite angles_representants_unitaires; auto with geo.
replace (representant_unitaire (vec O I)) with (vec O I); auto with geo.
elim def_representant_unitaire2 with (A := O) (B := M) (C := C);
 [ intros; elim H6; intros H7 H8; try clear H6 def_representant_unitaire2;
    auto with geo
 | auto
 | auto ].
Qed.
 
Lemma trivial_cos_Cos :
 forall (A B C : PO) (x : R),
 distance A B = 1 ->
 distance A C = 1 ->
 image_angle x = cons_AV (vec A B) (vec A C) ->
 cos x = Cos (cons_AV (vec A B) (vec A C)).
intros.
rewrite (def_cos (A:=A) (B:=B) (C:=C) (x:=x)); auto.
rewrite (def_Cos (A:=A) (B:=B) (C:=C)); auto.
Qed.
 
Lemma egalite_cos_Cos :
 forall (A B C : PO) (x : R),
 A <> B ->
 A <> C ->
 image_angle x = cons_AV (vec A B) (vec A C) ->
 cos x = Cos (cons_AV (vec A B) (vec A C)).
intros.
elim existence_representant_unitaire with (A := A) (B := B);
 [ intros B' H2; try clear existence_representant_unitaire; try exact H2
 | auto ].
elim existence_representant_unitaire with (A := A) (B := C);
 [ intros C' H3; try clear existence_representant_unitaire; try exact H3
 | auto ].
rewrite (trivial_cos_Cos (A:=A) (B:=B') (C:=C') (x:=x)); auto.
rewrite H2; rewrite H3; auto.
rewrite angles_representants_unitaires; auto.
elim def_representant_unitaire2 with (A := A) (B := B) (C := B'); auto;
 intros.
elim H5; auto with geo.
elim def_representant_unitaire2 with (A := A) (B := C) (C := C'); auto;
 intros.
elim H5; auto with geo.
rewrite H2; rewrite H3; rewrite H1; rewrite angles_representants_unitaires;
 auto with geo.
Qed.
 
Lemma trivial_sin_Sin :
 forall (A B C D : PO) (x : R),
 distance A B = 1 ->
 distance A C = 1 ->
 image_angle x = cons_AV (vec A B) (vec A C) ->
 repere_orthonormal_direct A B D -> sin x = Sin (cons_AV (vec A B) (vec A C)).
intros.
rewrite (def_sin (A:=A) (B:=B) (C:=C) (D:=D) (x:=x)); auto.
rewrite (def_Sin (A:=A) (B:=B) (C:=C) (D:=D)); auto.
Qed.
 
Lemma egalite_sin_Sin :
 forall (A B C : PO) (x : R),
 A <> B ->
 A <> C ->
 image_angle x = cons_AV (vec A B) (vec A C) ->
 sin x = Sin (cons_AV (vec A B) (vec A C)).
intros.
elim existence_representant_unitaire with (A := A) (B := B);
 [ intros B' H2; try clear existence_representant_unitaire; try exact H2
 | auto ].
elim existence_ROND_AB with (A := A) (B := B'); [ intros D H10 | auto ].
elim existence_representant_unitaire with (A := A) (B := C);
 [ intros C' H3; try clear existence_representant_unitaire; try exact H3
 | auto ].
rewrite (trivial_sin_Sin (A:=A) (B:=B') (C:=C') (D:=D) (x:=x)); auto.
rewrite H2; rewrite H3; auto.
rewrite angles_representants_unitaires; auto.
elim def_representant_unitaire2 with (A := A) (B := B) (C := B'); auto;
 intros.
elim H5; auto with geo.
elim def_representant_unitaire2 with (A := A) (B := C) (C := C'); auto;
 intros.
elim H5; auto with geo.
rewrite H2; rewrite H3; rewrite H1; rewrite angles_representants_unitaires;
 auto.
elim def_representant_unitaire2 with (A := A) (B := B) (C := B');
 auto with geo; intros.
elim H4; auto with geo.
Qed.
 
Lemma coordonnees_Cos_Sin :
 forall O I J M : PO,
 repere_orthonormal_direct O I J ->
 distance O M = 1 ->
 vec O M =
 add_PP (mult_PP (Cos (cons_AV (vec O I) (vec O M))) (vec O I))
   (mult_PP (Sin (cons_AV (vec O I) (vec O M))) (vec O J)) :>PP.
intros.
elim H; intros.
elim H2; intros H4 H5; try clear H2.
mesure O I O M.
rewrite H2.
rewrite <- (trivial_sin_Sin (A:=O) (B:=I) (C:=M) (D:=J) (x:=x));
 auto with geo.
rewrite <- (trivial_cos_Cos (A:=O) (B:=I) (C:=M) (x:=x)); auto with geo.
apply coordonnees_cos_sin; auto.
Qed.
 
Lemma calcul_Cos_Sin :
 forall (a b : R) (O I J M : PO),
 repere_orthonormal_direct O I J ->
 distance O M = 1 ->
 vec O M = add_PP (mult_PP a (vec O I)) (mult_PP b (vec O J)) :>PP ->
 a = Cos (cons_AV (vec O I) (vec O M)) /\
 b = Sin (cons_AV (vec O I) (vec O M)).
intros.
elim H; intros.
elim H3; intros H4 H5; try clear H3.
mesure O I O M.
rewrite H3.
rewrite <- (trivial_sin_Sin (A:=O) (B:=I) (C:=M) (D:=J) (x:=x));
 auto with geo.
rewrite <- (trivial_cos_Cos (A:=O) (B:=I) (C:=M) (x:=x)); auto with geo.
apply (calcul_cos_sin (x:=x) (a:=a) (b:=b) (O:=O) (I:=I) (J:=J) (M:=M)); auto.
Qed.
 
Axiom
  egalite_angle_trigo :
    forall x y : R,
    sin x = sin y -> cos x = cos y -> image_angle x = image_angle y.
Hint Resolve egalite_angle_trigo: geo.

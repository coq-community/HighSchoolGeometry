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


Require Export complexes.
Set Implicit Arguments.
Unset Strict Implicit.
Parameter partie_reelle : C -> R.
Parameter partie_imaginaire : C -> R.
 
Axiom
  partie_reelle_def :
    forall (z : C) (a b : R), z = cons_cart a b -> a = partie_reelle z.
 
Axiom
  partie_imaginaire_def :
    forall (z : C) (a b : R), z = cons_cart a b -> b = partie_imaginaire z.
 
Axiom
  forme_algebrique_def :
    forall (z : C) (a b : R),
    a = partie_reelle z -> b = partie_imaginaire z -> z = cons_cart a b.
 
Lemma car_image_forme_algebrique :
 forall (z : C) (M : PO),
 M = image z ->
 partie_reelle z = abscisse M /\ partie_imaginaire z = ordonnee M.
intros.
elim existence_coordonnees with (O := O) (I := I) (J := J) (M := M);
 [ intros x H2; elim H2; intros y H3 | auto with geo ].
cut (z = cons_cart x y); intros.
rewrite <- (partie_reelle_def H0).
rewrite <- (partie_imaginaire_def H0).
split; eauto with geo.
eauto with geo.
Qed.
 
Lemma coordonnees_affixe :
 forall M : PO, cons_cart (abscisse M) (ordonnee M) = affixe M :>C.
intros.
elim existence_affixe_point with (M := M); intros z H;
 try clear existence_affixe_point; try exact H.
elim car_image_forme_algebrique with (z := z) (M := M);
 [ intros; try exact H1 | eauto with geo ].
rewrite <- H1; rewrite <- H0; rewrite <- H.
symmetry  in |- *; eauto with geo.
Qed.
Hint Resolve coordonnees_affixe: geo.
 
Lemma absvec_ordvec_affixe :
 forall (a b : R) (A B : PO),
 a = absvec (vec A B) ->
 b = ordvec (vec A B) -> cons_cart a b = affixe_vec (vec A B).
intros a b A B.
elim existence_representant_vecteur with (A := O) (B := A) (C := B);
 intros D H1; try exact H1.
rewrite <- H1; intros.
apply affixe_point_vecteur.
rewrite H0; rewrite H; rewrite (ordvec_ordonnee (O:=O) (I:=I) (J:=J) D);
 auto with geo.
rewrite (absvec_abscisse (O:=O) (I:=I) (J:=J) D); auto with geo.
Qed.
Parameter module : C -> R.
Parameter argument : C -> AV.
 
Axiom
  module_def :
    forall (z : C) (M : PO), M = image z -> module z = distance O M.
 
Axiom
  argument_def :
    forall (M : PO) (z : C),
    O <> M -> M = image z -> argument z = cons_AV (vec O I) (vec O M).
Hint Resolve module_def argument_def: geo.
 
Lemma module_def2 :
 forall (z : C) (M : PO), z = affixe M -> module z = distance O M.
intros; eauto with geo.
Qed.
 
Lemma argument_def2 :
 forall (M : PO) (z : C),
 O <> M -> z = affixe M -> argument z = cons_AV (vec O I) (vec O M).
intros; eauto with geo.
Qed.
 
Lemma existence_module : forall z : C, exists r : R, module z = r.
intros.
elim existence_image_complexe with (z := z); intros M H1;
 try clear existence_image_complexe; try exact H1.
exists (distance O M); eauto with geo.
Qed.
 
Definition zeroC := cons_cart 0 0.
 
Lemma image_zeroC : image zeroC = O.
elim existence_image_complexe with (z := zeroC); unfold zeroC in |- *;
 intros M H1; try exact H1.
cut (vec O M = add_PP (mult_PP 0 (vec O I)) (mult_PP 0 (vec O J))); intros;
 eauto with geo.
rewrite <- H1.
symmetry  in |- *.
apply vecteur_nul_conf.
rewrite H.
Ringvec.
Qed.
Hint Resolve image_zeroC: geo.
 
Lemma affixe_origine : zeroC = affixe O.
eauto with geo.
Qed.
Hint Resolve affixe_origine: geo.
 
Lemma module_zeroC : module zeroC = 0.
rewrite (module_def (z:=zeroC) (M:=O)); auto with geo.
Qed.
 
Lemma module_nul_zeroC : forall z : C, module z = 0 -> z = zeroC.
intros.
elim existence_image_complexe with (z := z); intros M H1;
 try clear existence_image_complexe; try exact H1.
cut (O = M); intros.
rewrite (affixe_image H1).
rewrite <- H0; auto with geo.
apply distance_refl1.
rewrite <- H; symmetry  in |- *; auto with geo.
Qed.
Hint Resolve module_zeroC module_nul_zeroC: geo.
 
Lemma module_non_zero : forall z : C, z <> zeroC -> module z <> 0.
red in |- *; intros.
apply H; auto with geo.
Qed.
 
Lemma nonzero_module : forall z : C, module z <> 0 -> z <> zeroC.
red in |- *; intros.
apply H; rewrite H0; auto with geo.
Qed.
Hint Resolve module_non_zero nonzero_module: geo.
 
Lemma image_nonzero_nonorigine :
 forall (M : PO) (z : C), z <> zeroC :>C -> M = image z -> O <> M.
intros.
red in |- *; intros; apply H.
replace z with (affixe M).
rewrite <- H1; auto with geo.
symmetry  in |- *; auto with geo.
Qed.
Hint Resolve image_nonzero_nonorigine: geo.
 
Lemma nonorigine_image_nonzero :
 forall (M : PO) (z : C), O <> M -> M = image z -> z <> zeroC :>C.
intros.
red in |- *; intros; apply H.
rewrite H0; rewrite H1.
symmetry  in |- *; auto with geo.
Qed.
Hint Resolve nonorigine_image_nonzero: geo.
 
Lemma existence_argument :
 forall z : C, z <> zeroC -> exists a : R, argument z = image_angle a.
intros.
elim existence_image_complexe with (z := z); intros M H1;
 try clear existence_image_complexe; try exact H1.
cut (O <> M); intros; eauto with geo.
mesure O I O M.
exists x.
rewrite H2; eauto with geo.
Qed.
 
Lemma existence_forme_polaire :
 forall z : C,
 z <> zeroC ->
 exists r : R, (exists a : R, module z = r /\ argument z = image_angle a).
intros.
elim existence_module with (z := z); intros r H0; try clear existence_module;
 try exact H0.
elim existence_argument with (z := z);
 [ intros a H1; try clear existence_argument; try exact H1 | auto ].
exists r; exists a; auto.
Qed.
Parameter cons_pol : R -> R -> C.
 
Axiom
  forme_polaire_def :
    forall (z : C) (r a : R),
    z <> zeroC ->
    module z = r -> argument z = image_angle a -> z = cons_pol r a.
 
Axiom complexe_polaire_module : forall r a : R, module (cons_pol r a) = r.
 
Axiom
  complexe_polaire_argument :
    forall r a : R, r <> 0 -> argument (cons_pol r a) = image_angle a.
 
Lemma polaire_non_nul : forall r a : R, r <> 0 -> cons_pol r a <> zeroC.
intros.
apply nonzero_module.
rewrite complexe_polaire_module; auto.
Qed.
 
Lemma complexe_pol_module :
 forall (z : C) (r a : R), z <> zeroC -> z = cons_pol r a -> module z = r.
intros.
rewrite H0; rewrite complexe_polaire_module; auto.
Qed.
 
Lemma complexe_pol_argument :
 forall (z : C) (r a : R),
 z <> zeroC -> z = cons_pol r a -> argument z = image_angle a.
intros.
rewrite H0; rewrite complexe_polaire_argument; auto.
rewrite <- (complexe_pol_module (z:=z) (r:=r) (a:=a)); auto with geo.
Qed.
Hint Resolve forme_polaire_def complexe_pol_module complexe_pol_argument
  polaire_non_nul complexe_polaire_module complexe_polaire_module: geo.
 
Lemma pol_complexe_module :
 forall (z : C) (r a : R) (M : PO),
 z <> zeroC -> z = cons_pol r a -> M = image z -> distance O M = r.
intros.
rewrite <- (module_def H1); eauto with geo.
Qed.
 
Lemma pol_complexe_argument :
 forall (z : C) (r a : R) (M : PO),
 z <> zeroC ->
 z = cons_pol r a ->
 M = image z -> cons_AV (vec O I) (vec O M) = image_angle a.
intros.
rewrite <- (argument_def (M:=M) (z:=z)); eauto with geo.
Qed.
Hint Resolve pol_complexe_argument pol_complexe_module: geo.
 
Lemma image_forme_polaire :
 forall (z : C) (M : PO),
 O <> M ->
 M = image z ->
 module z = distance O M /\ argument z = cons_AV (vec O I) (vec O M).
intros.
split; eauto with geo.
Qed.
 
Lemma unicite_forme_polaire_nonzero :
 forall (z : C) (r a r' a' : R),
 z <> zeroC ->
 z = cons_pol r a ->
 z = cons_pol r' a' -> r = r' /\ image_angle a = image_angle a'.
intros.
split.
rewrite <- (complexe_pol_module (z:=z) (r:=r) (a:=a)); eauto with geo.
rewrite <- (complexe_pol_argument (z:=z) (r:=r) (a:=a)); eauto with geo.
Qed.
Hint Resolve unicite_forme_polaire_nonzero image_forme_polaire: geo.
 
Lemma passage_polaire_algebrique :
 forall (z : C) (r a x y : R),
 z <> zeroC ->
 z = cons_cart x y -> z = cons_pol r a -> x = r * cos a /\ y = r * sin a.
intros.
elim existence_image_complexe with (z := z); intros M H2;
 try clear existence_image_complexe; try exact H2.
elim
 coordonnees_polaires_cartesiennes
  with
    (x := x)
    (y := y)
    (a := a)
    (r := r)
    (O := O)
    (I := I)
    (J := J)
    (M := M);
 [ intros; eauto with geo
 | eauto with geo
 | eauto with geo
 | eauto with geo
 | eauto with geo
 | eauto with geo ].
symmetry  in |- *; eauto with geo.
symmetry  in |- *; eauto with geo.
Qed.
 
Lemma passage_algebrique_module :
 forall (z : C) (x y : R),
 z = cons_cart x y -> module z = sqrt (Rsqr x + Rsqr y).
intros.
elim existence_image_complexe with (z := z); intros M H2;
 try clear existence_image_complexe; try exact H2.
replace (module z) with (distance O M); auto.
rewrite (distance_coordonnees (O:=O) (I:=I) (J:=J) (M:=M) (x:=x) (y:=y));
 eauto with geo.
symmetry  in |- *; eauto with geo.
Qed.
 
Lemma passage_algebrique_argument :
 forall (z : C) (r x y a : R),
 z <> zeroC ->
 z = cons_cart x y -> z = cons_pol r a -> cos a = / r * x /\ sin a = / r * y.
intros.
elim
 passage_polaire_algebrique with (z := z) (r := r) (a := a) (x := x) (y := y);
 [ intros | eauto with geo | eauto with geo | eauto with geo ].
cut (r <> 0); intros.
split; [ try assumption | idtac ].
rewrite H2.
field; auto.
rewrite H3.
field; auto.
replace r with (module z); eauto with geo.
Qed.
 
Lemma egalite_forme_polaire :
 forall z z' : C,
 z <> zeroC ->
 z' <> zeroC -> module z = module z' -> argument z = argument z' -> z = z'.
intros.
elim existence_forme_polaire with (z := z);
 [ intros r H3; elim H3; intros a H4; elim H4; intros H5 H6;
    try clear H4 H3 existence_forme_polaire; try exact H6
 | auto ].
elim existence_forme_polaire with (z := z');
 [ intros r0 H7; elim H7; intros a0 H8; elim H8; intros H9 H10;
    try clear H8 H7 existence_forme_polaire; try exact H10
 | auto ].
rewrite (forme_polaire_def (z:=z) (r:=r) (a:=a)); auto.
rewrite (forme_polaire_def (z:=z') (r:=r) (a:=a)); auto.
rewrite <- H5; auto.
rewrite <- H6; auto.
Qed.
Hint Resolve passage_algebrique_module passage_algebrique_argument
  egalite_forme_polaire: geo.
 
Lemma algebrique_zeroC :
 forall a b : R, cons_cart a b = zeroC :>C -> a = 0 /\ b = 0.
intros.
apply unicite_parties_relles_imaginaires with zeroC; auto.
Qed.
 
Lemma polaire_calcul_algebrique :
 forall (z : C) (r a : R),
 z <> zeroC :>C ->
 z = cons_pol r a :>C -> z = cons_cart (r * cos a) (r * sin a) :>C.
intros.
elim existence_parties_relles_imaginaires with (z := z); intros a0 H1;
 elim H1; intros b H2; try clear H1 existence_parties_relles_imaginaires;
 try exact H2.
elim
 passage_polaire_algebrique
  with (z := z) (r := r) (a := a) (x := a0) (y := b);
 [ intros; try exact H4 | auto | auto | auto ].
rewrite H2; rewrite H3; rewrite H4; auto.
Qed.
Hint Resolve polaire_calcul_algebrique: geo.
 
Definition Rinj (x : R) := cons_cart x 0.
 
Definition oneC := cons_cart 1 0.
Hint Unfold oneC zeroC Rinj: geo.
 
Lemma Rinj_zero : Rinj 0 = zeroC.
unfold Rinj, zeroC in |- *; auto.
Qed.
 
Lemma Rinj_un : Rinj 1 = oneC.
unfold Rinj, oneC in |- *; auto.
Qed.
 
Lemma module_oneC : module oneC = 1.
intros.
rewrite (passage_algebrique_module (z:=oneC) (x:=1) (y:=0)).
replace (Rsqr 1 + Rsqr 0) with 1 by (unfold Rsqr; ring).
exact sqrt_1.
unfold oneC in |- *; auto.
Qed.
 
Lemma oneC_nonzero : oneC <> zeroC.
apply nonzero_module.
rewrite module_oneC; auto with real.
Qed.
Hint Resolve module_oneC oneC_nonzero: geo.
 
Lemma argument_oneC : argument oneC = image_angle 0.
elim existence_forme_polaire with (z := oneC);
 [ intros r H; elim H; intros a H0; elim H0; intros H1 H2;
    try clear H0 H existence_forme_polaire; try exact H2
 | auto with geo ].
rewrite module_oneC in H1.
rewrite H2.
elim
 passage_algebrique_argument
  with (z := oneC) (r := 1) (x := 1) (y := 0) (a := a);
 [ intros | auto with geo | auto with geo | auto with geo ].
apply egalite_angle_trigo.
rewrite sin_zero; rewrite H4; ring.
rewrite H3; rewrite cos_zero; field.
Qed.
Hint Resolve argument_oneC: geo.
 
Definition i := cons_cart 0 1.
Hint Unfold i: geo.
 
Lemma module_i : module i = 1.
intros.
rewrite (passage_algebrique_module (z:=i) (x:=0) (y:=1)).
replace (Rsqr 0 + Rsqr 1) with 1 by (unfold Rsqr; ring).
exact sqrt_1.
unfold i in |- *; auto.
Qed.
 
Lemma i_nonzero : i <> zeroC.
apply nonzero_module.
rewrite module_i; auto with real.
Qed.
Hint Resolve module_i i_nonzero: geo.
 
Lemma argument_i : argument i = image_angle pisurdeux.
elim existence_forme_polaire with (z := i);
 [ intros r H; elim H; intros a H0; elim H0; intros H1 H2;
    try clear H0 H existence_forme_polaire; try exact H2
 | auto with geo ].
elim
 passage_algebrique_argument
  with (z := i) (r := 1) (x := 0) (y := 1) (a := a);
 [ intros | auto with geo | auto with geo | auto with geo ].
rewrite module_i in H1.
rewrite H2.
elim
 passage_algebrique_argument
  with (z := i) (r := 1) (x := 0) (y := 1) (a := a);
 [ intros | auto with geo | auto with geo | auto with geo ].
apply egalite_angle_trigo.
rewrite sin_pisurdeux; rewrite H4; field.
rewrite H3; rewrite cos_pisurdeux; ring.
Qed.
Hint Resolve argument_i: geo.
 
Lemma forme_polaire_oneC : oneC = cons_pol 1 0.
apply forme_polaire_def; auto with geo.
Qed.
 
Lemma forme_polaire_i : i = cons_pol 1 pisurdeux.
apply forme_polaire_def; auto with geo.
Qed.
Hint Resolve forme_polaire_oneC forme_polaire_i: geo.
 
Lemma egalite_cart_pol :
 forall x y r a : R,
 r <> 0 ->
 module (cons_cart x y) = r ->
 argument (cons_cart x y) = image_angle a :>AV ->
 cons_cart x y = cons_pol r a :>C.
intros.
rewrite <- (forme_polaire_def (z:=cons_cart x y) (r:=r) (a:=a));
 auto with geo.
apply nonzero_module.
rewrite H0; auto.
Qed.
 
Lemma module_opp_un : module (Rinj (-1)) = 1.
unfold Rinj in |- *.
rewrite (passage_algebrique_module (z:=cons_cart (-1) 0) (x:=-1) (y:=0));
 auto with geo.
replace (Rsqr (-1) + Rsqr 0) with 1 by (unfold Rsqr; ring).
exact sqrt_1.
Qed.
 
Lemma opp_un_nonzero : Rinj (-1) <> zeroC :>C.
apply nonzero_module.
rewrite module_opp_un; auto with real.
Qed.
Hint Resolve opp_un_nonzero module_opp_un: geo.
 
Lemma argument_opp_un : argument (Rinj (-1)) = image_angle pi.
elim existence_forme_polaire with (z := Rinj (-1));
 [ intros r H1; elim H1; intros a H2; elim H2; intros H3 H4; try clear H2 H1;
    try exact H4
 | auto with geo ].
rewrite module_opp_un in H3.
elim
 passage_algebrique_argument
  with (z := Rinj (-1)) (r := 1) (x := -1) (y := 0) (a := a);
 [ intros | auto with geo | auto with geo | auto with geo ].
rewrite H4.
apply egalite_angle_trigo.
rewrite sin_pi; rewrite H0; ring.
rewrite H; rewrite cos_pi; field.
Qed.
Hint Resolve argument_opp_un: geo.
 
Lemma forme_polaire_opp_un : Rinj (-1) = cons_pol 1 pi.
apply forme_polaire_def; auto with geo.
Qed.
 
Lemma module_reel : forall x : R, module (Rinj x) = Rabs x.
unfold Rinj in |- *; intros.
rewrite (passage_algebrique_module (z:=cons_cart x 0) (x:=x) (y:=0));
 auto with geo.
replace (Rsqr x + Rsqr 0) with (Rsqr x) by (unfold Rsqr; ring).
rewrite sqrt_Rsqr_abs; auto.
Qed.
 
Lemma module_reel_pos : forall x : R, 0 <= x -> module (Rinj x) = x.
unfold Rinj in |- *; intros.
rewrite (passage_algebrique_module (z:=cons_cart x 0) (x:=x) (y:=0));
 auto with geo.
replace (Rsqr x + Rsqr 0) with (Rsqr x) by (unfold Rsqr in |- *; ring).
rewrite sqrt_Rsqr; auto.
Qed.
 
Lemma reel_non_nul : forall x : R, x <> 0 -> Rinj x <> zeroC.
intros.
apply nonzero_module.
rewrite module_reel.
apply Rabs_no_R0; auto.
Qed.
Hint Resolve reel_non_nul module_reel_pos module_reel: geo.
 
Lemma argument_reel_pos :
 forall x : R, 0 < x -> argument (Rinj x) = image_angle 0.
intros.
cut (x <> 0); intros.
elim existence_forme_polaire with (z := Rinj x);
 [ intros r H1; elim H1; intros a H2; elim H2; intros H3 H4; try clear H2 H1;
    try exact H4
 | auto with geo ].
cut (x = r); intros.
elim
 passage_algebrique_argument
  with (z := Rinj x) (r := r) (x := x) (y := 0) (a := a);
 [ intros | auto with geo | auto with geo | auto with geo ].
rewrite H4.
apply egalite_angle_trigo.
rewrite sin_zero; rewrite H5; ring.
rewrite H2; rewrite <- H1; rewrite cos_zero; field; trivial.
rewrite module_reel_pos in H3; auto.
fourier.
auto with real.
Qed.
Hint Resolve argument_reel_pos: geo.
 
Lemma forme_pol_reel_pos : forall x : R, 0 < x -> Rinj x = cons_pol x 0 :>C.
intros.
apply forme_polaire_def; auto with geo.
apply reel_non_nul; auto with real.
apply module_reel_pos; auto with real.
Qed.
 
Lemma module_reel_neg : forall x : R, 0 > x -> module (Rinj x) = - x.
intros.
rewrite module_reel; auto.
apply Rabs_left1; auto with real.
Qed.
Hint Resolve module_reel_neg: geo.
 
Lemma argument_reel_neg :
 forall x : R, 0 > x -> argument (Rinj x) = image_angle pi.
intros.
cut (x <> 0); intros.
elim existence_forme_polaire with (z := Rinj x);
 [ intros r H1; elim H1; intros a H2; elim H2; intros H3 H4; try clear H2 H1;
    try exact H4
 | auto with geo ].
elim
 passage_algebrique_argument
  with (z := Rinj x) (r := r) (x := x) (y := 0) (a := a);
 [ intros | auto with geo | auto with geo | auto with geo ].
rewrite H4.
apply egalite_angle_trigo.
rewrite sin_pi; rewrite H2; ring.
cut (r = - x); intros.
rewrite H1; rewrite H5; rewrite cos_pi;  field; trivial.
rewrite <- H3.
rewrite module_reel_neg in |- *; [  ring | auto with geo ].
auto with real.
Qed.
Hint Resolve argument_reel_neg: geo.
 
Lemma forme_pol_reel_neg :
 forall x : R, 0 > x -> Rinj x = cons_pol (- x) pi :>C.
intros.
apply forme_polaire_def; auto with geo.
apply reel_non_nul; auto with real.
Qed.
 
Lemma module_pos : forall z : C, module z >= 0.
intros.
elim existence_image_complexe with (z := z); intros M H;
 try clear existence_image_complexe; try exact H.
rewrite (module_def H); auto with geo.
Qed.
Hint Resolve module_pos: geo.
 
Lemma module_stric_pos : forall z : C, z <> zeroC :>C -> module z > 0.
intros.
cut (module z >= 0); intros; auto with geo.
elim H0; intros; auto.
absurd (module z = 0); auto with geo.
Qed.
Hint Resolve module_stric_pos: geo.
 
Lemma abs_module : forall z : C, module z = Rabs (module z).
intros.
cut (module z >= 0); intros; auto with geo.
rewrite Rabs_right; auto.
Qed.
Hint Resolve abs_module: geo.

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
 
Definition double_AV (angl : AV) := plus angl angl.
 
Lemma double_Chasles :
 forall A B C D E F : PO,
 A <> B :>PO ->
 C <> D :>PO ->
 E <> F :>PO ->
 plus (double_AV (cons_AV (vec A B) (vec C D)))
   (double_AV (cons_AV (vec C D) (vec E F))) =
 double_AV (cons_AV (vec A B) (vec E F)) :>AV.
unfold double_AV in |- *.
intros.
replace
 (plus (plus (cons_AV (vec A B) (vec C D)) (cons_AV (vec A B) (vec C D)))
    (plus (cons_AV (vec C D) (vec E F)) (cons_AV (vec C D) (vec E F)))) with
 (plus (plus (cons_AV (vec A B) (vec C D)) (cons_AV (vec C D) (vec E F)))
    (plus (cons_AV (vec A B) (vec C D)) (cons_AV (vec C D) (vec E F)))).
rewrite Chasles; auto.
mesure A B C D.
mesure C D E F.
replace (x + x0 + (x + x0)) with (x + x + (x0 + x0)); auto.
ring.
Qed.
 
Lemma double_opp :
 forall A B C D : PO,
 A <> B :>PO ->
 C <> D :>PO ->
 double_AV (opp (cons_AV (vec A B) (vec C D))) =
 opp (double_AV (cons_AV (vec A B) (vec C D))) :>AV.
unfold double_AV in |- *; intros.
rewrite <- opp_plus_plus_opp; auto.
Qed.
 
Lemma zero_plus_double :
 forall A B C D : PO,
 A <> B :>PO ->
 C <> D :>PO ->
 plus (image_angle 0) (double_AV (cons_AV (vec A B) (vec C D))) =
 double_AV (cons_AV (vec A B) (vec C D)) :>AV.
intros.
replace (image_angle 0) with (double_AV (cons_AV (vec A B) (vec A B))).
rewrite double_Chasles; auto.
unfold double_AV in |- *.
rewrite <- angle_nul; auto.
rewrite <- add_mes_compatible; auto.
replace (0 + 0) with 0; auto.
ring.
Qed.
 
Lemma angle_alignes :
 forall A B C : PO,
 A <> B :>PO ->
 A <> C :>PO ->
 alignes A B C -> double_AV (cons_AV (vec A B) (vec A C)) = image_angle 0.
intros A B C H H0 H1; unfold double_AV in |- *.
rewrite angles_representants_unitaires; auto.
elim alignes_representant_unitaire with (A := A) (B := B) (C := C);
 [ intros; try clear alignes_representant_unitaire; auto
 | intros; auto
 | auto
 | auto
 | auto ].
rewrite H2.
rewrite <- angles_representants_unitaires; auto.
rewrite <- angle_nul; auto.
rewrite <- add_mes_compatible.
replace (0 + 0) with 0; try ring; auto.
elim existence_representant_unitaire with (A := A) (B := B);
 [ intros; try clear existence_representant_unitaire | auto ].
rewrite <- H3.
replace (representant_unitaire (vec A C)) with (vec x A).
cut (A <> x); intros.
rewrite <- angle_plat; auto.
rewrite <- add_mes_compatible.
replace (pi + pi) with deuxpi; auto.
rewrite pi_plus_pi; auto.
apply distance_non_nulle.
elim def_representant_unitaire2 with (A := A) (B := B) (C := x);
 [ intros; elim H5; intros H22 H23; rewrite H22; try discrR | auto | auto ].
rewrite H2; rewrite <- H3.
Ringvec.
Qed.
 
Lemma angle_droites_paralleles :
 forall A B C D : PO,
 A <> B :>PO ->
 C <> D :>PO ->
 paralleles (droite C D) (droite A B) ->
 double_AV (cons_AV (vec A B) (vec C D)) = image_angle 0.
intros.
elim paralleles_vecteur with (A := C) (B := D) (C := A) (D := B);
 [ intros k H3; try clear paralleles_vecteur; auto | auto | auto | auto ].
elim
 existence_representant_mult_vecteur with (A := A) (B := A) (C := B) (k := k);
 intros E H4; try clear existence_representant_mult_vecteur; 
 try exact H4.
cut (vec C D = vec A E); intros.
rewrite H2.
cut (alignes A B E); intros.
apply angle_alignes with (3 := H5); auto.
unfold not in |- *; intros; apply H0.
apply conversion_PP with (a := 1) (b := 1); auto with real.
RingPP2 H2.
rewrite H6.
Ringvec.
apply colineaire_alignes with k; auto.
rewrite H4; auto.
Qed.
 
Lemma alignement_et_angles :
 forall A B C D E F : PO,
 A <> B :>PO ->
 D <> E :>PO ->
 A <> C :>PO ->
 D <> F :>PO ->
 alignes A B C ->
 alignes D E F ->
 double_AV (cons_AV (vec A B) (vec D E)) =
 double_AV (cons_AV (vec A C) (vec D F)) :>AV.
intros; unfold double_AV in |- *.
rewrite angles_representants_unitaires; auto.
rewrite angles_representants_unitaires; auto.
elim existence_representant_unitaire with (A := D) (B := E);
 [ intros; try clear existence_representant_unitaire | auto ].
cut (D <> x); intros.
elim existence_representant_unitaire with (A := A) (B := C);
 [ intros; try clear existence_representant_unitaire | auto ].
cut (A <> x0); intros.
elim existence_representant_vecteur with (A := A) (B := D) (C := x); intros.
cut (A <> x1); intros.
elim alignes_representant_unitaire with (A := A) (B := B) (C := C);
 [ intros; try clear alignes_representant_unitaire; auto
 | intros; auto
 | auto
 | auto
 | auto ].
elim alignes_representant_unitaire with (A := D) (B := E) (C := F);
 [ intros; try clear alignes_representant_unitaire; auto
 | intros; auto
 | auto
 | auto
 | auto ].
rewrite H12; rewrite H11; auto.
rewrite H12; rewrite H11; auto.
replace (mult_PP (-1) (representant_unitaire (vec D E))) with (vec x D).
rewrite <- H7; rewrite <- H5.
replace (cons_AV (vec A x0) (vec x D)) with
 (plus (cons_AV (vec A x0) (vec D x)) (cons_AV (vec D x) (vec x D))).
rewrite <- angle_plat; auto.
rewrite <- H9.
mesure A x0 A x1.
replace (x2 + pi + (x2 + pi)) with (x2 + x2 + deuxpi); auto.
rewrite (add_mes_compatible (x2 + x2) deuxpi).
rewrite pi_plus_pi.
rewrite <- add_mes_compatible.
replace (x2 + x2 + 0) with (x2 + x2); auto.
ring.
unfold deuxpi; ring.
rewrite Chasles; auto.
rewrite <- H5.
Ringvec.
elim alignes_representant_unitaire with (A := D) (B := E) (C := F);
 [ intros; try clear alignes_representant_unitaire; auto
 | intros; auto
 | auto
 | auto
 | auto ].
replace (representant_unitaire (vec A B)) with (vec x0 A).
rewrite <- H7; rewrite <- H12; rewrite <- H5; rewrite <- H9.
replace (cons_AV (vec x0 A) (vec A x1)) with
 (plus (cons_AV (vec x0 A) (vec A x0)) (cons_AV (vec A x0) (vec A x1))).
mesure A x0 A x1.
rewrite <- angle_plat; auto.
rewrite <- add_mes_compatible.
rewrite <- add_mes_compatible.
replace (pi + x2 + (pi + x2)) with (x2 + x2 + deuxpi); auto.
rewrite (add_mes_compatible (x2 + x2) deuxpi).
rewrite pi_plus_pi.
rewrite <- add_mes_compatible.
replace (x2 + x2 + 0) with (x2 + x2); auto.
ring.
unfold deuxpi; ring.
rewrite Chasles; auto.
replace (vec x0 A) with (mult_PP (-1) (representant_unitaire (vec A C)));
 auto.
rewrite H11.
Ringvec.
rewrite <- H7.
Ringvec.
replace (representant_unitaire (vec A B)) with (vec x0 A).
rewrite H12; auto.
replace (mult_PP (-1) (representant_unitaire (vec D E))) with (vec x1 A).
rewrite <- H7; rewrite <- H5; rewrite <- H9.
replace (cons_AV (vec x0 A) (vec A x1)) with
 (plus (cons_AV (vec x0 A) (vec A x0)) (cons_AV (vec A x0) (vec A x1))).
mesure A x0 A x1.
rewrite <- angle_plat; auto.
rewrite <- add_mes_compatible.
replace (cons_AV (vec A x0) (vec x1 A)) with
 (plus (cons_AV (vec A x0) (vec A x1)) (cons_AV (vec A x1) (vec x1 A))).
rewrite <- angle_plat; auto.
rewrite <- H13.
repeat rewrite <- add_mes_compatible.
replace (pi + x2 + (pi + x2)) with (x2 + x2 + (pi + pi)); auto.
replace (x2 + x2 + (pi + pi)) with (x2 + pi + (x2 + pi)); auto.
unfold deuxpi; ring.
ring.
rewrite Chasles; auto.
rewrite Chasles; auto.
VReplace (vec x1 A) (mult_PP (-1) (vec A x1)); auto.
rewrite H9; rewrite H5; auto.
VReplace (vec x0 A) (mult_PP (-1) (vec A x0)).
rewrite H7; rewrite H11.
Ringvec.
unfold not in |- *; intros; apply H6.
apply conversion_PP with (a := 1) (b := 1); auto with real.
cut (vec D x = vec A x1); intros.
RingPP2 H11.
rewrite H10.
Ringvec.
rewrite H9; auto.
apply distance_non_nulle.
elim def_representant_unitaire2 with (A := A) (B := C) (C := x0);
 [ intros; elim H9; intros H22 H23; rewrite H22; try discrR | auto | auto ].
apply distance_non_nulle.
elim def_representant_unitaire2 with (A := D) (B := E) (C := x);
 [ intros; elim H7; intros H22 H23; rewrite H22; try discrR | auto | auto ].
Qed.
Parameter AD : Type.
Parameter cons_AD : DR -> DR -> AD.
 
Axiom
  AV_vers_AD :
    forall A B C D E F G I : PO,
    A <> B :>PO ->
    C <> D :>PO ->
    E <> F :>PO ->
    G <> I :>PO ->
    double_AV (cons_AV (vec A B) (vec C D)) =
    double_AV (cons_AV (vec E F) (vec G I)) :>AV ->
    cons_AD (droite A B) (droite C D) = cons_AD (droite E F) (droite G I)
    :>AD.
 
Lemma egalite_angles_droites :
 forall A B C D E F : PO,
 A <> B :>PO ->
 D <> E :>PO ->
 A <> C :>PO ->
 D <> F :>PO ->
 alignes A B C ->
 alignes D E F ->
 cons_AD (droite A B) (droite D E) = cons_AD (droite A C) (droite D F) :>AD.
intros.
apply AV_vers_AD; auto.
apply alignement_et_angles; auto.
Qed.
 
Lemma angles_droites_colinearite :
 forall (A B C D E F G I : PO) (k1 k2 : R),
 A <> B :>PO ->
 C <> D :>PO ->
 E <> F :>PO ->
 G <> I :>PO ->
 vec E F = mult_PP k1 (vec A B) :>PP ->
 vec G I = mult_PP k2 (vec C D) :>PP ->
 cons_AD (droite A B) (droite C D) = cons_AD (droite E F) (droite G I) :>AD.
intros.
apply AV_vers_AD; auto.
cut (k1 <> 0); intros.
cut (k2 <> 0).
intros H16; try assumption.
elim existence_representant_vecteur with (A := A) (B := E) (C := F).
intros J H6; try assumption.
elim existence_representant_vecteur with (A := C) (B := G) (C := I).
intros K H7; try assumption.
rewrite <- H6 in H3.
rewrite <- H7 in H4.
cut (alignes A B J); intros.
cut (A <> J); intros.
cut (alignes C D K); intros.
cut (C <> K); intros.
rewrite (alignement_et_angles (A:=A) (B:=B) (C:=J) (D:=C) (E:=D) (F:=K));
 auto.
rewrite H6; rewrite H7; auto.
apply distinct_produit_vecteur with (3 := H4); auto.
apply colineaire_alignes with (1 := H4); auto.
apply distinct_produit_vecteur with (3 := H3); auto.
apply colineaire_alignes with (1 := H3); auto.
red in |- *; intros; apply H2.
apply conversion_PP with (a := 1) (b := 1); auto; try discrR.
unfold vec in H4.
RingPP2 H4.
rewrite H6.
RingPP.
red in |- *; intros; apply H1.
unfold vec in H3.
apply conversion_PP with (a := 1) (b := 1); auto; try discrR.
RingPP2 H3.
rewrite H5.
RingPP.
Qed.
 
Lemma angles_et_colinearite :
 forall (A B C D E F G I : PO) (k1 k2 : R),
 A <> B :>PO ->
 C <> D :>PO ->
 E <> F :>PO ->
 G <> I :>PO ->
 vec E F = mult_PP k1 (vec A B) :>PP ->
 vec G I = mult_PP k2 (vec C D) :>PP ->
 double_AV (cons_AV (vec A B) (vec C D)) =
 double_AV (cons_AV (vec E F) (vec G I)) :>AV.
intros A B C D E F G I k1 k2 H H0 H1 H2 H3 H4; try assumption.
cut (k1 <> 0); intros.
cut (k2 <> 0).
intros H16; try assumption.
elim existence_representant_vecteur with (A := A) (B := E) (C := F).
intros J H6; try assumption.
elim existence_representant_vecteur with (A := C) (B := G) (C := I).
intros K H7; try assumption.
rewrite <- H6 in H3.
rewrite <- H7 in H4.
cut (alignes A B J); intros.
cut (A <> J); intros.
cut (alignes C D K); intros.
cut (C <> K); intros.
rewrite (alignement_et_angles (A:=A) (B:=B) (C:=J) (D:=C) (E:=D) (F:=K));
 auto.
rewrite H6; rewrite H7; auto.
apply distinct_produit_vecteur with (3 := H4); auto.
apply colineaire_alignes with (1 := H4); auto.
apply distinct_produit_vecteur with (3 := H3); auto.
apply colineaire_alignes with (1 := H3); auto.
red in |- *; intros; apply H2.
apply conversion_PP with (a := 1) (b := 1); auto; try discrR.
unfold vec in H4.
RingPP2 H4.
rewrite H6.
RingPP.
red in |- *; intros; apply H1.
unfold vec in H3.
apply conversion_PP with (a := 1) (b := 1); auto; try discrR.
RingPP2 H3.
rewrite H5.
RingPP.
Qed.
 
Lemma angles_et_paralleles :
 forall A B C D E F G I : PO,
 A <> B :>PO ->
 C <> D :>PO ->
 E <> F :>PO ->
 G <> I :>PO ->
 paralleles (droite E F) (droite A B) ->
 paralleles (droite G I) (droite C D) ->
 double_AV (cons_AV (vec A B) (vec C D)) =
 double_AV (cons_AV (vec E F) (vec G I)) :>AV.
intros A B C D E F G I H H0 H1 H2 H3 H4; try assumption.
elim (paralleles_vecteur (A:=E) (B:=F) (C:=A) (D:=B)); auto.
intros x H5; try assumption.
elim (paralleles_vecteur (A:=G) (B:=I) (C:=C) (D:=D)); auto.
intros x0 H6; try assumption.
apply angles_et_colinearite with (k1 := x) (k2 := x0); auto.
Qed.
 
Lemma angles_droites_paralleles :
 forall A B C D E F G I : PO,
 A <> B :>PO ->
 C <> D :>PO ->
 E <> F :>PO ->
 G <> I :>PO ->
 paralleles (droite E F) (droite A B) ->
 paralleles (droite G I) (droite C D) ->
 cons_AD (droite A B) (droite C D) = cons_AD (droite E F) (droite G I) :>AD.
intros A B C D E F G I H H0 H1 H2 H3 H4; try assumption.
elim (paralleles_vecteur (A:=E) (B:=F) (C:=A) (D:=B)); auto.
intros x H5; try assumption.
elim (paralleles_vecteur (A:=G) (B:=I) (C:=C) (D:=D)); auto.
intros x0 H6; try assumption.
apply angles_droites_colinearite with (k1 := x) (k2 := x0); auto.
Qed.
 
Lemma angle_non_paralleles :
 forall A B C D : PO,
 A <> B :>PO ->
 C <> D :>PO ->
 double_AV (cons_AV (vec A B) (vec C D)) <> image_angle 0 :>AV ->
 ~ paralleles (droite C D) (droite A B).
intros; red in |- *; intros.
apply H1; apply angle_droites_paralleles; auto.
Qed.
 
Axiom
  droites_paralleles_angle :
    forall A B C D : PO,
    A <> B :>PO ->
    C <> D :>PO ->
    double_AV (cons_AV (vec A B) (vec C D)) = image_angle 0 ->
    paralleles (droite A B) (droite C D).
 
Lemma existence_orthogonal :
 forall A B : PO,
 A <> B :>PO ->
 ex (fun C : PO => A <> C :>PO /\ orthogonal (vec A B) (vec A C)).
intros.
elim existence_representant_unitaire with (A := A) (B := B);
 [ intros D H0; try clear existence_representant_unitaire; try exact H0
 | auto ].
elim
 existence_representant_angle
  with (A := A) (B := D) (C := A) (x := pisurdeux);
 [ intros C H2; elim H2; intros H3 H4; try clear H2; try exact H4 | auto ].
exists C.
split; [ auto with geo | idtac ].
apply pisurdeux_droit.
rewrite angles_representants_unitaires; auto with geo.
replace (representant_unitaire (vec A C)) with (vec A C); auto with geo.
rewrite <- H0; auto.
elim def_representant_unitaire2 with (A := A) (B := B) (C := D); auto; intros.
elim H2; intros; auto with geo.
Qed.
Comments "," "soit_orthogonal" "cree" "un" "vecteur" "AC" "orthogonal" "a"
  "AB" "et" "echoue" "si" "A=B".
 
Ltac soit_orthogonal A B C :=
  elim (existence_orthogonal (A:=A) (B:=B));
   [ intros C toto; elim toto; clear toto; intros | auto ].
 
Lemma orthogonal_angles :
 forall A B C D : PO,
 A <> B :>PO ->
 C <> D :>PO ->
 orthogonal (vec A B) (vec C D) ->
 double_AV (cons_AV (vec A B) (vec C D)) = image_angle pi.
intros.
elim existence_representant_unitaire with (A := A) (B := B);
 [ intros E H2; try clear existence_representant_unitaire; try exact H2
 | auto ].
elim
 existence_representant_angle
  with (A := A) (B := E) (C := A) (x := pisurdeux);
 [ intros F H5; elim H5; intros H3 H4; try clear H5; try exact H4 | auto ].
cut (orthogonal (vec A B) (vec A F)); intros.
elim (orthogonal_paralleles (A:=A) (B:=B) (C:=F) (E:=C) (F:=D));
 auto with geo; intros.
cut (x <> 0); intros.
rewrite
 (angles_et_colinearite (A:=A) (B:=B) (C:=C) (D:=D) (E:=A) (F:=B) (G:=A)
    (I:=F) (k1:=1) (k2:=/ x)); auto with geo.
rewrite angles_representants_unitaires; auto with geo.
replace (representant_unitaire (vec A F)) with (vec A F); auto with geo.
rewrite <- H2; auto.
unfold double_AV in |- *; rewrite <- H4.
rewrite <- add_mes_compatible; (unfold pi in |- *; auto with geo).
Ringvec.
rewrite H6.
Fieldvec x.
red in |- *; intros; apply H0.
apply (produit_zero_conf H6); auto.
apply pisurdeux_droit.
rewrite angles_representants_unitaires; auto with geo.
replace (representant_unitaire (vec A F)) with (vec A F); auto with geo.
rewrite <- H2; auto.
apply carre_scalaire_1_distance; auto.
elim def_representant_unitaire2 with (A := A) (B := B) (C := E); auto; intros.
elim H4; auto.
Qed.
 
Lemma angles_orthogonal :
 forall A B C D : PO,
 A <> B :>PO ->
 C <> D :>PO ->
 double_AV (cons_AV (vec A B) (vec C D)) = image_angle pi :>AV ->
 orthogonal (vec A B) (vec C D).
intros.
soit_orthogonal A B ipattern:E.
apply ortho_sym.
apply paralleles_orthogonal with (A := A) (B := E); auto with geo.
apply droites_paralleles_angle; auto.
replace (double_AV (cons_AV (vec A E) (vec C D))) with
 (plus (double_AV (cons_AV (vec A E) (vec A B)))
    (double_AV (cons_AV (vec A B) (vec C D)))); auto.
cut (double_AV (cons_AV (vec A E) (vec A B)) = image_angle pi); intros.
rewrite H1; rewrite H4; rewrite <- add_mes_compatible; rewrite <- pi_plus_pi;
 (unfold deuxpi in |- *; auto).
apply orthogonal_angles; auto with geo.
rewrite double_Chasles; auto with geo.
Qed.
 
Lemma angles_droites_orthogonales :
 forall A B C D E F G I : PO,
 A <> B :>PO ->
 C <> D :>PO ->
 E <> F :>PO ->
 G <> I :>PO ->
 orthogonal (vec A B) (vec E F) ->
 orthogonal (vec C D) (vec G I) ->
 double_AV (cons_AV (vec E F) (vec G I)) =
 double_AV (cons_AV (vec A B) (vec C D)).
unfold double_AV in |- *; intros.
replace (cons_AV (vec A B) (vec C D)) with
 (plus (plus (cons_AV (vec A B) (vec E F)) (cons_AV (vec E F) (vec G I)))
    (cons_AV (vec G I) (vec C D))).
mesure E F G I.
mesure A B E F.
mesure G I C D.
replace (x0 + x + x1 + (x0 + x + x1)) with (x + x + (x0 + x0) + (x1 + x1)).
symmetry  in |- *.
rewrite add_mes_compatible.
rewrite add_mes_compatible.
replace (image_angle (x0 + x0)) with (image_angle pi).
replace (image_angle (x1 + x1)) with (image_angle pi).
repeat rewrite <- add_mes_compatible.
replace (x + x + pi + pi) with (x + x + deuxpi).
rewrite add_mes_compatible; rewrite pi_plus_pi; rewrite <- add_mes_compatible.
replace (x + x + 0) with (x + x); auto.
ring.
unfold deuxpi in |- *; ring.
rewrite add_mes_compatible; rewrite H7.
replace (plus (cons_AV (vec G I) (vec C D)) (cons_AV (vec G I) (vec C D)))
 with (double_AV (cons_AV (vec G I) (vec C D))); auto.
rewrite orthogonal_angles; auto with geo.
rewrite add_mes_compatible; rewrite H6.
replace (plus (cons_AV (vec A B) (vec E F)) (cons_AV (vec A B) (vec E F)))
 with (double_AV (cons_AV (vec A B) (vec E F))); auto.
rewrite orthogonal_angles; auto with geo.
ring.
rewrite Chasles; auto.
rewrite Chasles; auto.
Qed.
 
Lemma angles_droites_droites_orthogonales :
 forall A B C D E F G I : PO,
 A <> B :>PO ->
 C <> D :>PO ->
 E <> F :>PO ->
 G <> I :>PO ->
 orthogonal (vec A B) (vec E F) ->
 orthogonal (vec C D) (vec G I) ->
 cons_AD (droite E F) (droite G I) = cons_AD (droite A B) (droite C D).
intros.
apply AV_vers_AD; auto.
apply angles_droites_orthogonales; auto.
Qed.
 
Lemma alignes_angle :
 forall A B C : PO,
 A <> B :>PO ->
 A <> C :>PO ->
 double_AV (cons_AV (vec A B) (vec A C)) = image_angle 0 -> alignes A B C.
intros.
cut (paralleles (droite A B) (droite A C)); intros.
elim (paralleles_vecteur (A:=A) (B:=B) (C:=A) (D:=C)); auto; intros.
lapply (colineaire_alignes (k:=x) (A:=A) (B:=C) (C:=B)); auto with geo.
apply droites_paralleles_angle; auto.
Qed.
Hint Resolve alignes_angle: geo.
 
Lemma non_alignes_angle :
 forall A B C : PO,
 A <> B :>PO ->
 A <> C :>PO ->
 ~ alignes A B C ->
 double_AV (cons_AV (vec A B) (vec A C)) <> image_angle 0 :>AV.
red in |- *; intros.
apply H1.
apply alignes_angle; auto with geo.
Qed.
 
Lemma angle_non_alignes :
 forall A B C : PO,
 A <> B :>PO ->
 A <> C :>PO ->
 double_AV (cons_AV (vec A B) (vec A C)) <> image_angle 0 :>AV ->
 ~ alignes A B C.
intros.
cut (~ paralleles (droite A C) (droite A B)); intros.
red in |- *; intros; apply H2.
apply paralleles_sym; auto.
apply alignes_paralleles; auto.
apply angle_non_paralleles; auto.
Qed.
 
Lemma alignement_triangle :
 forall A B C D E : PO,
 A <> D :>PO ->
 A <> E :>PO ->
 triangle A B C -> alignes A B D -> alignes A C E -> triangle A D E.
intros.
deroule_triangle A B C.
apply angle_non_alignes; auto with geo.
rewrite <- (alignement_et_angles (A:=A) (B:=B) (C:=D) (D:=A) (E:=C) (F:=E));
 auto with geo.
Qed.

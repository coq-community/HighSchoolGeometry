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


Require Export repere_ortho_plan.
Set Implicit Arguments.
Unset Strict Implicit.
Parameter AV : Type.
Parameter cons_AV : PP -> PP -> AV.
Parameter plus : AV -> AV -> AV.
Parameter opp : AV -> AV.
 
Axiom
  existence_AB_unitaire : exists A : PO, (exists B : PO, distance A B = 1).
(* Tout angle a un représentant non unique parmi les angles orientés de vecteurs unitaires*)
 
Axiom
  existence_representant_cons :
    forall (a : AV) (A B C : PO),
    distance A B = 1 ->
    exists D : PO, distance C D = 1 /\ a = cons_AV (vec A B) (vec C D).
(* Tout angle orienté de vecteurs non nuls est égal à l'angle orienté des vecteurs unitaires correspondants*)
 
Axiom
  angles_representants_unitaires :
    forall A B C D E F : PO,
    A <> B ->
    C <> D ->
    cons_AV (vec A B) (vec C D) =
    cons_AV (representant_unitaire (vec A B))
      (representant_unitaire (vec C D)).
 
Axiom
  Chasles :
    forall A B C D E F : PO,
    A <> B ->
    C <> D ->
    E <> F ->
    plus (cons_AV (vec A B) (vec C D)) (cons_AV (vec C D) (vec E F)) =
    cons_AV (vec A B) (vec E F).
 
Axiom
  def_opp :
    forall A B C D : PO,
    A <> B ->
    C <> D -> opp (cons_AV (vec A B) (vec C D)) = cons_AV (vec C D) (vec A B).
Parameter AV0 : AV.
(* Enroulement de R sur le cercle trigonométrique*)
Parameter image_angle : R -> AV.
 
Axiom AV0_zero : AV0 = image_angle 0.
 
Axiom
  unicite_representant_angle_nul :
    forall A B C : PO,
    distance A B = 1 ->
    distance A C = 1 -> cons_AV (vec A B) (vec A C) = image_angle 0 -> C = B.
 
Axiom
  tout_angle_a_une_mesure :
    forall A B C D : PO,
    A <> B :>PO ->
    C <> D :>PO ->
    exists x : R, image_angle x = cons_AV (vec A B) (vec C D) :>AV.
(* Compatibilité des opérations *)
 
Axiom
  add_mes_compatible :
    forall x y : R,
    image_angle (x + y) = plus (image_angle x) (image_angle y).
 
Axiom mes_opp : forall x : R, image_angle (- x) = opp (image_angle x).
(* Cas particuliers : angles plats et angles droits*)
Parameter pisurdeux : R.
 
Definition pi := pisurdeux + pisurdeux.
 
Definition deuxpi := pi + pi.
 
Axiom
  angle_plat :
    forall A B : PO, A <> B -> image_angle pi = cons_AV (vec A B) (vec B A).
 
Axiom
  pisurdeux_droit :
    forall A B C : PO,
    image_angle pisurdeux = cons_AV (vec A B) (vec A C) ->
    orthogonal (vec A B) (vec A C).
 
Axiom
  droit_direct_ou_indirect :
    forall A B C : PO,
    A <> B ->
    A <> C ->
    orthogonal (vec A B) (vec A C) ->
    image_angle pisurdeux = cons_AV (vec A B) (vec A C) \/
    image_angle (- pisurdeux) = cons_AV (vec A B) (vec A C).
 
Lemma existence_representant_angle :
 forall (A B C : PO) (x : R),
 distance A B = 1 ->
 exists D : PO,
   distance C D = 1 /\ image_angle x = cons_AV (vec A B) (vec C D).
intros.
apply existence_representant_cons; auto.
Qed.
 
Lemma tout_angle_mesure : forall a : AV, exists x : R, a = image_angle x :>AV.
intros.
elim existence_AB_unitaire;
 [ intros A H; elim H;
    [ intros B H0; try clear H existence_AB_unitaire; try exact H0 ] ].
elim existence_representant_cons with (a := a) (A := A) (B := B) (C := A);
 [ intros D H1; elim H1;
    [ intros H2 H3; try clear H1 existence_representant_cons; try exact H3 ]
 | auto ].
elim (tout_angle_a_une_mesure (A:=A) (B:=B) (C:=A) (D:=D)); auto with geo;
 intros.
exists x.
rewrite H4; auto.
Qed.
Hint Resolve mes_opp add_mes_compatible: geo.
 
Ltac mes a :=
  elim (tout_angle_mesure a); intros;
   match goal with
   | h:(a = image_angle ?X1) |- _ =>
       try rewrite h; repeat rewrite <- mes_opp;
        repeat rewrite <- add_mes_compatible; repeat rewrite <- mes_opp
   end.
Hint Resolve def_opp Chasles angles_representants_unitaires: geo.
 
Ltac mesure A B C D :=
  elim (tout_angle_a_une_mesure (A:=A) (B:=B) (C:=C) (D:=D)); auto with geo;
   intros;
   match goal with
   | h:(image_angle ?X1 = cons_AV (vec A B) (vec C D)) |- _ =>
       try rewrite <- h; repeat rewrite <- mes_opp;
        repeat rewrite <- add_mes_compatible; repeat rewrite <- mes_opp
   end.
 
Lemma plus_commutative : forall a b : AV, plus a b = plus b a :>AV.
intros.
mes a.
mes b.
repeat rewrite <- add_mes_compatible.
replace (x + x0) with (x0 + x); [ auto | ring ].
Qed.
 
Lemma plus_angle_zero : forall a : AV, plus a (image_angle 0) = a.
intros.
mes a.
replace (x + 0) with x; [ auto | ring ].
Qed.
 
Lemma plus_associative :
 forall a b c : AV, plus a (plus b c) = plus (plus a b) c :>AV.
intros.
mes a.
mes b.
mes c.
replace (x + (x0 + x1)) with (x + x0 + x1); [ auto | ring ].
Qed.
Hint Resolve plus_angle_zero: geo.
 
Lemma opp_angle :
 forall a b : AV, plus a b = image_angle 0 :>AV -> b = opp a :>AV.
intros.
mes a.
mes b.
replace (image_angle (- x)) with (plus (image_angle (- x)) (image_angle 0));
 auto with geo.
rewrite <- H.
rewrite H1; rewrite H0.
repeat rewrite <- add_mes_compatible.
pattern x0 at 1 in |- *.
replace x0 with (- x + (x + x0)); auto.
ring.
Qed.
 
Lemma plus_angle_oppose : forall a : AV, plus a (opp a) = image_angle 0.
intros.
mes a.
replace (x + - x) with 0; [ auto | ring ].
Qed.
 
Lemma mes_oppx :
 forall (A B C D : PO) (x : R),
 A <> B ->
 C <> D ->
 image_angle x = cons_AV (vec A B) (vec C D) ->
 image_angle (- x) = cons_AV (vec C D) (vec A B).
intros.
rewrite <- def_opp; auto.
rewrite <- H1; rewrite <- mes_opp; auto with geo.
Qed.
 
Lemma mes_opp_opp :
 forall (A B C D E F G I : PO) (a b : R),
 A <> B ->
 C <> D ->
 E <> F ->
 G <> I ->
 image_angle a = cons_AV (vec A B) (vec C D) ->
 image_angle b = cons_AV (vec E F) (vec G I) ->
 image_angle b = image_angle (- a) ->
 cons_AV (vec E F) (vec G I) = opp (cons_AV (vec A B) (vec C D)).
intros A B C D E F G I a b H H0 H1 H2 H3 H4 H5; try assumption.
rewrite <- H4; rewrite def_opp; auto.
rewrite <- (mes_oppx (A:=A) (B:=B) (C:=C) (D:=D) (x:=a)); auto.
Qed.
 
Lemma permute_angles :
 forall A B C D E F G I : PO,
 A <> B :>PO ->
 C <> D :>PO ->
 E <> F :>PO ->
 G <> I :>PO ->
 cons_AV (vec A B) (vec C D) = cons_AV (vec E F) (vec G I) :>AV ->
 cons_AV (vec C D) (vec A B) = cons_AV (vec G I) (vec E F) :>AV.
intros A B C D E F G I H H0 H1 H2 H3; try assumption.
rewrite <- def_opp; auto.
rewrite <- (def_opp (A:=E) (B:=F) (C:=G) (D:=I)); auto.
rewrite <- H3; auto.
Qed.
Hint Resolve permute_angles: geo.
 
Lemma opp_plus_plus_opp :
 forall A B C D E F G I : PO,
 A <> B :>PO ->
 C <> D :>PO ->
 E <> F :>PO ->
 G <> I :>PO ->
 opp (plus (cons_AV (vec A B) (vec C D)) (cons_AV (vec E F) (vec G I))) =
 plus (opp (cons_AV (vec A B) (vec C D))) (opp (cons_AV (vec E F) (vec G I)))
 :>AV.
intros A B C D E F G I H H0 H1 H2; try assumption.
mesure A B C D.
mesure E F G I.
replace (- (x + x0)) with (- x + - x0); auto.
ring.
Qed.
Hint Resolve opp_plus_plus_opp: geo.
 
Lemma Chasles_diff :
 forall A B C D E F : PO,
 A <> B :>PO ->
 C <> D :>PO ->
 E <> F :>PO ->
 plus (cons_AV (vec A B) (vec C D)) (opp (cons_AV (vec A B) (vec E F))) =
 cons_AV (vec E F) (vec C D) :>AV.
intros.
rewrite def_opp; auto.
rewrite plus_commutative; auto with geo.
Qed.
Hint Resolve pisurdeux_droit: geo.
 
Lemma pisurdeux_scalaire_nul :
 forall A B C : PO,
 image_angle pisurdeux = cons_AV (vec A B) (vec A C) ->
 scalaire (vec A B) (vec A C) = 0.
intros.
apply def_orthogonal.
apply pisurdeux_droit; auto.
Qed.
Hint Resolve pisurdeux_scalaire_nul: geo.
 
Lemma orthogonal_pisurdeux_or :
 forall A B C D : PO,
 A <> B ->
 C <> D ->
 orthogonal (vec A B) (vec C D) ->
 image_angle pisurdeux = cons_AV (vec A B) (vec C D) \/
 image_angle (- pisurdeux) = cons_AV (vec A B) (vec C D).
intros A B C D H H0; try assumption.
elim existence_representant_vecteur with (A := A) (B := C) (C := D);
 [ intros E H2; rewrite <- H2; intros ].
apply droit_direct_ou_indirect; auto.
apply distinct_egalite_vecteur with (2 := H2); auto.
Qed.
 
Lemma angle_nul :
 forall A B : PO, A <> B -> image_angle 0 = cons_AV (vec A B) (vec A B).
intros.
elim existence_representant_unitaire with (A := A) (B := B);
 [ intros C H0; try clear existence_representant_unitaire; try exact H0
 | auto ].
rewrite angles_representants_unitaires; auto.
rewrite <- H0.
cut (A <> C); intros.
cut (image_angle (- pi) = cons_AV (vec C A) (vec A C)); intros.
replace 0 with (pi + - pi).
rewrite add_mes_compatible; rewrite H2; rewrite (angle_plat (A:=A) (B:=C));
 auto.
rewrite Chasles; auto.
ring.
apply mes_oppx; auto.
rewrite (angle_plat (A:=A) (B:=C)); auto.
elim (def_representant_unitaire2 (A:=A) (B:=B) (C:=C)); auto; intros.
elim H2; auto with geo.
Qed.
 
Lemma pi_plus_pi : image_angle deuxpi = image_angle 0.
unfold deuxpi in |- *; intros.
elim existence_AB_unitaire; intros A H; elim H; intros B H0; try clear H;
 try exact H0.
cut (A <> B); intros.
rewrite add_mes_compatible.
pattern (image_angle pi) at 1 in |- *.
rewrite (angle_plat (A:=A) (B:=B)); auto.
rewrite (angle_plat (A:=B) (B:=A)); auto.
rewrite Chasles; auto.
rewrite <- angle_nul; auto.
auto with geo.
Qed.
 
Lemma mesure_mod_deuxpi :
 forall (x : R) (A B C D : PO),
 A <> B ->
 C <> D ->
 image_angle x = cons_AV (vec A B) (vec C D) ->
 image_angle (x + deuxpi) = cons_AV (vec A B) (vec C D).
intros.
rewrite add_mes_compatible.
rewrite pi_plus_pi.
rewrite H1.
rewrite (angle_nul (A:=C) (B:=D)); auto.
apply Chasles; auto.
Qed.
 
Lemma angle_oppu_oppv :
 forall A B C D : PO,
 A <> B :>PO ->
 C <> D :>PO ->
 cons_AV (vec B A) (vec D C) = cons_AV (vec A B) (vec C D) :>AV.
intros.
replace (cons_AV (vec B A) (vec D C)) with
 (plus (cons_AV (vec B A) (vec A B))
    (plus (cons_AV (vec A B) (vec C D)) (cons_AV (vec C D) (vec D C)))).
rewrite <- angle_plat; auto.
rewrite <- angle_plat; auto.
mesure A B C D.
replace (pi + (x + pi)) with (x + deuxpi); try ring; auto.
rewrite (mesure_mod_deuxpi (x:=x) (A:=A) (B:=B) (C:=C) (D:=D)); auto.
unfold deuxpi in |- *; ring.
repeat rewrite Chasles; auto.
Qed.
Hint Resolve angle_oppu_oppv: geo.
 
Theorem somme_triangle :
 forall A B C : PO,
 A <> B :>PO ->
 A <> C :>PO ->
 B <> C :>PO ->
 plus (cons_AV (vec A B) (vec A C))
   (plus (cons_AV (vec B C) (vec B A)) (cons_AV (vec C A) (vec C B))) =
 image_angle pi :>AV.
intros A B C H H0 H1; try assumption.
rewrite <- (angle_oppu_oppv (A:=C) (B:=A) (C:=C) (D:=B)); auto.
mesure A B A C.
mesure B C B A.
mesure A C B C.
replace (x + (x0 + x1)) with (x + x1 + x0).
repeat rewrite add_mes_compatible.
rewrite H4; rewrite H3; rewrite H2; repeat rewrite Chasles; auto.
rewrite <- angle_plat; auto.
ring.
Qed.
 
Lemma angle_triangle :
 forall A B C : PO,
 A <> B ->
 A <> C ->
 B <> C ->
 plus (image_angle pi)
   (opp (plus (cons_AV (vec A B) (vec A C)) (cons_AV (vec B C) (vec B A)))) =
 cons_AV (vec C A) (vec C B).
intros.
rewrite <- (somme_triangle (A:=A) (B:=B) (C:=C)); auto.
rewrite opp_plus_plus_opp; auto.
mesure B C B A.
mesure C A C B.
mesure A B A C.
replace (x1 + (x + x0) + (- x1 + - x)) with x0; auto.
ring.
Qed.
Hint Resolve angle_triangle: geo.
 
Lemma angles_complementaires_triangle_rectangle :
 forall (A B C : PO) (a : R),
 A <> B ->
 A <> C ->
 B <> C ->
 orthogonal (vec B A) (vec B C) ->
 image_angle a = cons_AV (vec A B) (vec A C) ->
 image_angle (pisurdeux + - a) = cons_AV (vec C A) (vec C B) \/
 image_angle (- pisurdeux + - a) = cons_AV (vec C A) (vec C B).
intros.
generalize (somme_triangle (A:=A) (B:=B) (C:=C)); intros.
replace (cons_AV (vec C A) (vec C B)) with
 (plus (image_angle pi)
    (opp (plus (cons_AV (vec A B) (vec A C)) (cons_AV (vec B C) (vec B A)))));
 auto with geo.
rewrite opp_plus_plus_opp; auto.
rewrite <- H3.
elim orthogonal_pisurdeux_or with (A := B) (B := C) (C := B) (D := A);
 [ intros H10; try clear orthogonal_pisurdeux_or
 | intros H10; try clear orthogonal_pisurdeux_or
 | auto
 | auto
 | auto with geo ].
rewrite <- H10.
repeat rewrite <- mes_opp.
repeat rewrite <- add_mes_compatible.
left; try assumption.
replace (pisurdeux + - a) with (pi + (- a + - pisurdeux)); auto.
unfold pi in |- *; ring.
rewrite <- H10.
repeat rewrite <- mes_opp.
repeat rewrite <- add_mes_compatible.
right; try assumption.
rewrite <- (plus_angle_zero (image_angle (- pisurdeux + - a))).
rewrite <- pi_plus_pi.
repeat rewrite <- add_mes_compatible.
replace (- pisurdeux + - a + deuxpi) with (pi + (- a + - - pisurdeux)); auto.
unfold deuxpi, pi in |- *; ring.
Qed.
 
Lemma angle_produit_positif_r :
 forall (k : R) (A B C D E : PO),
 A <> B :>PO ->
 D <> E :>PO ->
 k > 0 ->
 vec A C = mult_PP k (vec A B) :>PP ->
 cons_AV (vec D E) (vec A C) = cons_AV (vec D E) (vec A B).
intros.
cut (A <> C); intros.
2: apply distinct_produit_vecteur with (3 := H2); auto.
rewrite angles_representants_unitaires; auto.
rewrite angles_representants_unitaires; auto.
rewrite (produit_positif_representant_unitaire (k:=k) (A:=A) (B:=B) (C:=C));
 auto.
auto with real.
Qed.
Hint Resolve angles_representants_unitaires: geo.
 
Lemma angle_produit_negatif_r :
 forall (k : R) (A B C D E : PO),
 A <> B ->
 D <> E ->
 k < 0 ->
 vec A C = mult_PP k (vec A B) ->
 cons_AV (vec D E) (vec A C) =
 plus (cons_AV (vec D E) (vec A B)) (image_angle pi).
intros.
cut (A <> C); intros.
2: apply distinct_produit_vecteur with (3 := H2); auto.
rewrite angles_representants_unitaires; auto.
rewrite angles_representants_unitaires; auto.
rewrite (produit_negatif_representant_unitaire (k:=k) (A:=A) (B:=B) (C:=C));
 auto.
elim existence_representant_unitaire with (A := A) (B := B);
 [ intros B' H4 | auto ].
rewrite <- H4.
elim def_representant_unitaire2 with (A := A) (B := B) (C := B');
 [ intros; elim H6; intros H7 H8; try clear H6; try exact H7 | auto | auto ].
cut (A <> B'); intros; auto with geo.
replace (mult_PP (-1) (vec A B')) with (vec B' A); [ idtac | Ringvec ].
rewrite (angle_plat (A:=A) (B:=B')); auto.
elim existence_representant_unitaire with (A := D) (B := E);
 [ intros F H9 | auto ].
elim def_representant_unitaire2 with (A := D) (B := E) (C := F);
 [ intros; elim H11; intros H12 H13; try clear H11; try exact H12
 | auto
 | auto ].
cut (D <> F); intros; auto with geo.
rewrite <- H9; rewrite Chasles; auto.
auto with real.
Qed.
 
Lemma angle_produit_negatif_r2 :
 forall (k : R) (A B C D : PO),
 A <> B ->
 C <> D ->
 k < 0 ->
 cons_AV (vec C D) (mult_PP k (vec A B)) =
 plus (cons_AV (vec C D) (vec A B)) (image_angle pi).
intros.
elim
 existence_representant_mult_vecteur with (A := A) (B := A) (C := B) (k := k);
 intros E H2; try clear existence_representant_mult_vecteur; 
 rewrite <- H2.
rewrite (angle_produit_negatif_r (k:=k) (A:=A) (B:=B) (C:=E) (D:=C) (E:=D));
 auto.
Qed.
 
Lemma angle_produit_negatif_l :
 forall (k : R) (A B C D : PO),
 A <> B ->
 C <> D ->
 k < 0 ->
 cons_AV (mult_PP k (vec A B)) (vec C D) =
 plus (cons_AV (vec A B) (vec C D)) (image_angle pi).
intros.
elim
 existence_representant_mult_vecteur with (A := A) (B := A) (C := B) (k := k);
 intros E H2; try clear existence_representant_mult_vecteur; 
 rewrite <- H2.
cut (A <> E); intros.
cut
 (cons_AV (vec C D) (vec A E) =
  plus (cons_AV (vec C D) (vec A B)) (image_angle pi)); 
 intros.
2: rewrite
    (angle_produit_negatif_r (k:=k) (A:=A) (B:=B) (C:=E) (D:=C) (E:=D))
    ; auto.
rewrite (angle_plat (A:=C) (B:=D)); auto.
rewrite Chasles; auto.
apply permute_angles; auto.
rewrite H4.
rewrite (angle_plat (A:=D) (B:=C)); auto.
rewrite plus_commutative; rewrite Chasles; auto.
apply distinct_produit_vecteur with (3 := H2); auto with real.
Qed.
 
Lemma angle_produit_positif_r2 :
 forall (k : R) (A B C D : PO),
 A <> B ->
 C <> D ->
 k > 0 ->
 cons_AV (vec C D) (mult_PP k (vec A B)) = cons_AV (vec C D) (vec A B).
intros.
elim
 existence_representant_mult_vecteur with (A := A) (B := A) (C := B) (k := k);
 intros E H2; try clear existence_representant_mult_vecteur; 
 rewrite <- H2.
rewrite (angle_produit_positif_r (k:=k) (A:=A) (B:=B) (C:=E) (D:=C) (E:=D));
 auto.
Qed.
 
Lemma angle_produit_positif_l :
 forall (k : R) (A B C D : PO),
 A <> B ->
 C <> D ->
 k > 0 ->
 cons_AV (mult_PP k (vec A B)) (vec C D) = cons_AV (vec A B) (vec C D).
intros.
elim
 existence_representant_mult_vecteur with (A := A) (B := A) (C := B) (k := k);
 intros E H2; try clear existence_representant_mult_vecteur; 
 rewrite <- H2.
cut (A <> E); intros.
cut (cons_AV (vec C D) (vec A E) = cons_AV (vec C D) (vec A B)); intros.
2: rewrite
    (angle_produit_positif_r (k:=k) (A:=A) (B:=B) (C:=E) (D:=C) (E:=D))
    ; auto.
apply permute_angles; auto.
apply distinct_produit_vecteur with (3 := H2); auto with real.
Qed.
 
Lemma angle_nul_positif_colineaire :
 forall A B C : PO,
 A <> B ->
 A <> C ->
 cons_AV (vec A B) (vec A C) = image_angle 0 ->
 exists k : R, k > 0 /\ vec A C = mult_PP k (vec A B).
intros A B C H H0; try assumption.
cut
 (cons_AV (vec A B) (vec A C) =
  cons_AV (representant_unitaire (vec A B)) (representant_unitaire (vec A C)));
 auto with geo.
elim existence_representant_unitaire with (A := A) (B := B);
 [ intros B' H3; try clear existence_representant_unitaire; rewrite <- H3
 | auto ].
elim existence_representant_unitaire with (A := A) (B := C);
 [ intros C' H4; rewrite <- H4 | auto ].
intros H1; rewrite H1; intros.
elim def_representant_unitaire2 with (A := A) (B := B) (C := B');
 [ intros | auto | auto ].
elim def_representant_unitaire2 with (A := A) (B := C) (C := C');
 [ intros | auto | auto ].
elim H8; intros H9 H10; try clear H8; try exact H10.
elim H6; intros H8 H11; try clear H6; try exact H11.
cut (C' = B'); intros.
2: apply unicite_representant_angle_nul with A; auto with geo.
apply egalite_representant_unitaire; auto with geo.
rewrite <- H4; rewrite <- H3; rewrite <- H6; auto.
Qed.
 
Lemma angles_milieu :
 forall A B C I : PO,
 B <> C :>PO ->
 B <> A :>PO ->
 I = milieu B C :>PO ->
 cons_AV (vec B C) (vec B A) = cons_AV (vec B I) (vec B A) :>AV.
intros.
replace (vec B C) with (mult_PP 2 (vec B I)); auto with geo.
apply angle_produit_positif_l; auto.
rewrite H1; apply milieu_distinct; auto.
fourier.
rewrite <- (milieu_vecteur_double (A:=B) (B:=C) (M:=I)); auto.
Qed.
 
Lemma angles_milieu2 :
 forall A B C I : PO,
 B <> C :>PO ->
 C <> A :>PO ->
 I = milieu B C :>PO ->
 cons_AV (vec C A) (vec C B) = cons_AV (vec C A) (vec C I) :>AV.
intros.
replace (vec C B) with (mult_PP 2 (vec C I)); auto with geo.
apply angle_produit_positif_r2; auto.
rewrite H1; apply milieu_distinct2; auto.
fourier.
rewrite <- (milieu_vecteur_double (A:=C) (B:=B) (M:=I)); auto with geo.
Qed.
 
Lemma milieu_angles :
 forall A B M N : PO,
 A <> B ->
 M <> N ->
 M = milieu A B ->
 cons_AV (vec M A) (vec M N) =
 plus (cons_AV (vec M B) (vec M N)) (image_angle pi) :>AV.
intros.
VReplace (vec M A) (mult_PP (-1) (vec A M)).
rewrite <- (milieu_vecteur H1); auto.
apply angle_produit_negatif_l; auto.
cut (B <> M); intros; auto.
rewrite H1; apply milieu_distinct; auto.
rewrite H1; apply milieu_distinct2; auto.
fourier.
Qed.
 
Axiom
  milieu_angles_orthogonaux :
    forall A B M N : PO,
    A <> B ->
    M <> N ->
    M = milieu A B ->
    orthogonal (vec A B) (vec M N) ->
    cons_AV (vec M A) (vec M N) = cons_AV (vec M N) (vec M B) :>AV.
 
Lemma alignes_distance_positif_colineaire :
 forall (k : R) (A B C : PO),
 A <> B ->
 A <> C ->
 cons_AV (vec A B) (vec A C) = image_angle 0 ->
 distance A C = k * distance A B -> vec A C = mult_PP k (vec A B).
intros.
elim angle_nul_positif_colineaire with (A := A) (B := B) (C := C);
 [ intros k0 H3; elim H3; intros H4 H5; try clear H3; try exact H5
 | auto
 | auto
 | auto ].
replace k with k0; auto.
cut (distance A C = k0 * distance A B); intros.
apply Rmult_eq_reg_l with (distance A B); auto with geo real.
replace (distance A B * k0) with (distance A C) by (rewrite H3 in |- *;  ring).
rewrite H2 in |- *;  ring.
replace k0 with (Rabs k0); auto with geo real.
apply Rabs_right; auto with real.
fourier.
Qed.
 
Lemma angle_pi_negatif_colineaire :
 forall A B C : PO,
 A <> B ->
 A <> C ->
 cons_AV (vec A B) (vec A C) = image_angle pi ->
 exists k : R, k < 0 /\ vec A C = mult_PP k (vec A B).
intros A B C H H0; try assumption.
cut
 (cons_AV (vec A B) (vec A C) =
  cons_AV (representant_unitaire (vec A B)) (representant_unitaire (vec A C)));
 auto with geo.
elim existence_representant_unitaire with (A := A) (B := B);
 [ intros B' H3; try clear existence_representant_unitaire; rewrite <- H3
 | auto ].
elim existence_representant_unitaire with (A := A) (B := C);
 [ intros C' H4; rewrite <- H4 | auto ].
intros H1; rewrite H1; intros.
elim def_representant_unitaire2 with (A := A) (B := B) (C := B');
 [ intros | auto | auto ].
elim def_representant_unitaire2 with (A := A) (B := C) (C := C');
 [ intros | auto | auto ].
elim H8; intros H9 H10; try clear H8; try exact H10.
elim H6; intros H8 H11; try clear H6; try exact H11.
cut (A <> B'); intros; auto with geo.
cut (A <> C'); intros; auto with geo.
apply oppose_representant_unitaire; auto.
rewrite <- H4; rewrite <- H3.
elim
 existence_representant_mult_vecteur
  with (A := A) (B := A) (C := B') (k := -1); intros D; 
 intros.
rewrite <- H13.
replace D with C'; auto.
cut (scalaire (vec A D) (vec A D) = 1); intros.
apply unicite_representant_angle_nul with A; auto with geo.
replace (vec A D) with (vec B' A).
replace (cons_AV (vec B' A) (vec A C')) with
 (plus (cons_AV (vec B' A) (vec A B')) (cons_AV (vec A B') (vec A C'))).
rewrite <- angle_plat; [ idtac | auto ].
rewrite H2; rewrite <- add_mes_compatible.
replace (pi + pi) with deuxpi; auto.
rewrite pi_plus_pi; auto.
rewrite Chasles; auto.
rewrite H13; Ringvec.
rewrite H13; Simplscal; auto.
Qed.
 
Lemma alignes_distance_negatif_colineaire :
 forall (k : R) (A B C : PO),
 A <> B ->
 A <> C ->
 cons_AV (vec A B) (vec A C) = image_angle pi ->
 distance A C = k * distance A B -> vec A C = mult_PP (- k) (vec A B).
intros.
elim angle_pi_negatif_colineaire with (A := A) (B := B) (C := C);
 [ intros k0 H3; elim H3; intros H4 H5; try clear H3; try exact H5
 | auto
 | auto
 | auto ].
replace k with (- k0).
replace (- - k0) with k0; try ring; auto.
cut (distance A C = - k0 * distance A B); intros; auto.
apply Rmult_eq_reg_l with (distance A B); auto with geo.
replace (distance A B * -k0) with (distance A C)
 by (rewrite H3 in |- *;  ring).
rewrite H2 in |- *;  ring.
replace (- k0) with (Rabs k0); auto with geo.
apply Rabs_left; auto with real.
Qed.
Hint Resolve plus_angle_zero: geo.

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


Require Export cocyclicite.
Set Implicit Arguments.
Unset Strict Implicit.
 
Lemma cocycliques_ordre_cycle :
 forall A B C D : PO, sont_cocycliques A B C D -> sont_cocycliques B C D A.
unfold sont_cocycliques, circonscrit, isocele in |- *; intros.
elim H; intros O; intros.
elim H0; intros.
exists O.
elim H1; intros.
elim H2; intros; clear H H0 H1 H2.
split; [ idtac | split; [ idtac | try assumption ] ].
split; [ try assumption | idtac ].
rewrite <- H5; auto.
rewrite <- H5; auto.
rewrite <- H3; auto.
rewrite <- H5; auto.
Qed.
 
Lemma cocycliques_ordre_cycle2 :
 forall A B C D : PO, sont_cocycliques A B C D -> sont_cocycliques B C A D.
unfold sont_cocycliques, circonscrit, isocele in |- *; intros.
elim H; intros O H0; elim H0; intros H1 H2; elim H2; intros H3 H4;
 try clear H2 H0 H; try exact H3.
elim H1; intros H H0; try clear H1; try exact H0.
exists O.
split; [ split; auto | idtac ].
rewrite <- H3; auto.
split; [ idtac | try assumption ].
rewrite <- H; auto.
rewrite <- H; auto.
Qed.
 
Lemma cocycliques_ordre_permute :
 forall A B C D : PO, sont_cocycliques A B C D -> sont_cocycliques A C B D.
unfold sont_cocycliques, circonscrit, isocele in |- *; intros.
elim H; intros O; intros.
elim H0; intros.
exists O.
elim H1; intros.
elim H2; intros; clear H H0 H1 H2.
split; [ idtac | split; try assumption ].
split; try assumption.
Qed.
Hint Resolve cocycliques_ordre_cycle cocycliques_ordre_cycle2
  cocycliques_ordre_permute: geo.
 
Lemma circonscrit_trans :
 forall O A B C D : PO,
 circonscrit O A B C -> circonscrit O A B D -> circonscrit O A C D.
unfold circonscrit, isocele in |- *; intros.
elim H0; clear H0; intros.
elim H; clear H; intros.
split; auto.
Qed.
 
Lemma cocyclicite2 :
 forall A B C D : PO,
 D <> C ->
 triangle A B C ->
 triangle A B D ->
 sont_cocycliques A B C D ->
 double_AV (cons_AV (vec B C) (vec B A)) =
 double_AV (cons_AV (vec D C) (vec D A)) :>AV.
intros.
deroule_triangle A B C.
deroule_triangle A B D.
elim H2.
intros O; intros.
elim H11; intros.
deroule_circonscrit A B D O.
deroule_circonscrit A B C O.
rewrite (angle_inscrit (O:=O) (A:=B) (B:=C) (C:=A)); auto.
rewrite (angle_inscrit (O:=O) (A:=D) (B:=C) (C:=A)); auto.
apply circonscrit_permute; apply circonscrit_permute.
apply circonscrit_trans with B; auto.
apply circonscrit_permute; apply circonscrit_permute; auto.
Qed.
 
Lemma cocyclicite3 :
 forall A B C D : PO,
 D <> C ->
 triangle A B C ->
 triangle A B D ->
 sont_cocycliques A B C D ->
 double_AV (cons_AV (vec B D) (vec B A)) =
 double_AV (cons_AV (vec C D) (vec C A)) :>AV.
intros.
deroule_triangle A B C.
deroule_triangle A B D.
elim H2.
intros O; intros.
elim H11; intros.
deroule_circonscrit A B D O.
deroule_circonscrit A B C O.
rewrite (angle_inscrit (O:=O) (A:=B) (B:=D) (C:=A)); auto.
rewrite (angle_inscrit (O:=O) (A:=C) (B:=D) (C:=A)); auto.
apply circonscrit_permute; apply circonscrit_permute.
apply circonscrit_trans with B; auto.
apply circonscrit_permute; apply circonscrit_permute; auto.
Qed.
 
Lemma circonscrit_ordre_permute :
 forall O A B C : PO, circonscrit O A B C -> circonscrit O B A C.
unfold circonscrit, isocele in |- *; intros.
elim H; clear H; intros.
split; auto.
rewrite <- H; auto.
Qed.
 
Lemma cocyclicite4 :
 forall A B C D : PO,
 D <> C ->
 triangle A B C ->
 triangle A B D ->
 sont_cocycliques A B C D ->
 double_AV (cons_AV (vec A B) (vec A C)) =
 double_AV (cons_AV (vec D B) (vec D C)) :>AV.
intros.
deroule_triangle A B C.
deroule_triangle A B D.
elim H2.
intros O; intros.
elim H11; intros.
deroule_circonscrit A B D O.
deroule_circonscrit A B C O.
rewrite (angle_inscrit (O:=O) (A:=A) (B:=B) (C:=C)); auto.
rewrite (angle_inscrit (O:=O) (A:=D) (B:=B) (C:=C)); auto.
apply circonscrit_permute.
apply circonscrit_trans with A; auto.
apply circonscrit_ordre_permute; auto.
apply circonscrit_ordre_permute; auto.
Qed.
 
Lemma cocyclicite5 :
 forall A B C D : PO,
 D <> C ->
 triangle A B C ->
 triangle A B D ->
 sont_cocycliques A B C D ->
 double_AV (cons_AV (vec A B) (vec A D)) =
 double_AV (cons_AV (vec C B) (vec C D)) :>AV.
intros.
deroule_triangle A B C.
deroule_triangle A B D.
elim H2.
intros O; intros.
elim H11; intros.
deroule_circonscrit A B D O.
deroule_circonscrit A B C O.
rewrite (angle_inscrit (O:=O) (A:=A) (B:=B) (C:=D)); auto.
rewrite (angle_inscrit (O:=O) (A:=C) (B:=B) (C:=D)); auto.
apply circonscrit_permute.
apply circonscrit_trans with A; auto.
apply circonscrit_ordre_permute; auto.
apply circonscrit_ordre_permute; auto.
Qed.
 
Lemma cocyclicite6 :
 forall A B C D : PO,
 triangle A B C ->
 triangle A B D ->
 sont_cocycliques A B C D ->
 double_AV (cons_AV (vec A C) (vec A D)) =
 double_AV (cons_AV (vec B C) (vec B D)) :>AV.
intros.
deroule_triangle A B C.
deroule_triangle A B D.
elim H1.
intros O; intros.
elim H10; intros.
deroule_circonscrit A B D O.
deroule_circonscrit A B C O.
rewrite (angle_inscrit (O:=O) (A:=A) (B:=C) (C:=D)); auto.
rewrite (angle_inscrit (O:=O) (A:=B) (B:=C) (C:=D)); auto.
apply circonscrit_trans with A; auto.
apply circonscrit_ordre_permute; auto.
apply circonscrit_ordre_permute; auto.
apply circonscrit_trans with B; auto.
Qed.
 
Lemma centre_circonscrit_rectangle_milieu :
 forall A B C C' O : PO,
 triangle A B C ->
 C' = milieu A B ->
 circonscrit O A B C -> orthogonal (vec C A) (vec C B) -> O = C'.
intros.
deroule_triangle A B C.
deroule_circonscrit A B C O.
rewrite H0.
cut (cons_AV (vec O A) (vec O B) = image_angle pi); intros.
cut (alignes O A B); intros.
apply alignes_mediatrice_milieu; auto with geo.
unfold mediatrice in |- *.
elim H1; auto.
apply alignes_angle; auto.
unfold double_AV in |- *.
rewrite H10.
repeat rewrite <- add_mes_compatible.
replace (pi + pi) with deuxpi; auto.
rewrite pi_plus_pi; auto.
rewrite <- (angle_inscrit (O:=O) (A:=C) (B:=A) (C:=B)); auto.
apply orthogonal_angles; auto.
apply circonscrit_permute; auto.
Qed.
 
Lemma orthogonal_diametre_cercle :
 forall A B C A' O D : PO,
 triangle A B C ->
 circonscrit O A B C ->
 O = milieu A A' ->
 orthogonal (vec D A) (vec D A') -> sont_cocycliques A B C D.
intros.
discrimine D A.
discrimine D A'.
generalize H0; unfold sont_cocycliques, circonscrit, isocele in |- *; intros.
exists O.
split; [ try assumption | idtac ].
elim H5; intros H6 H7; try clear H5; try exact H6.
split; [ try assumption | idtac ].
apply milieu_distance; auto.
cut (circonscrit O A A' D); intros.
generalize H0; generalize H5.
unfold sont_cocycliques, circonscrit, isocele in |- *; intros.
exists O.
split; [ try assumption | idtac ].
elim H7; intros H8 H9; try clear H7; try exact H9.
elim H6; intros H7 H10; try clear H6; try exact H10.
split; auto.
cut (triangle D A A'); intros.
elim existence_cercle_circonscrit with (A := A) (B := A') (C := D);
 [ intros I H7 | auto with geo ].
cut (I = O); intros.
rewrite <- H6; auto with geo.
generalize (centre_circonscrit_rectangle_milieu (A:=A) (B:=A') (C:=D));
 intros H8; apply H8; auto with geo.
unfold triangle in |- *.
apply orthogonal_non_alignes; auto.
Qed.
 
Theorem Miquel :
 forall A B C D E F M : PO,
 A <> C ->
 A <> F ->
 B <> E ->
 B <> C ->
 alignes A D F ->
 alignes A E C ->
 alignes B D E ->
 alignes B F C ->
 triangle A E D ->
 triangle A E M ->
 triangle B D M ->
 triangle B F M ->
 sont_cocycliques A C F M ->
 sont_cocycliques A E D M ->
 sont_cocycliques E C B M /\ sont_cocycliques D F B M.
intros.
deroule_triangle A E D.
deroule_triangle A E M.
deroule_triangle B D M.
deroule_triangle B F M.
cut (triangle A C M); intros.
cut (triangle A C F); intros.
cut (triangle B E M); intros.
cut (triangle B C M); intros.
deroule_triangle A C M.
deroule_triangle A C F.
deroule_triangle B E M.
deroule_triangle B C M.
split; [ try assumption | idtac ].
apply cocycliques_ordre_cycle; apply cocycliques_ordre_cycle.
apply reciproque_cocyclicite; auto with geo.
replace (double_AV (cons_AV (vec E B) (vec E M))) with
 (double_AV (cons_AV (vec E D) (vec E M))).
replace (double_AV (cons_AV (vec E D) (vec E M))) with
 (double_AV (cons_AV (vec A D) (vec A M))).
replace (double_AV (cons_AV (vec A D) (vec A M))) with
 (double_AV (cons_AV (vec A F) (vec A M))).
replace (double_AV (cons_AV (vec C B) (vec C M))) with
 (double_AV (cons_AV (vec C F) (vec C M))).
apply cocyclicite6; auto with geo.
apply alignement_et_angles; auto with geo.
apply alignement_et_angles; auto with geo.
apply cocyclicite6; auto with geo.
apply alignement_et_angles; auto with geo.
apply cocycliques_ordre_cycle; apply cocycliques_ordre_cycle.
apply reciproque_cocyclicite; auto with geo.
replace (double_AV (cons_AV (vec D B) (vec D M))) with
 (double_AV (cons_AV (vec D E) (vec D M))).
replace (double_AV (cons_AV (vec D E) (vec D M))) with
 (double_AV (cons_AV (vec A E) (vec A M))).
replace (double_AV (cons_AV (vec A E) (vec A M))) with
 (double_AV (cons_AV (vec A C) (vec A M))).
replace (double_AV (cons_AV (vec F B) (vec F M))) with
 (double_AV (cons_AV (vec F C) (vec F M))).
apply cocyclicite5; auto with geo.
apply alignement_et_angles; auto with geo.
apply alignement_et_angles; auto with geo.
apply cocyclicite5; auto with geo.
apply alignement_et_angles; auto with geo.
apply alignement_triangle with (3 := H10); auto with geo.
apply alignement_triangle with (3 := H9); auto with geo.
apply alignement_triangle with (3 := H7); auto with geo.
apply alignement_triangle with (3 := H8); auto with geo.
Qed.
 
Lemma triangles_meme_hypotenuse :
 forall A B C D : PO,
 A <> B ->
 B <> C ->
 A <> D ->
 C <> D ->
 orthogonal (vec C A) (vec C B) ->
 orthogonal (vec D A) (vec D B) ->
 double_AV (cons_AV (vec B C) (vec B A)) =
 double_AV (cons_AV (vec D C) (vec D A)) :>AV.
intros.
discrimine A C.
rewrite <- angle_nul; auto.
rewrite <- angle_nul; auto.
discrimine B D.
generalize (orthogonal_non_alignes (A:=C) (B:=A) (C:=B)); intros.
generalize (orthogonal_non_alignes (A:=D) (B:=A) (C:=B)); intros.
lapply (orthogonal_angles (A:=C) (B:=A) (C:=C) (D:=B)); auto; intros.
lapply (orthogonal_angles (A:=D) (B:=A) (C:=D) (D:=B)); auto; intros.
cut (triangle A B C); intros.
cut (triangle A B D); intros.
apply cocyclicite2; auto.
apply reciproque_cocyclicite; auto.
rewrite H9; auto; rewrite H10; auto.
apply triangle_ordre_cycle; unfold triangle in |- *; auto.
apply triangle_ordre_cycle; unfold triangle in |- *; auto.
Qed.
 
Lemma triangle_ortho_cote :
 forall A B C M P Q R : PO,
 triangle A B C ->
 P = projete_orthogonal B C M ->
 Q = projete_orthogonal A C M ->
 ~ alignes A C M -> ~ alignes B C M -> ~ alignes M P Q.
intros.
deroule_triangle A B C.
elim (def_projete_orthogonal2 (A:=B) (B:=C) (C:=M) (H:=P)); auto; intros.
elim (def_projete_orthogonal2 (A:=A) (B:=C) (C:=M) (H:=Q)); auto; intros.
lapply (projete_non_axe (A:=B) (B:=C) (M:=M) (H:=P)); auto; intros.
lapply (projete_non_axe (A:=A) (B:=C) (M:=M) (H:=Q)); auto; intros.
apply angle_non_alignes; auto.
replace (double_AV (cons_AV (vec M P) (vec M Q))) with
 (double_AV (cons_AV (vec C B) (vec C A))).
apply non_alignes_angle; auto with geo.
rewrite
 (angles_droites_orthogonales (A:=C) (B:=B) (C:=C) (D:=A) (E:=M) (F:=P)
    (G:=M) (I:=Q)); auto with geo.
Qed.
 
Lemma triangle_ortho_cote2 :
 forall A B C M P Q : PO,
 triangle A B C ->
 P = projete_orthogonal B C M ->
 Q = projete_orthogonal A B M ->
 ~ alignes A B M -> ~ alignes B C M -> ~ alignes M P Q.
intros.
deroule_triangle A B C.
elim (def_projete_orthogonal2 (A:=B) (B:=C) (C:=M) (H:=P)); auto; intros.
elim (def_projete_orthogonal2 (A:=A) (B:=B) (C:=M) (H:=Q)); auto; intros.
lapply (projete_non_axe (A:=B) (B:=C) (M:=M) (H:=P)); auto; intros.
lapply (projete_non_axe (A:=A) (B:=B) (M:=M) (H:=Q)); auto; intros.
apply angle_non_alignes; auto.
replace (double_AV (cons_AV (vec M P) (vec M Q))) with
 (double_AV (cons_AV (vec B C) (vec B A))).
apply non_alignes_angle; auto with geo.
rewrite
 (angles_droites_orthogonales (A:=B) (B:=C) (C:=B) (D:=A) (E:=M) (F:=P)
    (G:=M) (I:=Q)); auto with geo.
Qed.
 
Lemma projete_ortho_cote :
 forall A B C M P Q R : PO,
 triangle A B C ->
 triangle B C M ->
 triangle A B M ->
 triangle A C M ->
 P = projete_orthogonal B C M ->
 Q = projete_orthogonal A C M ->
 R = projete_orthogonal A B M ->
 double_AV (cons_AV (vec P Q) (vec P R)) =
 plus (double_AV (cons_AV (vec C A) (vec C M)))
   (double_AV (cons_AV (vec B M) (vec B A))) :>AV.
intros.
deroule_triangle A B C.
deroule_triangle B C M.
cut (M <> P); intros.
elim (def_projete_orthogonal2 (A:=B) (B:=C) (C:=M) (H:=P)); auto; intros.
elim (def_projete_orthogonal2 (A:=A) (B:=C) (C:=M) (H:=Q)); auto; intros.
elim (def_projete_orthogonal2 (A:=A) (B:=B) (C:=M) (H:=R)); auto; intros.
cut (P <> R); intros.
cut (P <> Q); intros.
replace (double_AV (cons_AV (vec P Q) (vec P R))) with
 (plus (double_AV (cons_AV (vec P Q) (vec P M)))
    (double_AV (cons_AV (vec P M) (vec P R)))).
replace (double_AV (cons_AV (vec P Q) (vec P M))) with
 (double_AV (cons_AV (vec C A) (vec C M))).
replace (double_AV (cons_AV (vec P M) (vec P R))) with
 (double_AV (cons_AV (vec B M) (vec B A))); auto.
discrimine R B.
rewrite (orthogonal_angles (A:=P) (B:=M) (C:=P) (D:=B)); auto.
pattern B at 1 in |- *.
rewrite <- H23.
apply orthogonal_angles; auto with geo.
red in |- *; intros; apply H10; rewrite <- H23; auto with geo.
red in |- *; intros; apply H21; rewrite H23; auto with geo.
apply orthogonal_alignement2 with C; auto with geo.
replace (double_AV (cons_AV (vec B M) (vec B A))) with
 (double_AV (cons_AV (vec B M) (vec B R))).
rewrite <- (def_opp (A:=P) (B:=R) (C:=P) (D:=M)); auto.
rewrite double_opp; auto.
rewrite <- (triangles_meme_hypotenuse (A:=M) (B:=B) (C:=R) (D:=P)); auto.
rewrite <- double_opp; auto.
rewrite def_opp; auto.
apply orthogonal_alignement with A; auto.
apply orthogonal_alignement2 with C; auto.
apply alignement_et_angles; auto with geo.
discrimine Q C.
rewrite (orthogonal_angles (A:=P) (B:=C) (C:=P) (D:=M)); auto.
pattern C at 2 in |- *.
rewrite <- H23.
apply orthogonal_angles; auto with geo.
red in |- *; intros; apply H10; rewrite <- H23; auto with geo.
red in |- *; intros; apply H22; rewrite H23; auto.
apply ortho_sym.
apply orthogonal_alignement with B; auto.
replace (double_AV (cons_AV (vec C A) (vec C M))) with
 (double_AV (cons_AV (vec C Q) (vec C M))).
rewrite <- (triangles_meme_hypotenuse (A:=M) (B:=C) (C:=Q) (D:=P)); auto.
apply orthogonal_alignement with A; auto.
apply orthogonal_alignement with B; auto.
apply alignement_et_angles; auto with geo.
rewrite double_Chasles; auto.
apply non_alignes_distincts2 with M.
deroule_triangle A C M.
apply (triangle_ortho_cote (A:=A) (B:=B) (C:=C) (M:=M) (P:=P) (Q:=Q)); auto.
apply non_alignes_distincts2 with M.
deroule_triangle A B M.
apply (triangle_ortho_cote2 (A:=A) (B:=B) (C:=C) (M:=M) (P:=P) (Q:=R)); auto.
apply projete_non_axe with (2 := H3); auto.
Qed.
 
Theorem droite_Simson :
 forall A B C M P Q R : PO,
 triangle A B C ->
 triangle B C M ->
 triangle A B M ->
 triangle A C M ->
 P = projete_orthogonal B C M ->
 Q = projete_orthogonal A C M ->
 R = projete_orthogonal A B M -> (sont_cocycliques A B C M <-> alignes P Q R).
unfold iff in |- *; intros.
lapply (projete_ortho_cote (A:=A) (B:=B) (C:=C) (M:=M) (P:=P) (Q:=Q) (R:=R));
 auto; intros.
deroule_triangle A B C.
deroule_triangle B C M.
cut (M <> P); intros.
elim (def_projete_orthogonal2 (A:=B) (B:=C) (C:=M) (H:=P)); auto; intros.
elim (def_projete_orthogonal2 (A:=A) (B:=C) (C:=M) (H:=Q)); auto; intros.
elim (def_projete_orthogonal2 (A:=A) (B:=B) (C:=M) (H:=R)); auto; intros.
cut (P <> R); intros.
cut (P <> Q); intros.
split; intros.
apply alignes_angle; auto.
rewrite H6; auto.
cut
 (double_AV (cons_AV (vec C A) (vec C M)) =
  double_AV (cons_AV (vec B A) (vec B M))); intros.
rewrite H25; auto.
rewrite double_Chasles; auto.
unfold double_AV in |- *.
rewrite Chasles; auto.
rewrite <- angle_nul; auto.
lapply (cocyclicite3 (A:=A) (B:=B) (C:=C) (D:=M)); auto; intros.
rewrite <- def_opp; auto.
rewrite <- (def_opp (A:=B) (B:=M) (C:=B) (D:=A)); auto.
rewrite double_opp; auto.
rewrite double_opp; auto.
rewrite H25; auto.
lapply (angle_alignes (A:=P) (B:=Q) (C:=R)); auto; intros.
cut (sont_cocycliques A M C B); intros.
generalize H26; unfold sont_cocycliques, circonscrit, isocele in |- *; intros.
elim H27; intros.
elim H28; intros.
elim H30; intros.
elim H29; intros.
exists x; auto.
apply reciproque_cocyclicite; auto with geo.
replace (double_AV (cons_AV (vec C A) (vec C M))) with
 (plus (double_AV (cons_AV (vec P Q) (vec P R)))
    (opp (double_AV (cons_AV (vec B M) (vec B A))))).
replace (opp (double_AV (cons_AV (vec B M) (vec B A)))) with
 (double_AV (cons_AV (vec B A) (vec B M))).
rewrite H25; auto.
rewrite zero_plus_double; auto.
rewrite <- double_opp; auto.
rewrite def_opp; auto.
rewrite H6; auto.
replace (opp (double_AV (cons_AV (vec B M) (vec B A)))) with
 (double_AV (cons_AV (vec B A) (vec B M))).
replace
 (plus
    (plus (double_AV (cons_AV (vec C A) (vec C M)))
       (double_AV (cons_AV (vec B M) (vec B A))))
    (double_AV (cons_AV (vec B A) (vec B M)))) with
 (plus (double_AV (cons_AV (vec C A) (vec C M)))
    (plus (double_AV (cons_AV (vec B M) (vec B A)))
       (double_AV (cons_AV (vec B A) (vec B M))))).
rewrite double_Chasles; auto.
rewrite <- angle_nul; auto.
rewrite (angle_nul (A:=C) (B:=M)); auto.
rewrite double_Chasles; auto.
unfold double_AV in |- *.
mesure C A C M.
mesure B M B A.
mesure B A B M.
replace (x + x + (x0 + x0 + (x1 + x1))) with (x + x + (x0 + x0) + (x1 + x1));
 auto.
ring.
rewrite <- double_opp; auto.
rewrite def_opp; auto.
apply non_alignes_distincts2 with M.
deroule_triangle A C M.
apply (triangle_ortho_cote (A:=A) (B:=B) (C:=C) (M:=M) (P:=P) (Q:=Q)); auto.
apply non_alignes_distincts2 with M.
deroule_triangle A B M.
apply (triangle_ortho_cote2 (A:=A) (B:=B) (C:=C) (M:=M) (P:=P) (Q:=R)); auto.
apply projete_non_axe with (2 := H3); auto.
Qed.
Require Export orthocentre.
Require Export reflexion_plane.
 
Lemma orthocentre_double :
 forall A B C H : PO,
 H <> B :>PO ->
 H <> C :>PO ->
 triangle A B C ->
 H = orthocentre A B C :>PO ->
 double_AV (cons_AV (vec H C) (vec H B)) =
 double_AV (cons_AV (vec A B) (vec A C)) :>AV.
intros.
elim orthocentre_def2 with (A := A) (B := B) (C := C) (H := H);
 [ intros | auto ].
elim H4; intros H6 H7; try clear H4; try exact H7.
deroule_triangle A B C.
apply angles_droites_orthogonales; auto with geo.
Qed.
 
Theorem symetrique_orthocentre :
 forall A B C H H' : PO,
 triangle A B C ->
 triangle B C H ->
 H = orthocentre A B C :>PO ->
 H' = reflexion B C H :>PO -> sont_cocycliques A B C H'.
intros.
deroule_triangle A B C.
deroule_triangle B C H.
lapply (orthocentre_double (A:=A) (B:=B) (C:=C) (H:=H)); intros.
apply cocycliques_ordre_cycle; apply cocycliques_ordre_cycle;
 apply cocycliques_ordre_cycle.
apply reciproque_cocyclicite; auto with geo.
unfold triangle in |- *.
apply non_axe_image_non_axe with H; auto.
rewrite <- H12; auto.
unfold double_AV in |- *.
rewrite (reflexion_inverse_angle (A:=B) (B:=C) (M:=H) (M':=H')); auto.
rewrite def_opp; auto.
auto.
Qed.
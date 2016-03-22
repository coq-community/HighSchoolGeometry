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


Require Export cercle.
Set Implicit Arguments.
Unset Strict Implicit.
 
Theorem angle_inscrit :
 forall O A B C : PO,
 A <> B ->
 A <> C ->
 O <> B ->
 circonscrit O A B C ->
 double_AV (cons_AV (vec A B) (vec A C)) = cons_AV (vec O B) (vec O C).
unfold double_AV in |- *; intros O A B C H H0 H2 H4.
cut (O <> A); intros.
2: apply circonscrit_distinct3 with (2 := H4); auto.
cut (O <> C); intros.
2: apply circonscrit_distinct2 with (2 := H4); auto.
generalize (circonscrit_isocele (O:=O) (A:=A) (B:=B) (C:=C)); intros.
lapply (circonscrit_isocele (O:=O) (A:=A) (B:=B) (C:=C)); auto; intros.
unfold circonscrit in H4.
elim H4; clear H4; intros.
replace (cons_AV (vec O B) (vec O C)) with
 (plus (cons_AV (vec O B) (vec O A)) (cons_AV (vec O A) (vec O C))).
generalize (somme_triangle (A:=O) (B:=B) (C:=A)); intros.
replace (cons_AV (vec O B) (vec O A)) with
 (plus (image_angle pi)
    (opp (plus (cons_AV (vec B A) (vec B O)) (cons_AV (vec A O) (vec A B))))).
generalize (somme_triangle (A:=O) (B:=A) (C:=C)); intros.
replace (cons_AV (vec O A) (vec O C)) with
 (plus (image_angle pi)
    (opp (plus (cons_AV (vec A C) (vec A O)) (cons_AV (vec C O) (vec C A))))).
replace
 (opp (plus (cons_AV (vec B A) (vec B O)) (cons_AV (vec A O) (vec A B))))
 with
 (plus (opp (cons_AV (vec B A) (vec B O)))
    (opp (cons_AV (vec A O) (vec A B)))).
replace
 (opp (plus (cons_AV (vec A C) (vec A O)) (cons_AV (vec C O) (vec C A))))
 with
 (plus (opp (cons_AV (vec A C) (vec A O)))
    (opp (cons_AV (vec C O) (vec C A)))).
replace (cons_AV (vec A B) (vec A C)) with
 (plus (cons_AV (vec A B) (vec A O)) (cons_AV (vec A O) (vec A C))).
rewrite def_opp; auto.
rewrite def_opp; auto.
rewrite def_opp; auto.
rewrite def_opp; auto.
generalize (isocele_angles_base (A:=O) (B:=A) (C:=B)); auto; intros.
rewrite <- H10; auto.
generalize (isocele_angles_base (A:=O) (B:=C) (C:=A)); auto with geo; intros.
rewrite <- H11; auto with geo.
mesure A B A O.
mesure C A C O.
replace (pi + (x + x) + (pi + (x0 + x0))) with
 (pi + pi + (x + x + (x0 + x0))).
replace (pi + pi) with deuxpi; auto.
symmetry  in |- *.
rewrite add_mes_compatible; rewrite pi_plus_pi; rewrite <- add_mes_compatible.
replace (0 + (x + x + (x0 + x0))) with (x + x0 + (x + x0)); auto.
ring.
ring.
rewrite Chasles; auto.
rewrite <- opp_plus_plus_opp; auto.
rewrite <- opp_plus_plus_opp; auto.
rewrite <- H9; auto.
rewrite opp_plus_plus_opp; auto.
mesure A C A O.
mesure C O C A.
mesure O A O C.
replace (x1 + (x + x0) + (- x + - x0)) with x1; auto.
ring.
rewrite <- H8; auto.
rewrite opp_plus_plus_opp; auto.
mesure B A B O.
mesure A O A B.
mesure O B O A.
replace (x1 + (x + x0) + (- x + - x0)) with x1; auto.
ring.
rewrite Chasles; auto.
Qed.
 
Theorem angle_inscrit2 :
 forall O A B C : PO,
 A <> C ->
 B <> C ->
 O <> B ->
 circonscrit O A B C ->
 double_AV (cons_AV (vec C A) (vec C B)) = cons_AV (vec O A) (vec O B).
intros O A B C H H0 H1 H2; try assumption.
cut (O <> A); intros.
2: apply circonscrit_distinct3 with (2 := H2); auto.
apply angle_inscrit; auto.
hcercle H2.
rewrite <- H6; auto.
Qed.
 
Lemma circonscrit_triangle_non_point :
 forall O A B C : PO,
 triangle A B C -> circonscrit O A B C -> O <> A /\ O <> B /\ O <> C.
intros.
cut (O <> A); intros.
split; [ try assumption | idtac ].
split; [ try assumption | idtac ].
apply circonscrit_distinct1 with (2 := H0); auto.
apply circonscrit_distinct2 with (2 := H0); auto.
hcercle H0.
deroule_triangle A B C.
red in |- *; intros.
apply H6.
rewrite <- H7.
assert (distance O B = 0); auto with geo.
rewrite <- H2.
rewrite <- H7; auto with geo.
Qed.
 
Theorem cocyclicite :
 forall A B C D : PO,
 triangle A B C ->
 triangle A B D ->
 sont_cocycliques A B C D ->
 double_AV (cons_AV (vec C A) (vec C B)) =
 double_AV (cons_AV (vec D A) (vec D B)).
unfold sont_cocycliques in |- *; intros.
deroule_triangle A B C.
deroule_triangle A B D.
elim H1; (clear H1; (intros O; intros)).
elim H1; (clear H1; intros).
lapply (circonscrit_triangle_non_point (O:=O) (A:=A) (B:=B) (C:=C)); auto;
 intros.
lapply (circonscrit_triangle_non_point (O:=O) (A:=A) (B:=B) (C:=D)); auto;
 intros.
elim H12; (clear H12; intros).
elim H13; (clear H13; intros).
elim H11; (clear H11; intros).
elim H15; (clear H15; intros).
lapply (angle_inscrit2 (O:=O) (A:=A) (B:=B) (C:=C)); auto; intros.
lapply (angle_inscrit2 (O:=O) (A:=A) (B:=B) (C:=D)); auto; intros.
rewrite H18; auto.
try exact H1.
try exact H10.
Qed.
 
Theorem existence_cercle_circonscrit :
 forall A B C : PO, triangle A B C -> ex (fun O : PO => circonscrit O A B C).
intros.
deroule_triangle A B C.
soit_mediatrice A B ipattern:M ipattern:K.
soit_mediatrice B C ipattern:J ipattern:L.
lapply
 (mediatrices_triangle_concours (A:=A) (B:=B) (C:=C) (I:=M) (J:=J) (K:=K)
    (L:=L)); auto; intros.
elim (def_concours2 (A:=M) (B:=K) (C:=J) (D:=L)); auto; intros.
exists x.
apply circonscrit_permute.
unfold circonscrit in |- *.
elim H19; clear H19; intros.
split; apply mediatrice_isocele.
discrimine J x.
apply milieu_mediatrice; auto.
apply orthogonale_segment_milieu_mediatrice with J; auto.
apply ortho_sym; auto.
apply paralleles_orthogonal with (A := J) (B := L); auto.
apply alignes_paralleles; auto.
apply mediatrice_orthogonale_segment; auto.
apply milieu_mediatrice; auto.
discrimine M x.
apply mediatrice_permute.
apply milieu_mediatrice; auto.
apply mediatrice_permute.
apply orthogonale_segment_milieu_mediatrice with M; auto.
apply ortho_sym; auto.
apply paralleles_orthogonal with (A := M) (B := K); auto.
apply alignes_paralleles; auto.
apply mediatrice_orthogonale_segment; auto.
apply milieu_mediatrice; auto.
Qed.
 
Lemma existence_cercle_circonscrit_diametre :
 forall A B C : PO,
 triangle A B C ->
 exists O : PO,
   (exists D : PO,
      circonscrit O A B C /\
      cercle_diametre A D C /\ sont_cocycliques A B C D).
intros.
elim existence_cercle_circonscrit with (A := A) (B := B) (C := C);
 [ unfold circonscrit, isocele in |- *; intros O H0; try exact H0 | auto ].
exists O.
symetrique O A ipattern:D.
exists D.
split; [ try assumption | idtac ].
applatit_and.
icercle.
exists O.
icercle.
exists O.
icercle.
Qed.
 
Lemma cocycliques_trivial :
 forall A B C : PO, triangle A B C -> sont_cocycliques A B C A.
icercle.
elim existence_cercle_circonscrit with (A := A) (B := B) (C := C);
 [ unfold sont_cocycliques, circonscrit, isocele in |- *; intros O H0;
    try exact H0
 | auto ].
exists O.
split; [ try assumption | idtac ].
split; [ idtac | auto ].
elim H0; intros H1 H2; try clear H0; try exact H1.
Qed.
Hint Resolve cocycliques_trivial: geo.
(* soit_circonscrit construit le centre du cercle circonscrit du triangle ABC 
   et ne marche que si on a (triangle A B C) dans les hypotheses*)
 
Ltac soit_circonscrit A B C O :=
  elim (existence_cercle_circonscrit (A:=A) (B:=B) (C:=C));
   [ intros O; intros;
      generalize (circonscrit_triangle_non_point (O:=O) (A:=A) (B:=B) (C:=C));
      intros toto; elim toto; clear toto;
      [ intros; applatit_and | auto | auto ]
   | auto ].
(* deroule_circonscrit ne marche que si on a (cisrconscrit O A B C) dans les hypothèses*)
 
Ltac deroule_circonscrit A B C O :=
  elim (circonscrit_triangle_non_point (O:=O) (A:=A) (B:=B) (C:=C));
   try assumption; intro; intros toto; elim toto; clear toto; 
   intros.
 
Lemma triangle_intersection_mediatrices :
 forall A B C B' C' O : PO,
 triangle A B C ->
 C' <> O ->
 B' <> O ->
 C' = milieu A B ->
 B' = milieu A C -> circonscrit O A B C -> ~ alignes C' O B'.
unfold circonscrit, isocele in |- *; intros.
deroule_triangle A B C.
cut (~ paralleles (droite C' O) (droite B' O)); intros.
red in |- *; intros; apply H9.
rewrite droite_permute; auto.
rewrite (droite_permute (A:=B') (B:=O)); auto.
apply alignes_paralleles; auto with geo.
apply angle_non_paralleles; auto.
elim H4; intros H10 H11; try clear H4; try exact H11.
rewrite
 (angles_droites_orthogonales (A:=A) (B:=C) (C:=A) (D:=B) (E:=B') (F:=O)
    (G:=C') (I:=O)); auto with geo.
apply ortho_sym.
apply mediatrice_orthogonale_segment; auto.
apply milieu_mediatrice; auto.
apply ortho_sym.
apply mediatrice_orthogonale_segment; auto.
apply milieu_mediatrice; auto.
Qed.
 
Lemma milieu_centrecirconscrit_orthogonal_segment :
 forall A B C A' O : PO,
 A' = milieu B C -> circonscrit O A B C -> orthogonal (vec O A') (vec B C).
unfold circonscrit, isocele in |- *; intros.
elim H0; intros H1 H2; try clear H0; try exact H2.
discrimine O A'.
apply ortho_sym.
replace (vec A' A') with zero; [ idtac | Ringvec ].
auto with geo.
discrimine B C.
replace (vec C C) with zero; [ auto with geo | Ringvec ].
apply mediatrice_orthogonale_segment; auto.
unfold mediatrice in |- *.
rewrite <- H1; auto.
apply milieu_mediatrice; auto.
Qed.
 
Axiom
  angles_orthogonal :
    forall A B C D : PO,
    A <> B ->
    C <> D ->
    double_AV (cons_AV (vec A B) (vec C D)) = image_angle pi ->
    orthogonal (vec A B) (vec C D).
 
Theorem tangente :
 forall A B O T : PO,
 A <> B ->
 O <> A ->
 O <> B ->
 A <> T ->
 isocele O A B ->
 orthogonal (vec A T) (vec O A) ->
 double_AV (cons_AV (vec A T) (vec A B)) = cons_AV (vec O A) (vec O B).
intros A B O T H H0 H1 H2 H3 H4; try assumption.
lapply (isocele_angles_base (A:=O) (B:=A) (C:=B)); auto; intros.
lapply (orthogonal_angles (A:=A) (B:=T) (C:=O) (D:=A)); auto; intros.
lapply (somme_triangle (A:=O) (B:=A) (C:=B)); auto; intros.
replace (cons_AV (vec O A) (vec O B)) with
 (plus (image_angle pi)
    (opp (plus (cons_AV (vec A B) (vec A O)) (cons_AV (vec B O) (vec B A))))).
replace (cons_AV (vec A T) (vec A B)) with
 (plus (cons_AV (vec A T) (vec O A)) (cons_AV (vec O A) (vec A B))).
unfold double_AV in |- *.
rewrite <- H5; auto.
replace
 (plus (plus (cons_AV (vec A T) (vec O A)) (cons_AV (vec O A) (vec A B)))
    (plus (cons_AV (vec A T) (vec O A)) (cons_AV (vec O A) (vec A B)))) with
 (plus (plus (cons_AV (vec A T) (vec O A)) (cons_AV (vec A T) (vec O A)))
    (plus (cons_AV (vec O A) (vec A B)) (cons_AV (vec O A) (vec A B)))).
replace (plus (cons_AV (vec A T) (vec O A)) (cons_AV (vec A T) (vec O A)))
 with (double_AV (cons_AV (vec A T) (vec O A))); auto.
rewrite H6; auto.
rewrite opp_plus_plus_opp; auto.
replace (cons_AV (vec O A) (vec A B)) with
 (plus (cons_AV (vec O A) (vec A O)) (cons_AV (vec A O) (vec A B))); 
 auto.
rewrite <- angle_plat; auto.
rewrite def_opp; auto.
mesure A O A B.
replace (pi + (pi + x + (pi + x))) with (pi + (x + x) + (pi + pi)).
rewrite add_mes_compatible.
replace (pi + pi) with deuxpi; auto.
rewrite pi_plus_pi.
repeat rewrite <- add_mes_compatible.
replace (pi + (x + x) + 0) with (pi + (x + x)); auto.
ring.
ring.
rewrite Chasles; auto.
mesure A T O A.
mesure O A A B.
replace (x + x + (x0 + x0)) with (x + x0 + (x + x0)); auto.
ring.
rewrite Chasles; auto.
rewrite <- H7; auto.
rewrite opp_plus_plus_opp; auto.
rewrite <- H5; auto.
mesure A B A O.
mesure O A O B.
replace (x0 + (x + x) + (- x + - x)) with x0; auto.
ring.
Qed.
 
Theorem tangente_reciproque :
 forall A B O T T' : PO,
 A <> B ->
 O <> A ->
 O <> B ->
 A <> T' ->
 isocele O A B ->
 orthogonal (vec A T) (vec O A) ->
 double_AV (cons_AV (vec A T') (vec A B)) = cons_AV (vec O A) (vec O B) ->
 alignes A T T'.
intros A B O T T' H H0 H1 H3 H4 H5 H6; try assumption.
discrimine A T.
apply alignes_angle; auto.
unfold double_AV in |- *.
replace (cons_AV (vec A T) (vec A T')) with
 (plus (cons_AV (vec A T) (vec A B)) (cons_AV (vec A B) (vec A T'))); 
 auto.
replace
 (plus (plus (cons_AV (vec A T) (vec A B)) (cons_AV (vec A B) (vec A T')))
    (plus (cons_AV (vec A T) (vec A B)) (cons_AV (vec A B) (vec A T')))) with
 (plus (plus (cons_AV (vec A T) (vec A B)) (cons_AV (vec A T) (vec A B)))
    (plus (cons_AV (vec A B) (vec A T')) (cons_AV (vec A B) (vec A T'))));
 auto.
replace (plus (cons_AV (vec A B) (vec A T')) (cons_AV (vec A B) (vec A T')))
 with (cons_AV (vec O B) (vec O A)); auto.
rewrite <- (def_opp (A:=O) (B:=A) (C:=O) (D:=B)); auto.
rewrite <- (tangente (A:=A) (B:=B) (O:=O) (T:=T)); auto.
unfold double_AV in |- *.
rewrite opp_plus_plus_opp; auto.
mesure A T A B.
replace (x + x + (- x + - x)) with 0; auto.
ring.
rewrite <- (def_opp (A:=O) (B:=A) (C:=O) (D:=B)); auto.
rewrite <- H6.
unfold double_AV in |- *.
rewrite opp_plus_plus_opp; auto.
rewrite def_opp; auto.
mesure A T A B.
mesure A B A T'.
replace (x + x + (x0 + x0)) with (x + x0 + (x + x0)); auto.
ring.
rewrite Chasles; auto.
Qed.
 
Theorem unicite_circonscrit_triangle :
 forall A B C O O1 : PO,
 triangle A B C -> circonscrit O A B C -> circonscrit O1 A B C -> O = O1.
intros.
deroule_triangle A B C.
soit_mediatrice A B ipattern:M ipattern:K.
soit_mediatrice B C ipattern:J ipattern:L.
lapply
 (mediatrices_triangle_concours (A:=A) (B:=B) (C:=C) (I:=M) (J:=J) (K:=K)
    (L:=L)); auto; intros.
cut (M <> J); intros.
generalize H1; unfold circonscrit in |- *; intros.
generalize H0; unfold circonscrit in |- *; intros.
lapply (circonscrit_isocele (O:=O) (A:=A) (B:=B) (C:=C)); auto; intros.
lapply (circonscrit_isocele (O:=O1) (A:=A) (B:=B) (C:=C)); auto; intros.
elim H22; (clear H22; intros).
elim H23; (clear H23; intros).
lapply (milieu_mediatrice (A:=A) (B:=B) (M:=M)); auto; intros.
lapply (milieu_mediatrice (A:=B) (B:=C) (M:=J)); auto; intros.
lapply (mediatrice_droite (A:=A) (B:=B) (I:=M) (J:=K) (K:=O)); auto; intros.
lapply (mediatrice_droite (A:=B) (B:=C) (I:=J) (J:=L) (K:=O)); auto; intros.
lapply (mediatrice_droite (A:=A) (B:=B) (I:=M) (J:=K) (K:=O1)); auto; intros.
lapply (mediatrice_droite (A:=B) (B:=C) (I:=J) (J:=L) (K:=O1)); auto; intros.
cut
 (double_AV (cons_AV (vec M K) (vec J L)) =
  double_AV (cons_AV (vec B A) (vec B C))).
intros H101.
elim (classic (alignes J M L)); intros.
apply (concours_unique (A:=M) (B:=J) (A1:=K) (B1:=M) (I:=O) (J:=O1)).
red in |- *; intros; apply H2.
cut
 (double_AV (cons_AV (vec M K) (vec M J)) =
  double_AV (cons_AV (vec B A) (vec B C))); intros.
apply permute_alignes; auto.
apply alignes_angle; auto.
rewrite <- H36.
apply angle_alignes; auto.
rewrite <- H101.
halignes H34 ipattern:x.
absurd (J = M); auto.
cut (vec J L = mult_PP (- x) (vec M J)); intros.
cut (vec M K = mult_PP 1 (vec M K)); intros.
apply angles_et_colinearite with (5 := H38) (6 := H37); auto.
Ringvec.
rewrite H36.
Ringvec.
auto.
apply H30; auto.
discrimine O M.
discrimine O J.
apply alignes_ordre_cycle; auto.
apply alignes_ordre_cycle; auto.
apply alignes_trans with (B := L); auto with geo.
apply H32; auto.
discrimine O1 M.
discrimine O1 J.
apply alignes_ordre_cycle; auto.
apply alignes_ordre_cycle; auto.
apply alignes_trans with (B := L); auto with geo.
apply (concours_unique (A:=J) (B:=M) (A1:=L) (B1:=K) (I:=O) (J:=O1)); auto.
red in |- *; intros; apply H34.
apply alignes_ordre_permute; auto.
discrimine O M.
discrimine O K.
apply alignes_ordre_cycle; auto with geo.
discrimine O1 M.
discrimine O1 K.
apply alignes_ordre_cycle; auto with geo.
apply angles_droites_orthogonales; auto.
cut (orthogonal (vec M K) (vec A B)); intros; auto with geo.
apply mediatrice_orthogonale_segment; auto.
apply ortho_sym; auto.
apply mediatrice_orthogonale_segment; auto.
apply deux_milieux_distincts with (2 := H11) (3 := H18); auto.
Qed.
 
Lemma circonscrit_mediatrice :
 forall O A B C : PO,
 circonscrit O A B C ->
 mediatrice A B O /\ mediatrice B C O /\ mediatrice A C O.
unfold circonscrit, isocele, mediatrice in |- *; intros; auto.
elim H; intros; auto.
split; [ assumption | split; [ idtac | try assumption ] ].
rewrite <- H0; auto.
Qed.
Require Export rotation_plane.
 
Theorem reciproque_cocyclicite :
 forall A B C D : PO,
 triangle A B C ->
 triangle A B D ->
 double_AV (cons_AV (vec C A) (vec C B)) =
 double_AV (cons_AV (vec D A) (vec D B)) -> sont_cocycliques A B C D.
unfold sont_cocycliques in |- *; intros.
deroule_triangle A B C.
deroule_triangle A B D.
soit_circonscrit A B C ipattern:O2.
soit_circonscrit A B D ipattern:O1.
mesure C A C B.
lapply (angle_inscrit2 (O:=O2) (A:=A) (B:=B) (C:=C)); auto; intros.
lapply (angle_inscrit2 (O:=O1) (A:=A) (B:=B) (C:=D)); auto; intros.
exists O2.
split; [ try assumption | idtac ].
unfold circonscrit in |- *.
split; [ try assumption | idtac ].
elim H10; auto.
cut (double_AV (cons_AV (vec C A) (vec C B)) <> image_angle 0);
 [ intros H50 | idtac ].
cut (O2 = O1); intros.
rewrite H21.
elim H12; auto.
soit_mediatrice A B ipattern:M ipattern:J.
elim (circonscrit_mediatrice (O:=O2) (A:=A) (B:=B) (C:=C)); try assumption;
 intros H60 H61.
elim H61; clear H61; intros H61 H62.
elim (circonscrit_mediatrice (O:=O1) (A:=A) (B:=B) (C:=D)); try assumption;
 intros H70 H71.
elim H71; clear H71; intros H71 H72.
lapply (mediatrice_droite (A:=A) (B:=B) (I:=M) (J:=J) (K:=O2)); auto; intros.
lapply (mediatrice_droite (A:=A) (B:=B) (I:=M) (J:=J) (K:=O1)); auto; intros.
elim (existence_rotation_Ia A M (pisurdeux + - x)); intros K; intros.
cut (A <> K); intros.
cut (alignes A K O2); intros.
cut (alignes A K O1); intros.
elim (classic (alignes A K M)); intros.
apply (concours_unique (A:=M) (B:=A) (A1:=J) (B1:=K) (I:=O2) (J:=O1)); auto.
apply orthogonal_non_alignes; auto.
lapply (mediatrice_orthogonale_segment (A:=A) (B:=B) (M:=M) (N:=J)); auto;
 intros.
elim (orthogonal_segment_milieu (A:=A) (B:=B) (C:=M) (D:=J) (I:=M)); auto;
 intros.
auto with geo.
apply ortho_sym.
apply H35; auto.
apply milieu_mediatrice; auto.
apply permute_alignes; auto.
apply permute_alignes; auto.
apply (concours_unique (A:=A) (B:=M) (A1:=K) (B1:=J) (I:=O2) (J:=O1)); auto.
assert (alignes M J O2); auto with geo.
assert (alignes M J O1); auto with geo.
discrimine K O1.
apply alignes_angle; [ auto | auto | idtac ].
unfold double_AV in |- *.
replace (cons_AV (vec A K) (vec A O1)) with
 (plus (cons_AV (vec A K) (vec A M)) (cons_AV (vec A M) (vec A O1))).
generalize (somme_triangle (A:=O1) (B:=A) (C:=B)); intros.
generalize (isocele_angles_base (A:=O1) (B:=A) (C:=B)); auto; intros.
generalize (angles_milieu (A:=O1) (B:=A) (C:=B) (I:=M)); auto; intros.
rewrite <- H36; auto.
replace
 (plus (plus (cons_AV (vec A K) (vec A M)) (cons_AV (vec A B) (vec A O1)))
    (plus (cons_AV (vec A K) (vec A M)) (cons_AV (vec A B) (vec A O1)))) with
 (plus (plus (cons_AV (vec A K) (vec A M)) (cons_AV (vec A K) (vec A M)))
    (plus (cons_AV (vec A B) (vec A O1)) (cons_AV (vec A B) (vec A O1)))).
replace (plus (cons_AV (vec A B) (vec A O1)) (cons_AV (vec A B) (vec A O1)))
 with (plus (image_angle pi) (opp (cons_AV (vec O1 A) (vec O1 B)))).
rewrite def_opp; auto.
rewrite <- (mes_oppx (A:=O1) (B:=A) (C:=O1) (D:=B) (x:=x + x)); auto.
rewrite <- (mes_oppx (A:=A) (B:=M) (C:=A) (D:=K) (x:=pisurdeux + - x)); auto.
repeat rewrite <- add_mes_compatible.
replace pi with (pisurdeux + pisurdeux); auto.
replace
 (- (pisurdeux + - x) + - (pisurdeux + - x) +
  (pisurdeux + pisurdeux + - (x + x))) with 0; auto.
ring.
elim (rotation_def (I:=A) (A:=M) (B:=K) (a:=pisurdeux + - x)); auto.
rewrite <- H20; auto.
rewrite <- H1; unfold double_AV in |- *.
rewrite <- H16.
rewrite add_mes_compatible; auto.
rewrite <- H34; auto.
rewrite <- H35; auto.
mesure A B A O1.
mesure O1 A O1 B.
replace (x1 + (x0 + x0) + - x1) with (x0 + x0); auto.
ring.
mesure A K A M.
mesure A B A O1.
replace (x0 + x0 + (x1 + x1)) with (x0 + x1 + (x0 + x1)); auto.
ring.
rewrite Chasles; auto.
discrimine K O2.
apply alignes_angle; [ auto | auto | idtac ].
unfold double_AV in |- *.
replace (cons_AV (vec A K) (vec A O2)) with
 (plus (cons_AV (vec A K) (vec A M)) (cons_AV (vec A M) (vec A O2))).
generalize (somme_triangle (A:=O2) (B:=A) (C:=B)); intros.
generalize (isocele_angles_base (A:=O2) (B:=A) (C:=B)); auto; intros.
generalize (angles_milieu (A:=O2) (B:=A) (C:=B) (I:=M)); auto; intros.
rewrite <- H35; auto.
replace
 (plus (plus (cons_AV (vec A K) (vec A M)) (cons_AV (vec A B) (vec A O2)))
    (plus (cons_AV (vec A K) (vec A M)) (cons_AV (vec A B) (vec A O2)))) with
 (plus (plus (cons_AV (vec A K) (vec A M)) (cons_AV (vec A K) (vec A M)))
    (plus (cons_AV (vec A B) (vec A O2)) (cons_AV (vec A B) (vec A O2)))).
replace (plus (cons_AV (vec A B) (vec A O2)) (cons_AV (vec A B) (vec A O2)))
 with (plus (image_angle pi) (opp (cons_AV (vec O2 A) (vec O2 B)))).
rewrite def_opp; auto.
rewrite <- (mes_oppx (A:=O2) (B:=A) (C:=O2) (D:=B) (x:=x + x)); auto.
rewrite <- (mes_oppx (A:=A) (B:=M) (C:=A) (D:=K) (x:=pisurdeux + - x)); auto.
repeat rewrite <- add_mes_compatible.
replace pi with (pisurdeux + pisurdeux); auto.
replace
 (- (pisurdeux + - x) + - (pisurdeux + - x) +
  (pisurdeux + pisurdeux + - (x + x))) with 0; auto.
ring.
elim (rotation_def (I:=A) (A:=M) (B:=K) (a:=pisurdeux + - x)); auto.
rewrite <- H19; auto.
unfold double_AV in |- *.
rewrite <- H16.
rewrite add_mes_compatible; auto.
rewrite <- H33; auto.
rewrite <- H34; auto.
mesure A B A O2.
mesure O2 A O2 B.
replace (x1 + (x0 + x0) + - x1) with (x0 + x0); auto.
ring.
mesure A K A M.
mesure A B A O2.
replace (x0 + x0 + (x1 + x1)) with (x0 + x1 + (x0 + x1)); auto.
ring.
rewrite Chasles; auto.
apply image_distinct_centre with (2 := H30); auto.
red in |- *; intros; apply H2.
apply alignes_ordre_cycle; auto.
apply alignes_angle; auto.
Qed.
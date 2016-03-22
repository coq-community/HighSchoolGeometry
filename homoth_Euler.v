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


Require Export droite_Euler.
Require Export applications_cocyclicite.
Set Implicit Arguments.
Unset Strict Implicit.
 
Lemma homothetique_orthocentre :
 forall A B C O G H : PO,
 triangle A B C ->
 G = centre_gravite A B C ->
 circonscrit O A B C -> H = orthocentre A B C -> O = homothetie (- / 2) G H.
intros.
apply vecteur_homothetie.
cut (vec O H = mult_PP 3 (vec O G)); intros.
2: apply droite_Euler_fort with (1 := H0); auto.
replace (vec G H) with (add_PP (mult_PP (-1) (vec O G)) (vec O H));
 [ idtac | Ringvec ].
rewrite H4.
cut (2 <> 0); intros; auto with real.
replace
 (mult_PP (- / 2) (add_PP (mult_PP (-1) (vec O G)) (mult_PP 3 (vec O G))))
 with (mult_PP (/ 2) (mult_PP 2 (vec G O))); [ idtac | Ringvec ].
replace (mult_PP (/ 2) (mult_PP 2 (vec G O))) with
 (mult_PP (/ 2 * 2) (vec G O)); [ idtac | Ringvec ].
replace (/ 2 * 2) with 1; auto with real.
Ringvec.
Qed.
 
Lemma homothetique_centre_circonscrit :
 forall A B C O G H I : PO,
 triangle A B C ->
 G = centre_gravite A B C ->
 circonscrit O A B C ->
 H = orthocentre A B C -> I = milieu O H -> I = homothetie (- / 2) G O.
intros.
apply vecteur_homothetie.
cut (vec O H = mult_PP 3 (vec O G)); intros.
2: apply droite_Euler_fort with (1 := H0); auto.
cut (2 <> 0); intros; auto with real.
apply mult_PP_regulier with 2; auto.
replace (mult_PP 2 (vec G I)) with (add_PP (vec G O) (vec G H)).
replace (vec G H) with (add_PP (vec G O) (vec O H)); [ idtac | Ringvec ].
rewrite H5.
replace (mult_PP 2 (mult_PP (- / 2) (vec G O))) with
 (mult_PP (2 * / 2) (vec O G)); [ idtac | Ringvec ].
replace (2 * / 2) with 1; auto with real.
Ringvec.
rewrite (prop_vecteur_milieu (B:=O) (C:=H) (A':=I) G); auto.
Qed.
 
Lemma centre_circonscrit_triangle_homothetique :
 forall A B C A' B' C' O G H I : PO,
 triangle A B C ->
 A' = milieu B C ->
 B' = milieu A C ->
 C' = milieu A B ->
 G = centre_gravite A B C ->
 circonscrit O A B C ->
 H = orthocentre A B C -> I = milieu O H -> circonscrit I A' B' C'.
intros.
generalize H5; unfold circonscrit, isocele in |- *; intros.
elim H8; intros H9 H10; try clear H8; try exact H10.
split; apply carre_scalaire_egalite_distance.
rewrite (homothetie_bipoint (k:=- / 2) (I:=G) (A:=O) (B:=A) (A':=I) (B':=A'));
 auto.
Simplscal.
rewrite (homothetie_bipoint (k:=- / 2) (I:=G) (A:=O) (B:=B) (A':=I) (B':=B'));
 auto.
Simplscal.
repeat rewrite carre_scalaire_distance.
rewrite H9; ring.
apply
 (homothetique_centre_circonscrit (A:=A) (B:=B) (C:=C) (O:=O) (G:=G) (H:=H)
    (I:=I)); auto.
apply centre_gravite_homothetie with (1 := H2); auto.
rewrite H4.
rewrite centre_gravite_ordre_permute.
rewrite centre_gravite_ordre_cycle2; auto.
apply
 (homothetique_centre_circonscrit (A:=A) (B:=B) (C:=C) (O:=O) (G:=G) (H:=H)
    (I:=I)); auto.
apply centre_gravite_homothetie with (1 := H1); auto.
rewrite (homothetie_bipoint (k:=- / 2) (I:=G) (A:=O) (B:=A) (A':=I) (B':=A'));
 auto.
Simplscal.
rewrite (homothetie_bipoint (k:=- / 2) (I:=G) (A:=O) (B:=C) (A':=I) (B':=C'));
 auto.
Simplscal.
repeat rewrite carre_scalaire_distance.
rewrite H10; ring.
apply
 (homothetique_centre_circonscrit (A:=A) (B:=B) (C:=C) (O:=O) (G:=G) (H:=H)
    (I:=I)); auto.
apply centre_gravite_homothetie with (1 := H3); auto.
rewrite H4.
rewrite centre_gravite_ordre_cycle2; auto.
apply
 (homothetique_centre_circonscrit (A:=A) (B:=B) (C:=C) (O:=O) (G:=G) (H:=H)
    (I:=I)); auto.
apply centre_gravite_homothetie with (1 := H1); auto.
Qed.
Comments Image
  "file://C:/Documents and Settings/Frédérique Guilhot/.pcoq/figures/f1043165035.gif".
 
Lemma symetrique_milieu_cercle :
 forall A B C A' B' C' O G H I J : PO,
 triangle A B C ->
 A' = milieu B C ->
 B' = milieu A C ->
 C' = milieu A B ->
 G = centre_gravite A B C ->
 circonscrit O A B C ->
 H = orthocentre A B C ->
 I = milieu O H -> J = symetrie I A' -> sont_cocycliques A' B' C' J.
unfold symetrie in |- *; intros.
unfold sont_cocycliques, circonscrit, isocele in |- *.
exists I.
cut (circonscrit I A' B' C'); intros.
2: apply
    (centre_circonscrit_triangle_homothetique (A:=A) (B:=B) (C:=C) (A':=A')
       (B':=B') (C':=C') (O:=O) (G:=G) (H:=H) (I:=I)); 
    auto.
generalize H9; unfold circonscrit, isocele in |- *; intros.
split; [ try assumption | idtac ].
elim H10; intros H11 H12; try clear H10; try exact H11.
split; [ try assumption | idtac ].
apply carre_scalaire_egalite_distance.
rewrite (homothetie_vecteur (k:=-1) (I:=I) (A:=A') (A':=J)); auto.
Simplscal.
Qed.
 
Lemma symetrique_milieu_milieu :
 forall A B C A' B' C' O G H I J : PO,
 triangle A B C ->
 A' = milieu B C ->
 B' = milieu A C ->
 C' = milieu A B ->
 G = centre_gravite A B C ->
 circonscrit O A B C ->
 H = orthocentre A B C ->
 I = milieu O H -> J = milieu A H -> J = symetrie I A'.
unfold symetrie in |- *; intros.
Comments Image
  "file://C:/Documents and Settings/Frédérique Guilhot/.pcoq/figures/f1043312519.gif".
elim existence_homothetique with (k := -1) (I := I) (A := A'); intros L H13.
rewrite <- H13.
apply vecteur_nul_conf.
Comments Image
  "file://C:/Documents and Settings/Frédérique Guilhot/.pcoq/figures/f1043312668.gif".
cut (vec H L = vec H J); intros.
replace (vec J L) with (add_PP (vec H L) (mult_PP (-1) (vec H J)));
 [ idtac | Ringvec ].
rewrite <- H9; Ringvec.
rewrite (homothetie_bipoint (k:=-1) (I:=I) (A:=O) (B:=A') (A':=H) (B':=L));
 auto with geo.
rewrite (homothetie_bipoint (k:=- / 2) (I:=G) (A:=H) (B:=A) (A':=O) (B':=A'));
 auto.
cut (2 <> 0); intros; auto with real.
replace (mult_PP (-1) (mult_PP (- / 2) (vec H A))) with
 (mult_PP (-1 * - / 2) (vec H A)); [ idtac | Ringvec ].
replace (-1 * - / 2) with (/ 2); [ idtac | ring ].
rewrite (milieu_vecteur2 (A:=H) (B:=A) (M:=J)); auto with geo.
apply (homothetique_orthocentre (A:=A) (B:=B) (C:=C) (O:=O) (G:=G) (H:=H));
 auto.
apply centre_gravite_homothetie with (1 := H1); auto.
Qed.
 
Lemma milieu_sommet_orthocentre_cercle :
 forall A B C A' B' C' O G H I J : PO,
 triangle A B C ->
 A' = milieu B C ->
 B' = milieu A C ->
 C' = milieu A B ->
 G = centre_gravite A B C ->
 circonscrit O A B C ->
 H = orthocentre A B C ->
 I = milieu O H -> J = milieu A H -> sont_cocycliques A' B' C' J.
intros.
apply
 (symetrique_milieu_cercle (A:=A) (B:=B) (C:=C) (A':=A') (B':=B') (C':=C')
    (O:=O) (G:=G) (H:=H) (I:=I) (J:=J)); auto.
apply
 (symetrique_milieu_milieu (A:=A) (B:=B) (C:=C) (A':=A') (B':=B') (C':=C')
    (O:=O) (G:=G) (H:=H) (I:=I) (J:=J)); auto.
Qed.
 
Lemma pied_hauteur_cercle :
 forall A B C A' B' C' O G H I J HA : PO,
 triangle A B C ->
 A' = milieu B C ->
 B' = milieu A C ->
 C' = milieu A B ->
 G = centre_gravite A B C ->
 circonscrit O A B C ->
 H = orthocentre A B C ->
 I = milieu O H ->
 J = milieu A H ->
 HA = projete_orthogonal B C A -> sont_cocycliques A' B' C' HA.
intros.
generalize
 (orthogonal_diametre_cercle (A:=A') (B:=B') (C:=C') (A':=J) (O:=I));
 intros H14; apply H14.
apply triangle_triangle_milieux with (1 := H0); auto with geo.
generalize
 (centre_circonscrit_triangle_homothetique (A:=A) (B:=B) (C:=C) (A':=A')
    (B':=B') (C':=C') (O:=O) (G:=G) (H:=H)); intros H19; 
 apply H19; auto.
apply symetrie_milieu.
generalize
 (symetrique_milieu_milieu (A:=A) (B:=B) (C:=C) (A':=A') (B':=B') (C':=C')
    (O:=O) (G:=G) (H:=H)); intros H19; apply H19; auto.
deroule_triangle A B C.
elim def_projete_orthogonal2 with (A := B) (B := C) (C := A) (H := HA);
 [ intros | auto | auto ].
halignes H15 ipattern:k.
cut (alignes B C A'); intros; auto with geo.
halignes H18 ipattern:k0.
cut (orthogonal (vec B C) (vec HA J)); intros.
replace (vec HA A') with (add_PP (vec B A') (mult_PP (-1) (vec B HA)));
 [ idtac | Ringvec ].
rewrite H19; rewrite H17.
replace (mult_PP (-1) (mult_PP k (vec B C))) with (mult_PP (- k) (vec B C));
 [ idtac | Ringvec ].
Simplortho.
apply ortho_sym.
cut (alignes A H J); intros; auto with geo.
cut (alignes A HA H); intros.
halignes H20 ipattern:x.
assert (J = A).
rewrite H8; rewrite <- H20; auto with geo.
rewrite H22; auto with geo.
halignes H21 ipattern:y.
absurd (A = HA); auto.
red in |- *; intros; apply H10.
rewrite H21; auto with geo.
replace (vec HA J) with (add_PP (vec HA A) (vec A J)); [ idtac | Ringvec ].
rewrite H22; rewrite H23.
replace (add_PP (vec HA A) (mult_PP x (mult_PP y (vec A HA)))) with
 (mult_PP (1 + - (x * y)) (vec HA A)); [ idtac | Ringvec ].
Simplortho.
elim orthocentre_def2 with (A := A) (B := B) (C := C) (H := H);
 [ intros; elim H21; intros H23 H24; try clear H21 orthocentre_def2;
    try exact H24
 | auto ].
discrimine H A.
elim
 orthogonal_colineaires
  with (A := B) (B := C) (C := H) (D := A) (E := HA) (F := A);
 [ intros k1 H26; try clear orthogonal_colineaires
 | auto with geo
 | auto with geo
 | auto with geo
 | auto with geo ].
cut (alignes A H HA); intros.
apply alignes_ordre_permute; try trivial.
apply colineaire_alignes with k1.
replace (vec A HA) with (mult_PP (-1) (vec HA A)); [ idtac | Ringvec ].
rewrite H26; Ringvec.
Qed.
Hint Resolve orthocentre_ordre: geo.
 
Theorem cercle_neuf_points :
 forall A B C A' B' C' O G H I J K L H1 H2 H3 : PO,
 triangle A B C ->
 A' = milieu B C ->
 B' = milieu A C ->
 C' = milieu A B ->
 G = centre_gravite A B C ->
 circonscrit O A B C ->
 H = orthocentre A B C ->
 I = milieu O H ->
 J = milieu A H ->
 K = milieu B H ->
 L = milieu C H ->
 H1 = projete_orthogonal B C A ->
 H2 = projete_orthogonal C A B ->
 H3 = projete_orthogonal A B C ->
 (sont_cocycliques A' B' C' J /\ sont_cocycliques A' B' C' H1) /\
 (sont_cocycliques A' B' C' K /\ sont_cocycliques A' B' C' H2) /\
 sont_cocycliques A' B' C' L /\ sont_cocycliques A' B' C' H3.
intros.
split; [ try assumption | idtac ].
split; [ try assumption | idtac ].
apply
 (symetrique_milieu_cercle (A:=A) (B:=B) (C:=C) (A':=A') (B':=B') (C':=C')
    (O:=O) (G:=G) (H:=H) (I:=I)); auto.
apply
 (symetrique_milieu_milieu (A:=A) (B:=B) (C:=C) (A':=A') (B':=B') (C':=C')
    (O:=O) (G:=G) (H:=H) (I:=I) (J:=J)); auto.
Comments Image
  "file://C:/Documents and Settings/Frédérique Guilhot/.pcoq/figures/f1043314145.gif".
apply
 (pied_hauteur_cercle (A:=A) (B:=B) (C:=C) (A':=A') (B':=B') (C':=C') (O:=O)
    (G:=G) (H:=H) (I:=I) (J:=J) (HA:=H1)); auto.
split; [ split; [ try assumption | idtac ] | idtac ].
cut (sont_cocycliques B' C' A' K); intros; auto with geo.
apply
 (symetrique_milieu_cercle (A:=B) (B:=C) (C:=A) (A':=B') (B':=C') (C':=A')
    (O:=O) (G:=G) (H:=H) (I:=I)); auto with geo.
rewrite H7; apply centre_gravite_ordre_cycle.
apply circonscrit_permute; apply circonscrit_permute; auto with geo.
apply
 (symetrique_milieu_milieu (A:=B) (B:=C) (C:=A) (A':=B') (B':=C') (C':=A')
    (O:=O) (G:=G) (H:=H) (I:=I) (J:=K)); auto with geo.
rewrite H7; apply centre_gravite_ordre_cycle.
apply circonscrit_permute; apply circonscrit_permute; auto.
cut (sont_cocycliques B' C' A' H2); intros; auto with geo.
apply
 (pied_hauteur_cercle (A:=B) (B:=C) (C:=A) (A':=B') (B':=C') (C':=A') (O:=O)
    (G:=G) (H:=H) (I:=I) (J:=K) (HA:=H2)); auto with geo.
rewrite H7; apply centre_gravite_ordre_cycle.
apply circonscrit_permute; apply circonscrit_permute; auto.
split; [ try assumption | idtac ].
cut (sont_cocycliques C' A' B' L); intros.
apply cocycliques_ordre_cycle2; auto.
apply
 (symetrique_milieu_cercle (A:=C) (B:=A) (C:=B) (A':=C') (B':=A') (C':=B')
    (O:=O) (G:=G) (H:=H) (I:=I) (J:=L)); auto with geo.
rewrite H7; apply centre_gravite_ordre_cycle2.
apply circonscrit_permute; auto.
apply
 (symetrique_milieu_milieu (A:=C) (B:=A) (C:=B) (A':=C') (B':=A') (C':=B')
    (O:=O) (G:=G) (H:=H) (I:=I) (J:=L)); auto with geo.
rewrite H7; apply centre_gravite_ordre_cycle2.
apply circonscrit_permute; auto.
cut (sont_cocycliques C' A' B' H3); intros.
apply cocycliques_ordre_cycle2; auto with geo.
apply
 (pied_hauteur_cercle (A:=C) (B:=A) (C:=B) (A':=C') (B':=A') (C':=B') (O:=O)
    (G:=G) (H:=H) (I:=I) (J:=L) (HA:=H3)); auto with geo.
rewrite H7; apply centre_gravite_ordre_cycle2.
apply circonscrit_permute; auto.
Qed.
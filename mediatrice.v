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


Require Export angles_droites.
Require Export metrique_triangle.
Set Implicit Arguments.
Unset Strict Implicit.
 
Definition mediatrice (A B M : PO) := distance M A = distance M B :>R.
 
Lemma mediatrice_permute :
 forall A B M : PO, mediatrice A B M -> mediatrice B A M.
unfold mediatrice in |- *; intros.
rewrite H; auto.
Qed.
Hint Immediate mediatrice_permute: geo.
 
Lemma milieu_mediatrice :
 forall A B M : PO, M = milieu A B :>PO -> mediatrice A B M.
red in |- *; intros.
cut (vec A M = vec M B); intros; auto with geo.
Qed.
 
Lemma alignes_mediatrice_milieu :
 forall A B M : PO,
 A <> B -> alignes A B M -> mediatrice A B M -> M = milieu A B :>PO.
unfold mediatrice in |- *; intros.
halignes H0 ipattern:k.
cut (k = / 2); intros.
rewrite H3 in H2.
apply vecteur_milieu; auto.
cut (vec M B = mult_PP (1 + - k) (vec A B)); intros.
cut (scalaire (vec A M) (vec A M) = scalaire (vec M B) (vec M B)); intros.
rewrite H2 in H4.
rewrite H3 in H4.
cut (k * k = (1 + - k) * (1 + - k)); intros; auto with real.
apply
 resolution2
  with
    (x := scalaire (vec A B) (vec A B))
    (y := scalaire (vec A B) (vec A B)); auto with geo.
replace (scalaire (vec A B) (vec A B) * (k * k)) with
 (scalaire (mult_PP k (vec A B)) (mult_PP k (vec A B))).
rewrite H4.
Simplscal.
ring_simplify.
Simplscal.
replace (scalaire (vec A M) (vec A M)) with (scalaire (vec M A) (vec M A)).
repeat rewrite carre_scalaire_distance; rewrite H1; auto.
replace (vec M A) with (mult_PP (-1) (vec A M)).
Simplscal.
Ringvec.
replace (vec M B) with (add_PP (vec A B) (mult_PP (-1) (vec A M))).
rewrite H2.
Ringvec.
Ringvec.
Qed.
 
Lemma mediatrice_projete_orthogonal :
 forall A B M H : PO,
 A <> B :>PO ->
 H = projete_orthogonal A B M :>PO ->
 mediatrice A B M -> distance H A = distance H B :>R.
unfold mediatrice in |- *; intros.
generalize (Pythagore_projete_orthogonal (A:=A) (B:=B) (C:=M) (H:=H)); intros.
elim H3; [ try clear H3; intros | auto | auto ].
apply distance_carre.
replace (Rsqr (distance H A)) with
 (Rsqr (distance A M) + - Rsqr (distance H M)).
replace (Rsqr (distance H M)) with
 (Rsqr (distance B M) + - Rsqr (distance H B)).
rewrite (distance_sym A M); auto.
rewrite (distance_sym B M); auto.
rewrite H2; ring.
rewrite H4; ring.
rewrite H3; ring.
Qed.
 
Lemma mediatrice_projete_milieu :
 forall A B M H : PO,
 A <> B :>PO ->
 H = projete_orthogonal A B M :>PO -> mediatrice A B M -> H = milieu A B :>PO.
intros.
generalize (def_projete_orthogonal2 (A:=A) (B:=B) (C:=M) (H:=H)); intros.
elim H3; [ intros; clear H3 | auto | auto ].
apply alignes_mediatrice_milieu; auto.
red in |- *.
apply mediatrice_projete_orthogonal with M; auto.
Qed.
 
Lemma mediatrice_orthogonale_segment_milieu :
 forall A B M N : PO,
 A <> B :>PO ->
 M <> N :>PO ->
 M = milieu A B :>PO -> mediatrice A B N -> orthogonal (vec A B) (vec M N).
intros A B M N H3 H0 H1 H2; try assumption.
elim existence_projete_orthogonal with (A := A) (B := B) (C := N);
 [ intros H H4; try clear existence_projete_orthogonal; auto | auto ].
generalize (mediatrice_projete_milieu (A:=A) (B:=B) (M:=N) (H:=H)); intros H7.
rewrite H1; rewrite <- H7; auto.
generalize (def_projete_orthogonal2 (A:=A) (B:=B) (C:=N) (H:=H)); intros.
elim H5; [ intros; auto | auto | auto ].
Qed.
 
Lemma mediatrice_orthogonale_segment :
 forall A B M N : PO,
 A <> B :>PO ->
 mediatrice A B M -> mediatrice A B N -> orthogonal (vec M N) (vec A B).
intros.
discrimine M N.
VReplace (vec N N) zero.
auto with geo.
elim (classic (milieu A B = M)); intros.
rewrite <- H3; rewrite <- H3 in H0.
apply ortho_sym.
apply mediatrice_orthogonale_segment_milieu; auto.
rewrite H3; auto.
elim (classic (milieu A B = N)); intros.
rewrite <- H4; rewrite <- H4 in H2.
replace (vec M (milieu A B)) with
 (add_PP (mult_PP 0 (vec (milieu A B) M)) (mult_PP (-1) (vec (milieu A B) M))).
apply ortho_combinaison_lineaire; auto.
apply ortho_sym; apply mediatrice_orthogonale_segment_milieu; auto.
apply ortho_sym; apply mediatrice_orthogonale_segment_milieu; auto.
Ringvec.
cut (orthogonal (vec (milieu A B) N) (vec A B)); intros.
cut (orthogonal (vec (milieu A B) M) (vec A B)); intros.
replace (vec M N) with
 (add_PP (mult_PP 1 (vec (milieu A B) N)) (mult_PP (-1) (vec (milieu A B) M))).
apply ortho_combinaison_lineaire; auto with geo.
Ringvec.
apply ortho_sym; apply mediatrice_orthogonale_segment_milieu; auto with geo.
apply ortho_sym; apply mediatrice_orthogonale_segment_milieu; auto with geo.
Qed.
 
Lemma orthogonale_segment_milieu_mediatrice :
 forall A B M N : PO,
 A <> B :>PO ->
 M = milieu A B :>PO -> orthogonal (vec A B) (vec M N) -> mediatrice A B N.
unfold mediatrice in |- *; intros.
apply carre_egalite_distance.
repeat rewrite <- carre_scalaire_distance.
generalize (rectangle_Pythagore M N A); unfold iff in |- *; intros.
generalize (rectangle_Pythagore M N B); unfold iff in |- *; intros.
elim H2; [ intros H4 H7; try clear H2 ].
elim H3; [ intros H5 H6; try clear H3 ].
cut (orthogonal (vec M N) (vec M A)); intros.
rewrite H4; auto.
rewrite H5.
replace (scalaire (vec M A) (vec M A)) with (scalaire (vec A M) (vec A M)).
rewrite (milieu_vecteur H0); auto.
replace (vec M A) with (mult_PP (-1) (vec A M)).
Simplscal.
Ringvec.
rewrite <- (milieu_vecteur H0); auto.
auto with geo.
apply ortho_sym.
replace (vec M A) with (mult_PP (- / 2) (vec A B)).
auto with geo.
replace (vec M A) with (mult_PP (-1) (mult_PP (/ 2) (vec A B))).
cut (2 <> 0); intros; auto with real.
Fieldvec 2.
rewrite <- (milieu_vecteur2 H0); auto.
Ringvec.
Qed.
 
Lemma mediatrice_distinct_extremite :
 forall A B M : PO, A <> B -> mediatrice A B M -> M <> A /\ M <> B.
unfold mediatrice in |- *; intros.
cut (~ (M = A \/ M = B)); intros.
intuition.
unfold not in |- *; intros; apply H.
elim H1;
 [ intros H2; try clear H1; rewrite <- H2; rewrite <- H2 in H0
 | intros H2; try clear H1; rewrite <- H2; rewrite <- H2 in H0 ].
apply distance_nulle; auto.
rewrite carre_scalaire_distance; rewrite <- H0;
 rewrite <- carre_scalaire_distance.
replace (vec M M) with (mult_PP 0 (vec A B)).
Simplscal.
Ringvec.
apply distance_nulle.
replace (vec A M) with (mult_PP (-1) (vec M A)).
Simplscal.
rewrite carre_scalaire_distance; rewrite H0;
 rewrite <- carre_scalaire_distance.
replace (vec M M) with (mult_PP 0 (vec A B)).
Simplscal.
Ringvec.
Ringvec.
Qed.
 
Lemma existence_mediatrice :
 forall A B : PO,
 A <> B :>PO -> ex (fun J : PO => milieu A B <> J :>PO /\ mediatrice A B J).
intros.
soit_milieu A B ipattern:M.
soit_orthogonal M A ipattern:J.
exists J.
split; [ try assumption | idtac ].
apply orthogonale_segment_milieu_mediatrice with M; auto.
apply orthogonal_milieu with M; auto.
Qed.
Comments " " "soit_mediatrice" "pose" "IJ" "mediatrice" "de" "[AB]" "avec"
  "I" "milieu" "de" "AB" "et" "echoue" "si" "A=B" "et" "ajoute" "des"
  "hypotheses".
 
Ltac soit_mediatrice A B I J :=
  soit_milieu A B I;
   match goal with
   | h:(I = milieu A B) |- _ =>
       elim (existence_mediatrice (A:=A) (B:=B));
        [ intros J; intros HME; rewrite <- h in HME; elim HME; clear HME;
           intros; generalize h; intros; clear h;
           lapply (mediatrice_distinct_extremite (A:=A) (B:=B) (M:=J));
           try assumption; intros toto; elim toto; 
           try assumption; clear toto; intros
        | auto ]
   end.
 
Lemma mediatrice_milieu_angles :
 forall A B M N : PO,
 A <> B ->
 M <> N ->
 M = milieu A B ->
 mediatrice A B N ->
 cons_AV (vec N A) (vec N M) = cons_AV (vec N M) (vec N B) :>AV.
intros.
elim mediatrice_distinct_extremite with (A := A) (B := B) (M := N);
 (auto; intros).
cut (M <> A); intros.
cut (M <> B); intros.
elim
 cas_egalite_triangle_indirect
  with (A := M) (B := N) (C := A) (A' := M) (B' := N) (C' := B);
 (auto with geo; intros).
elim H8; intros H9 H10; try clear H8; try exact H9.
symmetry  in |- *.
generalize (milieu_angles_orthogonaux (A:=A) (B:=B) (M:=M) (N:=N)); intros.
mesure M A M N.
rewrite <- (mes_oppx (A:=M) (B:=A) (C:=M) (D:=N) (x:=x)); auto.
rewrite <- (mes_oppx (A:=M) (B:=N) (C:=M) (D:=B) (x:=x)); auto.
rewrite H8; rewrite H7; auto.
apply mediatrice_orthogonale_segment_milieu; auto.
lapply (milieu_distinct2 (A:=A) (B:=B)); auto; intros.
rewrite H1; auto.
lapply (milieu_distinct (A:=A) (B:=B)); auto; intros.
rewrite H1; auto.
Qed.
Require Export Droite_espace.
 
Lemma mediatrices_triangle_concours :
 forall A B C I J K L : PO,
 triangle A B C ->
 I = milieu A B :>PO ->
 J = milieu B C :>PO ->
 I <> K :>PO ->
 J <> L :>PO ->
 mediatrice A B K -> mediatrice B C L -> concours (droite I K) (droite J L).
intros.
deroule_triangle A B C.
lapply (position_relative_droites_coplanaires (A:=I) (B:=K) (C:=J) (D:=L));
 auto with geo; intros.
elim H10; auto with geo; intros.
absurd (paralleles (droite J L) (droite I K)); auto with geo.
cut
 (double_AV (cons_AV (vec I K) (vec J L)) =
  double_AV (cons_AV (vec B A) (vec B C))); intros.
apply angle_non_paralleles; auto.
rewrite H12.
red in |- *; intros.
apply H6; auto with geo.
apply angles_droites_orthogonales; auto.
cut (orthogonal (vec I K) (vec A B)); intros; auto with geo.
apply mediatrice_orthogonale_segment; auto.
apply milieu_mediatrice; auto.
apply ortho_sym; auto.
apply mediatrice_orthogonale_segment; auto.
apply milieu_mediatrice; auto.
Qed.
 
Lemma mediatrice_droite :
 forall A B I J K : PO,
 A <> B :>PO ->
 I = milieu A B :>PO -> mediatrice A B J -> mediatrice A B K -> alignes I J K.
intros.
discrimine I J.
discrimine J K.
discrimine I K.
lapply (milieu_mediatrice (A:=A) (B:=B) (M:=I)); auto; intros.
lapply (mediatrice_orthogonale_segment (A:=A) (B:=B) (M:=I) (N:=J)); auto;
 intros.
lapply (mediatrice_orthogonale_segment (A:=A) (B:=B) (M:=I) (N:=K)); auto;
 intros.
elim (orthogonal_paralleles (A:=I) (B:=B) (C:=J) (E:=I) (F:=K)); auto; intros.
apply colineaire_alignes with x; auto.
lapply (milieu_distinct2 (A:=A) (B:=B)); auto.
rewrite <- H0; auto.
lapply (orthogonal_segment_milieu (A:=A) (B:=B) (C:=I) (D:=J) (I:=I)); auto;
 intros.
elim H9; auto with geo; intros.
apply ortho_sym.
lapply (orthogonal_segment_milieu (A:=A) (B:=B) (C:=I) (D:=K) (I:=I)); auto;
 intros.
elim H9; auto with geo; intros.
Qed.

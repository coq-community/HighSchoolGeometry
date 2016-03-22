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


Require Export isocele.
Set Implicit Arguments.
Unset Strict Implicit.
Parameter reflexion : PO -> PO -> PO -> PO.
 
Axiom
  reflexion_def :
    forall A B M M' H : PO,
    A <> B ->
    H = projete_orthogonal A B M ->
    M' = reflexion A B M -> vec M M' = mult_PP 2 (vec M H).
 
Axiom
  reflexion_def2 :
    forall A B M M' H : PO,
    A <> B ->
    H = projete_orthogonal A B M ->
    vec M M' = mult_PP 2 (vec M H) -> M' = reflexion A B M.
 
Lemma reflexion_axe :
 forall A B M : PO, A <> B -> alignes A B M -> M = reflexion A B M.
intros A B M H2 H0; try assumption.
elim existence_projete_orthogonal with (A := A) (B := B) (C := M);
 [ intros H H3; try clear existence_projete_orthogonal; try exact H3 | auto ].
apply reflexion_def2 with H; auto.
cut (M = H); intros.
rewrite <- H1; Ringvec.
rewrite H3.
apply def_projete_orthogonal; auto.
replace (vec M M) with zero; auto with geo.
Ringvec.
Qed.
Hint Resolve reflexion_axe: geo.
 
Lemma reflexion_projete_orthogonal_milieu :
 forall A B M M' H : PO,
 A <> B ->
 H = projete_orthogonal A B M -> M' = reflexion A B M -> H = milieu M M'.
intros.
generalize (reflexion_def (A:=A) (B:=B) (M:=M) (M':=M') (H:=H)); intros H5.
cut (2 <> 0); intros.
apply vecteur_milieu.
rewrite H5; auto.
replace (mult_PP (/ 2) (mult_PP 2 (vec M H))) with
 (mult_PP (/ 2 * 2) (vec M H)).
replace (/ 2 * 2) with 1.
Ringvec.
auto with real.
Ringvec.
discrR.
Qed.
 
Lemma reflexion_image_distinct :
 forall A B M M' : PO, ~ alignes A B M -> M' = reflexion A B M -> M <> M'.
intros A B M M' H0 H1; try assumption.
cut (A <> B); intros H2; [ idtac | auto with geo ].
elim existence_projete_orthogonal with (A := A) (B := B) (C := M);
 [ intros H H3; try clear existence_projete_orthogonal; try exact H3 | auto ].
generalize (reflexion_def (A:=A) (B:=B) (M:=M) (M':=M') (H:=H)); intros H5.
generalize
 (reflexion_projete_orthogonal_milieu (A:=A) (B:=B) (M:=M) (M':=M') (H:=H));
 intros.
cut (M <> H); intros.
apply dist_non_nulle.
unfold not in |- *; intros; apply H6.
apply distance_nulle.
rewrite (milieu_vecteur2 (A:=M) (B:=M') (M:=H)); auto.
Simplscal.
rewrite carre_scalaire_distance; rewrite H7; ring.
unfold not in |- *; intros; apply H0.
rewrite H6.
elim def_projete_orthogonal2 with (A := A) (B := B) (C := M) (H := H);
 [ intros; try exact H7 | auto | auto ].
Qed.
 
Lemma reflexion_mediatrice :
 forall A B M M' : PO,
 ~ alignes A B M ->
 M' = reflexion A B M -> mediatrice M M' A /\ mediatrice M M' B.
intros A B M M' H1 H3; try assumption.
cut (A <> B); intros H0; [ idtac | auto with geo ].
elim existence_projete_orthogonal with (A := A) (B := B) (C := M);
 [ intros H H2; try clear existence_projete_orthogonal | auto ].
generalize (reflexion_image_distinct (A:=A) (B:=B) (M:=M) (M':=M'));
 intros H5.
generalize
 (reflexion_projete_orthogonal_milieu (A:=A) (B:=B) (M:=M) (M':=M') (H:=H));
 intros.
generalize (reflexion_def (A:=A) (B:=B) (M:=M) (M':=M') (H:=H)); intros.
elim def_projete_orthogonal2 with (A := A) (B := B) (C := M) (H := H);
 [ intros | auto | auto ].
halignes H7 ipattern:k.
split; [ try assumption | idtac ].
elim (classic (H = A)); intros.
rewrite <- H10.
apply milieu_mediatrice; auto.
apply orthogonale_segment_milieu_mediatrice with H; auto.
apply ortho_sym.
cut (orthogonal (vec A B) (vec M M')); intros.
replace (vec H A) with (mult_PP (- k) (vec A B)).
Simplortho.
replace (vec H A) with (mult_PP (-1) (vec A H)).
rewrite H9.
Ringvec.
Ringvec.
apply ortho_sym.
rewrite H6; auto.
Simplortho.
elim (classic (H = B)); intros.
rewrite <- H10.
apply milieu_mediatrice; auto.
apply orthogonale_segment_milieu_mediatrice with H; auto.
apply ortho_sym.
cut (orthogonal (vec A B) (vec M M')); intros.
replace (vec H B) with
 (add_PP (mult_PP (- k) (vec A B)) (mult_PP 1 (vec A B))).
Simplortho.
replace (mult_PP (- k) (vec A B)) with (mult_PP (-1) (mult_PP k (vec A B))).
rewrite <- H9.
Ringvec.
Ringvec.
apply ortho_sym.
rewrite H6; auto.
Simplortho.
Qed.
 
Lemma reflexion_axe_orthogonal_segment :
 forall A B M M' : PO,
 ~ alignes A B M -> M' = reflexion A B M -> orthogonal (vec M M') (vec A B).
intros.
assert (A <> B); auto with geo.
apply ortho_sym; auto.
elim (reflexion_mediatrice (A:=A) (B:=B) (M:=M) (M':=M')); auto; intros.
apply mediatrice_orthogonale_segment; auto.
apply reflexion_image_distinct with (2 := H0); auto.
Qed.
 
Lemma projete_orthogonal_image :
 forall A B M M' H : PO,
 A <> B ->
 H = projete_orthogonal A B M ->
 M' = reflexion A B M -> H = projete_orthogonal A B M'.
intros.
generalize (reflexion_def (A:=A) (B:=B) (M:=M) (M':=M') (H:=H)); intros H5.
generalize
 (reflexion_projete_orthogonal_milieu (A:=A) (B:=B) (M:=M) (M':=M') (H:=H));
 intros.
elim def_projete_orthogonal2 with (A := A) (B := B) (C := M) (H := H);
 [ intros | auto | auto ].
apply def_projete_orthogonal; auto.
apply ortho_sym.
replace (vec H M') with (vec M H); auto with geo.
Qed.
 
Lemma non_axe_image_non_axe :
 forall A B M M' : PO,
 ~ alignes A B M -> M' = reflexion A B M -> ~ alignes A B M'.
intros A B M M' H0 H2; try assumption.
cut (A <> B); intros H1; [ idtac | auto with geo ].
elim existence_projete_orthogonal with (A := A) (B := B) (C := M);
 [ intros H H3; try clear existence_projete_orthogonal; try exact H3 | auto ].
generalize (reflexion_def (A:=A) (B:=B) (M:=M) (M':=M') (H:=H)); intros H5.
generalize
 (reflexion_projete_orthogonal_milieu (A:=A) (B:=B) (M:=M) (M':=M') (H:=H));
 intros.
elim reflexion_mediatrice with (A := A) (B := B) (M := M) (M' := M');
 [ intros H6 H7; try clear reflexion_mediatrice; try exact H7 | auto | auto ].
generalize (mediatrice_orthogonale_segment (A:=M) (B:=M') (M:=A) (N:=B));
 intros.
generalize (reflexion_image_distinct (A:=A) (B:=B) (M:=M) (M':=M')); intros.
elim def_projete_orthogonal2 with (A := A) (B := B) (C := M) (H := H);
 [ intros | auto | auto ].
cut (H = projete_orthogonal A B M'); intros.
cut (M' <> H); intros.
unfold not in |- *; intros; apply H13.
rewrite H12.
apply def_projete_orthogonal; auto.
replace (vec M' M') with zero.
apply zero_ortho_tout.
Ringvec.
rewrite H4; auto.
apply milieu_distinct2; auto.
apply projete_orthogonal_image with M; auto.
Qed.
 
Lemma reflexion_symetrie :
 forall A B M M' : PO, A <> B -> M' = reflexion A B M -> M = reflexion A B M'.
intros A B M M' H1 H0; try assumption.
elim (classic (alignes A B M)); intros H20.
rewrite H0.
rewrite <- reflexion_axe.
rewrite <- reflexion_axe; auto.
auto.
rewrite <- reflexion_axe; auto.
elim existence_projete_orthogonal with (A := A) (B := B) (C := M);
 [ intros H H3; try clear existence_projete_orthogonal; try exact H3 | auto ].
generalize (reflexion_def (A:=A) (B:=B) (M:=M) (M':=M') (H:=H)); intros H5.
generalize
 (reflexion_projete_orthogonal_milieu (A:=A) (B:=B) (M:=M) (M':=M') (H:=H));
 intros.
generalize (projete_orthogonal_image (A:=A) (B:=B) (M:=M) (M':=M') (H:=H));
 intros.
generalize (non_axe_image_non_axe (A:=A) (B:=B) (M:=M) (M':=M')); intros.
apply reflexion_def2 with H; auto with geo.
Qed.
 
Lemma reflexion_isocele :
 forall A B M M' : PO, A <> B -> M' = reflexion A B M -> isocele A M M'.
intros.
elim (classic (alignes A B M)); intros.
replace M' with M; auto.
unfold isocele in |- *; auto.
rewrite H0; rewrite <- reflexion_axe; auto.
apply mediatrice_isocele.
elim (reflexion_mediatrice (A:=A) (B:=B) (M:=M) (M':=M')); auto.
Qed.
 
Lemma axe_reflexion_droite :
 forall A B C M M' : PO,
 A <> B ->
 A <> C -> alignes A B C -> M' = reflexion A B M -> M' = reflexion C A M.
intros A B C M M' H10 H0 H1 H2; try assumption.
elim existence_projete_orthogonal with (A := A) (B := B) (C := M);
 [ intros H H4; try clear existence_projete_orthogonal; try exact H3 | auto ].
halignes H1 ipattern:k.
elim def_projete_orthogonal2 with (A := A) (B := B) (C := M) (H := H);
 [ intros | auto | auto ].
apply reflexion_def2 with H; auto.
apply def_projete_orthogonal.
auto.
halignes H5 ipattern:k0.
elim (classic (k = 0)); intros.
absurd (A = C); auto.
rewrite H8 in H3.
apply conversion_PP with (a := 1) (b := 1); auto with real.
RingPP2 H3.
Ringvec.
apply colineaire_alignes with (/ k * (k + - k0)).
replace (vec C H) with (add_PP (vec A H) (mult_PP (-1) (vec A C))).
replace (vec C A) with (mult_PP (-1) (vec A C)).
rewrite H7; rewrite H3.
replace (mult_PP (/ k * (k + - k0)) (mult_PP (-1) (mult_PP k (vec A B))))
 with (mult_PP (/ k * (k + - k0) * (-1 * k)) (vec A B)).
replace (/ k * (k + - k0) * (-1 * k)) with (/ k * k * (-1 * (k + - k0))).
replace (/ k * k) with 1.
Ringvec.
auto with real.
ring.
Ringvec.
Ringvec.
Ringvec.
replace (vec C A) with
 (add_PP (mult_PP 0 (vec A B)) (mult_PP (- k) (vec A B))).
apply ortho_combinaison_lineaire; auto.
replace (vec C A) with (mult_PP (-1) (vec A C)).
rewrite H3.
Ringvec.
Ringvec.
rewrite (reflexion_def (A:=A) (B:=B) (M:=M) (M':=M') (H:=H)); auto.
Qed.
 
Theorem axe_reflexion_bissectrice :
 forall A B M M' : PO,
 ~ alignes A B M ->
 M' = reflexion A B M ->
 cons_AV (vec A M) (vec A B) = cons_AV (vec A B) (vec A M').
intros A B M M' H1 H2; try assumption.
cut (A <> B); intros H0; [ idtac | auto with geo ].
elim existence_projete_orthogonal with (A := A) (B := B) (C := M);
 [ intros H H4; try clear existence_projete_orthogonal; try exact H3 | auto ].
generalize (non_axe_image_non_axe (A:=A) (B:=B) (M:=M) (M':=M')); intros.
generalize (non_alignes_distincts (A:=A) (B:=B) (C:=M')); intros.
generalize (non_alignes_distincts (A:=A) (B:=B) (C:=M)); intros.
elim def_projete_orthogonal2 with (A := A) (B := B) (C := M) (H := H);
 [ intros; try exact H13 | auto | auto ].
elim (classic (A = H)); intros.
generalize
 (reflexion_projete_orthogonal_milieu (A:=A) (B:=B) (M:=M) (M':=M') (H:=H));
 intros.
apply milieu_angles_orthogonaux; auto.
apply reflexion_image_distinct with (2 := H2); auto.
rewrite H9; auto.
generalize (reflexion_def (A:=A) (B:=B) (M:=M) (M':=M') (H:=H)); intros.
replace (vec M M') with
 (add_PP (mult_PP (-1) (vec H M)) (mult_PP (-1) (vec H M))).
apply ortho_combinaison_lineaire; apply ortho_sym; auto.
rewrite H11; auto.
Ringvec.
cut (cons_AV (vec A M) (vec A H) = cons_AV (vec A H) (vec A M')); intros;
 auto.
rewrite angles_representants_unitaires; auto.
rewrite angles_representants_unitaires; auto.
elim existence_representant_unitaire with (A := A) (B := H);
 [ intros; try clear existence_representant_unitaire | auto ].
elim existence_representant_unitaire with (A := A) (B := M');
 [ intros; try clear existence_representant_unitaire | auto ].
elim existence_representant_unitaire with (A := A) (B := M);
 [ intros; try clear existence_representant_unitaire | auto ].
elim alignes_representant_unitaire with (A := A) (B := B) (C := H);
 [ intros; try clear alignes_representant_unitaire; auto
 | intros; auto
 | auto
 | auto
 | auto ].
rewrite H14.
rewrite <- angles_representants_unitaires; auto.
rewrite <- angles_representants_unitaires; auto.
replace (representant_unitaire (vec A B)) with
 (mult_PP (-1) (representant_unitaire (vec A H))).
cut (A <> x); intros.
replace (mult_PP (-1) (representant_unitaire (vec A H))) with (vec x A).
replace (cons_AV (representant_unitaire (vec A M)) (vec x A)) with
 (plus (cons_AV (representant_unitaire (vec A M)) (vec A x))
    (cons_AV (vec A x) (vec x A))).
replace (cons_AV (vec x A) (representant_unitaire (vec A M'))) with
 (plus (cons_AV (vec x A) (vec A x))
    (cons_AV (vec A x) (representant_unitaire (vec A M')))).
rewrite <- angle_plat; auto.
rewrite <- angle_plat; auto.
rewrite H11.
rewrite <- angles_representants_unitaires; auto.
rewrite <- angles_representants_unitaires; auto.
rewrite <- H10; auto.
mesure A M A H.
replace (x2 + pi) with (pi + x2); (try ring; auto).
rewrite <- H12.
cut (A <> x0); intros.
rewrite Chasles; auto.
apply distance_non_nulle.
elim def_representant_unitaire2 with (A := A) (B := M') (C := x0);
 [ intros; elim H17; intros H22 H23; try clear H17 def_representant_unitaire2;
    rewrite H22; try discrR
 | auto
 | auto ].
rewrite <- H13.
cut (A <> x1); intros.
rewrite Chasles; auto.
apply distance_non_nulle.
elim def_representant_unitaire2 with (A := A) (B := M) (C := x1);
 [ intros; elim H17; intros H22 H23; try clear H18 def_representant_unitaire2;
    rewrite H22; try discrR
 | auto
 | auto ].
rewrite <- H11; Ringvec.
apply distance_non_nulle.
elim def_representant_unitaire2 with (A := A) (B := H) (C := x);
 [ intros; elim H16; intros H22 H23; try clear H18 def_representant_unitaire2;
    rewrite H22; try discrR
 | auto
 | auto ].
rewrite H14.
elim existence_representant_unitaire with (A := A) (B := B);
 [ intros; try clear existence_representant_unitaire | auto ].
rewrite <- H15; Ringvec.
generalize (reflexion_image_distinct (A:=A) (B:=B) (M:=M) (M':=M')); intros.
generalize (reflexion_mediatrice (A:=A) (B:=B) (M:=M) (M':=M')); intros.
elim H11; auto; intros.
generalize
 (reflexion_projete_orthogonal_milieu (A:=A) (B:=B) (M:=M) (M':=M') (H:=H));
 intros.
apply mediatrice_milieu_angles; auto.
Qed.
 
Lemma reflexion_isocele2 :
 forall A B M M' : PO, A <> B -> M' = reflexion A B M -> isocele B M M'.
intros.
apply reflexion_isocele with A; auto.
apply axe_reflexion_droite with B; auto with geo.
Qed.
 
Lemma reflexion_inverse_angle :
 forall A B M M' : PO,
 A <> B ->
 M <> A ->
 M <> B ->
 M' = reflexion A B M ->
 cons_AV (vec M' A) (vec M' B) = opp (cons_AV (vec M A) (vec M B)).
intros.
elim (classic (alignes A B M)); intros.
replace M' with M; auto.
cut (double_AV (cons_AV (vec M A) (vec M B)) = image_angle 0); intros.
replace (opp (cons_AV (vec M A) (vec M B))) with
 (plus (image_angle 0) (opp (cons_AV (vec M A) (vec M B)))); 
 auto.
rewrite <- H4; unfold double_AV in |- *.
mesure M A M B.
replace (x + x + - x) with x; auto.
ring.
mesure M A M B.
replace (0 + - x) with (- x); auto.
ring.
apply angle_alignes; auto with geo.
rewrite H2; rewrite <- reflexion_axe; auto.
cut (M <> M'); intros.
cut (~ alignes A B M'); intros.
cut (A <> M'); intros.
cut (B <> M'); intros.
replace (cons_AV (vec M A) (vec M B)) with
 (plus (cons_AV (vec M A) (vec M M')) (cons_AV (vec M M') (vec M B))).
rewrite opp_plus_plus_opp; auto.
rewrite def_opp; auto.
lapply (reflexion_isocele (A:=A) (B:=B) (M:=M) (M':=M')); auto; intros.
lapply (reflexion_isocele2 (A:=A) (B:=B) (M:=M) (M':=M')); auto; intros.
lapply (isocele_angles_base (A:=A) (B:=M) (C:=M')); auto; intros.
lapply (isocele_angles_base (A:=B) (B:=M) (C:=M')); auto; intros.
rewrite H11; auto.
rewrite H10; auto.
rewrite def_opp; auto.
rewrite Chasles; auto.
rewrite Chasles; auto.
lapply (non_alignes_distincts2 (A:=A) (B:=B) (C:=M')); auto; intros.
lapply (non_alignes_distincts (A:=A) (B:=B) (C:=M')); auto; intros.
apply non_axe_image_non_axe with M; auto.
apply reflexion_image_distinct with (2 := H2); auto.
Qed.
 
Lemma reflexion_isometrie :
 forall A B M M' N N' : PO,
 A <> B ->
 M' = reflexion A B M ->
 N' = reflexion A B N -> distance M N = distance M' N'.
intros.
discrimine M N.
rewrite H2 in H0.
rewrite H0; rewrite <- H1.
rewrite distance_refl2; auto.
rewrite distance_refl2; auto.
elim (classic (alignes A B M)); intros.
replace M' with M; auto.
elim (classic (alignes A B N)); intros.
replace N' with N; auto.
rewrite H1; rewrite <- reflexion_axe; auto.
cut (A <> N); intros.
cut (A <> N'); intros.
discrimine M A.
elim (reflexion_mediatrice (A:=A) (B:=B) (M:=N) (M':=N')); auto;
 unfold mediatrice in |- *; intros.
lapply (axe_reflexion_droite (A:=A) (B:=B) (C:=M) (M:=N) (M':=N')); auto;
 intros.
elim (reflexion_mediatrice (A:=M) (B:=A) (M:=N) (M':=N')); auto with geo;
 unfold mediatrice in |- *; intros.
lapply (alignes_non_alignes_trans (A:=A) (B:=B) (C:=N) (D:=M)); auto with geo;
 intros.
lapply (non_alignes_distincts (A:=A) (B:=B) (C:=N')); auto with geo; intros.
apply non_axe_image_non_axe with N; auto with geo.
apply non_alignes_distincts with B; auto with geo.
rewrite H0; rewrite <- reflexion_axe; auto.
cut (A <> M); intros.
cut (A <> M'); intros.
elim (classic (alignes A B N)); intros.
replace N' with N; auto.
discrimine N A.
rewrite distance_sym; rewrite (distance_sym M' A).
elim (reflexion_mediatrice (A:=A) (B:=B) (M:=M) (M':=M')); auto with geo;
 unfold mediatrice in |- *; intros.
lapply (axe_reflexion_droite (A:=A) (B:=B) (C:=N) (M:=M) (M':=M'));
 auto with geo; intros.
rewrite distance_sym; rewrite (distance_sym M' N).
elim (reflexion_mediatrice (A:=N) (B:=A) (M:=M) (M':=M')); auto with geo;
 unfold mediatrice in |- *; intros.
lapply (alignes_non_alignes_trans (A:=A) (B:=B) (C:=M) (D:=N)); auto with geo;
 intros.
rewrite H1; rewrite <- reflexion_axe; auto.
cut (A <> N); intros.
cut (A <> N'); intros.
elim
 cas_egalite_triangle_indirect
  with (A := A) (B := M) (C := N) (A' := A) (B' := M') (C' := N');
 (auto; intros).
elim (reflexion_mediatrice (A:=A) (B:=B) (M:=M) (M':=M')); auto with geo;
 unfold mediatrice in |- *; intros.
elim (reflexion_mediatrice (A:=A) (B:=B) (M:=N) (M':=N')); auto with geo;
 unfold mediatrice in |- *; intros.
replace (cons_AV (vec A M) (vec A N)) with
 (plus (cons_AV (vec A M) (vec A B)) (cons_AV (vec A B) (vec A N))).
rewrite (axe_reflexion_bissectrice (A:=A) (B:=B) (M:=M) (M':=M')); auto.
replace (cons_AV (vec A B) (vec A N)) with (cons_AV (vec A N') (vec A B)).
replace (plus (cons_AV (vec A B) (vec A M')) (cons_AV (vec A N') (vec A B)))
 with (plus (cons_AV (vec A N') (vec A B)) (cons_AV (vec A B) (vec A M'))).
rewrite Chasles; auto.
mesure A B A M'.
mesure A N' A B.
replace (x0 + x) with (x + x0); auto.
ring.
apply permute_angles; auto.
rewrite (axe_reflexion_bissectrice (A:=A) (B:=B) (M:=N) (M':=N')); auto.
rewrite Chasles; auto.
lapply (non_alignes_distincts (A:=A) (B:=B) (C:=N')); auto; intros.
apply non_axe_image_non_axe with N; auto.
apply non_alignes_distincts with B; auto.
lapply (non_alignes_distincts (A:=A) (B:=B) (C:=M')); auto; intros.
apply non_axe_image_non_axe with M; auto.
apply non_alignes_distincts with B; auto.
Qed.
 
Lemma reflexion_inverse_AMN :
 forall A B M M' N N' : PO,
 A <> B ->
 A <> M ->
 A <> N ->
 M' = reflexion A B M ->
 N' = reflexion A B N ->
 cons_AV (vec A M') (vec A N') = opp (cons_AV (vec A M) (vec A N)).
intros.
elim (classic (alignes A B M)); intros.
replace M' with M; auto.
elim (classic (alignes A B N)); intros.
replace N' with N; auto.
lapply (alignes_trans (A:=A) (B:=B) (C:=M) (D:=N)); auto; intros.
cut (double_AV (cons_AV (vec A M) (vec A N)) = image_angle 0); intros.
replace (opp (cons_AV (vec A M) (vec A N))) with
 (plus (image_angle 0) (opp (cons_AV (vec A M) (vec A N)))); 
 auto.
rewrite <- H7; unfold double_AV in |- *.
mesure A M A N.
replace (x + x + - x) with x; auto.
ring.
rewrite plus_commutative; auto with geo.
apply angle_alignes; auto.
rewrite H3; rewrite <- reflexion_axe; auto.
cut (A <> N'); intros.
lapply (axe_reflexion_droite (A:=A) (B:=B) (C:=M) (M:=N) (M':=N')); auto;
 intros.
rewrite <- (axe_reflexion_bissectrice (A:=A) (B:=M) (M:=N) (M':=N')); auto.
rewrite def_opp; auto.
lapply (alignes_non_alignes_trans (A:=A) (B:=B) (C:=N) (D:=M)); auto; intros.
lapply (axe_reflexion_droite (A:=M) (B:=A) (C:=A) (M:=N) (M':=N'));
 auto with geo; intros.
lapply (non_alignes_distincts (A:=A) (B:=B) (C:=N')); auto; intros.
apply non_axe_image_non_axe with N; auto.
rewrite H2; rewrite <- reflexion_axe; auto.
cut (A <> M'); intros.
elim (classic (alignes A B N)); intros.
replace N' with N; auto.
lapply (axe_reflexion_droite (A:=A) (B:=B) (C:=N) (M:=M) (M':=M')); auto;
 intros.
rewrite (axe_reflexion_bissectrice (A:=A) (B:=N) (M:=M) (M':=M')); auto.
rewrite def_opp; auto.
lapply (alignes_non_alignes_trans (A:=A) (B:=B) (C:=M) (D:=N)); auto; intros.
lapply (axe_reflexion_droite (A:=N) (B:=A) (C:=A) (M:=M) (M':=M'));
 auto with geo; intros.
rewrite H3; rewrite <- reflexion_axe; auto.
cut (A <> N'); intros.
replace (cons_AV (vec A M) (vec A N)) with
 (plus (cons_AV (vec A M) (vec A B)) (cons_AV (vec A B) (vec A N))).
rewrite (axe_reflexion_bissectrice (A:=A) (B:=B) (M:=M) (M':=M')); auto.
replace (cons_AV (vec A B) (vec A N)) with (cons_AV (vec A N') (vec A B)).
replace (plus (cons_AV (vec A B) (vec A M')) (cons_AV (vec A N') (vec A B)))
 with (plus (cons_AV (vec A N') (vec A B)) (cons_AV (vec A B) (vec A M'))).
rewrite Chasles; auto.
rewrite def_opp; auto.
mesure A B A M'.
mesure A N' A B.
replace (x0 + x) with (x + x0); auto.
ring.
apply permute_angles; auto.
rewrite (axe_reflexion_bissectrice (A:=A) (B:=B) (M:=N) (M':=N')); auto.
rewrite Chasles; auto.
lapply (non_alignes_distincts (A:=A) (B:=B) (C:=N')); auto; intros.
apply non_axe_image_non_axe with N; auto.
apply non_alignes_distincts with B; auto.
apply non_axe_image_non_axe with M; auto.
Qed.
 
Theorem reflexion_anti_deplacement :
 forall A B M M' N N' P P' : PO,
 A <> B ->
 M <> N ->
 M <> P ->
 N <> P ->
 M' = reflexion A B M ->
 N' = reflexion A B N ->
 P' = reflexion A B P ->
 cons_AV (vec M' N') (vec M' P') = opp (cons_AV (vec M N) (vec M P)).
intros.
cut (M' <> N'); intros.
cut (M' <> P'); intros.
discrimine M A.
cut (M' = A); intros.
rewrite H9.
cut (A <> N); intros.
cut (A <> P); intros.
apply reflexion_inverse_AMN with B; auto.
red in |- *; intros; apply H1.
rewrite H8; auto.
red in |- *; intros; apply H0.
rewrite H8; auto.
rewrite H3; rewrite H8; rewrite <- reflexion_axe; auto with geo.
discrimine N A.
cut (N' = A); intros.
rewrite H10.
cut (A <> P); intros.
elim
 cas_egalite_triangle_indirect
  with (A := A) (B := M) (C := P) (A' := A) (B' := M') (C' := P');
 (auto; intros).
elim H13; intros.
rewrite <- H14; rewrite def_opp; auto.
rewrite (reflexion_isometrie (A:=A) (B:=B) (M:=A) (M':=A) (N:=M) (N':=M'));
 auto with geo.
rewrite (reflexion_isometrie (A:=A) (B:=B) (M:=A) (M':=A) (N:=P) (N':=P'));
 auto with geo.
rewrite (reflexion_inverse_AMN (A:=A) (B:=B) (M:=P) (M':=P') (N:=M) (N':=M'));
 auto.
rewrite def_opp; auto.
red in |- *; intros; apply H2.
rewrite H9; auto.
rewrite H4; rewrite H9; rewrite <- reflexion_axe; auto with geo.
discrimine P A.
cut (P' = A); intros.
rewrite H11.
elim
 cas_egalite_triangle_indirect
  with (A := A) (B := M) (C := N) (A' := A) (B' := M') (C' := N');
 (auto; intros).
elim H13; intros.
rewrite H14; rewrite def_opp; auto.
red in |- *; intros; apply H7.
rewrite H16; auto.
rewrite (reflexion_isometrie (A:=A) (B:=B) (M:=A) (M':=A) (N:=M) (N':=M'));
 auto with geo.
rewrite (reflexion_isometrie (A:=A) (B:=B) (M:=A) (M':=A) (N:=N) (N':=N'));
 auto with geo.
rewrite (reflexion_inverse_AMN (A:=A) (B:=B) (M:=N) (M':=N') (N:=M) (N':=M'));
 auto.
rewrite def_opp; auto.
rewrite H5; rewrite H10; rewrite <- reflexion_axe; auto with geo.
cut (A <> M'); intros.
elim
 cas_egalite_triangle_indirect
  with (A := A) (B := M) (C := N) (A' := A) (B' := M') (C' := N');
 (auto; intros).
elim H13; intros.
elim
 cas_egalite_triangle_indirect
  with (A := A) (B := M) (C := P) (A' := A) (B' := M') (C' := P');
 (auto; intros).
elim H17; intros.
replace (cons_AV (vec M N) (vec M P)) with
 (plus (cons_AV (vec M N) (vec M A)) (cons_AV (vec M A) (vec M P))).
replace (cons_AV (vec M A) (vec M P)) with (cons_AV (vec M' P') (vec M' A)).
rewrite H14.
replace
 (plus (cons_AV (vec M' A) (vec M' N')) (cons_AV (vec M' P') (vec M' A)))
 with
 (plus (cons_AV (vec M' P') (vec M' A)) (cons_AV (vec M' A) (vec M' N'))).
rewrite Chasles; auto.
rewrite def_opp; auto.
mesure M' P' M' A.
mesure M' A M' N'.
replace (x + x0) with (x0 + x); auto.
ring.
apply permute_angles; auto.
rewrite Chasles; auto.
rewrite (reflexion_isometrie (A:=A) (B:=B) (M:=A) (M':=A) (N:=M) (N':=M'));
 auto with geo.
rewrite (reflexion_isometrie (A:=A) (B:=B) (M:=A) (M':=A) (N:=P) (N':=P'));
 auto with geo.
rewrite (reflexion_inverse_AMN (A:=A) (B:=B) (M:=P) (M':=P') (N:=M) (N':=M'));
 auto.
rewrite def_opp; auto.
rewrite (reflexion_isometrie (A:=A) (B:=B) (M:=A) (M':=A) (N:=M) (N':=M'));
 auto with geo.
rewrite (reflexion_isometrie (A:=A) (B:=B) (M:=A) (M':=A) (N:=N) (N':=N'));
 auto with geo.
rewrite (reflexion_inverse_AMN (A:=A) (B:=B) (M:=N) (M':=N') (N:=M) (N':=M'));
 auto.
rewrite def_opp; auto.
apply (isometrie_distinct (A:=A) (B:=M) (A':=A) (B':=M')); auto with geo.
rewrite (reflexion_isometrie (A:=A) (B:=B) (M:=A) (M':=A) (N:=M) (N':=M'));
 auto with geo.
apply (isometrie_distinct (A:=M) (B:=P) (A':=M') (B':=P')); auto.
rewrite (reflexion_isometrie (A:=A) (B:=B) (M:=M) (M':=M') (N:=P) (N':=P'));
 auto.
apply (isometrie_distinct (A:=M) (B:=N) (A':=M') (B':=N')); auto.
rewrite (reflexion_isometrie (A:=A) (B:=B) (M:=M) (M':=M') (N:=N) (N':=N'));
 auto.
Qed.
 
Lemma mediatrices_reflexion :
 forall A B M M' : PO,
 M <> M' ->
 ~ alignes A B M ->
 mediatrice M M' A -> mediatrice M M' B -> M' = reflexion A B M.
intros A B M M' H0 H1 H2 H3; try assumption.
cut (A <> B); intros H; [ idtac | auto with geo ].
soit_milieu M M' ipattern:K.
apply reflexion_def2 with K; auto with geo.
apply def_projete_orthogonal; auto.
discrimine K A.
apply alignes_ordre_cycle; auto.
apply mediatrice_droite with (2 := H4); auto.
cut (orthogonal (vec M M') (vec A B)); intros.
apply ortho_sym.
replace (vec K M) with (mult_PP (-1) (vec M K)).
rewrite (milieu_vecteur2 (A:=M) (B:=M') (M:=K)); auto.
replace (mult_PP (-1) (mult_PP (/ 2) (vec M M'))) with
 (mult_PP (- / 2) (vec M M')).
Simplortho.
cut (2 <> 0); intros; auto with real.
Fieldvec 2.
Ringvec.
apply ortho_sym.
apply mediatrice_orthogonale_segment; auto.
Qed.
 
Lemma existence_reflexion_AB :
 forall A B M : PO, A <> B -> exists M' : PO, M' = reflexion A B M.
intros A B M H1; try assumption.
elim existence_projete_orthogonal with (A := A) (B := B) (C := M);
 [ intros H H4; try clear existence_projete_orthogonal; try exact H3 | auto ].
elim existence_representant_vecteur with (A := H) (B := M) (C := H);
 intros M' H3; try clear existence_representant_vecteur; 
 try exact H3.
exists M'.
apply reflexion_def2 with H; auto.
replace (vec M M') with (add_PP (vec M H) (vec H M')).
rewrite H3; Ringvec.
Ringvec.
Qed.
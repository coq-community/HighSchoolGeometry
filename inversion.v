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


Require Export puissance_cercle.
Set Implicit Arguments.
Unset Strict Implicit.
Parameter inversion : PO -> R -> PO -> PO.
 
Axiom
  inversion_def :
    forall (I A B : PO) (k : R),
    k <> 0 ->
    I <> A ->
    B = inversion I k A -> alignes I A B /\ scalaire (vec I A) (vec I B) = k.
 
Axiom
  inversion_def2 :
    forall (I A B : PO) (k : R),
    k <> 0 ->
    I <> A ->
    alignes I A B -> scalaire (vec I A) (vec I B) = k -> B = inversion I k A.
 
Lemma definition_inversion :
 forall (I A B : PO) (k : R),
 k <> 0 ->
 I <> A ->
 (B = inversion I k A <-> alignes I A B /\ scalaire (vec I A) (vec I B) = k).
intros; red in |- *; try split; intros.
apply inversion_def; auto.
apply inversion_def2; tauto.
Qed.
 
Lemma image_distinct_pole :
 forall (I A B : PO) (k : R),
 k <> 0 -> I <> A -> B = inversion I k A -> I <> B.
intros.
elim (inversion_def (I:=I) (A:=A) (B:=B) (k:=k)); intros; auto.
red in |- *; intros; apply H.
rewrite <- H3; rewrite <- H4; Simplscal.
VReplace (vec I I) (mult_PP 0 (vec I A)).
Simplscal.
Qed.
 
Ltac deroule_inversion I A B k :=
  elim (inversion_def (I:=I) (A:=A) (B:=B) (k:=k)); intros; auto;
   assert (I <> B);
   [ apply (image_distinct_pole (I:=I) (A:=A) (B:=B) (k:=k)); auto | idtac ].
 
Lemma inversion_involution :
 forall (I A B : PO) (k : R),
 k <> 0 -> I <> A -> B = inversion I k A -> A = inversion I k B.
intros.
deroule_inversion I A B k.
apply inversion_def2; auto.
auto with geo.
rewrite <- H3; auto with geo.
apply scalaire_sym.
Qed.
Hint Immediate inversion_involution: geo.
 
Lemma inversion_droite_pole :
 forall (A A' M M' I : PO) (k : R),
 k <> 0 ->
 I <> A ->
 I <> M ->
 alignes I A M ->
 A' = inversion I k A ->
 M' = inversion I k M -> alignes I A A' /\ alignes I A' M'.
intros.
deroule_inversion I M M' k.
deroule_inversion I A A' k.
assert (A = inversion I k A'); auto with geo.
deroule_inversion I A' A k.
split; [ try assumption | idtac ].
halignes H12 ipattern:a.
halignes H5 ipattern:b.
halignes H2 ipattern:c.
apply colineaire_alignes with (a * (b * c)).
rewrite H16; rewrite H17; rewrite H15.
Ringvec.
Qed.
 
Lemma inversion_homothetie :
 forall (I A B : PO) (k : R),
 k <> 0 ->
 I <> A ->
 B = inversion I k A -> B = homothetie (/ Rsqr (distance I A) * k) I A.
intros.
deroule_inversion I A B k.
apply vecteur_homothetie.
halignes H2 ipattern:k0.
assert (k0 = / Rsqr (distance I A) * k).
apply Rmult_eq_reg_l with (scalaire (vec I A) (vec I A)); auto with geo.
replace (scalaire (vec I A) (vec I A) * k0) with
 (scalaire (vec I A) (vec I B)).
unfold Rsqr in |- *; rewrite <- carre_scalaire_distance.
rewrite <- H3.
field; auto with geo.
rewrite H5; Simplscal.
rewrite H5; rewrite H6; auto.
Qed.
 
Lemma homothetie_inversion :
 forall (I A B : PO) (k : R),
 k <> 0 ->
 I <> A ->
 B = homothetie (/ Rsqr (distance I A) * k) I A -> B = inversion I k A.
intros.
generalize (homothetie_vecteur H1); intros.
apply inversion_def2; auto.
apply colineaire_alignes with (/ Rsqr (distance I A) * k); auto.
rewrite H2; Simplscal.
unfold Rsqr in |- *; rewrite <- carre_scalaire_distance.
field; auto with geo.
Qed.
 
Lemma inversion_est_homothetie :
 forall (I A B : PO) (k : R),
 k <> 0 ->
 I <> A ->
 (B = inversion I k A <-> B = homothetie (/ Rsqr (distance I A) * k) I A).
intros; red in |- *; try split; intros.
apply inversion_homothetie; auto.
apply homothetie_inversion; auto.
Qed.
 
Lemma inversion_pole_vecteur :
 forall (k : R) (O M M' : PO),
 k <> 0 ->
 O <> M ->
 M' = inversion O k M :>PO ->
 vec O M' = mult_PP (/ Rsqr (distance O M) * k) (vec O M) :>PP.
intros.
apply homothetie_vecteur.
apply inversion_homothetie; auto.
Qed.
 
Lemma existence_inversion :
 forall (I A : PO) (k : R),
 k <> 0 -> I <> A -> exists A' : PO, A' = inversion I k A.
intros.
elim
 existence_homothetique
  with (k := / Rsqr (distance I A) * k) (I := I) (A := A);
 [ intros A' H1; try clear existence_homothetique; try exact H1 ].
exists A'.
apply homothetie_inversion; auto.
Qed.
 
Lemma inversion_oppose_puissance :
 forall (I A B C : PO) (k : R),
 k <> 0 ->
 I <> A -> B = inversion I k A -> C = symetrie I A -> B = inversion I (- k) C.
intros.
generalize H2; unfold symetrie in |- *; intros.
assert (I <> C).
assert (I = homothetie (-1) I I); auto with geo.
apply
 (image_homothetie_distincts (k:=-1) (I:=I) (A:=I) (A':=I) (B:=A) (B':=C));
 auto with real.
generalize (inversion_homothetie (I:=I) (A:=A) (B:=B) (k:=k)); intros.
apply homothetie_inversion; auto with real.
generalize
 (homothetie_vecteur (k:=/ Rsqr (distance I A) * k) (I:=I) (A:=A) (A':=B));
 intros.
apply vecteur_homothetie.
rewrite
 (homothetie_vecteur (k:=/ Rsqr (distance I A) * k) (I:=I) (A:=A) (A':=B))
 ; auto.
assert (I = milieu A C); auto with geo.
replace (distance I A) with (distance I C); auto with geo.
rewrite (homothetie_vecteur H3).
assert (Rsqr (distance I C) <> 0).
assert (distance I C <> 0); auto with geo.
unfold Rsqr in |- *; auto with real.
Ringvec.
Qed.
 
Theorem inversion_cocyclicite :
 forall (A B C D I : PO) (k : R),
 k <> 0 ->
 I <> A ->
 I <> C ->
 C <> D ->
 triangle A B C ->
 B = inversion I k A -> D = inversion I k C -> sont_cocycliques A B C D.
intros.
deroule_inversion I A B k.
deroule_inversion I C D k.
apply egalite_puissance_cocycliques with I; auto.
deroule_triangle A B C.
apply alignes_ordre_cycle; auto.
apply alignes_ordre_cycle; auto.
rewrite H10; auto.
Qed.
 
Definition droite_perpendiculaire (A B C D : PO) :=
  orthogonal (vec C D) (vec A B).
 
Theorem inversion_cercle_diametre_pole :
 forall (A M A' M' I : PO) (k : R),
 k <> 0 ->
 triangle I A M ->
 A' = inversion I k A ->
 M' = inversion I k M ->
 cercle_diametre I A M -> droite_perpendiculaire I A A' M'.
unfold droite_perpendiculaire in |- *; intros A M A' M' I k H H0 H2 H3 H1.
generalize H1; unfold cercle_diametre in |- *; intros.
elim H4;
 [ intros O H5; elim H5; [ intros H6 H7; try clear H5 H4; try exact H7 ] ].
assert (orthogonal (vec M I) (vec M A)).
apply triangle_diametre with O; auto with geo.
hcercle H6.
rewrite <- H8; auto.
deroule_triangle I A M.
deroule_inversion I A A' k.
deroule_inversion I M M' k.
elim existence_projete_orthogonal with (A := I) (B := A) (C := M');
 [ intros H' H17; try clear existence_projete_orthogonal; try exact H16
 | auto ].
elim def_projete_orthogonal2 with (A := I) (B := A) (C := M') (H := H');
 [ intros; try clear def_projete_orthogonal2; try exact H17 | auto | auto ].
halignes H14 ipattern:x.
halignes H18 ipattern:y.
assert (scalaire (vec I M') (vec I A) = scalaire (vec I M') (vec I M)).
apply (scalaire_avec_projete (A:=I) (B:=M') (C:=A) (H:=M)); auto with geo.
rewrite H20; Simplortho.
assert (scalaire (vec I A) (vec I M') = scalaire (vec I A) (vec I H')).
apply (scalaire_avec_projete (A:=I) (B:=A) (C:=M') (H:=H')); auto with geo.
assert (scalaire (vec I A) (vec I A') = scalaire (vec I A) (vec I H')).
rewrite H12; rewrite <- H15.
rewrite scalaire_sym; rewrite <- H22.
rewrite scalaire_sym; rewrite H23; auto.
assert (A' = H').
apply egalite_scalaire_alignes with (4 := H24); auto with geo.
rewrite H25; auto with geo.
Qed.
 
Ltac image_inversion I A B k :=
  elim (existence_inversion (I:=I) (A:=A) (k:=k)); intros B; intros; auto;
   deroule_inversion I A B k.
Hint Resolve inversion_involution: geo.
Require Export applications_cocyclicite.
 
Theorem inversion_droite_non_pole :
 forall (A B M M' I : PO) (k : R),
 k <> 0 ->
 triangle A B I ->
 I <> M ->
 alignes A B M ->
 M' = inversion I k M ->
 exists C : PO, orthogonal (vec A B) (vec I C) /\ cercle_diametre I C M'.
intros.
deroule_triangle A B I.
soit_projete A B I ipattern:K.
assert (I <> K).
red in |- *; intros; apply H4.
rewrite H11; auto.
image_inversion I K ipattern:K' k.
exists K'.
unfold cercle_diametre in |- *.
soit_milieu I K' ipattern:D.
deroule_inversion I M M' k.
soit_projete I M K' ipattern:L.
halignes H2 ipattern:x.
halignes H9 ipattern:y.
assert (vec K M = mult_PP (x + - y) (vec A B)).
VReplace (vec K M) (add_PP (vec A M) (mult_PP (-1) (vec A K))).
rewrite H26; rewrite H25; Ringvec.
halignes H13 ipattern:z.
assert (orthogonal (vec I K') (vec A B)).
rewrite H28; Simplortho.
split; [ auto with geo | idtac ].
exists D; (split; auto).
assert (scalaire (vec I M) (vec I K') = scalaire (vec I M) (vec I L)).
apply (scalaire_avec_projete (A:=I) (B:=M) (C:=K') (H:=L)); auto with geo.
assert (scalaire (vec I K') (vec I M) = scalaire (vec I K') (vec I K)).
apply (scalaire_avec_projete (A:=I) (B:=K') (C:=M) (H:=K)); auto with geo.
apply ortho_sym.
rewrite H27; Simplortho.
assert (scalaire (vec I M) (vec I L) = scalaire (vec I M) (vec I M')).
rewrite <- H30; rewrite scalaire_sym; rewrite H31; rewrite scalaire_sym;
 rewrite H14; auto.
assert (L = M').
apply egalite_scalaire_alignes with (4 := H32); auto.
rewrite <- H33; auto with geo.
discrimine L K'.
icercle.
assert (orthogonal (vec L I) (vec L K')).
halignes H23 ipattern:t.
VReplace (vec L I) (mult_PP (-1) (vec I L)).
rewrite H35.
VReplace (mult_PP (-1) (mult_PP t (vec I M))) (mult_PP (- t) (vec I M)).
auto with geo.
assert (triangle L I K').
unfold triangle in |- *.
apply orthogonal_non_alignes; auto.
rewrite H33; auto.
elim existence_cercle_circonscrit with (A := I) (B := K') (C := L);
 [ intros O H37 | auto with geo ].
cut (O = D); intros.
rewrite <- H38; auto.
apply
 (centre_circonscrit_rectangle_milieu (A:=I) (B:=K') (C:=L) (C':=D) (O:=O));
 auto with geo.
Qed.
 
Lemma cercle_inversion_homothetie :
 forall (A A' B B' I A1 B1 : PO) (k : R),
 k <> 0 ->
 triangle A B I ->
 B <> B' ->
 I <> A' ->
 triangle A A' B ->
 sont_cocycliques A A' B B' ->
 alignes A A' I ->
 alignes B B' I ->
 A1 = inversion I k A ->
 B1 = inversion I k B ->
 A1 = homothetie (k * / scalaire (vec I A) (vec I A')) I A' /\
 B1 = homothetie (k * / scalaire (vec I A) (vec I A')) I B'.
intros.
assert (scalaire (vec I A) (vec I A') = scalaire (vec I B) (vec I B')).
apply puissance_cercle; auto.
deroule_triangle A B I.
deroule_triangle A A' B.
assert (alignes I A A'); auto with geo.
assert (alignes I B B'); auto with geo.
halignes H18 ipattern:x.
absurd (I = A); auto.
halignes H19 ipattern:y.
absurd (I = B); auto.
assert (distance I A <> 0); auto with geo real.
assert (distance I A * distance I A <> 0).
unfold Rsqr in |- *; auto with real.
assert (scalaire (vec I A) (vec I A') <> 0).
red in |- *; intros; apply H2.
apply (produit_zero_conf H20).
apply Rmult_eq_reg_l with (scalaire (vec I A) (vec I A)).
RReplace (scalaire (vec I A) (vec I A) * 0) 0.
rewrite <- H24.
rewrite H20; Simplscal.
rewrite carre_scalaire_distance; auto.
assert (x <> 0).
contrapose H24.
rewrite H20; rewrite H25; Simplscal.
split; [ try assumption | idtac ].
apply vecteur_homothetie.
rewrite (inversion_pole_vecteur (k:=k) (O:=I) (M:=A) (M':=A1)); auto.
rewrite H20; Simplscal.
rewrite carre_scalaire_distance.
unfold Rsqr in |- *.
RReplace (/ (x * (distance I A * distance I A)))
 (/ x * / (distance I A * distance I A)).
VReplace
 (mult_PP (k * (/ x * / (distance I A * distance I A))) (mult_PP x (vec I A)))
 (mult_PP (k * (/ (distance I A * distance I A) * (/ x * x))) (vec I A)).
replace (/ (distance I A * distance I A) * k) with
     (k * (/ (distance I A * distance I A) * (/x * x))); auto.
field; auto.
field; auto.
apply vecteur_homothetie.
rewrite (inversion_pole_vecteur (k:=k) (O:=I) (M:=B) (M':=B1)); auto.
rewrite H9.
rewrite H21; Simplscal.
rewrite carre_scalaire_distance.
unfold Rsqr in |- *.
assert (distance I B <> 0); auto with geo real.
assert (distance I B * distance I B <> 0).
unfold Rsqr in |- *; auto with real.
assert (scalaire (vec I B) (vec I B') <> 0).
rewrite <- H9; auto.
assert (y <> 0).
contrapose H26.
rewrite H21; rewrite H29; Simplscal.
RReplace (/ (y * (distance I B * distance I B)))
 (/ y * / (distance I B * distance I B)).
VReplace
 (mult_PP (k * (/ y * / (distance I B * distance I B))) (mult_PP y (vec I B)))
 (mult_PP (k * (/ (distance I B * distance I B) * (/ y * y))) (vec I B)).
replace (/ (distance I B * distance I B) * k) with
  (k * (/ (distance I B * distance I B) * (/ y * y))); auto.
field;auto.
field;auto.
Qed.
 
Lemma cercle_tangente_inversion_homothetie :
 forall (A A' B M I M' O : PO) (k : R),
 k <> 0 ->
 A <> B ->
 I <> A ->
 I <> M ->
 cercle_diametre A B M ->
 O = milieu A B ->
 orthogonal (vec M O) (vec M I) ->
 alignes A B I ->
 A' = inversion I k A ->
 M' = inversion I k M ->
 A' = homothetie (k * / scalaire (vec I A) (vec I B)) I B /\
 M' = homothetie (k * / scalaire (vec I A) (vec I B)) I M.
intros.
assert
 (scalaire (vec I A) (vec I B) = Rsqr (distance I O) + - Rsqr (distance O A)).
apply scalaire_diametre with B; auto with geo.
elim (Pythagore M I O); intros.
assert (scalaire (vec I A) (vec I B) = Rsqr (distance I M)).
rewrite H9.
rewrite H10; auto with geo.
rewrite (distance_sym M O).
replace (Rsqr (distance O M)) with (Rsqr (distance O A)).
rewrite distance_sym; ring.
hcercle H3.
elim H12;
 [ intros O0 H13; elim H13;
    [ intros H14 H15; elim H14;
       [ intros H16 H17; try clear H14 H13 H12; try exact H17 ] ] ].
assert (O0 = O).
rewrite H4; auto.
rewrite <- H12; rewrite H17; auto.
assert (alignes I A B); auto with geo.
halignes H13 ipattern:x.
assert (distance I A <> 0); auto with geo real.
assert (distance I A * distance I A <> 0).
unfold Rsqr in |- *; auto with real.
assert (distance I M <> 0); auto with geo real.
assert (distance I M * distance I M <> 0).
unfold Rsqr in |- *; auto with real.
assert (scalaire (vec I A) (vec I B) <> 0).
rewrite H12.
unfold Rsqr in |- *; auto.
assert (x <> 0).
contrapose H18.
rewrite H14; rewrite H20; Simplscal.
split; [ try assumption | idtac ].
apply vecteur_homothetie.
rewrite (inversion_pole_vecteur (k:=k) (O:=I) (M:=A) (M':=A')); auto.
rewrite H14; Simplscal.
rewrite carre_scalaire_distance.
unfold Rsqr in |- *.
RReplace (/ (x * (distance I A * distance I A)))
 (/ x * / (distance I A * distance I A)).
VReplace
 (mult_PP (k * (/ x * / (distance I A * distance I A))) (mult_PP x (vec I A)))
 (mult_PP (k * (/ (distance I A * distance I A) * (/ x * x))) (vec I A)).
RReplace (/ x * x) 1.
RReplace (/ (distance I A * distance I A) * k)
 (k * (/ (distance I A * distance I A) * 1)); auto.
rewrite <- Rinv_mult_distr; auto.
RReplace (distance I A * distance I A * x)
 (x * (distance I A * distance I A)); auto.
apply vecteur_homothetie.
rewrite (inversion_pole_vecteur (k:=k) (O:=I) (M:=M) (M':=M')); auto.
rewrite H12.
unfold Rsqr in |- *.
Ringvec.
Qed.
 
Theorem inversion_cercle_non_pole :
 forall (A B M A' B' M' I : PO) (k : R),
 k <> 0 ->
 A <> B ->
 ~ cercle_diametre A B I ->
 alignes A B I ->
 A' = inversion I k A ->
 B' = inversion I k B ->
 M' = inversion I k M -> cercle_diametre A B M -> cercle_diametre A' B' M'.
intros A B M A' B' M' I k H H50 H0 H1 H2 H3 H4 H5; try assumption.
assert (I <> A).
red in |- *; intros; apply H0.
rewrite H6; auto with geo.
assert (I <> B).
red in |- *; intros; apply H0.
rewrite H7; auto with geo.
assert (I <> M).
red in |- *; intros; apply H0.
rewrite H8; auto with geo.
elim (classic (alignes A B M)); intros.
assert (M = A \/ M = B).
apply alignes_diametre; auto.
elim H10;
 [ intros H11; try clear H10 | intros H11; try clear H10; try exact H11 ].
rewrite H4; rewrite H11; rewrite <- H2; auto with geo.
rewrite H4; rewrite H11; rewrite <- H3; auto with geo.
generalize H5.
unfold cercle_diametre, circonscrit, isocele in H5; intros.
elim H5;
 [ intros O H11; elim H11;
    [ intros H12 H13; elim H12;
       [ intros H14 H15; try clear H12 H11 H5; try exact H15 ] ] ].
soit_projete M I O ipattern:K.
assert (scalaire (vec I A) (vec I B) <> 0); [ idtac | auto with real ].
assert (alignes I A B); auto with geo.
halignes H16 ipattern:x.
rewrite H17.
Simplscal.
apply integre_not; auto with geo.
apply (distinct_col_nonzero (A:=I) (B:=B) (C:=I) (D:=A)); auto.
discrimine M K.
2: assert (distance O K < distance O M).
rewrite <- H17 in H12.
elim
 cercle_tangente_inversion_homothetie
  with
    (A := A)
    (A' := A')
    (B := B)
    (M := M)
    (I := I)
    (M' := M')
    (O := O)
    (k := k);
 [ intros
 | auto
 | auto
 | auto
 | auto
 | auto with geo
 | auto
 | auto with geo
 | auto
 | auto
 | auto ].
elim
 cercle_tangente_inversion_homothetie
  with
    (A := B)
    (A' := B')
    (B := A)
    (M := M)
    (I := I)
    (M' := M')
    (O := O)
    (k := k); (intros; auto with geo).
apply
 (homothetie_cercle_diametre (k:=k * / scalaire (vec I A) (vec I B)) (I:=I)
    (A:=B) (A':=A') (B:=A) (B':=B') (M:=M) (M':=M')); 
 auto with geo.
apply integre_not; auto with real.
rewrite scalaire_sym; auto.
apply projete_distance_Rlt with I; auto.
apply def_projete_orthogonal; auto with geo.
elim intersection2_cercle_droite with (A := M) (B := I) (O := O) (H := K);
 [ intros C H19; elim H19;
    [ intros H21 H20; elim H20; [ intros; try clear H20 H19 ] ]
 | auto
 | auto
 | auto
 | auto ].
assert (triangle A B M).
unfold triangle in |- *; auto.
halignes H1 ipattern:y.
assert (triangle A M I); unfold triangle in |- *.
red in |- *; intros; apply H9.
assert (alignes A I M); auto with geo.
halignes H25 ipattern:x.
absurd (A = I); auto.
apply colineaire_alignes with (x * y).
rewrite H26; rewrite H20; Ringvec.
assert (sont_cocycliques A B M C).
hcercle H23.
hcercle H10.
elim H26;
 [ intros O0 H28; elim H28;
    [ intros H29 H30; elim H29;
       [ intros H31 H32; try clear H29 H28 H27; try exact H32 ] ] ].
exists O; split; try split; auto with geo.
assert (O0 = O).
rewrite H30; auto.
rewrite H15; rewrite H25; auto.
assert (alignes M C I).
apply alignes_ordre_permute; auto.
elim
 cercle_inversion_homothetie
  with
    (A := A)
    (A' := B)
    (B := M)
    (B' := C)
    (I := I)
    (A1 := A')
    (B1 := M')
    (k := k);
 [ intros
 | auto
 | auto
 | auto
 | auto
 | auto
 | auto
 | auto
 | auto
 | auto
 | auto ].
elim
 cercle_inversion_homothetie
  with
    (A := B)
    (A' := A)
    (B := M)
    (B' := C)
    (I := I)
    (A1 := B')
    (B1 := M')
    (k := k);
 [ intros
 | auto
 | auto
 | auto
 | auto
 | auto
 | auto
 | auto
 | auto
 | auto
 | auto ].
apply
 (homothetie_cercle_diametre (k:=k * / scalaire (vec I B) (vec I A)) (I:=I)
    (A:=B) (A':=A') (B:=A) (B':=B') (M:=C) (M':=M')); 
 auto.
rewrite scalaire_sym; apply integre_not; auto with real.
rewrite scalaire_sym; auto.
hcercle H23.
hcercle H10.
elim H32;
 [ intros O0 H33; elim H33;
    [ intros H34 H35; elim H34;
       [ intros H36 H37; try clear H34 H33 H32; try exact H37 ] ] ].
exists O; split; try split; auto with geo.
assert (O0 = O).
rewrite H35; auto.
rewrite <- H14; rewrite <- H31; rewrite <- H32; auto.
unfold triangle in |- *.
red in |- *; intros; apply H9.
assert (alignes I B M); auto with geo.
halignes H30 ipattern:x.
apply colineaire_alignes with (x * (1 + - y) + y).
VReplace (vec A M) (add_PP (vec A I) (vec I M)).
rewrite H31.
VReplace (vec I B) (add_PP (vec A B) (mult_PP (-1) (vec A I))).
rewrite H20; Ringvec.
auto with geo.
auto with geo.
auto with geo.
auto with geo.
elim circonscrit_triangle_non_point with (O := O) (A := A) (B := B) (C := M);
 [ intros H27 H28; elim H28; [ intros H29 H30; try clear H28; try exact H30 ]
 | auto
 | auto ].
hcercle H10.
Qed.

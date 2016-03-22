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


Require Export orthogonalite_espace.
Require Export affine_classiques.
Set Implicit Arguments.
Unset Strict Implicit.
 
Definition tetraedre (A B C D : PO) := ~ coplanaires A B C D.
 
Lemma tetraedre_non_alignes :
 forall A B C D : PO, tetraedre A B C D -> ~ alignes A B C.
unfold tetraedre in |- *; intros.
elim non_coplanaires_expl with (A := A) (B := B) (C := C) (D := D);
 [ intros H0 H1; try clear non_coplanaires_expl; try exact H0 | auto ].
Qed.
Hint Resolve tetraedre_non_alignes: geo.
 
Lemma deux_milieux_tetraedre :
 forall A B C D I J K L : PO,
 tetraedre A B C D ->
 I = milieu D A ->
 J = milieu D B -> K = milieu C A -> L = milieu C B -> vec I J = vec K L.
intros.
cut (mult_PP 2 (vec I J) = vec A B); intros.
cut (mult_PP 2 (vec K L) = vec A B); intros.
apply mult_PP_regulier with 2; auto with real.
rewrite H5; auto.
apply droite_milieu with C; auto.
apply droite_milieu with D; auto.
Qed.
 
Definition parallelepipede (A B C D E F G H : PO) :=
  (vec A B = vec D C /\ vec D C = vec H G) /\
  vec H G = vec E F /\ vec E H = vec A D.
 
Definition parallelepipede_rectangle (A B C D E F G H : PO) :=
  parallelepipede A B C D E F G H /\
  orthogonal (vec A B) (vec A D) /\
  orthogonal (vec A B) (vec A E) /\ orthogonal (vec A D) (vec A E).
 
Definition carre (A B C D : PO) :=
  vec A B = vec D C /\
  orthogonal (vec A B) (vec A D) /\
  scalaire (vec A B) (vec A B) = 1 /\ scalaire (vec A D) (vec A D) = 1.
 
Definition cube (A B C D E F G H : PO) :=
  parallelepipede_rectangle A B C D E F G H /\
  carre A B C D /\ scalaire (vec A E) (vec A E) = 1.
 
Lemma parallelepipede_parallelogramme :
 forall A B C D E F G H : PO,
 parallelepipede A B C D E F G H -> vec F G = vec A D.
unfold parallelepipede in |- *; intros A B C D E F G H' H.
elim H; intros H0 H1; elim H1; intros H2 H3; try clear H1 H; try exact H3.
elim H0; intros H H1; try clear H0; try exact H1.
rewrite <- H3.
apply egalite_vecteur.
VReplace (vec F E) (mult_PP (-1) (vec E F)).
rewrite <- H2.
Ringvec.
Qed.
 
Lemma diagonales_carre :
 forall A B C D : PO, carre A B C D -> orthogonal (vec A C) (vec D B).
intros.
elim H; clear H; intros.
apply def_orthogonal2.
elim H0; intros H2 H3; elim H3; intros H4 H5; try clear H3 H0; try exact H5.
cut (scalaire (vec A B) (vec A D) = 0); intros.
replace (vec A C) with (add_PP (mult_PP 1 (vec A B)) (mult_PP 1 (vec A D))).
replace (vec D B) with
 (add_PP (mult_PP (-1) (vec A D)) (mult_PP 1 (vec A B))).
rewrite scalaire_bilineaire.
rewrite H4; rewrite H5; rewrite H0.
rewrite scalaire_sym; rewrite H0; ring.
Ringvec.
rewrite H.
Ringvec.
apply def_orthogonal; auto.
Qed.
 
Lemma centre_gravite_coplanaire :
 forall A B C : PO,
 ~ alignes A B C -> coplanaires A B C (centre_gravite A B C).
unfold centre_gravite, milieu, coplanaires in |- *; intros.
right; try assumption.
exists (/ 3); exists (/ 3).
cut (3 <> 0); intros; auto with real.
apply mult_PP_regulier with 3; auto with real.
FVReplace
 (mult_PP 3
    (add_PP (cons (/ 3) A)
       (add_PP (cons (/ 3) B) (cons (1 + - (/ 3 + / 3)) C))))
 (add_PP (cons 1 A) (add_PP (cons 1 B) (cons 1 C))) 3.
VReplace
 (mult_PP 3
    (cons 1
       (barycentre (cons 1 A) (cons 2 (barycentre (cons 1 B) (cons 1 C))))))
 (cons 3 (barycentre (cons 1 A) (cons 2 (barycentre (cons 1 B) (cons 1 C))))).
repeat rewrite <- add_PP_barycentre; auto with real.
Qed.
Hint Resolve centre_gravite_coplanaire: geo.
 
Lemma exercice :
 forall A B C D E F G H I : PO,
 D <> F ->
 ~ alignes E B G ->
 parallelepipede A B C D E F G H ->
 I = centre_gravite E B G -> coplanaires E B G I /\ alignes F D I.
intros A B C D E F G H I H20 H0 H1 H51; try assumption.
rewrite H51.
split; [ auto with geo | idtac ].
cut (vec F G = vec A D).
intros H10.
unfold parallelepipede in H1.
elim H1; intros H2 H3; elim H2; intros H4 H5; try clear H2 H1; try exact H4.
elim H3; intros H2 H12; try clear H3.
cut (vec F D = mult_PP 3 (vec F (centre_gravite E B G))); intros.
cut (3 <> 0); intros; auto with real.
apply colineaire_alignes with (/ 3); auto.
rewrite H1.
Fieldvec 3; auto.
cut (add_PP (mult_PP 3 (vec (centre_gravite E B G) F)) (vec F D) = zero);
 intros.
VReplace (vec F D) (add_PP (vec F D) (mult_PP (-1) zero)).
rewrite <- H1.
Ringvec.
VReplace (vec F D) (add_PP (vec F B) (add_PP (vec B A) (vec A D))).
replace (vec B A) with (vec F E); auto.
replace (vec A D) with (vec F G); auto.
VReplace (add_PP (vec F B) (add_PP (vec F E) (vec F G)))
 (add_PP (vec F E) (add_PP (vec F B) (vec F G))).
replace (add_PP (vec F E) (add_PP (vec F B) (vec F G))) with
 (mult_PP 3
    (vec F
       (barycentre (cons 1 E) (cons 2 (barycentre (cons 1 B) (cons 1 G))))));
 auto.
unfold vec, centre_gravite, milieu in |- *; RingPP.
VReplace (add_PP (vec F B) (vec F G))
 (add_PP (mult_PP 1 (vec F B)) (mult_PP 1 (vec F G))).
rewrite
 (prop_vecteur_bary (a:=1) (b:=1) (A:=B) (B:=G)
    (G:=barycentre (cons 1 B) (cons 1 G)) F); auto.
VReplace (vec F E) (mult_PP 1 (vec F E)).
rewrite
 (prop_vecteur_bary (a:=1) (b:=2) (A:=E)
    (B:=barycentre (cons 1 B) (cons 1 G))
    (G:=barycentre (cons 1 E) (cons 2 (barycentre (cons 1 B) (cons 1 G)))) F)
 ; auto.
discrR.
discrR.
cut (vec A B = vec E F); intros; auto.
VReplace (vec B A) (mult_PP (-1) (vec A B)).
rewrite H1.
Ringvec.
rewrite H4.
rewrite H5; auto.
apply parallelepipede_parallelogramme with (1 := H1).
Qed.
 
Lemma exercice_cube :
 forall A B C D E F G H I : PO,
 D <> F ->
 ~ alignes E B G ->
 cube A B C D E F G H ->
 I = centre_gravite E B G ->
 alignes F D I /\ orthogonaux (droite F D) (plan E B G).
intros A B C D E F G H I H0 H1 H2 H51; try assumption.
elim H2; intros; clear H2.
elim H3; intros; clear H3.
elim H5; intros H3 H6; elim H6; intros H7 H8; try clear H6 H5; try exact H8.
elim H4; intros H5 H6; try clear H4; try exact H6.
split; [ try assumption | idtac ].
elim
 exercice
  with
    (A := A)
    (B := B)
    (C := C)
    (D := D)
    (E := E)
    (F := F)
    (G := G)
    (H := H)
    (I := I); [ try clear exercice; auto | auto | auto | auto | auto ].
elim H5; intros; clear H5.
elim H9; intros H5 H10; elim H10; intros H11 H12; try clear H10 H9;
 try exact H12.
elim H2; intros.
elim H10; intros H13 H14; try clear H10; try exact H14.
elim H9; intros H10 H15; try clear H9; try exact H15.
cut (scalaire (vec A B) (vec A E) = 0); intros.
cut (scalaire (vec A B) (vec A D) = 0); intros.
cut (scalaire (vec A D) (vec A E) = 0); intros.
cut (E <> B); intros.
cut (E <> G); intros.
cut (vec F D = add_PP (vec F A) (vec A D)); intros.
apply def_orthogonaux; auto.
apply def_orthogonales; auto.
apply def_orthogonal2.
rewrite scalaire_sym.
rewrite H20.
rewrite scalaire_somme_g.
replace (scalaire (vec F A) (vec E B)) with 0.
replace (scalaire (vec A D) (vec E B)) with 0.
ring.
replace (vec E B) with
 (add_PP (mult_PP (-1) (vec A E)) (mult_PP 1 (vec A B))).
rewrite scalaire_lineaire_d.
rewrite H17.
rewrite scalaire_sym.
rewrite H16.
ring.
Ringvec.
replace (vec E B) with
 (add_PP (mult_PP (-1) (vec A E)) (mult_PP 1 (vec A B))).
replace (vec F A) with
 (add_PP (mult_PP (-1) (vec A E)) (mult_PP (-1) (vec A B))).
rewrite scalaire_bilineaire.
rewrite H11; rewrite H6; rewrite H9.
rewrite scalaire_sym.
rewrite H9.
ring.
rewrite H10; rewrite H15; rewrite H13.
Ringvec.
Ringvec.
apply def_orthogonales; auto.
apply def_orthogonal2.
replace (vec E G) with (add_PP (vec A B) (vec A D)).
rewrite scalaire_somme_g.
rewrite scalaire_sym.
rewrite (scalaire_sym A D F D).
rewrite H20.
rewrite scalaire_somme_g.
rewrite scalaire_somme_g.
rewrite H12.
rewrite (scalaire_sym A D A B).
rewrite H16.
replace (vec F A) with
 (add_PP (mult_PP (-1) (vec A E)) (mult_PP (-1) (vec A B))).
rewrite scalaire_lineaire_g.
rewrite scalaire_lineaire_g.
rewrite H11; rewrite H16.
rewrite scalaire_sym.
rewrite H9.
rewrite scalaire_sym.
rewrite H17.
ring.
rewrite H10; rewrite H15; rewrite H13.
Ringvec.
replace (vec E G) with (add_PP (vec E F) (vec F G)).
rewrite H10; rewrite H15; rewrite H13.
rewrite parallelepipede_parallelogramme with (1 := H2); auto.
Ringvec.
Ringvec.
apply distance_non_nulle.
replace (vec E G) with (add_PP (mult_PP 1 (vec A B)) (mult_PP 1 (vec A D))).
rewrite scalaire_bilineaire.
rewrite H11; rewrite H12; rewrite H16.
rewrite scalaire_sym; rewrite H16.
replace (1 * 1 * 1 + 1 * 1 * 0 + (1 * 1 * 0 + 1 * 1 * 1)) with 2.
discrR.
ring.
replace (vec E G) with (add_PP (vec E F) (vec F G)).
rewrite H10; rewrite H15; rewrite H13.
rewrite parallelepipede_parallelogramme with (1 := H2); auto.
Ringvec.
Ringvec.
apply distance_non_nulle.
replace (vec E B) with
 (add_PP (mult_PP (-1) (vec A E)) (mult_PP 1 (vec A B))).
rewrite scalaire_bilineaire.
rewrite H11; rewrite H9; rewrite H6.
rewrite scalaire_sym; rewrite H9.
replace (-1 * -1 * 1 + -1 * 1 * 0 + (1 * -1 * 0 + 1 * 1 * 1)) with 2.
discrR.
ring.
Ringvec.
apply def_orthogonal; auto.
apply def_orthogonal; auto.
apply def_orthogonal; auto.
Qed.
 
Lemma equilateral_non_alignes :
 forall A B C : PO,
 A <> B ->
 scalaire (vec A B) (vec A B) = scalaire (vec A C) (vec A C) ->
 scalaire (vec A B) (vec A B) = scalaire (vec B C) (vec B C) ->
 ~ alignes A B C.
intros A B C H H0 H1; red in |- *; intros H2; try exact H2.
halignes H2 ipattern:k.
rewrite H3 in H0.
cut (vec B C = mult_PP (k + -1) (vec A B)); intros.
rewrite H4 in H1.
cut (k * k = 1); intros.
cut ((k + -1) * (k + -1) = 1); intros.
cut (k = 1 \/ k = -1); intros.
elim H7; [ intros H8; try clear H7; try exact H8 | intros H8; try clear H7 ].
rewrite H8 in H6.
absurd (0 = 1); auto with *.
rewrite <- H6; ring.
rewrite H8 in H6.
absurd ((-1 + -1) * (-1 + -1) = 1).
try discrR.
try assumption.
cut (k + -1 = 0 \/ k + 1 = 0); intros.
elim H7; [ intros H8; try clear H7; try exact H8 | intros H8; try clear H7 ].
left; try assumption.
replace k with (k + -1 + 1).
rewrite H8; ring.
ring.
right; try assumption.
replace k with (k + 1 + -1).
rewrite H8; ring.
ring.
apply Rmult_integral.
replace 0 with (k * k + -1).
ring.
rewrite H5; ring.
apply Rmult_eq_reg_l with (scalaire (vec A B) (vec A B)).
replace (scalaire (vec A B) (vec A B) * 1) with
 (scalaire (vec A B) (vec A B)).
pattern (scalaire (vec A B) (vec A B)) at 2 in |- *.
rewrite H1.
rewrite scalaire_mult_mult; ring.
ring.
unfold not in |- *; intros; apply H.
apply distance_nulle; auto.
apply Rmult_eq_reg_l with (scalaire (vec A B) (vec A B)).
replace (scalaire (vec A B) (vec A B) * 1) with
 (scalaire (vec A B) (vec A B)).
pattern (scalaire (vec A B) (vec A B)) at 2 in |- *.
rewrite H0.
rewrite scalaire_mult_mult; ring.
ring.
unfold not in |- *; intros; apply H.
apply distance_nulle; auto.
replace (vec B C) with (add_PP (vec A C) (mult_PP (-1) (vec A B))).
rewrite H3.
Ringvec.
Ringvec.
Qed.
 
Theorem the_cube :
 forall A B C D E F G H I : PO,
 cube A B C D E F G H ->
 I = centre_gravite E B G ->
 alignes F D I /\ orthogonaux (droite F D) (plan E B G).
intros A B C D E F G H I H0 H51; try assumption.
elim H0; intros.
elim H1; intros.
elim H3; intros.
elim H6; intros H7 H8; try clear H6; try exact H8.
elim H5; intros H6 H9; try clear H5; try exact H9.
elim H4; intros H5 H10; elim H10; intros H11 H12; try clear H10 H4;
 try exact H12.
elim H2; intros H4 H10; try clear H2; try exact H10.
elim H4; intros.
elim H13; intros H14 H15; elim H15; intros H16 H17; try clear H15 H13;
 try exact H16.
cut (vec A F = add_PP (mult_PP 1 (vec A B)) (mult_PP 1 (vec A E))); intros.
cut (scalaire (vec A B) (vec A E) = 0); intros.
cut (scalaire (vec A B) (vec A D) = 0); intros.
cut (scalaire (vec A D) (vec A E) = 0); intros.
apply exercice_cube with (3 := H0); auto.
apply distance_non_nulle.
replace (vec D F) with
 (add_PP (mult_PP 1 (vec A F)) (mult_PP (-1) (vec A D))).
rewrite scalaire_bilineaire.
replace (scalaire (vec A F) (vec A F)) with 2.
cut (scalaire (vec A F) (vec A D) = 0); intros.
rewrite H20; rewrite H17.
rewrite scalaire_sym; rewrite H20.
try discrR.
rewrite H13.
rewrite scalaire_lineaire_g.
rewrite H18.
rewrite scalaire_sym; rewrite H19.
ring.
rewrite H13.
rewrite scalaire_bilineaire.
rewrite H15; rewrite H10; rewrite H16.
rewrite scalaire_sym; rewrite H15.
ring.
Ringvec.
cut (vec E B = add_PP (mult_PP 1 (vec A B)) (mult_PP (-1) (vec A E))); intros.
cut (vec E G = add_PP (mult_PP 1 (vec A B)) (mult_PP 1 (vec A D))); intros.
apply equilateral_non_alignes; auto.
apply distance_non_nulle.
rewrite H20.
rewrite scalaire_bilineaire.
rewrite H15; rewrite H10; rewrite H16.
rewrite scalaire_sym; rewrite H15.
try discrR.
rewrite H20.
rewrite scalaire_bilineaire.
rewrite H21.
rewrite scalaire_bilineaire.
rewrite H15; rewrite H10; rewrite H16.
rewrite scalaire_sym; rewrite H15.
rewrite H17; rewrite H18.
rewrite scalaire_sym; rewrite H18.
ring.
replace (vec B G) with
 (add_PP (mult_PP 1 (vec E G)) (mult_PP (-1) (vec E B))).
rewrite scalaire_bilineaire.
rewrite H20.
rewrite scalaire_bilineaire.
rewrite H21.
repeat rewrite scalaire_bilineaire.
rewrite H15; rewrite H10; rewrite H16.
rewrite scalaire_sym; rewrite H15.
rewrite H17; rewrite H18.
rewrite scalaire_sym; rewrite H18.
rewrite H19; rewrite scalaire_sym; rewrite H19.
ring.
Ringvec.
rewrite <- H8.
rewrite H6; rewrite H9.
Ringvec.
Ringvec.
apply def_orthogonal; auto.
apply def_orthogonal; auto.
apply def_orthogonal; auto.
rewrite H6; rewrite H9; rewrite H7.
Ringvec.
Qed.
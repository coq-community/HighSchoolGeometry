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


Require Export homothetie_plane.
Require Export cocyclicite.
Require Export orthocentre.
Set Implicit Arguments.
Unset Strict Implicit.
 
Lemma vec_OAplusOBplusOC_orthogonal :
 forall A B C A' O M : PO,
 A' = milieu B C ->
 circonscrit O A B C ->
 vec O M = add_PP (vec O A) (add_PP (vec O B) (vec O C)) ->
 orthogonal (vec A M) (vec B C).
intros.
cut (orthogonal (vec O A') (vec B C)); intros.
replace (vec A M) with (add_PP (mult_PP (-1) (vec O A)) (vec O M));
 [ idtac | Ringvec ].
replace (add_PP (mult_PP (-1) (vec O A)) (vec O M)) with
 (add_PP (vec O B) (vec O C)).
rewrite (prop_vecteur_milieu (B:=B) (C:=C) (A':=A') O); auto with geo.
rewrite H1; Ringvec.
apply milieu_centrecirconscrit_orthogonal_segment with A; auto.
Qed.
 
Lemma vec_OAplusOBplusOC_orthocentre :
 forall A B C O M : PO,
 triangle A B C ->
 circonscrit O A B C ->
 vec O M = add_PP (vec O A) (add_PP (vec O B) (vec O C)) ->
 M = orthocentre A B C.
intros.
deroule_triangle A B C.
soit_milieu B C ipattern:A'.
lapply
 (vec_OAplusOBplusOC_orthogonal (A:=A) (B:=B) (C:=C) (A':=A') (O:=O) (M:=M));
 intros; auto.
cut (orthogonal (vec C M) (vec A B)); intros.
cut (orthogonal (vec B M) (vec C A)); intros.
apply orthocentre_def; auto with geo.
cut (orthogonal (vec A M) (vec B C)); intros; auto with geo.
soit_milieu A C ipattern:B'.
apply
 (vec_OAplusOBplusOC_orthogonal (A:=B) (B:=C) (C:=A) (A':=B') (O:=O) (M:=M));
 auto with geo.
apply circonscrit_permute; auto.
apply circonscrit_permute; auto.
rewrite H1; Ringvec.
soit_milieu A B ipattern:C'.
apply
 (vec_OAplusOBplusOC_orthogonal (A:=C) (B:=A) (C:=B) (A':=C') (O:=O) (M:=M));
 auto.
apply circonscrit_permute; auto.
rewrite H1; Ringvec.
Qed.
 
Lemma centre_gravite_prop_vecteur :
 forall A B C G O : PO,
 G = centre_gravite A B C ->
 add_PP (vec O A) (add_PP (vec O B) (vec O C)) = mult_PP 3 (vec O G).
unfold centre_gravite in |- *; intros.
discrimine B C.
rewrite <- (prop_vecteur_bary (a:=1) (b:=2) (A:=A) (B:=C) (G:=G) O); auto.
Ringvec.
discrR.
rewrite H; rewrite H0; rewrite <- (milieu_trivial C); auto.
soit_milieu B C ipattern:A'.
rewrite (prop_vecteur_milieu (B:=B) (C:=C) (A':=A') O); auto.
rewrite <- (prop_vecteur_bary (a:=1) (b:=2) (A:=A) (B:=A') (G:=G) O); auto.
Ringvec.
discrR.
rewrite H1; auto.
Qed.
Hint Resolve centre_gravite_prop_vecteur: geo.
 
Theorem droite_Euler_fort :
 forall A B C O G H : PO,
 triangle A B C ->
 G = centre_gravite A B C ->
 circonscrit O A B C ->
 H = orthocentre A B C -> vec O H = mult_PP 3 (vec O G).
intros.
rewrite <- (centre_gravite_prop_vecteur (A:=A) (B:=B) (C:=C) (G:=G) O); auto.
elim
 existence_representant_som_vecteur with (A := O) (B := B) (C := O) (D := C);
 intros E H4; try clear existence_representant_som_vecteur; 
 rewrite <- H4.
elim
 existence_representant_som_vecteur with (A := O) (B := A) (C := O) (D := E);
 intros M H5; try clear existence_representant_som_vecteur; 
 rewrite <- H5.
cut (M = H); intros.
rewrite <- H6; auto.
rewrite H3.
apply vec_OAplusOBplusOC_orthocentre with O; auto.
rewrite <- H4; auto.
Qed.
 
Theorem droite_Euler :
 forall A B C O G H : PO,
 triangle A B C ->
 G = centre_gravite A B C ->
 circonscrit O A B C -> H = orthocentre A B C -> alignes O G H.
intros.
apply colineaire_alignes with 3; auto.
apply droite_Euler_fort with (1 := H0); auto.
Qed.
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


Require Export contact.
Require Export reflexion_plane.
Require Export similitudes_directes.
Set Implicit Arguments.
Unset Strict Implicit.
Hint Resolve translation_trivial rec_translation_vecteur: geo.
 
Lemma translation_isometrie :
 forall A A' B B' C C' : PO,
 B' = translation A A' B ->
 C' = translation A A' C -> distance B' C' = distance B C.
intros.
apply Rsqr_inj; auto with real geo.
unfold Rsqr in |- *.
repeat rewrite <- carre_scalaire_distance.
rewrite <-
 (translation_bipoint (I:=A) (J:=A') (A:=B) (A':=B') (B:=C) (B':=C'))
 ; auto.
Qed.
 
Lemma translation_conserve_orthogonalite :
 forall I J A A' B B' M M' : PO,
 A' = translation I J A ->
 B' = translation I J B ->
 M' = translation I J M ->
 orthogonal (vec A B) (vec A M) -> orthogonal (vec A' B') (vec A' M').
intros.
rewrite <-
 (translation_bipoint (I:=I) (J:=J) (A:=A) (A':=A') (B:=M) (B':=M'))
 ; auto.
rewrite <-
 (translation_bipoint (I:=I) (J:=J) (A:=A) (A':=A') (B:=B) (B':=B'))
 ; auto.
Qed.
 
Lemma translation_conserve_contact_cercle_droite :
 forall I J A A' B B' M M' O O' : PO,
 A' = translation I J A ->
 B' = translation I J B ->
 M' = translation I J M ->
 O' = translation I J O ->
 tangente_cercle O A B M -> tangente_cercle O' A' B' M'.
icercle.
rewrite
 (translation_isometrie (A:=I) (A':=J) (B:=O) (B':=O') (C:=A) (C':=A'))
 ; auto.
rewrite
 (translation_isometrie (A:=I) (A':=J) (B:=O) (B':=O') (C:=B) (C':=B'))
 ; auto.
apply
 (translation_conserve_orthogonalite (I:=I) (J:=J) (A:=B) (A':=B') (B:=M)
    (B':=M') (M:=O) (M':=O')); auto.
Qed.
 
Lemma translation_conserve_contact_cercle_cercle :
 forall I J A A' B B' K K' O O' : PO,
 O <> A ->
 K <> B ->
 A' = translation I J A ->
 B' = translation I J B ->
 K' = translation I J K ->
 O' = translation I J O ->
 cercles_tangents O A K B -> cercles_tangents O' A' K' B'.
intros.
elim
 cercles_tangents_tangente_commune with (O := O) (A := A) (O' := K) (A' := B);
 [ intros T H6; elim H6;
    [ intros M H7; elim H7;
       [ intros H8 H9; elim H9;
          [ intros H10 H11; try clear H9 H7 H6; try exact H10 ] ] ]
 | auto
 | auto
 | auto ].
elim existence_representant_vecteur with (A := T) (B := I) (C := J);
 [ intros T' H6; try clear existence_representant_vecteur; try exact H6 ].
elim existence_representant_vecteur with (A := M) (B := I) (C := J);
 [ intros M' H7; try clear existence_representant_vecteur; try exact H7 ].
assert (distance O' A' = distance O A).
rewrite <-
 (translation_isometrie (A:=I) (A':=J) (B:=O) (B':=O') (C:=A) (C':=A'))
 ; auto with geo.
assert (distance K' B' = distance K B).
rewrite <-
 (translation_isometrie (A:=I) (A':=J) (B:=K) (B':=K') (C:=B) (C':=B'))
 ; auto with geo.
assert (O' <> A').
apply (isometrie_distinct (A:=O) (B:=A) (A':=O') (B':=A')); auto.
assert (K' <> B').
apply (isometrie_distinct (A:=K) (B:=B) (A':=K') (B':=B')); auto.
assert (distance T' M' = distance T M).
rewrite <-
 (translation_isometrie (A:=I) (A':=J) (B:=T) (B':=T') (C:=M) (C':=M'))
 ; auto with geo.
assert (T' <> M').
apply (isometrie_distinct (A:=T) (B:=M) (A':=T') (B':=M')); auto.
apply tangente_commune_cercles_tangents with (B := T') (M := M'); auto.
apply translation_conserve_contact_cercle_droite with (1 := H1) (5 := H10);
 auto with geo.
apply translation_conserve_contact_cercle_droite with (1 := H2) (5 := H11);
 auto with geo.
Qed.
 
Lemma homothetie_conserve_orthogonalite :
 forall (k : R) (I A A' B B' M M' : PO),
 k <> 0 :>R ->
 A' = homothetie k I A :>PO ->
 B' = homothetie k I B :>PO ->
 M' = homothetie k I M :>PO ->
 orthogonal (vec A B) (vec A M) -> orthogonal (vec A' B') (vec A' M').
intros.
generalize (homothetie_bipoint (k:=k) (I:=I) (A:=A) (B:=B) (A':=A') (B':=B'));
 intros.
generalize (homothetie_bipoint (k:=k) (I:=I) (A:=A) (B:=M) (A':=A') (B':=M'));
 intros.
assert (orthogonal (vec A B) (vec A' M')).
apply ortho_sym; rewrite H5; auto with geo.
rewrite H4; auto with geo.
Qed.
 
Lemma homothetie_conserve_contact_cercle_droite :
 forall (k : R) (I A A' B B' M M' O O' : PO),
 k <> 0 :>R ->
 A' = homothetie k I A :>PO ->
 B' = homothetie k I B :>PO ->
 M' = homothetie k I M :>PO ->
 O' = homothetie k I O ->
 tangente_cercle O A B M -> tangente_cercle O' A' B' M'.
icercle.
rewrite (distance_homothetie (k:=k) (I:=I) (A:=O) (A':=O') (B:=A) (B':=A'));
 auto.
rewrite (distance_homothetie (k:=k) (I:=I) (A:=O) (A':=O') (B:=B) (B':=B'));
 auto.
rewrite H5; auto.
apply
 (homothetie_conserve_orthogonalite (k:=k) (I:=I) (A:=B) (A':=B') (B:=M)
    (B':=M') (M:=O) (M':=O')); auto.
Qed.
 
Lemma produit_distance_distinct :
 forall (A B C D : PO) (k : R),
 k <> 0 -> A <> B -> distance C D = k * distance A B -> C <> D.
intros.
contrapose H0.
assert (distance A B = 0); auto with geo.
replace (distance A B) with (/ k * distance C D).
rewrite H2.
replace (distance D D) with 0.
ring.
symmetry  in |- *; auto with geo.
rewrite H1.
field; auto.
Qed.
 
Lemma homothetie_conserve_contact_cercle_cercle :
 forall (k : R) (I J A A' B B' K K' O O' : PO),
 O <> A ->
 K <> B ->
 k <> 0 ->
 A' = homothetie k I A ->
 B' = homothetie k I B ->
 K' = homothetie k I K ->
 O' = homothetie k I O ->
 cercles_tangents O A K B -> cercles_tangents O' A' K' B'.
intros.
elim
 cercles_tangents_tangente_commune with (O := O) (A := A) (O' := K) (A' := B);
 [ intros T H7; elim H7;
    [ intros M H8; elim H8;
       [ intros H9 H10; elim H10;
          [ intros H11 H12; try clear H10 H8 H7; try exact H11 ] ] ]
 | auto
 | auto
 | auto ].
elim existence_homothetique with (k := k) (I := I) (A := T); [ intros T' H7 ].
elim existence_homothetique with (k := k) (I := I) (A := M); [ intros M' H8 ].
assert (O' <> A').
apply image_homothetie_distincts with (3 := H5) (4 := H2); auto.
assert (K' <> B').
apply image_homothetie_distincts with (3 := H4) (4 := H3); auto.
assert (T' <> M').
apply image_homothetie_distincts with (3 := H7) (4 := H8); auto.
apply tangente_commune_cercles_tangents with (B := T') (M := M'); auto.
apply homothetie_conserve_contact_cercle_droite with (2 := H2) (6 := H11);
 auto with geo.
apply homothetie_conserve_contact_cercle_droite with (2 := H3) (6 := H12);
 auto with geo.
Qed.
 
Lemma reflexion_conserve_orthogonalite :
 forall I J A A' B B' M M' : PO,
 I <> J ->
 A' = reflexion I J A :>PO ->
 B' = reflexion I J B :>PO ->
 M' = reflexion I J M :>PO ->
 orthogonal (vec A B) (vec A M) -> orthogonal (vec A' B') (vec A' M').
intros.
assert (distance A' B' = distance A B).
rewrite <-
 (reflexion_isometrie (A:=I) (B:=J) (M:=A) (M':=A') (N:=B) (N':=B'))
 ; auto with geo.
assert (distance A' M' = distance A M).
rewrite <-
 (reflexion_isometrie (A:=I) (B:=J) (M:=A) (M':=A') (N:=M) (N':=M'))
 ; auto with geo.
discrimine A B.
assert (distance A' B' = 0).
rewrite H4; rewrite H6; auto with geo.
assert (A' = B'); auto with geo.
rewrite H8.
VReplace (vec B' B') zero; auto with geo.
discrimine A M.
assert (distance A' M' = 0).
rewrite H5; rewrite H7; auto with geo.
assert (A' = M'); auto with geo.
rewrite H9.
VReplace (vec M' M') zero; auto with geo.
assert (~ alignes A B M); auto with geo.
assert (B <> M); auto with geo.
apply non_alignes_distincts2 with A; auto.
assert (cons_AV (vec A' B') (vec A' M') = opp (cons_AV (vec A B) (vec A M))).
apply reflexion_anti_deplacement with (A := I) (B := J); auto.
assert (double_AV (cons_AV (vec A M) (vec A B)) = image_angle pi).
apply orthogonal_angles; auto with geo.
apply angles_orthogonal.
apply (isometrie_distinct (A:=A) (B:=B) (A':=A') (B':=B')); auto.
apply (isometrie_distinct (A:=A) (B:=M) (A':=A') (B':=M')); auto.
rewrite H10.
rewrite def_opp; auto.
Qed.
 
Lemma reflexion_conserve_contact_cercle_droite :
 forall I J A A' B B' M M' O O' : PO,
 I <> J ->
 A' = reflexion I J A ->
 B' = reflexion I J B ->
 M' = reflexion I J M ->
 O' = reflexion I J O ->
 tangente_cercle O A B M -> tangente_cercle O' A' B' M'.
icercle.
rewrite <-
 (reflexion_isometrie (A:=I) (B:=J) (M:=O) (M':=O') (N:=A) (N':=A'))
 ; auto.
rewrite <-
 (reflexion_isometrie (A:=I) (B:=J) (M:=O) (M':=O') (N:=B) (N':=B'))
 ; auto.
apply
 (reflexion_conserve_orthogonalite (I:=I) (J:=J) (A:=B) (A':=B') (B:=M)
    (B':=M') (M:=O) (M':=O')); auto.
Qed.
 
Lemma reflexion_conserve_contact_cercle_cercle :
 forall I J A A' B B' K K' O O' : PO,
 I <> J ->
 O <> A ->
 K <> B ->
 A' = reflexion I J A ->
 B' = reflexion I J B ->
 K' = reflexion I J K ->
 O' = reflexion I J O ->
 cercles_tangents O A K B -> cercles_tangents O' A' K' B'.
intros.
elim
 cercles_tangents_tangente_commune with (O := O) (A := A) (O' := K) (A' := B);
 [ intros T H7; elim H7;
    [ intros M H8; elim H8;
       [ intros H9 H10; elim H10;
          [ intros H11 H12; try clear H10 H8 H7; try exact H11 ] ] ]
 | auto
 | auto
 | auto ].
elim existence_reflexion_AB with (A := I) (B := J) (M := T);
 [ intros T' H7; try clear existence_reflexion_AB; try exact H7 | auto ].
elim existence_reflexion_AB with (A := I) (B := J) (M := M);
 [ intros M' H8; try clear existence_reflexion_AB; try exact H7 | auto ].
assert (distance O' A' = distance O A).
rewrite <-
 (reflexion_isometrie (A:=I) (B:=J) (M:=O) (M':=O') (N:=A) (N':=A'))
 ; auto.
assert (O' <> A').
apply (isometrie_distinct (A:=O) (B:=A) (A':=O') (B':=A')); auto.
assert (distance K' B' = distance K B).
rewrite <-
 (reflexion_isometrie (A:=I) (B:=J) (M:=K) (M':=K') (N:=B) (N':=B'))
 ; auto.
assert (K' <> B').
apply (isometrie_distinct (A:=K) (B:=B) (A':=K') (B':=B')); auto.
assert (distance T' M' = distance T M).
rewrite <-
 (reflexion_isometrie (A:=I) (B:=J) (M:=T) (M':=T') (N:=M) (N':=M'))
 ; auto.
assert (T' <> M').
apply (isometrie_distinct (A:=T) (B:=M) (A':=T') (B':=M')); auto.
apply tangente_commune_cercles_tangents with (B := T') (M := M'); auto.
apply reflexion_conserve_contact_cercle_droite with (2 := H2) (6 := H11);
 auto with geo.
apply reflexion_conserve_contact_cercle_droite with (2 := H3) (6 := H12);
 auto with geo.
Qed.
 
Lemma rotation_conserve_orthogonalite :
 forall (I A B M A' B' M' : PO) (a : R),
 A' = rotation I a A ->
 B' = rotation I a B ->
 M' = rotation I a M ->
 orthogonal (vec A B) (vec A M) -> orthogonal (vec A' B') (vec A' M').
intros.
assert (distance A' B' = distance A B).
rewrite <- (rotation_isometrie (I:=I) (A:=A) (B:=B) (A':=A') (B':=B') (a:=a));
 auto with geo.
assert (distance A' M' = distance A M).
rewrite <- (rotation_isometrie (I:=I) (A:=A) (B:=M) (A':=A') (B':=M') (a:=a));
 auto with geo.
discrimine A B.
assert (distance A' B' = 0).
rewrite H3; rewrite H5; auto with geo.
assert (A' = B'); auto with geo.
rewrite H7.
VReplace (vec B' B') zero; auto with geo.
discrimine A M.
assert (distance A' M' = 0).
rewrite H4; rewrite H6; auto with geo.
assert (A' = M'); auto with geo.
rewrite H8.
VReplace (vec M' M') zero; auto with geo.
assert (cons_AV (vec A B) (vec A M) = cons_AV (vec A' B') (vec A' M')).
apply rotation_conserve_angle with (a := a) (I := I); auto.
assert (double_AV (cons_AV (vec A B) (vec A M)) = image_angle pi).
apply orthogonal_angles; auto with geo.
apply angles_orthogonal.
apply (isometrie_distinct (A:=A) (B:=B) (A':=A') (B':=B')); auto.
apply (isometrie_distinct (A:=A) (B:=M) (A':=A') (B':=M')); auto.
rewrite <- H7; auto.
Qed.
 
Lemma rotation_conserve_contact_cercle_droite :
 forall (I A A' B B' M M' O O' : PO) (a : R),
 A' = rotation I a A ->
 B' = rotation I a B ->
 M' = rotation I a M ->
 O' = rotation I a O ->
 tangente_cercle O A B M -> tangente_cercle O' A' B' M'.
icercle.
rewrite (rotation_isometrie (I:=I) (A:=O) (B:=A) (A':=O') (B':=A') (a:=a));
 auto.
rewrite (rotation_isometrie (I:=I) (A:=O) (B:=B) (A':=O') (B':=B') (a:=a));
 auto.
apply
 (rotation_conserve_orthogonalite (I:=I) (A:=B) (B:=M) (M:=O) (A':=B')
    (B':=M') (M':=O') (a:=a)); auto.
Qed.
 
Lemma rotation_conserve_contact_cercle_cercle :
 forall (I A A' B B' K K' O O' : PO) (a : R),
 O <> A ->
 K <> B ->
 A' = rotation I a A ->
 B' = rotation I a B ->
 K' = rotation I a K ->
 O' = rotation I a O ->
 cercles_tangents O A K B -> cercles_tangents O' A' K' B'.
intros.
elim
 cercles_tangents_tangente_commune with (O := O) (A := A) (O' := K) (A' := B);
 [ intros T H6; elim H6;
    [ intros M H7; elim H7;
       [ intros H8 H9; elim H9;
          [ intros H10 H11; try clear H9 H7 H6; try exact H10 ] ] ]
 | auto
 | auto
 | auto ].
elim existence_rotation_Ia with (I := I) (M := T) (a := a);
 [ intros T' H6; try clear existence_rotation_Ia; try exact H6 ].
elim existence_rotation_Ia with (I := I) (M := M) (a := a);
 [ intros M' H7; try clear existence_rotation_Ia; try exact H7 ].
assert (O' <> A').
apply (image_bipoint_distinct (I:=I) (A:=O) (B:=A) (A':=O') (B':=A') (a:=a));
 auto.
assert (K' <> B').
apply (image_bipoint_distinct (I:=I) (A:=K) (B:=B) (A':=K') (B':=B') (a:=a));
 auto.
assert (T' <> M').
apply (image_bipoint_distinct (I:=I) (A:=T) (B:=M) (A':=T') (B':=M') (a:=a));
 auto.
apply tangente_commune_cercles_tangents with (B := T') (M := M'); auto.
apply rotation_conserve_contact_cercle_droite with (1 := H1) (5 := H10);
 auto with geo.
apply rotation_conserve_contact_cercle_droite with (1 := H2) (5 := H11);
 auto with geo.
Qed.
 
Lemma similitude_conserve_orthogonalite :
 forall (I A B M A' B' M' : PO) (k a : R),
 k > 0 ->
 A' = similitude I k a A ->
 B' = similitude I k a B ->
 M' = similitude I k a M ->
 orthogonal (vec A B) (vec A M) -> orthogonal (vec A' B') (vec A' M').
intros.
assert (distance A' B' = k * distance A B).
rewrite <-
 (distance_similitude (k:=k) (a:=a) (I:=I) (A:=A) (B:=B) (A':=A') (B':=B'))
 ; auto with geo.
assert (distance A' M' = k * distance A M).
rewrite <-
 (distance_similitude (k:=k) (a:=a) (I:=I) (A:=A) (B:=M) (A':=A') (B':=M'))
 ; auto with geo.
discrimine A B.
assert (distance A' B' = 0).
rewrite H4; rewrite H6.
replace (distance B B) with 0.
ring.
symmetry  in |- *; auto with geo.
assert (A' = B'); auto with geo.
rewrite H8.
VReplace (vec B' B') zero; auto with geo.
discrimine A M.
assert (distance A' M' = 0).
rewrite H5; rewrite H7.
replace (distance M M) with 0.
ring.
symmetry  in |- *; auto with geo.
assert (A' = M'); auto with geo.
rewrite H9.
VReplace (vec M' M') zero; auto with geo.
assert (cons_AV (vec A B) (vec A M) = cons_AV (vec A' B') (vec A' M')).
apply similitude_conserve_angle with (a := a) (k := k) (I := I); auto.
assert (double_AV (cons_AV (vec A B) (vec A M)) = image_angle pi).
apply orthogonal_angles; auto with geo.
assert (k <> 0); auto with real.
apply angles_orthogonal.
apply produit_distance_distinct with (3 := H4); auto.
apply produit_distance_distinct with (3 := H5); auto.
rewrite <- H8; auto.
Qed.
 
Lemma similitude_conserve_contact_cercle_droite :
 forall (I A B M A' B' M' O O' : PO) (k a : R),
 k > 0 ->
 A' = similitude I k a A ->
 B' = similitude I k a B ->
 M' = similitude I k a M ->
 O' = similitude I k a O ->
 tangente_cercle O A B M -> tangente_cercle O' A' B' M'.
icercle.
rewrite
 (distance_similitude (k:=k) (a:=a) (I:=I) (A:=O) (B:=A) (A':=O') (B':=A'))
 ; auto.
rewrite
 (distance_similitude (k:=k) (a:=a) (I:=I) (A:=O) (B:=B) (A':=O') (B':=B'))
 ; auto.
rewrite H5; auto.
apply
 (similitude_conserve_orthogonalite (I:=I) (A:=B) (B:=M) (M:=O) (A':=B')
    (B':=M') (M':=O') (k:=k) (a:=a)); auto.
Qed.
 
Lemma similitude_conserve_contact_cercle_cercle :
 forall (I A A' B B' K K' O O' : PO) (k a : R),
 k > 0 ->
 O <> A ->
 K <> B ->
 A' = similitude I k a A ->
 B' = similitude I k a B ->
 K' = similitude I k a K ->
 O' = similitude I k a O ->
 cercles_tangents O A K B -> cercles_tangents O' A' K' B'.
intros.
elim
 cercles_tangents_tangente_commune with (O := O) (A := A) (O' := K) (A' := B);
 [ intros T H7; elim H7;
    [ intros M H8; elim H8;
       [ intros H9 H10; elim H10;
          [ intros H11 H12;
             try clear H10 H8 H7 cercles_tangents_tangente_commune;
             try exact H11 ] ] ]
 | auto
 | auto
 | auto ].
elim existence_similitude_Ika with (I := I) (M := T) (k := k) (a := a);
 [ intros T' H13; try clear existence_similitude_Ika; try exact H13 | auto ].
elim existence_similitude_Ika with (I := I) (M := M) (k := k) (a := a);
 [ intros M' H14; try clear existence_similitude_Ika; try exact H14 | auto ].
assert (distance O' A' = k * distance O A).
rewrite <-
 (distance_similitude (k:=k) (a:=a) (I:=I) (A:=O) (B:=A) (A':=O') (B':=A'))
 ; auto with geo.
assert (distance K' B' = k * distance K B).
rewrite <-
 (distance_similitude (k:=k) (a:=a) (I:=I) (A:=K) (B:=B) (A':=K') (B':=B'))
 ; auto with geo.
assert (distance T' M' = k * distance T M).
rewrite <-
 (distance_similitude (k:=k) (a:=a) (I:=I) (A:=T) (B:=M) (A':=T') (B':=M'))
 ; auto with geo.
assert (k <> 0); auto with real.
assert (O' <> A').
apply produit_distance_distinct with (3 := H15); auto.
assert (K' <> B').
apply produit_distance_distinct with (3 := H16); auto.
assert (T' <> M').
apply produit_distance_distinct with (3 := H17); auto.
apply tangente_commune_cercles_tangents with (B := T') (M := M'); auto.
apply similitude_conserve_contact_cercle_droite with (2 := H2) (6 := H11);
 auto with geo.
apply similitude_conserve_contact_cercle_droite with (2 := H3) (6 := H12);
 auto with geo.
Qed.
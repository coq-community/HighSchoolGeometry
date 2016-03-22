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


Require Export parallelisme_concours.
Require Export coplanarite.
Set Implicit Arguments.
Unset Strict Implicit.
 
Lemma paralleles_coplanaires :
 forall A B C D : PO,
 A <> B ->
 C <> D -> paralleles (droite A B) (droite C D) -> coplanaires A B C D.
unfold coplanaires in |- *; intros A B C D H H10 H0.
elim def_paralleles2 with (3 := H0); auto.
intros k H1.
elim (classic (k = 0)); intros.
rewrite H2 in H1.
absurd (A = B); auto.
apply conversion_PP with (a := 1) (b := 1); auto with *.
RingPP1 H1.
RingPP.
right; try assumption.
exists (- / k).
exists (/ k).
apply mult_PP_regulier with k; auto.
replace
 (mult_PP k
    (add_PP (cons (- / k) A)
       (add_PP (cons (/ k) B) (cons (1 + - (- / k + / k)) C)))) with
 (add_PP (cons (-1) A) (add_PP (cons 1 B) (cons k C))).
RingPP1 H1.
RingPP.
FieldPP k.
Qed.
 
Lemma concours_coplanaires :
 forall A B C D : PO,
 A <> B :>PO ->
 C <> D :>PO -> concours (droite A B) (droite C D) -> coplanaires A B D C.
unfold coplanaires in |- *; intros A B C D H20 H21 H11.
elim def_concours2 with (A := A) (B := B) (C := C) (D := D);
 [ intros I H0; elim H0; intros H1 H2; try clear H0; try exact H2
 | auto
 | auto
 | auto ].
hPPalignes H2 ipattern:k.
hPPalignes H1 ipattern:k0.
cut
 (add_PP (cons k C) (cons (1 + - k) D) =
  add_PP (cons k0 A) (cons (1 + - k0) B)); intros.
elim (classic (k = 0)); intros.
left; try assumption.
unfold alignes, alignes1 in |- *.
right; try assumption.
rewrite H0 in H.
exists k0.
VReplace (cons 1 D) (cons (1 + -0) D).
RingPP2 H; RingPP.
right; try assumption.
exists (/ k * k0).
exists (/ k * (1 + - k0)).
apply mult_PP_regulier with k; auto.
VReplace (mult_PP k (cons 1 C)) (cons k C).
RingPP1 H.
FieldPP k.
rewrite <- H2; trivial.
Qed.
 
Lemma droites_non_paralleles :
 forall A B C D : PO,
 A <> B :>PO ->
 C <> D :>PO ->
 ~ paralleles (droite C D) (droite A B) ->
 concours (droite C D) (droite A B) \/ ~ coplanaires A B C D.
intros A B C D H20 H21 H; try assumption.
elim (classic (coplanaires A B C D)); intros.
left; try assumption.
hPPcoplanaires H0 ipattern:a ipattern:b.
apply def_concours with C; auto with geo.
cut (a + b <> 0); intros.
apply def_concours with (barycentre (cons a A) (cons b B)); auto.
replace (barycentre (cons a A) (cons b B)) with
 (barycentre (cons (- (1 + - (a + b))) C) (cons 1 D)).
apply barycentre_alignes.
replace (- (1 + - (a + b)) + 1) with (a + b); auto.
ring.
apply conversion_PP with (a := - (1 + - (a + b)) + 1) (b := a + b).
rewrite <- add_PP_barycentre; auto.
rewrite <- add_PP_barycentre; auto.
rewrite H0.
RingPP.
replace (- (1 + - (a + b)) + 1) with (a + b); auto.
ring.
replace (- (1 + - (a + b)) + 1) with (a + b); auto.
ring.
ring.
apply barycentre_alignes; auto.
unfold not in |- *; intros; apply H.
apply def_paralleles with (- a); auto.
rewrite H0.
rewrite H1.
replace b with (- a + (a + b)); auto.
rewrite H1.
RingPP.
ring.
right; try assumption.
Qed.
 
Lemma concours_sym :
 forall A B C D : PO,
 A <> B :>PO ->
 C <> D :>PO ->
 concours (droite A B) (droite C D) -> concours (droite C D) (droite A B).
intros A B C D H10 H11 H; try assumption.
elim def_concours2 with (3 := H); auto; intros.
apply def_concours with x; auto.
elim H0; intros H1 H2; try clear H0; try exact H2.
elim H0; intros H1 H2; try clear H0; try exact H1.
Qed.
Hint Resolve concours_sym paralleles_sym paralleles_trans: geo.
 
Theorem position_relative_droites_espace :
 forall A B C D : PO,
 A <> B :>PO ->
 C <> D :>PO ->
 ~ coplanaires A B C D \/
 concours (droite A B) (droite C D) \/ paralleles (droite A B) (droite C D).
intros A B C D H10 H; try assumption.
elim (classic (paralleles (droite A B) (droite C D))); intros.
right; right; try assumption.
elim droites_non_paralleles with (A := A) (B := B) (C := C) (D := D);
 auto with geo; intros.
Qed.
 
Theorem position_relative_droites_coplanaires :
 forall A B C D : PO,
 A <> B :>PO ->
 C <> D :>PO ->
 coplanaires A B C D ->
 concours (droite A B) (droite C D) \/ paralleles (droite A B) (droite C D).
intros A B C D H10 H H0; try assumption.
elim
 position_relative_droites_espace with (A := A) (B := B) (C := C) (D := D);
 [ intros H1; try clear position_relative_droites_espace
 | intros H1; try clear position_relative_droites_espace; auto
 | auto
 | auto ].
absurd (coplanaires A B C D); auto.
Qed.
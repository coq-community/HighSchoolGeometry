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


Require Export milieu.
Set Implicit Arguments.
Unset Strict Implicit.
Parameter DR : Type.
Parameter droite : PO -> PO -> DR.
 
Axiom
  droite_permute : forall A B : PO, A <> B :>PO -> droite A B = droite B A.
Hint Resolve droite_permute: geo.
 
Axiom
  alignes_droite :
    forall A B C : PO,
    A <> B :>PO -> A <> C :>PO -> alignes A B C -> droite A B = droite A C.
 
Lemma alignes_droite2 :
 forall A B C : PO,
 A <> B :>PO -> B <> C :>PO -> alignes A B C -> droite A B = droite B C.
intros.
rewrite droite_permute; auto.
apply alignes_droite; auto with geo.
Qed.
Hint Resolve alignes_droite alignes_droite2: geo.
Parameter paralleles : DR -> DR -> Prop.
 
Axiom
  def_paralleles :
    forall (A B C D : PO) (k : R),
    A <> B :>PO ->
    C <> D :>PO ->
    add_PP (cons 1 B) (cons (-1) A) = add_PP (cons k D) (cons (- k) C) ->
    paralleles (droite A B) (droite C D).
 
Axiom
  def_paralleles2 :
    forall A B C D : PO,
    A <> B :>PO ->
    C <> D :>PO ->
    paralleles (droite A B) (droite C D) ->
    exists k : R,
      add_PP (cons 1 B) (cons (-1) A) = add_PP (cons k D) (cons (- k) C) :>PP.
 
Lemma paralleles_refl :
 forall A B : PO, A <> B :>PO -> paralleles (droite A B) (droite A B).
intros A B H; try assumption.
apply def_paralleles with (k := 1); auto.
Qed.
Hint Resolve paralleles_refl: geo.
 
Lemma paralleles_sym :
 forall A B C D : PO,
 A <> B ->
 C <> D ->
 paralleles (droite A B) (droite C D) -> paralleles (droite C D) (droite A B).
intros A B C D H H1 H0; try assumption.
elim def_paralleles2 with (3 := H0); intros; auto.
elim (classic (x = 0)); intros.
rewrite H3 in H2.
absurd (A = B); auto.
apply conversion_PP with (a := 1) (b := 1); auto.
RingPP1 H2; RingPP; auto with *.
auto with *.
apply def_paralleles with (k := / x); auto.
apply mult_PP_regulier with x; auto.
VReplace (mult_PP x (add_PP (cons 1 D) (cons (-1) C)))
 (add_PP (cons x D) (cons (- x) C)).
rewrite <- H2.
FieldPP x.
Qed.
 
Lemma paralleles_trans :
 forall A B C D E F : PO,
 A <> B ->
 C <> D :>PO ->
 E <> F :>PO ->
 paralleles (droite A B) (droite C D) ->
 paralleles (droite C D) (droite E F) -> paralleles (droite A B) (droite E F).
intros A B C D E F H H10 H11 H0 H1; try assumption.
elim def_paralleles2 with (3 := H0); intros; auto.
elim def_paralleles2 with (3 := H1); intros; auto.
apply def_paralleles with (k := x * x0); auto.
rewrite H2.
elim (classic (x = 0)); intros.
rewrite H4 in H2.
absurd (A = B); auto.
apply conversion_PP with (a := 1) (b := 1); auto.
RingPP1 H2; RingPP; auto with *.
auto with *.
replace (add_PP (cons x D) (cons (- x) C)) with
 (mult_PP x (add_PP (cons 1 D) (cons (-1) C))).
rewrite H3.
RingPP.
RingPP.
Qed.
 
Lemma paralleles_vecteur :
 forall A B C D : PO,
 A <> B :>PO ->
 C <> D :>PO ->
 paralleles (droite A B) (droite C D) ->
 exists k : R, vec A B = mult_PP k (vec C D) :>PP.
unfold vec in |- *; intros.
elim def_paralleles2 with (3 := H1); auto.
intros k H2; try assumption.
exists k.
RingPP1 H2; RingPP.
Qed.
 
Lemma colineaires_paralleles :
 forall (k : R) (A B C D : PO),
 A <> B :>PO ->
 C <> D :>PO ->
 vec A B = mult_PP k (vec C D) -> paralleles (droite A B) (droite C D).
unfold vec in |- *; intros.
apply def_paralleles with k; auto.
RingPP1 H1; RingPP.
Qed.
 
Lemma alignes_paralleles :
 forall A B C : PO,
 A <> B -> A <> C -> alignes A B C -> paralleles (droite A B) (droite A C).
intros.
apply paralleles_sym; auto.
halignes H1 ipattern:x.
apply colineaires_paralleles with x; intros; auto.
Qed.
 
Lemma paralleles_ABBA :
 forall A B : PO, A <> B -> paralleles (droite A B) (droite B A).
intros.
apply def_paralleles with (-1); auto.
RingPP.
Qed.
Hint Immediate paralleles_ABBA paralleles_sym: geo.
 
Lemma non_paralleles_trans :
 forall A B C D E F : PO,
 A <> B :>PO ->
 C <> D :>PO ->
 E <> F :>PO ->
 paralleles (droite A B) (droite C D) ->
 ~ paralleles (droite A B) (droite E F) ->
 ~ paralleles (droite C D) (droite E F).
intros; red in |- *; intros.
apply H3.
apply paralleles_trans with (4 := H2); auto.
Qed.
Hint Resolve alignes_paralleles: geo.
 
Lemma paralleles_alignes :
 forall A B C D : PO,
 A <> B :>PO ->
 C <> D :>PO ->
 paralleles (droite A B) (droite C D) -> alignes A B C -> alignes A B D.
intros.
elim (paralleles_vecteur (A:=C) (B:=D) (C:=A) (D:=B)); intros; auto with geo.
halignes H2 ipattern:x0.
apply colineaire_alignes with (x + x0).
VReplace (vec A D) (add_PP (vec A C) (vec C D)).
rewrite H3; rewrite H4; Ringvec.
Qed.
 
Lemma paralleles_alignes1 :
 forall A B C D E F : PO,
 A <> B :>PO ->
 C <> D :>PO ->
 vec E F = vec A B :>PP ->
 paralleles (droite A B) (droite C D) -> alignes C D E -> alignes C D F.
intros A B C D E F H H0 H1 H2 H3; try assumption.
elim (paralleles_vecteur (A:=A) (B:=B) (C:=C) (D:=D)); intros; auto.
halignes H3 ipattern:x0.
apply colineaire_alignes with (x0 + x).
VReplace (vec C F) (add_PP (vec C E) (vec E F)).
rewrite H5; rewrite H1; rewrite H4.
Ringvec.
Qed.
 
Lemma paralleles_alignes2 :
 forall A B C D E F : PO,
 A <> B :>PO ->
 C <> D :>PO ->
 vec E F = vec A B :>PP ->
 paralleles (droite A B) (droite C D) -> alignes C D E -> alignes F C E.
intros A B C D E F H H0 H1 H2 H3; try assumption.
elim (paralleles_vecteur (A:=C) (B:=D) (C:=A) (D:=B)); intros; auto with geo.
halignes H3 ipattern:x0.
rewrite H4 in H5.
discrimine F C.
cut (1 + x0 * x <> 0); intros.
apply colineaire_alignes with (/ (1 + x0 * x)).
VReplace (vec F C) (add_PP (vec F E) (mult_PP (-1) (vec C E))).
VReplace (vec F E) (mult_PP (-1) (vec E F)).
rewrite H1; rewrite H5.
Fieldvec (1 + x0 * x).
red in |- *; intros; apply H6.
apply vecteur_nul_conf.
VReplace (vec F C) (add_PP (mult_PP (-1) (vec E F)) (mult_PP (-1) (vec C E))).
rewrite H1; rewrite H5.
VReplace
 (add_PP (mult_PP (-1) (vec A B))
    (mult_PP (-1) (mult_PP x0 (mult_PP x (vec A B)))))
 (mult_PP (-1) (mult_PP (1 + x0 * x) (vec A B))).
rewrite H7; Ringvec.
Qed.
 
Lemma paralleles_alignes3 :
 forall A B C D : PO,
 A <> B :>PO ->
 C <> D :>PO ->
 paralleles (droite A B) (droite C D) -> alignes C D A -> alignes A C B.
intros A B C D H H0 H1 H2; try assumption.
elim (paralleles_vecteur (A:=A) (B:=B) (C:=C) (D:=D)); intros; auto.
discrimine C A.
assert (alignes C A D); auto with geo.
halignes H5 ipattern:x0.
rewrite H6 in H3.
apply colineaire_alignes with (- (x * x0)).
rewrite H3; Ringvec.
Qed.
 
Lemma alignes_paralleles_confondus :
 forall A B C J : PO,
 triangle A B C ->
 alignes A C J -> paralleles (droite B C) (droite B J) -> J = C :>PO.
intros.
cut (triangle B C A); auto with geo; intros.
deroule_triangle B C A.
apply (concours_unique (A:=B) (B:=A) (A1:=C) (B1:=C) (I:=J) (J:=C));
 auto with geo.
cut (B <> J); intros.
elim paralleles_vecteur with (A := B) (B := J) (C := B) (D := C);
 [ intros k0 H8 | auto | auto | auto with geo ].
apply colineaire_alignes with k0; auto.
cut (triangle A C B); auto with geo; intros.
deroule_triangle A C B.
red in |- *; intros; apply H8.
rewrite H12; auto.
Qed.
Parameter concours : DR -> DR -> Prop.
 
Axiom
  def_concours :
    forall A B C D I : PO,
    A <> B ->
    C <> D ->
    alignes A B I -> alignes C D I -> concours (droite A B) (droite C D).
 
Axiom
  def_concours2 :
    forall A B C D : PO,
    A <> B ->
    C <> D ->
    concours (droite A B) (droite C D) ->
    exists I : PO, alignes A B I /\ alignes C D I.
 
Lemma paralleles_non_concours :
 forall A B C D : PO,
 A <> B :>PO ->
 C <> D :>PO ->
 ~ alignes A B D ->
 paralleles (droite C D) (droite A B) -> ~ concours (droite C D) (droite A B).
intros A B C D H10 H11 H H0.
elim def_paralleles2 with (3 := H0); intros; auto.
unfold not in |- *; intros.
elim def_concours2 with (3 := H2); intros; auto.
elim H3; [ intros H4 H5; try clear H3; try exact H5 ].
elim H4; clear H4; (unfold alignes1 in |- *; intros); [ tauto | idtac ].
elim H3; [ intros k H4; try clear H3; try exact H4 ].
elim H5; clear H5; (unfold alignes1 in |- *; intros); [ tauto | idtac ].
elim H3; [ intros k0 H5; try clear H3; try exact H5 ].
apply H.
cut
 (add_PP (cons k0 A) (cons (1 + - k0) B) =
  add_PP (cons k C) (cons (1 + - k) D)); intros.
unfold alignes, alignes1 in |- *.
right; try assumption.
exists (k0 + - (x * k)).
pattern 1 at 1 in |- *.
replace 1 with (k + (1 + - k)); try ring.
replace (cons (k + (1 + - k)) D) with (add_PP (cons k D) (cons (1 + - k) D)).
replace (cons k D) with (mult_PP k (cons 1 D)).
RingPP1 H1.
replace (cons (k0 + - (x * k)) A) with
 (add_PP (cons k0 A) (cons (- (x * k)) A)).
replace (1 + - (k0 + - (x * k))) with (1 + - k0 + x * k); try ring.
RingPP1 H3.
RingPP.
RingPP.
RingPP.
RingPP.
rewrite <- H4; auto.
Qed.
 
Lemma concours_non_paralleles :
 forall A B C D : PO,
 A <> B :>PO ->
 C <> D :>PO ->
 ~ alignes A B D ->
 concours (droite C D) (droite A B) -> ~ paralleles (droite C D) (droite A B).
intros A B C D H10 H20 H H0; try assumption.
cut (~ ~ concours (droite C D) (droite A B)); intros.
unfold not in |- *; intros.
apply H1.
apply paralleles_non_concours; auto.
intuition.
Qed.
Parameter pt_intersection : DR -> DR -> PO.
 
Axiom
  def_pt_intersection :
    forall A B C D I : PO,
    A <> B ->
    C <> D ->
    ~ alignes A B C \/ ~ alignes A B D ->
    alignes A B I ->
    alignes C D I -> I = pt_intersection (droite A B) (droite C D).
 
Axiom
  def_pt_intersection2 :
    forall A B C D I : PO,
    A <> B ->
    C <> D ->
    ~ alignes A B C \/ ~ alignes A B D ->
    I = pt_intersection (droite A B) (droite C D) ->
    alignes A B I /\ alignes C D I.
 
Lemma existence_pt_intersection :
 forall A B C D : PO,
 A <> B ->
 C <> D ->
 ~ alignes A B C \/ ~ alignes A B D ->
 concours (droite A B) (droite C D) ->
 exists I : PO, I = pt_intersection (droite A B) (droite C D) :>PO.
intros.
elim def_concours2 with (A := A) (B := B) (C := C) (D := D);
 [ intros I H3; elim H3; intros H4 H5; try clear H3 def_concours2;
    try exact H5
 | auto
 | auto
 | auto ].
exists I.
apply def_pt_intersection; auto.
Qed.
 
Lemma ordre_alignement_4points :
 forall A B C D : PO,
 A <> B :>PO ->
 alignes A B C /\ alignes A B D -> alignes C D A /\ alignes C D B.
intros.
elim H0; intros H1 H2; try clear H0; try exact H2.
split; [ try assumption | idtac ].
eauto with geo.
eauto with geo.
Qed.
 
Lemma pt_intersection_commute :
 forall A B C D I : PO,
 A <> B :>PO ->
 C <> D :>PO ->
 ~ alignes A B C \/ ~ alignes A B D ->
 I = pt_intersection (droite A B) (droite C D) :>PO ->
 I = pt_intersection (droite C D) (droite A B) :>PO.
intros.
elim def_pt_intersection2 with (A := A) (B := B) (C := C) (D := D) (I := I);
 [ try clear def_pt_intersection2; intros | auto | auto | auto | auto ].
apply def_pt_intersection; auto.
apply not_and_or; auto.
cut (~ (alignes A B C /\ alignes A B D)); intros.
red in |- *; intros; apply H5.
apply ordre_alignement_4points; auto.
apply or_not_and; auto.
Qed.
 
Lemma concours_barycentre :
 forall A B C D : PO,
 A <> B ->
 C <> D ->
 concours (droite A B) (droite C D) ->
 exists I : PO,
   ex
     (fun a : R =>
      ex
        (fun b : R =>
         I = barycentre (cons (1 + - a) A) (cons a B) :>PO /\
         I = barycentre (cons (1 + - b) C) (cons b D) :>PO)).
intros A B C D H10 H11 H; try assumption.
elim def_concours2 with (3 := H); auto.
intros I H0; elim H0; intros H1 H2; clear H0 H; try exact H2.
elim alignes_barycentre with (A := A) (B := B) (C := I);
 [ intros a H; try clear alignes_barycentre; try exact H | auto | auto ].
elim alignes_barycentre with (A := C) (B := D) (C := I);
 [ intros b H'; try clear alignes_barycentre | auto | auto ].
exists I; exists (1 + - a); exists (1 + - b).
replace (1 + - (1 + - a)) with a; try ring.
replace (1 + - (1 + - b)) with b; try ring.
split; [ try assumption | try assumption ].
Qed.
 
Lemma barycentre_concours :
 forall (a b c d : R) (A B C D I : PO),
 A <> B ->
 C <> D :>PO ->
 a + b <> 0 :>R ->
 barycentre (cons a A) (cons b B) = I :>PO ->
 c + d <> 0 :>R ->
 barycentre (cons c C) (cons d D) = I :>PO ->
 concours (droite A B) (droite C D).
intros a b c d A B C D I H H0 H1 H2 H3 H4; try assumption.
apply def_concours with I; auto.
rewrite <- H2.
apply barycentre_alignes; auto.
rewrite <- H4.
apply barycentre_alignes; auto.
Qed.
 
Lemma add_PP_concours :
 forall (a b c d : R) (A B C D I : PO),
 A <> B :>PO ->
 C <> D :>PO ->
 a + b <> 0 :>R ->
 add_PP (cons a A) (cons b B) = cons (a + b) I :>PP ->
 c + d <> 0 :>R ->
 add_PP (cons c C) (cons d D) = cons (c + d) I :>PP ->
 concours (droite A B) (droite C D).
intros a b c d A B C D I H H0 H1 H2 H3 H4; try assumption.
apply def_concours with I; auto.
apply add_PP_alignes with (a := a) (b := b); auto.
apply add_PP_alignes with (a := c) (b := d); auto.
Qed.
 
Lemma concours_mediane :
 forall A B C : PO,
 A <> milieu B C :>PO ->
 milieu A B <> C :>PO ->
 concours (droite A (milieu B C)) (droite (milieu A B) C).
intros A B C H H0; try assumption.
generalize (add_PP_milieu_asso A B C); intros.
generalize
 (add_PP_concours (a:=1) (b:=2) (c:=2) (d:=1) (A:=A) (B:=
    milieu B C) (C:=milieu A B) (D:=C)
    (I:=barycentre (cons 1 A) (cons 2 (milieu B C)))); 
 intros H8; apply H8; auto.
try discrR; auto with *.
rewrite add_PP_barycentre; try discrR; auto with *.
try discrR; auto with *.
rewrite <- H1; auto.
rewrite add_PP_barycentre; try discrR; auto with *.
apply cons_comp; try ring; auto.
Qed.
 
Definition concours_3 (A B C D E F : PO) :=
  exists I : PO, alignes A B I /\ alignes C D I /\ alignes E F I.
 
Lemma concours_3_mediane :
 forall A B C : PO, concours_3 A (milieu B C) (milieu A B) C (milieu A C) B.
intros A B C; try assumption.
generalize (add_PP_milieu_asso A B C); intros.
generalize (add_PP_milieu_permute A B C); intros.
unfold concours_3 in |- *.
exists (barycentre (cons 1 A) (cons 2 (milieu B C))).
split; [ try assumption | idtac ].
apply barycentre_alignes; try discrR; auto with *.
split; [ try assumption | idtac ].
apply add_PP_alignes with (a := 2) (b := 1); try discrR; auto with *.
rewrite <- H; auto.
rewrite add_PP_barycentre; try discrR; auto with *.
apply cons_comp; (try ring; auto).
apply add_PP_alignes with (a := 2) (b := 1); try discrR; auto with *.
rewrite <- H0; auto.
rewrite add_PP_barycentre; try discrR; auto with *.
apply cons_comp; try ring; auto.
Qed.
 
Lemma concours_3_barycentre :
 forall (a b c : R) (A B C : PO),
 a + (b + c) <> 0 :>R ->
 a + b <> 0 :>R ->
 b + c <> 0 :>R ->
 a + c <> 0 :>R ->
 concours_3 A (barycentre (cons b B) (cons c C))
   (barycentre (cons a A) (cons b B)) C (barycentre (cons a A) (cons c C)) B.
unfold concours_3 in |- *.
intros a b c A B C H H0 H1 H2; try assumption.
exists
 (barycentre (cons a A) (cons (b + c) (barycentre (cons b B) (cons c C)))).
generalize (add_PP_assoc (cons a A) (cons b B) (cons c C)); intros.
generalize (add_PP_assoc_permute (cons a A) (cons b B) (cons c C)); intros.
split; [ try assumption | idtac ].
apply add_PP_alignes with (a := a) (b := b + c); auto with geo.
split; [ try assumption | idtac ].
apply add_PP_alignes with (a := a + b) (b := c); auto with geo.
unfold not in |- *; intros; apply H.
rewrite <- H5; ring.
rewrite <- add_PP_barycentre; auto with geo.
rewrite <- H3; auto.
repeat rewrite add_PP_barycentre; auto with geo.
apply cons_comp; auto.
ring.
apply add_PP_alignes with (a := a + c) (b := b); auto with geo.
unfold not in |- *; intros; apply H.
rewrite <- H5; ring.
rewrite <- add_PP_barycentre; auto.
rewrite <- H4; auto.
repeat rewrite add_PP_barycentre; auto.
apply cons_comp; auto.
ring.
Qed.
 
Lemma centre_gravite_intersection_medianes :
 forall A B C I J G : PO,
 triangle A B C ->
 I = milieu B C :>PO ->
 J = milieu A B :>PO ->
 G = centre_gravite A B C :>PO ->
 G = pt_intersection (droite A I) (droite C J) :>PO.
intros.
deroule_triangle A B C.
cut (triangle B C A); auto with geo; unfold triangle in |- *; intros.
cut (C <> J); intros.
cut (A <> I); intros.
cut (3 <> 0); intros; auto with real.
replace (droite C J) with (droite J C); auto with geo.
apply def_pt_intersection; auto.
left.
apply triangle_medianes_triangle with (1 := H); auto.
apply colineaire_alignes with (/ 3 * 2); auto.
rewrite (centre_gravite_mediane_vecteur (A:=A) (B:=B) (C:=C) (I:=I) (G:=G));
 auto.
Fieldvec 3.
apply permute_alignes; auto.
apply colineaire_alignes with (/ 3 * 2); auto.
rewrite (centre_gravite_mediane_vecteur (A:=C) (B:=A) (C:=B) (I:=J) (G:=G));
 auto.
Fieldvec 3.
rewrite H2; auto with geo.
rewrite H0.
apply triangle_milieu_distinct; auto.
rewrite H1.
apply triangle_milieu_distinct; auto.
Qed.
 
Lemma centre_gravite_intersection_trois_medianes :
 forall A B C I J K G : PO,
 triangle A B C ->
 I = milieu B C :>PO ->
 J = milieu A B :>PO ->
 K = milieu A C :>PO ->
 G = centre_gravite A B C :>PO ->
 G = pt_intersection (droite A I) (droite B K) :>PO /\
 G = pt_intersection (droite A I) (droite C J) :>PO.
intros.
split; [ idtac | try assumption ].
apply centre_gravite_intersection_medianes with (B := C); auto with geo.
rewrite H3; auto with geo.
apply centre_gravite_intersection_medianes with (B := B); auto.
Qed.
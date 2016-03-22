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


Require Export produit_scalaire.
Set Implicit Arguments.
Unset Strict Implicit.
Parameter orthogonal : PP -> PP -> Prop.
 
Axiom
  def_orthogonal :
    forall A B C D : PO,
    orthogonal (vec A B) (vec C D) -> scalaire (vec A B) (vec C D) = 0.
 
Axiom
  def_orthogonal2 :
    forall A B C D : PO,
    scalaire (vec A B) (vec C D) = 0 -> orthogonal (vec A B) (vec C D).
 
Lemma ortho_somme :
 forall A B C D E F : PO,
 orthogonal (vec A B) (vec E F) ->
 orthogonal (vec C D) (vec E F) ->
 orthogonal (add_PP (vec A B) (vec C D)) (vec E F).
intros A B C D E F H H0; try assumption.
elim
 existence_representant_som_vecteur with (A := A) (B := B) (C := C) (D := D);
 intros I H1; try clear existence_representant_som_vecteur; 
 rewrite <- H1.
apply def_orthogonal2.
rewrite H1.
Simplscal.
rewrite (def_orthogonal (A:=A) (B:=B) (C:=E) (D:=F)); auto.
rewrite (def_orthogonal (A:=C) (B:=D) (C:=E) (D:=F)); auto.
ring.
Qed.
 
Lemma ortho_combinaison_lineaire :
 forall (a b : R) (A B C D E F : PO),
 orthogonal (vec A B) (vec E F) ->
 orthogonal (vec C D) (vec E F) ->
 orthogonal (add_PP (mult_PP a (vec A B)) (mult_PP b (vec C D))) (vec E F).
intros a b A B C D E F H H0; try assumption.
elim
 existence_representant_comb_lin_vecteur
  with (A := A) (B := B) (C := C) (D := D) (a := a) (b := b); 
 intros E0 H1; try clear existence_representant_comb_lin_vecteur;
 rewrite <- H1.
apply def_orthogonal2.
rewrite H1.
Simplscal.
rewrite (def_orthogonal (A:=A) (B:=B) (C:=E) (D:=F)); auto.
rewrite (def_orthogonal (A:=C) (B:=D) (C:=E) (D:=F)); auto.
ring.
Qed.
 
Lemma ortho_mult :
 forall (a : R) (A B C D : PO),
 orthogonal (vec A B) (vec C D) -> orthogonal (mult_PP a (vec A B)) (vec C D).
intros.
replace (mult_PP a (vec A B)) with
 (add_PP (mult_PP a (vec A B)) (mult_PP 0 (vec A B))).
apply ortho_combinaison_lineaire; auto.
Ringvec.
Qed.
 
Lemma ortho_sym :
 forall A B C D : PO,
 orthogonal (vec A B) (vec C D) -> orthogonal (vec C D) (vec A B).
intros A B C D H; try assumption.
apply def_orthogonal2.
rewrite scalaire_sym.
rewrite (def_orthogonal (A:=A) (B:=B) (C:=C) (D:=D)); auto.
Qed.
Hint Immediate ortho_sym: geo.
 
Lemma zero_ortho_tout : forall A B : PO, orthogonal (vec A B) zero.
intros A B; try assumption.
VReplace zero (vec A A).
apply def_orthogonal2.
VReplace (vec A A) (mult_PP 0 (vec A B)).
Simplscal.
Qed.
 
Lemma zero_ortho_tout2 : forall A B : PO, orthogonal zero (vec A B).
intros.
VReplace zero (vec A A).
apply def_orthogonal2.
VReplace (vec A A) (mult_PP 0 (vec A B)).
Simplscal.
Qed.
Hint Resolve ortho_sym ortho_mult zero_ortho_tout zero_ortho_tout2
  def_orthogonal2 def_orthogonal: geo.
 
Ltac Simplortho :=
  (apply ortho_combinaison_lineaire; auto with geo) ||
    (apply ortho_mult; auto with geo) || (apply ortho_somme; auto with geo);
   try Ringvec.
 
Lemma opp_orthogonal :
 forall A B C D : PO,
 orthogonal (vec A B) (vec C D) -> orthogonal (vec B A) (vec C D).
intros.
replace (vec B A) with (mult_PP (-1) (vec A B)); [ Simplortho | Ringvec ].
Qed.
Hint Immediate opp_orthogonal: geo.
 
Lemma opp_orthogonal2 :
 forall A B C D : PO,
 orthogonal (vec A B) (vec C D) -> orthogonal (vec C D) (vec B A).
auto with geo.
Qed.
Hint Immediate opp_orthogonal2: geo.
 
Lemma opp_orthogonal3 :
 forall A B C D : PO,
 orthogonal (vec A B) (vec C D) -> orthogonal (vec A B) (vec D C).
intros.
apply ortho_sym.
replace (vec D C) with (mult_PP (-1) (vec C D)); [ Simplortho | Ringvec ].
Qed.
Hint Immediate opp_orthogonal3: geo.
 
Lemma opp_orthogonal4 :
 forall A B C D : PO,
 orthogonal (vec A B) (vec C D) -> orthogonal (vec D C) (vec A B).
auto with geo.
Qed.
Hint Immediate opp_orthogonal4: geo.
 
Lemma opp_orthogonal5 :
 forall A B C D : PO,
 orthogonal (vec A B) (vec C D) -> orthogonal (vec B A) (vec D C).
intros.
apply opp_orthogonal.
auto with geo.
Qed.
Hint Immediate opp_orthogonal5: geo.
 
Lemma opp_orthogonal6 :
 forall A B C D : PO,
 orthogonal (vec A B) (vec C D) -> orthogonal (vec D C) (vec B A).
auto with geo.
Qed.
Hint Immediate opp_orthogonal6: geo.
 
Lemma orthogonal_milieu :
 forall A B C D I : PO,
 A <> B ->
 I = milieu A B ->
 orthogonal (vec I A) (vec C D) \/ orthogonal (vec I B) (vec C D) ->
 orthogonal (vec A B) (vec C D).
intros.
elim H1; intros.
replace (vec A B) with (mult_PP (-2) (vec I A)).
Simplortho.
replace (vec A B) with (add_PP (vec A I) (vec I B)).
rewrite <- (milieu_vecteur (A:=A) (B:=B) (M:=I)); auto.
Ringvec.
Ringvec.
replace (vec A B) with (mult_PP 2 (vec I B)).
Simplortho.
replace (vec A B) with (add_PP (vec A I) (vec I B)).
rewrite (milieu_vecteur (A:=A) (B:=B) (M:=I)); auto.
Ringvec.
Ringvec.
Qed.
 
Lemma orthogonal_segment_milieu :
 forall A B C D I : PO,
 A <> B ->
 I = milieu A B ->
 orthogonal (vec A B) (vec C D) ->
 orthogonal (vec I A) (vec C D) /\ orthogonal (vec I B) (vec C D).
intros.
cut (orthogonal (vec A I) (vec C D)); intros.
split; [ try assumption | idtac ].
VReplace (vec I A) (mult_PP (-1) (vec A I)).
Simplortho.
rewrite <- (milieu_vecteur (A:=A) (B:=B) (M:=I)); auto.
rewrite (milieu_vecteur2 (A:=A) (B:=B) (M:=I)); auto.
Simplortho.
Qed.
 
Lemma non_orthogonal_def :
 forall A B C D : PO,
 scalaire (vec A B) (vec C D) <> 0 -> ~ orthogonal (vec A B) (vec C D).
intros.
contrapose H.
apply def_orthogonal; auto.
Qed.
 
Lemma alignes_non_orthogonal :
 forall A B C : PO,
 A <> B :>PO ->
 A <> C :>PO -> alignes A B C -> ~ orthogonal (vec A B) (vec A C).
intros.
halignes H1 ipattern:x.
cut (x <> 0); intros.
2: apply distinct_col_nonzero with (2 := H2); auto.
apply non_orthogonal_def.
rewrite H2.
Simplscal.
apply integre_not; auto with geo.
Qed.
 
Lemma orthogonal_non_alignes :
 forall A B C : PO,
 A <> B :>PO ->
 A <> C :>PO -> orthogonal (vec A B) (vec A C) -> ~ alignes A B C.
intros.
cut (~ ~ orthogonal (vec A B) (vec A C)); intros.
contrapose H2.
apply alignes_non_orthogonal; auto.
tauto.
Qed.
Hint Resolve orthogonal_non_alignes alignes_non_orthogonal: geo.
 
Lemma orthogonal_alignement :
 forall A B C D : PO,
 A <> B ->
 alignes A B C ->
 orthogonal (vec A B) (vec C D) -> orthogonal (vec C D) (vec C B).
intros.
halignes H0 ipattern:x.
apply ortho_sym.
replace (vec C B) with (add_PP (vec A B) (mult_PP (-1) (vec A C))).
rewrite H2.
replace (add_PP (vec A B) (mult_PP (-1) (mult_PP x (vec A B)))) with
 (mult_PP (1 + - x) (vec A B)).
Simplortho.
Ringvec.
Ringvec.
Qed.
 
Lemma orthogonal_alignement2 :
 forall A B C D : PO,
 A <> B ->
 alignes A B C ->
 orthogonal (vec A B) (vec C D) -> orthogonal (vec C D) (vec C A).
intros.
halignes H0 ipattern:x.
apply ortho_sym.
replace (vec C A) with (mult_PP (-1) (vec A C)).
rewrite H2.
replace (mult_PP (-1) (mult_PP x (vec A B))) with (mult_PP (- x) (vec A B)).
Simplortho.
Ringvec.
Ringvec.
Qed.
 
Lemma paralleles_orthogonal :
 forall A B C D E F : PO,
 A <> B ->
 C <> D ->
 paralleles (droite A B) (droite C D) ->
 orthogonal (vec A B) (vec E F) -> orthogonal (vec C D) (vec E F).
intros.
elim (paralleles_vecteur (A:=C) (B:=D) (C:=A) (D:=B)); auto with geo; intros.
rewrite H3.
Simplortho.
Qed.
 
Lemma alignes_unitaire :
 forall A B C : PO,
 alignes A B C ->
 scalaire (vec A B) (vec A B) = 1 ->
 vec A C = mult_PP (scalaire (vec A B) (vec A C)) (vec A B).
intros.
assert (A <> B); auto with geo.
halignes H ipattern:x.
pattern (vec A C) at 2 in |- *.
rewrite H2.
Simplscal.
rewrite H0; rewrite H2.
RingPP.
Qed.
 
Lemma scalaire_avec_projete :
 forall A B C H : PO,
 alignes A B H ->
 orthogonal (vec A B) (vec H C) ->
 scalaire (vec A B) (vec A C) = scalaire (vec A B) (vec A H).
intros.
discrimine A B.
VReplace (vec B B) (mult_PP 0 (vec B C)).
Simplscal.
halignes H0 ipattern:k.
replace (vec A C) with (add_PP (vec A H) (vec H C)).
Simplscal.
replace (scalaire (vec A B) (vec H C)) with 0.
ring.
symmetry  in |- *.
apply def_orthogonal; auto.
Ringvec.
Qed.
 
Lemma scalaire_alignes :
 forall A B C D : PO,
 A <> B ->
 alignes A B C ->
 alignes A B D ->
 scalaire (vec A B) (vec A C) = scalaire (vec A B) (vec A D) -> C = D.
intros A B C D H H0 H10 H1; try assumption.
halignes H0 ipattern:k.
halignes H10 ipattern:k'.
rewrite H2 in H1.
rewrite H3 in H1.
repeat rewrite scalaire_mult_d in H1.
elim (classic (k = k')); intros.
rewrite H4 in H2.
cut (vec A C = vec A D); intros.
apply egalite_vecteur_point with A; auto.
rewrite H2; rewrite H3; auto.
absurd ((k + - k') * scalaire (vec A B) (vec A B) = 0); auto.
apply integre_not; auto with geo.
contrapose H4.
RReplace k (k + - k' + k').
rewrite H5; ring.
RReplace ((k + - k') * scalaire (vec A B) (vec A B))
 (k * scalaire (vec A B) (vec A B) + - k' * scalaire (vec A B) (vec A B)).
rewrite H1; ring.
Qed.
 
Lemma unicite_projete_orthogonal :
 forall A B C H H' : PO,
 A <> B ->
 alignes A B H ->
 orthogonal (vec A B) (vec H C) ->
 alignes A B H' -> orthogonal (vec A B) (vec H' C) -> H = H'.
intros.
apply scalaire_alignes with (2 := H1) (3 := H3); auto.
rewrite <- (scalaire_avec_projete (A:=A) (B:=B) (C:=C) (H:=H)); auto.
rewrite <- (scalaire_avec_projete (A:=A) (B:=B) (C:=C) (H:=H')); auto.
Qed.
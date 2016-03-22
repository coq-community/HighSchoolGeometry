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


Require Export complexes_inversion.
Set Implicit Arguments.
Unset Strict Implicit.
 
Lemma translation_analytique :
 forall A M M' : PO,
 M' = translation O A M :>PO ->
 abscisse M' = abscisse M + abscisse A /\
 ordonnee M' = ordonnee M + ordonnee A.
intros.
paffixe M ipattern:z.
paffixe A ipattern:a.
paffixe M' ipattern:z'.
assert (z' = Cplus z a).
apply rec_complexe_translation with (4 := H); auto.
generalize H0 H1 H2.
repeat rewrite <- coordonnees_affixe; intros.
apply unicite_parties_relles_imaginaires with z'; auto.
rewrite H3; rewrite H4; rewrite H5; rewrite Cplus_algebrique; auto.
Qed.
 
Lemma homothetie_analytique :
 forall (k : R) (J M M' : PO),
 M' = homothetie k J M :>PO ->
 abscisse M' + - abscisse J = k * (abscisse M + - abscisse J) /\
 ordonnee M' + - ordonnee J = k * (ordonnee M + - ordonnee J).
intros.
paffixe M ipattern:z.
paffixe J ipattern:j.
paffixe M' ipattern:z'.
assert (Cplus z' (Copp j) = Cmult (Rinj k) (Cplus z (Copp j))).
apply rec_complexe_homothetie with (4 := H); auto.
generalize H0 H1 H2.
repeat rewrite <- coordonnees_affixe; intros.
apply unicite_parties_relles_imaginaires with (Cplus z' (Copp j)); auto.
rewrite H6; rewrite H5.
rewrite Copp_algebrique; rewrite Cplus_algebrique; auto.
rewrite H3; rewrite H4; rewrite H5.
rewrite Copp_algebrique; rewrite Cplus_algebrique.
unfold Rinj in |- *; rewrite Cmult_algebrique.
RReplace
 (k * (abscisse M + - abscisse J) + - (0 * (ordonnee M + - ordonnee J)))
 (k * (abscisse M + - abscisse J)).
RReplace (0 * (abscisse M + - abscisse J) + k * (ordonnee M + - ordonnee J))
 (k * (ordonnee M + - ordonnee J)).
auto.
Qed.
 
Lemma rotation_analytique :
 forall (a : R) (J M M' : PO),
 M' = rotation J a M ->
 abscisse M' + - abscisse J =
 cos a * (abscisse M + - abscisse J) +
 - (sin a * (ordonnee M + - ordonnee J)) /\
 ordonnee M' + - ordonnee J =
 sin a * (abscisse M + - abscisse J) + cos a * (ordonnee M + - ordonnee J).
intros.
assert (cons_pol 1 a = cons_cart (cos a) (sin a)).
elim existence_parties_relles_imaginaires with (z := cons_pol 1 a);
 [ intros a0 H0; elim H0;
    [ intros b H1; try clear H0 existence_parties_relles_imaginaires;
       try exact H1 ] ].
assert (a0 = 1 * cos a /\ b = 1 * sin a).
apply passage_polaire_algebrique with (cons_pol 1 a); auto with geo.
elim H2; [ intros H3 H4; try clear H2; try exact H4 ].
rewrite H1; rewrite H4; rewrite H3.
RReplace (1 * cos a) (cos a).
RReplace (1 * sin a) (sin a).
auto.
paffixe M ipattern:z.
paffixe J ipattern:j.
paffixe M' ipattern:z'.
assert (Cplus z' (Copp j) = Cmult (cons_pol 1 a) (Cplus z (Copp j))).
apply rotation_complexe with (4 := H); auto.
generalize H3 H1 H2.
repeat rewrite <- coordonnees_affixe; intros.
apply unicite_parties_relles_imaginaires with (Cplus z' (Copp j)); auto.
rewrite H7; rewrite H5.
rewrite Copp_algebrique; rewrite Cplus_algebrique; auto.
rewrite H4; rewrite H6; rewrite H7.
rewrite Copp_algebrique; rewrite Cplus_algebrique.
rewrite H0; rewrite Cmult_algebrique.
auto.
Qed.
 
Lemma similitude_analytique :
 forall (k a : R) (J M M' : PO),
 k > 0 ->
 M' = similitude J k a M ->
 abscisse M' + - abscisse J =
 k *
 (cos a * (abscisse M + - abscisse J) +
  - (sin a * (ordonnee M + - ordonnee J))) /\
 ordonnee M' + - ordonnee J =
 k *
 (sin a * (abscisse M + - abscisse J) + cos a * (ordonnee M + - ordonnee J)).
intros.
assert (k <> 0); auto with real.
assert (cons_pol k a = cons_cart (k * cos a) (k * sin a)).
elim existence_parties_relles_imaginaires with (z := cons_pol k a);
 [ intros a0 H2; elim H2; [ intros b H3 ] ].
assert (a0 = k * cos a /\ b = k * sin a).
apply passage_polaire_algebrique with (cons_pol k a); auto with geo.
elim H4; [ intros H5 H6; try clear H4; try exact H6 ].
rewrite H3; rewrite H5; rewrite H6.
auto.
paffixe M ipattern:z.
paffixe J ipattern:j.
paffixe M' ipattern:z'.
assert (Cplus z' (Copp j) = Cmult (cons_pol k a) (Cplus z (Copp j))).
apply similitude_complexe with (5 := H0); auto.
generalize H3 H4 H5.
repeat rewrite <- coordonnees_affixe; intros.
apply unicite_parties_relles_imaginaires with (Cplus z' (Copp j)); auto.
rewrite H9; rewrite H8.
rewrite Copp_algebrique; rewrite Cplus_algebrique; auto.
rewrite H6; rewrite H7; rewrite H8.
rewrite Copp_algebrique; rewrite Cplus_algebrique.
rewrite H2; rewrite Cmult_algebrique.
RReplace
 (k * cos a * (abscisse M + - abscisse J) +
  - (k * sin a * (ordonnee M + - ordonnee J)))
 (k *
  (cos a * (abscisse M + - abscisse J) +
   - (sin a * (ordonnee M + - ordonnee J)))).
RReplace
 (k * sin a * (abscisse M + - abscisse J) +
  k * cos a * (ordonnee M + - ordonnee J))
 (k *
  (sin a * (abscisse M + - abscisse J) + cos a * (ordonnee M + - ordonnee J))).
auto.
Qed.
 
Lemma inversion_pole_origine_analytique :
 forall (k : R) (M M' : PO),
 O <> M :>PO ->
 k <> 0 ->
 M' = inversion O k M :>PO ->
 abscisse M' = k * abscisse M / (Rsqr (abscisse M) + Rsqr (ordonnee M)) /\
 ordonnee M' = k * ordonnee M / (Rsqr (abscisse M) + Rsqr (ordonnee M)).
intros.
paffixe M ipattern:z.
paffixe M' ipattern:z'.
assert (z <> zeroC).
apply points_distincts_non_zeroC with (1 := H); auto with geo.
assert (module z <> 0); auto with geo.
assert (Rsqr (module z) <> 0).
unfold Rsqr in |- *; auto with real.
generalize H3 H2.
repeat rewrite <- coordonnees_affixe; intros.
assert (z' = Cmult (Rinj k) (Cinv (Conj z))).
apply inversion_pole_origine_complexe with (5 := H1); auto with geo.
apply unicite_parties_relles_imaginaires with z'; auto.
rewrite H9.
rewrite Conj_Cinv; auto.
rewrite <- Rinj_Cinv; auto.
ring_simplify.
rewrite <- Rinj_Cmult.
rewrite (carre_module H8).
rewrite H8.
rewrite Cmult_Rinj_algebrique.
unfold Rdiv in |- *.
replace (k * / (Rsqr (abscisse M) + Rsqr (ordonnee M)) * abscisse M)
 with (k * abscisse M * / (Rsqr (abscisse M) + Rsqr (ordonnee M))) by ring.
replace (k * / (Rsqr (abscisse M) + Rsqr (ordonnee M)) * ordonnee M)
  with(k * ordonnee M * / (Rsqr (abscisse M) + Rsqr (ordonnee M))) by ring.
auto.
Qed.

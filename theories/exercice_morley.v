From HighSchoolGeometry Require Export trigo.
Set  Implicit Arguments.
Unset Strict Implicit.
(* Formules de trigonometrie necessaires.*)
 
Lemma prod_sin:
 forall (a b : R),  2 * (sin (a + b) * sin (a - b)) = cos (2 * b) - cos (2 * a).
intros.
assert
 (cos ((a + b) + (a - b)) =
  cos (a + b) * cos (a - b) - sin (a + b) * sin (a - b)).
rewrite cos_som; auto.
assert
 (cos ((a + b) - (a - b)) =
  cos (a + b) * cos (a - b) + sin (a + b) * sin (a - b)).
rewrite <- cos_diff; auto.
assert
 (2 * (sin (a + b) * sin (a - b)) =
  cos ((a + b) - (a - b)) - cos ((a + b) + (a - b))).
rewrite H0; rewrite H.
ring.
rewrite H1.
RReplace ((a + b) - (a - b)) (2 * b).
RReplace ((a + b) + (a - b)) (2 * a); auto.
Qed.
 
Lemma sin_3_a: forall (a : R),  sin (3 * a) = sin a * (2 * cos (2 * a) + 1).
intros.
RReplace (3 * a) (a + 2 * a).
rewrite sin_som.
rewrite duplication_sin.
RReplace (sin a * cos (2 * a) + (2 * (sin a * cos a)) * cos a)
         (sin a * (cos (2 * a) + 2 * (cos a * cos a))).
assert (2 * Rsqr (cos a) = cos (2 * a) + 1).
rewrite duplication_cos.
ring.
RReplace (cos a * cos a) (Rsqr (cos a)).
rewrite H.
ring.
Qed.
 
Lemma Al_Kashi_sin_cos:
 forall (a b c : R),
 (a + b) + c = pi ->
  Rsqr (sin c) = (Rsqr (sin a) + Rsqr (sin b)) - ((2 * sin a) * sin b) * cos c.
intros.
RReplace ((Rsqr (sin a) + Rsqr (sin b)) - ((2 * sin a) * sin b) * cos c)
         (((Rsqr (sin a) * Rsqr (cos c) + Rsqr (sin b)) -
           ((2 * sin a) * sin b) * cos c) - Rsqr (sin a) * (Rsqr (cos c) - 1)).
replace
 ((Rsqr (sin a) * Rsqr (cos c) + Rsqr (sin b)) - ((2 * sin a) * sin b) * cos c)
     with (Rsqr (sin a * cos c - sin b)).
2:unfold Rsqr; ring.
rewrite <- (trigo_Pythagore c).
RReplace (Rsqr (cos c) - (Rsqr (cos c) + Rsqr (sin c))) (- Rsqr (sin c)).
elim pi_moins_x with ( x := a + c ); [intros H0 H1].
replace b with (pi + - (a + c)).
rewrite H1.
rewrite sin_som.
RReplace (sin a * cos c - (sin a * cos c + sin c * cos a)) (- (sin c * cos a)).
replace (Rsqr (- (sin c * cos a))) with (Rsqr (sin c) * Rsqr (cos a)).
2:unfold Rsqr; ring.
RReplace (Rsqr (sin c) * Rsqr (cos a) - Rsqr (sin a) * - Rsqr (sin c))
         (Rsqr (sin c) * (Rsqr (cos a) + Rsqr (sin a))).
rewrite trigo_Pythagore.
ring.
rewrite <- H; ring.
Qed.
(* Definition de pisurtrois et formules de trigonometrie.*)
Parameter pisurtrois : R.
 
Axiom pisurtrois_def : 3 * pisurtrois = pi.
 
Axiom sin_pisurtrois_non_zero : sin pisurtrois <> 0.
 
Lemma cos_2_pisurtrois: 2 * cos (2 * pisurtrois) + 1 = 0.
RReplace (2 * cos (2 * pisurtrois) + 1) (sin pi * / sin pisurtrois).
rewrite sin_pi; ring.
rewrite <- pisurtrois_def.
rewrite sin_3_a.
field.
apply sin_pisurtrois_non_zero.
Qed.
 
Lemma sin_3_a_pisurtrois:
 forall (a : R),
  sin (3 * a) = 4 * (sin a * (sin (pisurtrois + a) * sin (pisurtrois - a))).
intros.
rewrite sin_3_a.
RReplace (4 * (sin a * (sin (pisurtrois + a) * sin (pisurtrois - a))))
         ((2 * sin a) * (2 * (sin (pisurtrois + a) * sin (pisurtrois - a)))).
rewrite prod_sin.
RReplace ((2 * sin a) * (cos (2 * a) - cos (2 * pisurtrois)))
         (sin a * (2 * cos (2 * a) - 2 * cos (2 * pisurtrois))).
assert (2 * cos (2 * pisurtrois) = - 1).
RReplace (- 1) (- 1 + 0).
rewrite <- cos_2_pisurtrois.
ring.
rewrite H.
ring.
Qed.
 
Lemma Al_Kashi_pisurtrois:
 forall a b c,
 (a + b) + c = pisurtrois ->
  Rsqr (sin b) =
  (Rsqr (sin (pisurtrois + a)) + Rsqr (sin (pisurtrois + c))) -
  ((2 * sin (pisurtrois + a)) * sin (pisurtrois + c)) * cos b.
intros.
apply Al_Kashi_sin_cos.
rewrite <- pisurtrois_def.
RReplace (((pisurtrois + a) + (pisurtrois + c)) + b)
         (((a + b) + c) + (pisurtrois + pisurtrois)).
rewrite H; ring.
Qed.
From HighSchoolGeometry Require Export cocyclicite.
(* lemme a mettre dans distance_euclidienne apres colinearite_distance*)
 
Lemma distance_double_milieu:
 forall (B C A' : PO), A' = milieu B C ->  distance B C = 2 * distance A' C.
intros.
rewrite <- (milieu_distance H); auto.
assert (vec B C = mult_PP 2 (vec B A')).
apply milieu_vecteur_double; auto.
rewrite (distance_sym A' B).
RReplace 2 (Rabs 2).
apply colinearite_distance; auto.
rewrite Rabs_right; auto.
lra.
Qed.
(* corollaire du theoreme de l'angle inscrit et de l'angle au centre
   on utilise le triangle rectangle forme par un cote et sa mediatrice*)
 
Lemma demi_angle_centre:
 forall (A B C A' O : PO),
 triangle A B C ->
 O <> A' ->
 A' = milieu B C ->
 circonscrit O A B C ->
  double_AV (cons_AV (vec A B) (vec A C)) =
  double_AV (cons_AV (vec O A') (vec O C)).
intros.
deroule_triangle A B C.
deroule_circonscrit A B C O.
assert (double_AV (cons_AV (vec A B) (vec A C)) = cons_AV (vec O B) (vec O C)).
apply angle_inscrit; auto.
rewrite H10.
assert (double_AV (cons_AV (vec O A') (vec O C)) = cons_AV (vec O B) (vec O C)).
unfold double_AV.
replace (cons_AV (vec O B) (vec O C))
     with (plus (cons_AV (vec O B) (vec O A')) (cons_AV (vec O A') (vec O C))).
assert (cons_AV (vec O B) (vec O A') = cons_AV (vec O A') (vec O C)).
apply isocele_mediane_bissectrice; auto.
apply (circonscrit_isocele H2).
rewrite H11; auto.
apply Chasles; auto.
rewrite H11; auto.
Qed.
(*deux angles ayant des mesures differant d'un multiple de pi ont des sinus egaux ou opposes*)
 
Axiom
   egalite_double_abs_Sin :
   forall A B C E F G,
   double_AV (cons_AV (vec A B) (vec A C)) =
   double_AV (cons_AV (vec E F) (vec E G)) ->
    Rabs (Sin (cons_AV (vec A B) (vec A C))) =
    Rabs (Sin (cons_AV (vec E F) (vec E G))).

From HighSchoolGeometry Require Export complements_cercle.
(* theoreme : dans un triangle avec les notations habituelles  a = 2 R sin A
   cas particulier : le cote est un diametre du cercle circonscrit*)
 
Lemma diametre_Sinus:
 forall (A B C O : PO),
 triangle A B C ->
 O = milieu B C ->
 circonscrit O A B C ->
  distance B C = 2 * (distance O C * Rabs (Sin (cons_AV (vec A B) (vec A C)))).
intros.
assert (orthogonal (vec A B) (vec A C)).
apply triangle_diametre with O; auto.
deroule_triangle A B C.
elim droit_direct_ou_indirect with ( A := A ) ( B := B ) ( C := C );
 (intros; auto).
rewrite <- (egalite_sin_Sin (A:=A) (B:=B) (C:=C) (x:=pisurdeux)); auto.
rewrite sin_pisurdeux.
rewrite Rabs_right; auto.
rewrite (distance_double_milieu H0); ring.
lra.
rewrite <- (egalite_sin_Sin (A:=A) (B:=B) (C:=C) (x:=- pisurdeux)); auto.
rewrite sin_impaire.
rewrite sin_pisurdeux.
rewrite Rabs_left; auto.
rewrite (distance_double_milieu H0); ring.
lra.
Qed.
(* cas general*)
 
Lemma rayon_Sinus_general:
 forall (A B C A' O : PO),
 triangle A B C ->
 O <> A' ->
 A' = milieu B C ->
 circonscrit O A B C ->
  distance B C = 2 * (distance O C * Rabs (Sin (cons_AV (vec A B) (vec A C)))).
intros.
deroule_triangle A B C.
deroule_circonscrit A B C O.
assert (orthogonal (vec O A') (vec B C)).
apply milieu_centrecirconscrit_orthogonal_segment with A; auto.
rewrite (distance_double_milieu H1).
replace (distance O C * Rabs (Sin (cons_AV (vec A B) (vec A C))))
     with (distance C O * Rabs (Sin (cons_AV (vec O A') (vec O C)))).
rewrite <- triangle_rectangle_absolu_Sin; auto.
rewrite (distance_sym A' C); auto.
rewrite H1.
generalize (milieu_distinct2 H5); auto.
apply ortho_sym.
rewrite <- (milieu_vecteur H1); auto.
rewrite (milieu_vecteur2 H1); auto.
Simplortho.
rewrite distance_sym.
assert
 (double_AV (cons_AV (vec A B) (vec A C)) =
  double_AV (cons_AV (vec O A') (vec O C))).
apply demi_angle_centre; auto.
rewrite (egalite_double_abs_Sin H11); auto.
Qed.
(* Ce theoreme montre que dans un triangle  a = 2R sin A  avec les notations habituelles.*)
 
Theorem rayon_Sinus:
 forall A B C O,
 triangle A B C ->
 circonscrit O A B C ->
  distance B C = 2 * (distance O C * Rabs (Sin (cons_AV (vec A B) (vec A C)))).
intros.
deroule_triangle A B C.
soit_milieu B C A'.
elim (classic (A' = O)); intros.
apply diametre_Sinus; auto.
rewrite <- H8; auto.
apply rayon_Sinus_general with A'; auto.
Qed.
 
Lemma existence_rayon_circonscrit:
 forall A B C,
 triangle A B C ->
  (exists O : PO , circonscrit O A B C /\ (exists r : R , r = distance O C ) ).
intros.
elim existence_cercle_circonscrit with ( A := A ) ( B := B ) ( C := C );
 [intros O H0; (try clear existence_cercle_circonscrit); (try exact H0) | auto].
exists O.
split; [try assumption | idtac].
exists (distance O C); auto.
Qed.
 
Ltac
soit_rayon_circonscrit A B C O r :=
elim (existence_rayon_circonscrit (A:=A) (B:=B) (C:=C)); [intros O | auto];
 intros toto; elim toto; clear toto; intro; intros toto; elim toto; clear toto;
 intros r; intro.
(* on doit pouvoir le demontrer*)
 
Axiom
   triangle_Sin_not_0 :
   forall A B C, triangle A B C ->  (Sin (cons_AV (vec A B) (vec A C)) <> 0).
#[export] Hint Resolve triangle_Sin_not_0 :geo.
 
Lemma triangle_abs_Sin_not_0:
 forall A B C,
 triangle A B C ->  (Rabs (Sin (cons_AV (vec A B) (vec A C))) <> 0).
intros.
apply Rabs_no_R0.
auto with geo.
Qed.
#[export] Hint Resolve triangle_abs_Sin_not_0 :geo.
(* Theoreme connu sous le nom de loi des Sinus.*)
 
Theorem loi_Sinus:
 forall A B C,
 triangle A B C ->
  and
   (distance B C / Rabs (Sin (cons_AV (vec A B) (vec A C))) =
    distance A B / Rabs (Sin (cons_AV (vec C A) (vec C B))))
   (distance B C / Rabs (Sin (cons_AV (vec A B) (vec A C))) =
    distance C A / Rabs (Sin (cons_AV (vec B C) (vec B A)))).
intros.
deroule_triangle A B C.
soit_rayon_circonscrit A B C D a.
rewrite (rayon_Sinus (A:=A) (B:=B) (C:=C) (O:=D)); auto.
rewrite <- H5; auto.
generalize H4; unfold circonscrit, isocele; intros.
elim H6; [intros H7 H8; (try clear H6); (try exact H8)].
split; [try assumption | idtac].
rewrite (rayon_Sinus (A:=C) (B:=A) (C:=B) (O:=D)); auto with geo.
rewrite <- H7; rewrite H8; rewrite H5.
field.
split; auto with geo.
apply circonscrit_permute; auto.
rewrite (rayon_Sinus (A:=B) (B:=C) (C:=A) (O:=D)); auto with geo.
rewrite H8; rewrite H5.
field.
split; auto with geo.
unfold circonscrit, isocele.
split; auto.
rewrite <- H7; rewrite H8; auto.
Qed.
 
Definition rayon_circonscrit (A B C : PO) (r : R) : Prop :=
   exists O : PO , circonscrit O A B C /\ r = distance O C .
 
Lemma triangle_sin_not_0:
 forall A B C x,
 triangle A B C -> image_angle x = cons_AV (vec A B) (vec A C) ->  (sin x <> 0).
intros.
deroule_triangle A B C.
rewrite (egalite_sin_Sin (A:=A) (B:=B) (C:=C) (x:=x)); auto.
auto with geo.
Qed.
(* consequence de l'enroulement de la droite des reels sur le cercle trigonometrique dans le sens positif*)
 
Axiom sin_pos : forall (x : R), ( 0 <= x <= pi ) ->  (sin x >= 0).
 
Axiom
   non_multiple_pi_triangle :
   forall a A B C,
   ( 0 < a < pi ) ->
   A <> B ->
   A <> C -> image_angle a = cons_AV (vec A B) (vec A C) ->  triangle A B C.
(* debut de la demonstration du theoreme de Morley*)
 
Lemma pisurtrois_utile:
 forall a b c,
 0 < a -> 0 < b -> 0 < c -> (a + b) + c = pisurtrois ->  ( 0 <= 3 * a <= pi ).
intros.
rewrite <- pisurtrois_def.
split.
lra.
lra.
Qed.
 
Lemma pisurtrois_utile1:
 forall a b c,
 0 < a -> 0 < b -> 0 < c -> (a + b) + c = pisurtrois ->  ( 0 <= b + c <= pi ).
intros.
rewrite <- pisurtrois_def.
split.
lra.
lra.
Qed.
 
Lemma pisurtrois_utile2:
 forall a b c,
 0 < a -> 0 < b -> 0 < c -> (a + b) + c = pisurtrois ->  ( 0 <= c <= pi ).
intros.
rewrite <- pisurtrois_def.
split.
lra.
lra.
Qed.
#[export] Hint Resolve pisurtrois_utile sin_pos pisurtrois_utile1 pisurtrois_utile2 :geo.
 
Lemma pisurtrois_triangle_utile:
 forall a b c A B C,
 0 < a ->
 0 < b ->
 0 < c ->
 (a + b) + c = pisurtrois ->
 A <> B ->
 A <> C -> image_angle (3 * a) = cons_AV (vec A B) (vec A C) ->  triangle A B C.
intros.
apply non_multiple_pi_triangle with (3 * a); auto.
rewrite <- pisurtrois_def.
split.
lra.
lra.
Qed.
 
Lemma pisurtrois_triangle_utile2:
 forall a b c B C P,
 0 < a ->
 0 < b ->
 0 < c ->
 (a + b) + c = pisurtrois ->
 B <> C ->
 B <> P -> image_angle b = cons_AV (vec B C) (vec B P) ->  triangle B C P.
intros.
apply non_multiple_pi_triangle with b; auto.
split.
lra.
rewrite <- pisurtrois_def.
lra.
Qed.
 
Lemma Rabs_neg: forall (r : R), r <= 0 ->  Rabs r = - r.
intros.
elim H; intros.
rewrite Rabs_left; auto.
rewrite H0.
rewrite Rabs_R0; ring.
Qed.
(* Application des theoremes rayon_Sinus et loi_Sinus dans un triangle forme par un cote et deux trissectrices.
   Calcul de la longueur du cote BP dans le triangle BPC.*)
 
Lemma Morley_1:
 forall (a b c r : R) (A B C P : PO),
 0 < a ->
 0 < b ->
 0 < c ->
 (a + b) + c = pisurtrois ->
 A <> B ->
 A <> C ->
 B <> C ->
 B <> P ->
 rayon_circonscrit A B C r ->
 image_angle b = cons_AV (vec B C) (vec B P) ->
 image_angle c = cons_AV (vec C P) (vec C B) ->
 image_angle (3 * a) = cons_AV (vec A B) (vec A C) ->
  distance B P = (2 * (r * sin (3 * a))) * (sin c / sin (pisurtrois - a)).
unfold rayon_circonscrit; intros.
elim H7; [intros O [H13 H12]].
assert (triangle A B C).
apply (pisurtrois_triangle_utile (a:=a) (b:=b) (c:=c) (A:=A) (B:=B) (C:=C));
 auto.
assert (triangle B C P).
apply (pisurtrois_triangle_utile2 (a:=a) (b:=b) (c:=c) (B:=B) (C:=C) (P:=P));
 auto.
deroule_triangle B C P.
clear H18 H16 H15.
assert (distance B C = 2 * (r * sin (3 * a))).
rewrite (rayon_Sinus (A:=A) (B:=B) (C:=C) (O:=O)); auto.
rewrite H12.
rewrite <- (egalite_sin_Sin (A:=A) (B:=B) (C:=C) (x:=3 * a)); auto.
rewrite Rabs_right; eauto with geo.
rewrite <- H15.
rewrite <- H2.
RReplace (((a + b) + c) - a) (b + c).
elim pi_moins_x with ( x := b + c ); [intros].
rewrite <- H18.
elim (loi_Sinus (A:=C) (B:=B) (C:=P)); intros; auto with geo.
assert
 (distance B P =
  (distance C B / Rabs (Sin (cons_AV (vec P C) (vec P B)))) *
  Rabs (Sin (cons_AV (vec C B) (vec C P)))).
rewrite <- H19.
field.
auto with geo.
rewrite H21.
rewrite distance_sym.
assert (image_angle (- c) = cons_AV (vec C B) (vec C P)).
apply mes_oppx; auto.
rewrite <- (egalite_sin_Sin (A:=C) (B:=B) (C:=P) (x:=- c)); auto.
rewrite sin_impaire.
rewrite (Rabs_neg (r:=- sin c)).
assert (image_angle (- b) = cons_AV (vec B P) (vec B C)).
apply mes_oppx; auto.
assert (image_angle (pi + (b + c)) = cons_AV (vec P C) (vec P B)).
rewrite <- (angle_triangle (A:=C) (B:=B) (C:=P)); auto.
rewrite <- H23.
rewrite <- H22.
rewrite <- add_mes_compatible.
rewrite <- mes_opp.
rewrite <- add_mes_compatible.
RReplace (- (- c + - b)) (b + c); auto.
rewrite <- (egalite_sin_Sin (A:=P) (B:=C) (C:=B) (x:=pi + (b + c))); auto.
rewrite H18.
elim pi_plus_x with ( x := b + c ); intros.
rewrite H26.
rewrite Rabs_neg.
field.
assert (- sin (b + c) <> 0).
rewrite <- H26.
apply (triangle_sin_not_0 (A:=P) (B:=C) (C:=B) (x:=pi + (b + c))); auto with geo.
auto with real.
assert (sin (b + c) >= 0); eauto with geo.
lra.
assert (sin c >= 0); eauto with geo.
lra.
Qed.
(* application de la formule sin 3 a  qui utilise pisurtrois dons le calcul de BP*)
 
Lemma Morley_2:
 forall (a b c r : R) (A B C P : PO),
 0 < a ->
 0 < b ->
 0 < c ->
 (a + b) + c = pisurtrois ->
 A <> B ->
 A <> C ->
 B <> C ->
 B <> P ->
 rayon_circonscrit A B C r ->
 image_angle b = cons_AV (vec B C) (vec B P) ->
 image_angle c = cons_AV (vec C P) (vec C B) ->
 image_angle (3 * a) = cons_AV (vec A B) (vec A C) ->
  distance B P = (8 * (r * sin a)) * (sin c * sin (pisurtrois + a)).
intros.
assert (triangle B C P).
apply (pisurtrois_triangle_utile2 (a:=a) (b:=b) (c:=c) (B:=B) (C:=C) (P:=P));
 auto.
deroule_triangle B C P.
clear H13 H12 H15.
rewrite (Morley_1 (a:=a) (b:=b) (c:=c) (r:=r) (A:=A) (B:=B) (C:=C) (P:=P)); auto.
rewrite sin_3_a_pisurtrois; auto.
field.
rewrite <- H2.
RReplace (((a + b) + c) + - a) (b + c); auto.
assert (image_angle (- c) = cons_AV (vec C B) (vec C P)).
apply mes_oppx; auto.
assert (image_angle (- b) = cons_AV (vec B P) (vec B C)).
apply mes_oppx; auto.
assert (image_angle (pi + (b + c)) = cons_AV (vec P C) (vec P B)).
rewrite <- (angle_triangle (A:=C) (B:=B) (C:=P)); auto.
rewrite <- H13.
rewrite <- H12.
rewrite <- add_mes_compatible.
rewrite <- mes_opp.
rewrite <- add_mes_compatible.
RReplace (- (- c + - b)) (b + c); auto.
elim pi_plus_x with ( x := b + c ); intros.
assert (- sin (b + c) <> 0).
rewrite <- H17.
apply (triangle_sin_not_0 (A:=P) (B:=C) (C:=B) (x:=pi + (b + c))); auto with geo.
replace (a + b + c - a) with (b + c) by ring.
auto with real.
Qed.
(* calcul de la longueur du cote  CP dans le triangle BPC*)
 
Lemma Morley_3:
 forall (a b c r : R) (A B C P : PO),
 0 < a ->
 0 < b ->
 0 < c ->
 (a + b) + c = pisurtrois ->
 A <> B ->
 A <> C ->
 B <> C ->
 B <> P ->
 rayon_circonscrit A B C r ->
 image_angle b = cons_AV (vec B C) (vec B P) ->
 image_angle c = cons_AV (vec C P) (vec C B) ->
 image_angle (3 * a) = cons_AV (vec A B) (vec A C) ->
  distance C P = (8 * (r * sin a)) * (sin b * sin (pisurtrois + a)).
unfold rayon_circonscrit; intros.
elim H7; clear H7; [intros O [H13 H12]].
assert (triangle A B C).
apply (pisurtrois_triangle_utile (a:=a) (b:=b) (c:=c) (A:=A) (B:=B) (C:=C));
 auto.
assert (triangle B C P).
apply (pisurtrois_triangle_utile2 (a:=a) (b:=b) (c:=c) (B:=B) (C:=C) (P:=P));
 auto.
deroule_triangle B C P.
clear H17 H14 H15.
assert (distance C P = (2 * (r * sin (3 * a))) * (sin b / sin (pisurtrois - a))).
assert (distance B C = 2 * (r * sin (3 * a))).
rewrite (rayon_Sinus (A:=A) (B:=B) (C:=C) (O:=O)); auto.
rewrite H12.
rewrite <- (egalite_sin_Sin (A:=A) (B:=B) (C:=C) (x:=3 * a)); auto.
rewrite Rabs_right; eauto with geo.
rewrite <- H14.
rewrite <- H2.
RReplace (((a + b) + c) - a) (b + c).
elim pi_moins_x with ( x := b + c ); [intros].
rewrite <- H17.
elim (loi_Sinus (A:=C) (B:=B) (C:=P)); intros; auto with geo.
assert
 (distance C B / Rabs (Sin (cons_AV (vec P C) (vec P B))) =
  distance P C / Rabs (Sin (cons_AV (vec B P) (vec B C)))).
rewrite <- H19; auto.
assert
 (distance P C =
  (distance C B / Rabs (Sin (cons_AV (vec P C) (vec P B)))) *
  Rabs (Sin (cons_AV (vec B P) (vec B C)))).
rewrite H20.
field.
auto with geo.
rewrite distance_sym.
rewrite H21.
rewrite distance_sym.
assert (image_angle (- b) = cons_AV (vec B P) (vec B C)).
apply mes_oppx; auto.
assert (image_angle (- c) = cons_AV (vec C B) (vec C P)).
apply mes_oppx; auto.
rewrite <- (egalite_sin_Sin (A:=B) (B:=P) (C:=C) (x:=- b)); auto.
rewrite sin_impaire.
rewrite (Rabs_neg (r:=- sin b)).
assert (image_angle (pi + (b + c)) = cons_AV (vec P C) (vec P B)).
rewrite <- (angle_triangle (A:=C) (B:=B) (C:=P)); auto.
rewrite <- H23.
rewrite <- H22.
rewrite <- add_mes_compatible.
rewrite <- mes_opp.
rewrite <- add_mes_compatible.
RReplace (- (- c + - b)) (b + c); auto.
rewrite <- (egalite_sin_Sin (A:=P) (B:=C) (C:=B) (x:=pi + (b + c))); auto.
rewrite H17.
elim pi_plus_x with ( x := b + c ); intros.
rewrite H26.
rewrite Rabs_neg.
field.
assert (- sin (b + c) <> 0).
rewrite <- H26.
apply (triangle_sin_not_0 (A:=P) (B:=C) (C:=B) (x:=pi + (b + c))); auto with geo.
auto with real.
assert (sin (b + c) >= 0); eauto with geo.
lra.
assert (sin b >= 0).
apply sin_pos.
apply (pisurtrois_utile2 H H1 H0); auto with real.
rewrite <- H2; ring.
lra.
rewrite H14.
rewrite sin_3_a_pisurtrois; auto.
field.
rewrite <- H2.
RReplace (((a + b) + c) + - a) (b + c); auto.
assert (image_angle (- c) = cons_AV (vec C B) (vec C P)).
apply mes_oppx; auto.
assert (image_angle (- b) = cons_AV (vec B P) (vec B C)).
apply mes_oppx; auto.
assert (image_angle (pi + (b + c)) = cons_AV (vec P C) (vec P B)).
rewrite <- (angle_triangle (A:=C) (B:=B) (C:=P)); auto.
rewrite <- H15.
rewrite <- H17.
rewrite <- add_mes_compatible.
rewrite <- mes_opp.
rewrite <- add_mes_compatible.
RReplace (- (- c + - b)) (b + c); auto.
elim pi_plus_x with ( x := b + c ); intros.
assert (- sin (b + c) <> 0).
rewrite <- H20.
apply (triangle_sin_not_0 (A:=P) (B:=C) (C:=B) (x:=pi + (b + c))); auto with geo.
replace (a + b + c - a) with (b + c) by ring.
auto with real.
Qed.
(* on applique le lemme precedent dans un autre triangle ABQ forme par un cote et deux trissectrices*)
 
Lemma Morley_4:
 forall (a b c r : R) (A B C Q : PO),
 0 < a ->
 0 < b ->
 0 < c ->
 (a + b) + c = pisurtrois ->
 A <> B ->
 A <> C ->
 B <> C ->
 A <> Q ->
 rayon_circonscrit A B C r ->
 image_angle b = cons_AV (vec B Q) (vec B A) ->
 image_angle a = cons_AV (vec A B) (vec A Q) ->
 image_angle (3 * c) = cons_AV (vec C A) (vec C B) ->
  distance B Q = (8 * (r * sin c)) * (sin a * sin (pisurtrois + c)).
intros.
rewrite <- (Morley_3 (a:=c) (b:=a) (c:=b) (r:=r) (A:=C) (B:=A) (C:=B) (P:=Q));
 auto with geo.
rewrite <- H2; ring.
generalize H7; unfold rayon_circonscrit, circonscrit, isocele; intros.
elim H11; [intros O [H13 H14]].
elim H13; [intros H12 H15].
exists O.
split; auto.
split; auto.
rewrite <- H12; auto.
rewrite H14; rewrite <- H15; auto.
Qed.
(*dans le triangle BPQ on peut caculer le 3eme cote en utilisant Al_Kashi*)
 
Lemma Morley_5:
 forall (a b c r : R) (A B C P Q : PO),
 0 < a ->
 0 < b ->
 0 < c ->
 (a + b) + c = pisurtrois ->
 A <> B ->
 A <> C ->
 B <> C ->
 B <> P ->
 B <> Q ->
 A <> Q ->
 rayon_circonscrit A B C r ->
 image_angle b = cons_AV (vec B Q) (vec B A) ->
 image_angle b = cons_AV (vec B C) (vec B P) ->
 image_angle b = cons_AV (vec B P) (vec B Q) ->
 image_angle c = cons_AV (vec C P) (vec C B) ->
 image_angle a = cons_AV (vec A B) (vec A Q) ->
 image_angle (3 * a) = cons_AV (vec A B) (vec A C) ->
 image_angle (3 * c) = cons_AV (vec C A) (vec C B) ->
  Rsqr (distance P Q) =
  (Rsqr 8 * (Rsqr r * (Rsqr (sin a) * Rsqr (sin c)))) *
  ((Rsqr (sin (pisurtrois + a)) + Rsqr (sin (pisurtrois + c))) -
   2 * (sin (pisurtrois + a) * (sin (pisurtrois + c) * cos b))).
intros.
rewrite (Al_Kashi (A:=B) (B:=P) (C:=Q) (a:=b)); auto.
rewrite (Morley_2 (a:=a) (b:=b) (c:=c) (r:=r) (A:=A) (B:=B) (C:=C) (P:=P)); auto.
rewrite (Morley_4 (a:=a) (b:=b) (c:=c) (r:=r) (A:=A) (B:=B) (C:=C) (Q:=Q)); auto.
replace (Rsqr ((8 * (r * sin a)) * (sin c * sin (pisurtrois + a))))
     with
      ((Rsqr 8 * (Rsqr r * (Rsqr (sin a) * Rsqr (sin c)))) *
       Rsqr (sin (pisurtrois + a))).
2:unfold Rsqr; ring.
replace (Rsqr ((8 * (r * sin c)) * (sin a * sin (pisurtrois + c))))
     with
      ((Rsqr 8 * (Rsqr r * (Rsqr (sin a) * Rsqr (sin c)))) *
       Rsqr (sin (pisurtrois + c))).
2:unfold Rsqr; ring.
replace
 (((8 * (r * sin a)) * (sin c * sin (pisurtrois + a))) *
  (((8 * (r * sin c)) * (sin a * sin (pisurtrois + c))) * cos b))
     with
      ((Rsqr 8 * (Rsqr r * (Rsqr (sin a) * Rsqr (sin c)))) *
       (sin (pisurtrois + a) * (sin (pisurtrois + c) * cos b))).
2:unfold Rsqr; ring.
ring.
Qed.
(* utilisation de la formule de trigonometrie Al_Kashi_pisurtrois pour simplifier le calcul.*)
 
Lemma Morley_6:
 forall (a b c r : R) (A B C P Q : PO),
 0 < a ->
 0 < b ->
 0 < c ->
 (a + b) + c = pisurtrois ->
 A <> B ->
 A <> C ->
 B <> C ->
 B <> P ->
 B <> Q ->
 A <> Q ->
 rayon_circonscrit A B C r ->
 image_angle b = cons_AV (vec B Q) (vec B A) ->
 image_angle b = cons_AV (vec B C) (vec B P) ->
 image_angle b = cons_AV (vec B P) (vec B Q) ->
 image_angle c = cons_AV (vec C P) (vec C B) ->
 image_angle a = cons_AV (vec A B) (vec A Q) ->
 image_angle (3 * a) = cons_AV (vec A B) (vec A C) ->
 image_angle (3 * c) = cons_AV (vec C A) (vec C B) ->
  Rsqr (distance P Q) =
  (Rsqr 8 * (Rsqr r * (Rsqr (sin a) * Rsqr (sin b)))) * Rsqr (sin c).
intros.
rewrite (Morley_5 (a:=a) (b:=b) (c:=c) (r:=r) (A:=A) (B:=B) (C:=C) (P:=P) (Q:=Q));
 auto.
rewrite (Al_Kashi_pisurtrois (a:=a) (b:=b) (c:=c)); auto.
ring.
Qed.
 
Definition equilateral (A B C : PO) := and (isocele A B C) (isocele B C A).
(*Theoreme de Morley : utilisation de la symetrie de la formule pour conclure.*)
 
Theorem Morley:
 forall (a b c : R) (A B C P Q T : PO),
 0 < a ->
 0 < b ->
 0 < c ->
 (a + b) + c = pisurtrois ->
 A <> B ->
 A <> C ->
 B <> C ->
 B <> P ->
 B <> Q ->
 A <> T ->
 C <> T ->
 image_angle b = cons_AV (vec B C) (vec B P) ->
 image_angle b = cons_AV (vec B P) (vec B Q) ->
 image_angle b = cons_AV (vec B Q) (vec B A) ->
 image_angle c = cons_AV (vec C P) (vec C B) ->
 image_angle c = cons_AV (vec C T) (vec C P) ->
 image_angle a = cons_AV (vec A B) (vec A Q) ->
 image_angle a = cons_AV (vec A Q) (vec A T) ->
 image_angle a = cons_AV (vec A T) (vec A C) ->  equilateral P Q T.
intros.
assert (triangle B C P).
  apply (pisurtrois_triangle_utile2 (a:=a) (b:=b) (c:=c) (B:=B) (C:=C) (P:=P));
  auto.
deroule_triangle B C P.
assert (triangle B Q A).
  apply (pisurtrois_triangle_utile2 (a:=a) (b:=b) (c:=c) (B:=B) (C:=Q) (P:=A));
  auto.
deroule_triangle B Q A.
assert (image_angle (3 * a) = cons_AV (vec A B) (vec A C)).
  RReplace (3 * a) (a + (a + a)).
  replace (cons_AV (vec A B) (vec A C))
     with (plus (cons_AV (vec A B) (vec A Q)) (cons_AV (vec A Q) (vec A C))).
  replace (cons_AV (vec A Q) (vec A C))
     with (plus (cons_AV (vec A Q) (vec A T)) (cons_AV (vec A T) (vec A C))).
  rewrite <- H15; rewrite <- H16; rewrite <- H17.
  rewrite <- add_mes_compatible.
  rewrite <- add_mes_compatible; auto.
  apply Chasles; auto.
  apply Chasles; auto.
assert (triangle A B C).
  apply (pisurtrois_triangle_utile (a:=a) (b:=b) (c:=c) (A:=A) (B:=B) (C:=C));
  auto.
assert (image_angle (3 * b) = cons_AV (vec B C) (vec B A)).
  RReplace (3 * b) (b + (b + b)).
  replace (cons_AV (vec B C) (vec B A))
     with (plus (cons_AV (vec B C) (vec B P)) (cons_AV (vec B P) (vec B A))).
  replace (cons_AV (vec B P) (vec B A))
     with (plus (cons_AV (vec B P) (vec B Q)) (cons_AV (vec B Q) (vec B A))).
  rewrite <- H12; rewrite <- H11; rewrite <- H10.
  rewrite <- add_mes_compatible.
  rewrite <- add_mes_compatible; auto.
  apply Chasles; auto.
  apply Chasles; auto.
assert (image_angle (3 * c) = cons_AV (vec C A) (vec C B)).
  rewrite <- (angle_triangle (A:=A) (B:=B) (C:=C)); auto.
  rewrite <- H28.
  rewrite <- H30.
  rewrite <- add_mes_compatible.
  rewrite <- mes_opp.
  rewrite <- add_mes_compatible.
  rewrite <- pisurtrois_def.
  rewrite <- H2.
  RReplace (3 * ((a + b) + c) + - (3 * a + 3 * b)) (3 * c); auto.
assert (image_angle c = cons_AV (vec C A) (vec C T)).
  RReplace c ((3 * c + - c) + - c).
  rewrite add_mes_compatible.
  rewrite add_mes_compatible.
  rewrite H31.
  assert (image_angle (- c) = cons_AV (vec C B) (vec C P)).
    apply mes_oppx; auto.
  pattern (image_angle (- c)) at 1.
  rewrite H32.
  replace (plus (cons_AV (vec C A) (vec C B)) (cons_AV (vec C B) (vec C P)))
     with (cons_AV (vec C A) (vec C P)).
  assert (image_angle (- c) = cons_AV (vec C P) (vec C T)).
    apply mes_oppx; auto.
  rewrite H33.
  apply Chasles; auto.
  symmetry; apply Chasles; auto.
elim existence_rayon_circonscrit with ( A := A ) ( B := B ) ( C := C );
 [intros O [H33 [r H34]] | auto].
assert (rayon_circonscrit A B C r).
  unfold rayon_circonscrit.
  exists O; (split; auto).
assert
 (and
   (Rsqr (distance P Q) = Rsqr (distance T P))
   (Rsqr (distance P Q) = Rsqr (distance Q T))).
  rewrite (Morley_6 (a:=a) (b:=b) (c:=c) (r:=r) (A:=A) (B:=B) (C:=C) (P:=P) (Q:=Q));
  auto.
  rewrite (Morley_6 (a:=b) (b:=c) (c:=a) (r:=r) (A:=B) (B:=C) (C:=A) (P:=T) (Q:=P));
  auto.
  rewrite (Morley_6 (a:=c) (b:=a) (c:=b) (r:=r) (A:=C) (B:=A) (C:=B) (P:=Q) (Q:=T));
  auto.
  split; ring.
  rewrite <- H2; ring.
  exists O.
  rewrite H34.
  generalize H33; unfold circonscrit, isocele; intros.
  elim H36; [intros; (split; auto)].
  rewrite <- H38; auto.
  rewrite <- H37; auto.
  rewrite <- H2; ring.
  exists O.
  rewrite H34.
  generalize H33; unfold circonscrit, isocele; intros.
  elim H36; [intros; (split; auto)].
  rewrite <- H38; auto.
unfold equilateral, isocele.
elim H36; [intros].
split.
  rewrite (distance_sym P T); auto with geo.
rewrite (distance_sym Q P); auto with geo.
Qed.



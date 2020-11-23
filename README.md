# High School Geometry

[![CI][action-shield]][action-link]
[![Contributing][contributing-shield]][contributing-link]
[![Code of Conduct][conduct-shield]][conduct-link]
[![Zulip][zulip-shield]][zulip-link]

[action-shield]: https://github.com/coq-community/HighSchoolGeometry/workflows/CI/badge.svg?branch=master
[action-link]: https://github.com/coq-community/HighSchoolGeometry/actions?query=workflow%3ACI

[contributing-shield]: https://img.shields.io/badge/contributions-welcome-%23f7931e.svg
[contributing-link]: https://github.com/coq-community/manifesto/blob/master/CONTRIBUTING.md

[conduct-shield]: https://img.shields.io/badge/%E2%9D%A4-code%20of%20conduct-%23f15a24.svg
[conduct-link]: https://github.com/coq-community/manifesto/blob/master/CODE_OF_CONDUCT.md

[zulip-shield]: https://img.shields.io/badge/chat-on%20zulip-%23c1272d.svg
[zulip-link]: https://coq.zulipchat.com/#narrow/stream/237663-coq-community-devs.20.26.20users



This Coq library is dedicated to high-shool geometry teaching. The
axiomatisation for affine Euclidean space is in a non analytic setting.
Includes a proof of Ptolemy's theorem.

## Meta

- Author(s):
  - Frédérique Guilhot (initial)
  - Tuan-Minh Pham
- Coq-community maintainer(s):
  - Laurent Théry ([**@thery**](https://github.com/thery))
- License: [GNU Lesser General Public License v2.1 or later](LICENSE)
- Compatible Coq versions: 8.11 or later
- Additional dependencies: none
- Coq namespace: `HighSchoolGeometry`
- Related publication(s):
  - [Premiers pas vers un cours de géométrie en Coq pour le lycée](https://hal.inria.fr/inria-00071689/) 
  - [Similar Triangles and Orientation in Plane Elementary Geometry for Coq-based Proofs](https://hal.inria.fr/inria-00585203/) doi:[10.1145/1774088.1774358](https://doi.org/10.1145/1774088.1774358)

## Building and installation instructions

The easiest way to install the latest released version of High School Geometry
is via [OPAM](https://opam.ocaml.org/doc/Install.html):

```shell
opam repo add coq-released https://coq.inria.fr/opam/released
opam install coq-high-school-geometry
```

To instead build and install manually, do:

``` shell
git clone https://github.com/coq-community/HighSchoolGeometry.git
cd HighSchoolGeometry
make   # or make -j <number-of-cores-on-your-machine> 
make install
```


## Documentation in English

See also the [documentation in French](#Documentation-en-français) below.

This library consists in a collection of "chapters" spanning most of geometry taught
to French high-shool students. We do not even try to minimize the number of axioms but
rather to get as close as possible to informal definitions, theorems and proofs.
In order to focus on reasoning issues, we use a non analytic description of euclidean geometry.
The interested reader can find details about this work in Inria research report RR-4893:
[Premiers pas vers un cours de géométrie en Coq pour le lycée][report-link].

The first part "2-3 dimensional affine geometry" deals with formalising:
- points, vectors, barycenters, oriented lengths,
 (Rutile.v, Field_affine.v, vecteur.v, barycentre.v, milieu.v, mesure_algebrique.v)
- collinearity, coplanarity, (alignement.v, coplanarite.v)
- parallelism and incidence of straight lines, (parallelisme_concours.v)
- proofs of Thales and Desargues theorems.(affine_classiques.v)

In the second part "3 dimensional affine geometry", we prove theorems about:
- relative positions of two straight lines in the space (Droite_espace.v)
- relative positions of a straight line and a plane (Droite_plan_espace.v)
- relative positions of two planes (Plans_paralleles.v)
- parallelism and incidence properties for several planes and straight lines
  (Plan_espace.v)

The third part "2-3 dimensional euclidean geometry" deals with formalising:
- scalar product, orthogonal vectors, and unitary vectors
  (produit_scalaire.v, orthogonalite.v, representant_unitaire.v)
- eulidean distance and orthogonal projection on a line
  (distance_euclidienne.v, projection_orthogonale.v)
- proofs of Pythagorean theorem, median theorem (euclidien_classiques.v)

The fourth part "space orthogonality" deals with formalising:
- orthogonal line and plan (orthogonalite_espace.v)
We use these definitions to solve a high-school diploma (baccalaureat) exercise
in a formal way.(exercice_espace.v).

The fifth part "plane euclidean geometry" deals with formalising:
- affine coordinate system, orthogonal coordinate system, affine coordinates
  (repere_plan.v, repere_ortho_plan.v)
- oriented angles (angles_vecteurs.v, angles_droites.v)
- trigonometry (trigo.v)
- proofs of Pythagorean theorem, median theorem, Al-Kashi and sine theorems
  (metrique_triangle.v)
- perpendicular bisector, isocel triangle, orthocenter,
  (mediatrice.v, isocele.v, orthocentre.v)
- circle, cocyclicity, tangency (line or circle tangent)
  (cercle.v, cocyclicite.v, complements_cercle.v, contact.v)
- signed area, determinant (aire_signee.v, determinant.v)
- equations for straight lines and circles in plane geometry
  (equations_droites.v, equations_cercles.v)

The sixth part "plane transformations", deals with formalising:
- translations, homothety
  (dilatations.v, composee_dilatations.v, homothetie_plane.v)
- rotations, reflexions (rotation_plane.v, reflexion_plane.v)
- composition of these transformations.
  (composee_reflexions.v, composee_translation_rotation.v, composee_transformations.v, similitudes_directes.v)
- conservation of tangency for these transformations. (transformations_contact.v)

In the seventh part "applications", we prove:
- Miquel's theorem, orthocenter theorem, Simson line
  (applications_cocyclicite.v)
- circle power and plane inversion (puissance_cercle.v, inversion.v) 
- Euler line theorem and nine point circle theorem
  (droite_Euler.v, homoth_Euler.v).

The eighth part "complex numbers", deals with formalising:
- the field properties of complex numbers
  (complexes.v, formes_complexes.v, operations_complexes.v, complexes_conjugaison.v)
- application to geometry of complex numbers
  (complexes_dilations.v, complexes_similitudes.v, complexes_transformations.v, complexes_exercice.v,
   complexes_inversion.v, complexes_analytique.v)

Tuan-Minh Pham introduced the concept of orientation and proved Ptolemy's theorem
(orientation.v, triangles_semblables.v, Ptolemee.v). This work is described in
a [separate paper][ptolemy-link].

## Documentation en français

Ce développement propose une collection de "chapitres" couvrant
une large partie du programme de géométrie du lycée en France.
Le but n'est pas d'avoir un nombre minimal d'axiomes mais de "coller au plus près"
des définitions, théorèmes et démonstrations donnés au lycée.
Pour privilégier le raisonnement, la formalisation choisie n'utilise pas
le recours à la méthode analytique.
On trouvera expliquée en détail la démarche utilisée dans le Inria rapport de recherche
RR-4893: [Premiers pas vers un cours de géométrie en Coq pour le lycée][report-link].

Dans la partie "géométrie affine (dimension 2 et 3)", sont formalisés
- les points, vecteurs, barycentres, mesures algébriques,
  (Rutile.v, Field_affine.v, vecteur.v, barycentre.v, milieu.v, mesure_algebrique.v)
- les notions d'alignement et de coplanarité, (alignement.v, coplanarite.v)
- les notions de parallélisme et concours de droites, (parallelisme_concours.v)
- les preuves des théorèmes de Thalès et de Desargues. (affine_classiques.v)

Dans la partie  "géométrie affine dans l'espace", ont été démontrés les théorèmes concernant:
- les positions relatives de deux droites dans l'espace (Droite_espace.v)
- les positions relatives d'une droite et d'un plan (Droite_plan_espace.v)
- les positions relatives de deux plans (Plans_paralleles.v)
- les propriétés d'incidence et de parallélisme de plusieurs droites et plans de l'espace.
  (Plan_espace.v)

Dans la partie "géométrie euclidienne (dimension 2 et 3)", sont formalisés
- le produit scalaire, la notion d'orthogonalité de vecteurs et de vecteurs unitaires,
  (produit_scalaire.v, orthogonalite.v, representant_unitaire.v)
- la distance euclidienne et la projection orthogonale sur une droite.
  (distance_euclidienne.v, projection_orthogonale.v)
- les preuves des théorèmes de Pythagore, de la médiane et l'étude de ligne de niveau
  (euclidien_classiques.v)

Dans la partie  "orthogonalité dans l'espace", est formalisée
- la notion de droite et plan orthogonaux (orthogonalite_espace.v)
- un exercice donné au baccalauréat S est traité comme application (exercice_espace.v).

Dans la partie  "géométrie euclidienne plane", sont formalisés
- les repères affines, les repère orthogonaux et la notion de coordonnées de points
  (repere_plan.v, repere_ortho_plan.v)
- les angles orientés de vecteurs et de droites (angles_vecteurs.v, angles_droites.v)
- la trigonométrie (trigo.v)
- la trigonométrie du triangle rectangle et les théorèmes d'Al-Kashi et des sinus
  (metrique_triangle.v)
- les notions de médiatrice, triangle isocèle, orthocentre
  (mediatrice.v, isocele.v, orthocentre.v)
- les notions de cercle, cocyclicité, contact (tangente et cercles tangents)
  (cercle.v, cocyclicite.v, complements_cercle.v, contact.v)
- les notions d'aires signées et de déterminant de vecteurs (aire_signee.v, determinant.v)
- une partie de géométrie analytique concernant les équations de droites et les équations de cercle
 (equations_droites.v, equations_cercles.v)

Dans la partie  "transformations planes", sont étudiées
- les translations, homothéties et leur composées
  (dilatations.v, composee_dilatations.v, homothetie_plane.v)
- les rotations, symétries axiales (rotation_plane.v, reflexion_plane.v)
- les composées de ces transformations dont les similitudes directes.
  (composee_reflexions.v, composee_translation_rotation.v, composee_transformations.v, similitudes_directes.v)
- les propriétés de conservation du contact par ces transformations (transformations_contact.v)

Dans la partie  "applications", sont démontrés
- les théorèmes de Miquel, des symétriques de l'orthocentre, de la droite de Simson
  (applications_cocyclicite.v)
- les notions de puissance d'un point par rapport à un cercle et d'inversion plane
  (puissance_cercle.v, inversion.v)
- les théorèmes de la droite d'Euler et du cercle des neuf points
  (droite_Euler.v et homoth_Euler.v).

Dans la partie  "nombres complexes", sont démontrées
- les propriétés algébriques du corps des nombres complexes
  (complexes.v, formes_complexes.v, operations_complexes.v, complexes_conjugaison.v)
- la caractérisation géométrique des transformations d'écriture complexe :  z -> a z + b
  (complexes_dilations.v, complexes_similitudes.v, complexes_transformations.v, complexes_exercice.v)
- l'écriture complexe de l'inversion (complexes_inversion.v)
- l'écriture analytique de toutes les transformations étudiées (complexes_analytique.v)

[report-link]: https://hal.inria.fr/inria-00071689/
[ptolemy-link]: https://hal.inria.fr/inria-00585203/

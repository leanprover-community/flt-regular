WARNING types not equal
<def homology_zero_zero : Π {V : Type u} [_inst_1 : category_theory.category V]
[_inst_2 : category_theory.limits.has_zero_morphisms V] {A B C : V} [_inst_6 : category_theory.limits.has_zero_object V]
[_inst_7 : category_theory.limits.has_image 0]
[_inst_8 : category_theory.limits.has_cokernel (image_to_kernel 0 0 homology_zero_zero._proof_3)],
  homology 0 0 homology_zero_zero._proof_5 ≅ B := λ {V : Type u} [_inst_1 : category_theory.category V]
[_inst_2 : category_theory.limits.has_zero_morphisms V] {A B C : V} [_inst_6 : category_theory.limits.has_zero_object V]
[_inst_7 : category_theory.limits.has_image 0]
[_inst_8 : category_theory.limits.has_cokernel (image_to_kernel 0 0 homology_zero_zero._proof_8)],
  {hom := homology.desc 0 0 homology_zero_zero._proof_12 (category_theory.limits.kernel_subobject 0).arrow
            homology_zero_zero._proof_13,
   inv := category_theory.inv (category_theory.limits.kernel_subobject 0).arrow ≫
            homology.π 0 0 homology_zero_zero._proof_15,
   hom_inv_id' := _,
   inv_hom_id' := _}>
WARNING types not equal
<def function_field.ring_of_integers.class_group.fintype : Π (Fq F : Type) [_inst_1 : field Fq] [_inst_2 : fintype Fq]
[_inst_3 : field F] [_inst_4 : algebra (polynomial Fq) F] [_inst_5 : algebra (ratfunc Fq) F]
[_inst_6 : is_scalar_tower (polynomial Fq) (ratfunc Fq) F] [_inst_7 : function_field Fq F]
[_inst_8 : is_separable (ratfunc Fq) F], fintype (class_group ↥(function_field.ring_of_integers Fq F) F) := λ
(Fq F : Type) [_inst_1 : field Fq] [_inst_2 : fintype Fq] [_inst_3 : field F] [_inst_4 : algebra (polynomial Fq) F]
[_inst_5 : algebra (ratfunc Fq) F] [_inst_6 : is_scalar_tower (polynomial Fq) (ratfunc Fq) F]
[_inst_7 : function_field Fq F] [_inst_8 : is_separable (ratfunc Fq) F],
  class_group.fintype_of_admissible_of_finite (ratfunc Fq) F polynomial.card_pow_degree_is_admissible>
WARNING types not equal
<def algebraic_geometry.stalk_function_field_algebra : Π (X : algebraic_geometry.Scheme)
[_inst_1 : irreducible_space ↥(X.to_LocallyRingedSpace.to_SheafedSpace.to_PresheafedSpace.carrier)]
(x : ↥(X.to_LocallyRingedSpace.to_SheafedSpace.to_PresheafedSpace.carrier)),
  algebra ↥(X.to_LocallyRingedSpace.to_SheafedSpace.to_PresheafedSpace.presheaf.stalk x) ↥(X.function_field) := λ
(X : algebraic_geometry.Scheme)
[_inst_1 : irreducible_space ↥(X.to_LocallyRingedSpace.to_SheafedSpace.to_PresheafedSpace.carrier)]
(x : ↥(X.to_LocallyRingedSpace.to_SheafedSpace.to_PresheafedSpace.carrier)),
  ring_hom.to_algebra (X.to_LocallyRingedSpace.to_SheafedSpace.to_PresheafedSpace.presheaf.stalk_specializes _)>
WARNING types not equal
<def category_theory.limits.prod_comparison_nat_iso : Π {C : Type u} [_inst_1 : category_theory.category C]
{D : Type u₂} [_inst_2 : category_theory.category D] (F : C ⥤ D)
[_inst_7 : category_theory.limits.has_binary_products C] [_inst_8 : category_theory.limits.has_binary_products D]
(A : C) [_inst_9 : ∀ (B : C), category_theory.is_iso (category_theory.limits.prod_comparison F A B)],
  category_theory.limits.prod.functor.obj A ⋙ F ≅ F ⋙ category_theory.limits.prod.functor.obj (F.obj A) := λ
{C : Type u} [_inst_1 : category_theory.category C] {D : Type u₂} [_inst_2 : category_theory.category D] (F : C ⥤ D)
[_inst_7 : category_theory.limits.has_binary_products C] [_inst_8 : category_theory.limits.has_binary_products D]
(A : C) [_inst_9 : ∀ (B : C), category_theory.is_iso (category_theory.limits.prod_comparison F A B)],
  {hom := category_theory.limits.prod_comparison_nat_trans F A,
   inv := (category_theory.as_iso
             {app := λ (B : C), category_theory.limits.prod_comparison F A B, naturality' := _}).inv,
   hom_inv_id' := _,
   inv_hom_id' := _}>
WARNING types not equal
<def algebraic_geometry.Scheme.function_field.algebra : Π (X : algebraic_geometry.Scheme)
[_inst_1 : irreducible_space ↥(X.to_LocallyRingedSpace.to_SheafedSpace.to_PresheafedSpace.carrier)]
(U : topological_space.opens ↥(X.to_LocallyRingedSpace.to_SheafedSpace.to_PresheafedSpace.carrier))
[_inst_2 : nonempty ↥U],
  algebra ↥(X.to_LocallyRingedSpace.to_SheafedSpace.to_PresheafedSpace.presheaf.obj (opposite.op U))
    ↥(X.function_field) := λ (X : algebraic_geometry.Scheme)
[_inst_1 : irreducible_space ↥(X.to_LocallyRingedSpace.to_SheafedSpace.to_PresheafedSpace.carrier)]
(U : topological_space.opens ↥(X.to_LocallyRingedSpace.to_SheafedSpace.to_PresheafedSpace.carrier))
[_inst_2 : nonempty ↥U], ring_hom.to_algebra (X.germ_to_function_field U)>
WARNING types not equal
<def algebraic_geometry.Scheme.function_field.algebra : Π (X : algebraic_geometry.Scheme)
[_inst_1 : irreducible_space ↥(X.to_LocallyRingedSpace.to_SheafedSpace.to_PresheafedSpace.carrier)]
(U : topological_space.opens ↥(X.to_LocallyRingedSpace.to_SheafedSpace.to_PresheafedSpace.carrier))
[_inst_2 : nonempty ↥U],
  algebra ↥(X.to_LocallyRingedSpace.to_SheafedSpace.to_PresheafedSpace.presheaf.obj (opposite.op U))
    ↥(X.function_field) := λ (X : algebraic_geometry.Scheme)
[_inst_1 : irreducible_space ↥(X.to_LocallyRingedSpace.to_SheafedSpace.to_PresheafedSpace.carrier)]
(U : topological_space.opens ↥(X.to_LocallyRingedSpace.to_SheafedSpace.to_PresheafedSpace.carrier))
[_inst_2 : nonempty ↥U], ring_hom.to_algebra (X.germ_to_function_field U)>
WARNING types not equal
<def category_theory.triangulated.pretriangulated.triangulated_functor.map_triangle : Π {C : Type u₁}
[_inst_1 : category_theory.category C] [_inst_2 : category_theory.limits.has_zero_object C]
[_inst_3 : category_theory.has_shift C ℤ] [_inst_4 : category_theory.preadditive C]
[_inst_5 : ∀ (n : ℤ), (category_theory.shift_functor C n).additive] {D : Type u₂}
[_inst_6 : category_theory.category D] [_inst_7 : category_theory.limits.has_zero_object D]
[_inst_8 : category_theory.has_shift D ℤ] [_inst_9 : category_theory.preadditive D]
[_inst_10 : ∀ (n : ℤ), (category_theory.shift_functor D n).additive]
[_inst_11 : category_theory.triangulated.pretriangulated C] [_inst_12 : category_theory.triangulated.pretriangulated D],
  category_theory.triangulated.pretriangulated.triangulated_functor C D →
  category_theory.triangulated.triangle C ⥤ category_theory.triangulated.triangle D := λ {C : Type u₁}
[_inst_1 : category_theory.category C] [_inst_2 : category_theory.limits.has_zero_object C]
[_inst_3 : category_theory.has_shift C ℤ] [_inst_4 : category_theory.preadditive C]
[_inst_5 : ∀ (n : ℤ), (category_theory.shift_functor C n).additive] {D : Type u₂}
[_inst_6 : category_theory.category D] [_inst_7 : category_theory.limits.has_zero_object D]
[_inst_8 : category_theory.has_shift D ℤ] [_inst_9 : category_theory.preadditive D]
[_inst_10 : ∀ (n : ℤ), (category_theory.shift_functor D n).additive]
[_inst_11 : category_theory.triangulated.pretriangulated C] [_inst_12 : category_theory.triangulated.pretriangulated D]
(F : category_theory.triangulated.pretriangulated.triangulated_functor C D),
  F.to_triangulated_functor_struct.map_triangle>
WARNING types not equal
<def category_theory.triangulated.pretriangulated.triangulated_functor.map_triangle : Π {C : Type u₁}
[_inst_1 : category_theory.category C] [_inst_2 : category_theory.limits.has_zero_object C]
[_inst_3 : category_theory.has_shift C ℤ] [_inst_4 : category_theory.preadditive C]
[_inst_5 : ∀ (n : ℤ), (category_theory.shift_functor C n).additive] {D : Type u₂}
[_inst_6 : category_theory.category D] [_inst_7 : category_theory.limits.has_zero_object D]
[_inst_8 : category_theory.has_shift D ℤ] [_inst_9 : category_theory.preadditive D]
[_inst_10 : ∀ (n : ℤ), (category_theory.shift_functor D n).additive]
[_inst_11 : category_theory.triangulated.pretriangulated C] [_inst_12 : category_theory.triangulated.pretriangulated D],
  category_theory.triangulated.pretriangulated.triangulated_functor C D →
  category_theory.triangulated.triangle C ⥤ category_theory.triangulated.triangle D := λ {C : Type u₁}
[_inst_1 : category_theory.category C] [_inst_2 : category_theory.limits.has_zero_object C]
[_inst_3 : category_theory.has_shift C ℤ] [_inst_4 : category_theory.preadditive C]
[_inst_5 : ∀ (n : ℤ), (category_theory.shift_functor C n).additive] {D : Type u₂}
[_inst_6 : category_theory.category D] [_inst_7 : category_theory.limits.has_zero_object D]
[_inst_8 : category_theory.has_shift D ℤ] [_inst_9 : category_theory.preadditive D]
[_inst_10 : ∀ (n : ℤ), (category_theory.shift_functor D n).additive]
[_inst_11 : category_theory.triangulated.pretriangulated C] [_inst_12 : category_theory.triangulated.pretriangulated D]
(F : category_theory.triangulated.pretriangulated.triangulated_functor C D),
  F.to_triangulated_functor_struct.map_triangle>
WARNING types not equal
<def category_theory.functor.right_derived : Π {C : Type u} [_inst_1 : category_theory.category C] {D : Type u_1}
[_inst_2 : category_theory.category D] [_inst_3 : category_theory.abelian C]
[_inst_4 : category_theory.has_injective_resolutions C] [_inst_5 : category_theory.abelian D] (F : C ⥤ D)
[_inst_6 : F.additive], ℕ → C ⥤ D := λ {C : Type u} [_inst_1 : category_theory.category C] {D : Type u_1}
[_inst_2 : category_theory.category D] [_inst_3 : category_theory.abelian C]
[_inst_4 : category_theory.has_injective_resolutions C] [_inst_5 : category_theory.abelian D] (F : C ⥤ D)
[_inst_6 : F.additive] (n : ℕ),
  category_theory.injective_resolutions C ⋙
    category_theory.functor.map_homotopy_category (complex_shape.up ℕ) F ⋙
      homotopy_category.homology_functor D (complex_shape.up ℕ) n>
WARNING types not equal
<def algebraic_geometry.SheafedSpace.is_open_immersion.SheafedSpace_forget_preserves_of_left : Π {C : Type u}
[_inst_1 : category_theory.category C] [_inst_2 : category_theory.limits.has_products C]
{X : algebraic_geometry.SheafedSpace C} {Y : algebraic_geometry.SheafedSpace C} {Z : algebraic_geometry.SheafedSpace C}
(f : X ⟶ Z) (g : Y ⟶ Z) [H : algebraic_geometry.SheafedSpace.is_open_immersion f],
  category_theory.limits.preserves_limit (category_theory.limits.cospan f g)
    (algebraic_geometry.SheafedSpace.forget C) := λ {C : Type u} [_inst_1 : category_theory.category C]
[_inst_2 : category_theory.limits.has_products C] {X : algebraic_geometry.SheafedSpace C}
{Y : algebraic_geometry.SheafedSpace C} {Z : algebraic_geometry.SheafedSpace C} (f : X ⟶ Z) (g : Y ⟶ Z)
[H : algebraic_geometry.SheafedSpace.is_open_immersion f],
  category_theory.limits.comp_preserves_limit algebraic_geometry.SheafedSpace.forget_to_PresheafedSpace
    (algebraic_geometry.PresheafedSpace.forget C)>
WARNING types not equal
<def algebraic_geometry.Scheme.J.fintype : Π {X : algebraic_geometry.Scheme} (𝒰 : X.open_cover)
[H : compact_space ↥(X.to_LocallyRingedSpace.to_SheafedSpace.to_PresheafedSpace.carrier)],
  fintype 𝒰.finite_subcover.J := λ {X : algebraic_geometry.Scheme} (𝒰 : X.open_cover)
[H : compact_space ↥(X.to_LocallyRingedSpace.to_SheafedSpace.to_PresheafedSpace.carrier)],
  id (finset.subtype.fintype _.some)>
WARNING types not equal
<def algebraic_geometry.PresheafedSpace.is_open_immersion.to_LocallyRingedSpace_hom : Π
{X : algebraic_geometry.PresheafedSpace CommRing} (Y : algebraic_geometry.LocallyRingedSpace)
(f : X ⟶ Y.to_SheafedSpace.to_PresheafedSpace) [H : algebraic_geometry.PresheafedSpace.is_open_immersion f],
  algebraic_geometry.PresheafedSpace.is_open_immersion.to_LocallyRingedSpace Y f ⟶ Y := λ
{X : algebraic_geometry.PresheafedSpace CommRing} (Y : algebraic_geometry.LocallyRingedSpace)
(f : X ⟶ Y.to_SheafedSpace.to_PresheafedSpace) [H : algebraic_geometry.PresheafedSpace.is_open_immersion f],
  ⟨f, _⟩>
WARNING types not equal
<def algebraic_geometry.SheafedSpace.is_open_immersion.SheafedSpace_forget_preserves_of_right : Π {C : Type u}
[_inst_1 : category_theory.category C] [_inst_2 : category_theory.limits.has_products C]
{X : algebraic_geometry.SheafedSpace C} {Y : algebraic_geometry.SheafedSpace C} {Z : algebraic_geometry.SheafedSpace C}
(f : X ⟶ Z) (g : Y ⟶ Z) [H : algebraic_geometry.SheafedSpace.is_open_immersion f],
  category_theory.limits.preserves_limit (category_theory.limits.cospan g f)
    (algebraic_geometry.SheafedSpace.forget C) := λ {C : Type u} [_inst_1 : category_theory.category C]
[_inst_2 : category_theory.limits.has_products C] {X : algebraic_geometry.SheafedSpace C}
{Y : algebraic_geometry.SheafedSpace C} {Z : algebraic_geometry.SheafedSpace C} (f : X ⟶ Z) (g : Y ⟶ Z)
[H : algebraic_geometry.SheafedSpace.is_open_immersion f],
  category_theory.limits.preserves_pullback_symmetry (algebraic_geometry.SheafedSpace.forget C) f g>
WARNING types not equal
<def category_theory.injective_resolutions : Π (C : Type u) [_inst_1 : category_theory.category C]
[_inst_2 : category_theory.abelian C] [_inst_3 : category_theory.has_injective_resolutions C],
  C ⥤ homotopy_category C (complex_shape.up ℕ) := λ (C : Type u) [_inst_1 : category_theory.category C]
[_inst_2 : category_theory.abelian C] [_inst_3 : category_theory.has_injective_resolutions C],
  {obj := λ (X : C),
            (homotopy_category.quotient C (complex_shape.up ℕ)).obj (category_theory.injective_resolution X),
   map := λ (X Y : C) (f : X ⟶ Y),
            (homotopy_category.quotient C (complex_shape.up ℕ)).map (category_theory.injective_resolution.desc f),
   map_id' := _,
   map_comp' := _}>
WARNING types not equal
<def algebraic_geometry.SheafedSpace.is_open_immersion.forget_creates_pullback_of_left : Π {C : Type u}
[_inst_1 : category_theory.category C] [_inst_2 : category_theory.limits.has_products C]
{X : algebraic_geometry.SheafedSpace C} {Y : algebraic_geometry.SheafedSpace C} {Z : algebraic_geometry.SheafedSpace C}
(f : X ⟶ Z) (g : Y ⟶ Z) [H : algebraic_geometry.SheafedSpace.is_open_immersion f],
  category_theory.creates_limit (category_theory.limits.cospan f g)
    algebraic_geometry.SheafedSpace.forget_to_PresheafedSpace := λ {C : Type u} [_inst_1 : category_theory.category C]
[_inst_2 : category_theory.limits.has_products C] {X : algebraic_geometry.SheafedSpace C}
{Y : algebraic_geometry.SheafedSpace C} {Z : algebraic_geometry.SheafedSpace C} (f : X ⟶ Z) (g : Y ⟶ Z)
[H : algebraic_geometry.SheafedSpace.is_open_immersion f],
  category_theory.creates_limit_of_fully_faithful_of_iso
    (algebraic_geometry.PresheafedSpace.is_open_immersion.to_SheafedSpace Y category_theory.limits.pullback.snd)
    (category_theory.eq_to_iso _ ≪≫
       category_theory.limits.has_limit.iso_of_nat_iso
         (category_theory.limits.diagram_iso_cospan
            (category_theory.limits.cospan f g ⋙ algebraic_geometry.SheafedSpace.forget_to_PresheafedSpace)).symm)>
WARNING types not equal
<def category_theory.nat_trans.right_derived : Π {C : Type u} [_inst_1 : category_theory.category C] {D : Type u_1}
[_inst_2 : category_theory.category D] [_inst_3 : category_theory.abelian C]
[_inst_4 : category_theory.has_injective_resolutions C] [_inst_5 : category_theory.abelian D] {F G : C ⥤ D}
[_inst_6 : F.additive] [_inst_7 : G.additive], (F ⟶ G) → Π (n : ℕ), F.right_derived n ⟶ G.right_derived n := λ
{C : Type u} [_inst_1 : category_theory.category C] {D : Type u_1} [_inst_2 : category_theory.category D]
[_inst_3 : category_theory.abelian C] [_inst_4 : category_theory.has_injective_resolutions C]
[_inst_5 : category_theory.abelian D] {F G : C ⥤ D} [_inst_6 : F.additive] [_inst_7 : G.additive] (α : F ⟶ G)
(n : ℕ),
  category_theory.whisker_left (category_theory.injective_resolutions C)
    (category_theory.whisker_right (category_theory.nat_trans.map_homotopy_category α (complex_shape.up ℕ))
       (homotopy_category.homology_functor D (complex_shape.up ℕ) n))>
WARNING types not equal
<def algebraic_geometry.PresheafedSpace.is_open_immersion.to_Scheme_hom : Π
{X : algebraic_geometry.PresheafedSpace CommRing} (Y : algebraic_geometry.Scheme)
(f : X ⟶ Y.to_LocallyRingedSpace.to_SheafedSpace.to_PresheafedSpace)
[H : algebraic_geometry.PresheafedSpace.is_open_immersion f],
  algebraic_geometry.PresheafedSpace.is_open_immersion.to_Scheme Y f ⟶ Y := λ
{X : algebraic_geometry.PresheafedSpace CommRing} (Y : algebraic_geometry.Scheme)
(f : X ⟶ Y.to_LocallyRingedSpace.to_SheafedSpace.to_PresheafedSpace)
[H : algebraic_geometry.PresheafedSpace.is_open_immersion f],
  algebraic_geometry.PresheafedSpace.is_open_immersion.to_LocallyRingedSpace_hom Y.to_LocallyRingedSpace f>
WARNING types not equal
<def algebraic_geometry.SheafedSpace.is_open_immersion.forget_creates_pullback_of_right : Π {C : Type u}
[_inst_1 : category_theory.category C] [_inst_2 : category_theory.limits.has_products C]
{X : algebraic_geometry.SheafedSpace C} {Y : algebraic_geometry.SheafedSpace C} {Z : algebraic_geometry.SheafedSpace C}
(f : X ⟶ Z) (g : Y ⟶ Z) [H : algebraic_geometry.SheafedSpace.is_open_immersion f],
  category_theory.creates_limit (category_theory.limits.cospan g f)
    algebraic_geometry.SheafedSpace.forget_to_PresheafedSpace := λ {C : Type u} [_inst_1 : category_theory.category C]
[_inst_2 : category_theory.limits.has_products C] {X : algebraic_geometry.SheafedSpace C}
{Y : algebraic_geometry.SheafedSpace C} {Z : algebraic_geometry.SheafedSpace C} (f : X ⟶ Z) (g : Y ⟶ Z)
[H : algebraic_geometry.SheafedSpace.is_open_immersion f],
  category_theory.creates_limit_of_fully_faithful_of_iso
    (algebraic_geometry.PresheafedSpace.is_open_immersion.to_SheafedSpace Y category_theory.limits.pullback.fst)
    (category_theory.eq_to_iso _ ≪≫
       category_theory.limits.has_limit.iso_of_nat_iso
         (category_theory.limits.diagram_iso_cospan
            (category_theory.limits.cospan g f ⋙ algebraic_geometry.SheafedSpace.forget_to_PresheafedSpace)).symm)>
WARNING types not equal
<def category_theory.functor.final.colimit_comp_coyoneda_iso : Π {C : Type v}
[_inst_1 : category_theory.small_category C] {D : Type v} [_inst_2 : category_theory.small_category D] (F : C ⥤ D)
[_inst_3 : F.final] (d : D)
[_inst_5 :
  category_theory.is_iso (category_theory.limits.colimit.pre (category_theory.coyoneda.obj (opposite.op d)) F)],
  category_theory.limits.colimit (F ⋙ category_theory.coyoneda.obj (opposite.op d)) ≅ punit := λ {C : Type v}
[_inst_1 : category_theory.small_category C] {D : Type v} [_inst_2 : category_theory.small_category D] (F : C ⥤ D)
[_inst_3 : F.final] (d : D)
[_inst_5 :
  category_theory.is_iso (category_theory.limits.colimit.pre (category_theory.coyoneda.obj (opposite.op d)) F)],
  category_theory.as_iso (category_theory.limits.colimit.pre (category_theory.coyoneda.obj (opposite.op d)) F) ≪≫
    category_theory.coyoneda.colimit_coyoneda_iso (opposite.op d)>
WARNING types not equal
<theorem category_theory.limits.image_map.map_ι : ∀ {C : Type u} [_inst_1 : category_theory.category C]
{f g : category_theory.arrow C} [_inst_2 : category_theory.limits.has_image f.hom]
[_inst_3 : category_theory.limits.has_image g.hom] {sq : f ⟶ g} (self : category_theory.limits.image_map sq),
  self.map ≫ category_theory.limits.image.ι g.hom = category_theory.limits.image.ι f.hom ≫ sq.right := λ
(C : Type u) [_inst_1 : category_theory.category C] (f g : category_theory.arrow C)
[_inst_2 : category_theory.limits.has_image f.hom] [_inst_3 : category_theory.limits.has_image g.hom] (sq : f ⟶ g)
(self : category_theory.limits.image_map sq), [category_theory.limits.image_map.map_ι' self]>
WARNING types not equal
<theorem category_theory.limits.image_map.map_ι : ∀ {C : Type u} [_inst_1 : category_theory.category C]
{f g : category_theory.arrow C} [_inst_2 : category_theory.limits.has_image f.hom]
[_inst_3 : category_theory.limits.has_image g.hom] {sq : f ⟶ g} (self : category_theory.limits.image_map sq),
  self.map ≫ category_theory.limits.image.ι g.hom = category_theory.limits.image.ι f.hom ≫ sq.right := λ
(C : Type u) [_inst_1 : category_theory.category C] (f g : category_theory.arrow C)
[_inst_2 : category_theory.limits.has_image f.hom] [_inst_3 : category_theory.limits.has_image g.hom] (sq : f ⟶ g)
(self : category_theory.limits.image_map sq), [category_theory.limits.image_map.map_ι' self]>
WARNING types not equal
<def category_theory.biprod.iso_elim : Π {C : Type u} [_inst_1 : category_theory.category C]
[_inst_2 : category_theory.preadditive C] [_inst_3 : category_theory.limits.has_binary_biproducts C]
{X₁ X₂ Y₁ Y₂ : C} (f : X₁ ⊞ X₂ ≅ Y₁ ⊞ Y₂)
[_inst_4 : category_theory.is_iso (category_theory.limits.biprod.inl ≫ f.hom ≫ category_theory.limits.biprod.fst)],
  X₂ ≅ Y₂ := λ {C : Type u} [_inst_1 : category_theory.category C] [_inst_2 : category_theory.preadditive C]
[_inst_3 : category_theory.limits.has_binary_biproducts C] {X₁ X₂ Y₁ Y₂ : C}
(f : X₁ ⊞ X₂ ≅ Y₁ ⊞ Y₂)
[_inst_4 : category_theory.is_iso (category_theory.limits.biprod.inl ≫ f.hom ≫ category_theory.limits.biprod.fst)],
  let _inst : category_theory.is_iso
        (category_theory.biprod.of_components
           (category_theory.limits.biprod.inl ≫ f.hom ≫ category_theory.limits.biprod.fst)
           (category_theory.limits.biprod.inl ≫ f.hom ≫ category_theory.limits.biprod.snd)
           (category_theory.limits.biprod.inr ≫ f.hom ≫ category_theory.limits.biprod.fst)
           (category_theory.limits.biprod.inr ≫ f.hom ≫ category_theory.limits.biprod.snd)) :=
        _
  in category_theory.biprod.iso_elim'
       (category_theory.limits.biprod.inl ≫ f.hom ≫ category_theory.limits.biprod.fst)
       (category_theory.limits.biprod.inl ≫ f.hom ≫ category_theory.limits.biprod.snd)
       (category_theory.limits.biprod.inr ≫ f.hom ≫ category_theory.limits.biprod.fst)
       (category_theory.limits.biprod.inr ≫ f.hom ≫ category_theory.limits.biprod.snd)>
WARNING types not equal
<def algebraic_geometry.PresheafedSpace.is_open_immersion.to_LocallyRingedSpace : Π
{X : algebraic_geometry.PresheafedSpace CommRing} (Y : algebraic_geometry.LocallyRingedSpace)
(f : X ⟶ Y.to_SheafedSpace.to_PresheafedSpace) [H : algebraic_geometry.PresheafedSpace.is_open_immersion f],
  algebraic_geometry.LocallyRingedSpace := λ {X : algebraic_geometry.PresheafedSpace CommRing}
(Y : algebraic_geometry.LocallyRingedSpace) (f : X ⟶ Y.to_SheafedSpace.to_PresheafedSpace)
[H : algebraic_geometry.PresheafedSpace.is_open_immersion f],
  {to_SheafedSpace := algebraic_geometry.PresheafedSpace.is_open_immersion.to_SheafedSpace Y.to_SheafedSpace f H,
   local_ring := _}>
WARNING types not equal
<def category_theory.biprod.gaussian : Π {C : Type u} [_inst_1 : category_theory.category C]
[_inst_2 : category_theory.preadditive C] [_inst_3 : category_theory.limits.has_binary_biproducts C]
{X₁ X₂ Y₁ Y₂ : C} (f : X₁ ⊞ X₂ ⟶ Y₁ ⊞ Y₂)
[_inst_4 : category_theory.is_iso (category_theory.limits.biprod.inl ≫ f ≫ category_theory.limits.biprod.fst)],
  Σ' (L : X₁ ⊞ X₂ ≅ X₁ ⊞ X₂) (R : Y₁ ⊞ Y₂ ≅ Y₁ ⊞ Y₂) (g₂₂ : X₂ ⟶ Y₂),
    L.hom ≫ f ≫ R.hom =
      category_theory.limits.biprod.map (category_theory.limits.biprod.inl ≫ f ≫ category_theory.limits.biprod.fst)
        g₂₂ := λ {C : Type u} [_inst_1 : category_theory.category C] [_inst_2 : category_theory.preadditive C]
[_inst_3 : category_theory.limits.has_binary_biproducts C] {X₁ X₂ Y₁ Y₂ : C}
(f : X₁ ⊞ X₂ ⟶ Y₁ ⊞ Y₂)
[_inst_4 : category_theory.is_iso (category_theory.limits.biprod.inl ≫ f ≫ category_theory.limits.biprod.fst)],
  let this : Σ' (L : X₁ ⊞ X₂ ≅ X₁ ⊞ X₂) (R : Y₁ ⊞ Y₂ ≅ Y₁ ⊞ Y₂) (g₂₂ : X₂ ⟶ Y₂),
        L.hom ≫
            category_theory.biprod.of_components
                (category_theory.limits.biprod.inl ≫ f ≫ category_theory.limits.biprod.fst)
                (category_theory.limits.biprod.inl ≫ f ≫ category_theory.limits.biprod.snd)
                (category_theory.limits.biprod.inr ≫ f ≫ category_theory.limits.biprod.fst)
                (category_theory.limits.biprod.inr ≫ f ≫ category_theory.limits.biprod.snd) ≫
              R.hom =
          category_theory.limits.biprod.map
            (category_theory.limits.biprod.inl ≫ f ≫ category_theory.limits.biprod.fst)
            g₂₂ :=
        category_theory.biprod.gaussian' (category_theory.limits.biprod.inl ≫ f ≫ category_theory.limits.biprod.fst)
          (category_theory.limits.biprod.inl ≫ f ≫ category_theory.limits.biprod.snd)
          (category_theory.limits.biprod.inr ≫ f ≫ category_theory.limits.biprod.fst)
          (category_theory.limits.biprod.inr ≫ f ≫ category_theory.limits.biprod.snd)
  in _.mpr (_.mp this)>
WARNING types not equal
<def category_theory.limits.coprod_comparison_nat_iso : Π {C : Type u} [_inst_1 : category_theory.category C]
{D : Type u₂} [_inst_2 : category_theory.category D] (F : C ⥤ D)
[_inst_7 : category_theory.limits.has_binary_coproducts C] [_inst_8 : category_theory.limits.has_binary_coproducts D]
(A : C) [_inst_9 : ∀ (B : C), category_theory.is_iso (category_theory.limits.coprod_comparison F A B)],
  F ⋙ category_theory.limits.coprod.functor.obj (F.obj A) ≅ category_theory.limits.coprod.functor.obj A ⋙ F := λ
{C : Type u} [_inst_1 : category_theory.category C] {D : Type u₂} [_inst_2 : category_theory.category D] (F : C ⥤ D)
[_inst_7 : category_theory.limits.has_binary_coproducts C] [_inst_8 : category_theory.limits.has_binary_coproducts D]
(A : C) [_inst_9 : ∀ (B : C), category_theory.is_iso (category_theory.limits.coprod_comparison F A B)],
  {hom := category_theory.limits.coprod_comparison_nat_trans F A,
   inv := (category_theory.as_iso
             {app := λ (B : C), category_theory.limits.coprod_comparison F A B, naturality' := _}).inv,
   hom_inv_id' := _,
   inv_hom_id' := _}>
WARNING types not equal
<def category_theory.injective_resolution.desc : Π {C : Type u} [_inst_1 : category_theory.category C]
[_inst_2 : category_theory.abelian C] {X Y : C},
  (X ⟶ Y) →
  Π [_inst_3 : category_theory.has_injective_resolution X] [_inst_4 : category_theory.has_injective_resolution Y],
    category_theory.injective_resolution X ⟶ category_theory.injective_resolution Y := λ {C : Type u}
[_inst_1 : category_theory.category C] [_inst_2 : category_theory.abelian C] {X Y : C} (f : X ⟶ Y)
[_inst_3 : category_theory.has_injective_resolution X] [_inst_4 : category_theory.has_injective_resolution Y],
  category_theory.InjectiveResolution.desc f _.some _.some>
WARNING types not equal
<def category_theory.injective_resolution.desc : Π {C : Type u} [_inst_1 : category_theory.category C]
[_inst_2 : category_theory.abelian C] {X Y : C},
  (X ⟶ Y) →
  Π [_inst_3 : category_theory.has_injective_resolution X] [_inst_4 : category_theory.has_injective_resolution Y],
    category_theory.injective_resolution X ⟶ category_theory.injective_resolution Y := λ {C : Type u}
[_inst_1 : category_theory.category C] [_inst_2 : category_theory.abelian C] {X Y : C} (f : X ⟶ Y)
[_inst_3 : category_theory.has_injective_resolution X] [_inst_4 : category_theory.has_injective_resolution Y],
  category_theory.InjectiveResolution.desc f _.some _.some>
WARNING types not equal
<def category_theory.triangulated.pretriangulated.triangulated_functor.inhabited : Π (C : Type u₁)
[_inst_1 : category_theory.category C] [_inst_2 : category_theory.limits.has_zero_object C]
[_inst_3 : category_theory.has_shift C ℤ] [_inst_4 : category_theory.preadditive C]
[_inst_5 : ∀ (n : ℤ), (category_theory.shift_functor C n).additive]
[_inst_11 : category_theory.triangulated.pretriangulated C],
  inhabited (category_theory.triangulated.pretriangulated.triangulated_functor C C) := λ (C : Type u₁)
[_inst_1 : category_theory.category C] [_inst_2 : category_theory.limits.has_zero_object C]
[_inst_3 : category_theory.has_shift C ℤ] [_inst_4 : category_theory.preadditive C]
[_inst_5 : ∀ (n : ℤ), (category_theory.shift_functor C n).additive]
[_inst_11 : category_theory.triangulated.pretriangulated C],
  {default := {to_triangulated_functor_struct := {to_functor := {obj := λ (X : C), X,
                                                                 map := λ (_x _x_1 : C) (f : _x ⟶ _x_1), f,
                                                                 map_id' := _,
                                                                 map_comp' := _},
                                                  comm_shift := category_theory.iso.refl
                                                                  (category_theory.shift_functor C 1 ⋙
                                                                     {obj := λ (X : C), X,
                                                                      map := λ (_x _x_1 : C) (f : _x ⟶ _x_1), f,
                                                                      map_id' := _,
                                                                      map_comp' := _})},
               map_distinguished' := _}}>
WARNING types not equal
<def algebraic_geometry.Scheme.germ_to_function_field : Π (X : algebraic_geometry.Scheme)
[_inst_1 : irreducible_space ↥(X.to_LocallyRingedSpace.to_SheafedSpace.to_PresheafedSpace.carrier)]
(U : topological_space.opens ↥(X.to_LocallyRingedSpace.to_SheafedSpace.to_PresheafedSpace.carrier))
[h : nonempty ↥U],
  X.to_LocallyRingedSpace.to_SheafedSpace.to_PresheafedSpace.presheaf.obj (opposite.op U) ⟶ X.function_field := λ
(X : algebraic_geometry.Scheme)
[_inst_1 : irreducible_space ↥(X.to_LocallyRingedSpace.to_SheafedSpace.to_PresheafedSpace.carrier)]
(U : topological_space.opens ↥(X.to_LocallyRingedSpace.to_SheafedSpace.to_PresheafedSpace.carrier))
[h : nonempty ↥U],
  X.to_LocallyRingedSpace.to_SheafedSpace.to_PresheafedSpace.presheaf.germ
    ⟨generic_point ↥(X.to_LocallyRingedSpace.to_SheafedSpace.to_PresheafedSpace.carrier) _inst_1, _⟩>
WARNING types not equal
<def algebraic_geometry.Scheme.germ_to_function_field : Π (X : algebraic_geometry.Scheme)
[_inst_1 : irreducible_space ↥(X.to_LocallyRingedSpace.to_SheafedSpace.to_PresheafedSpace.carrier)]
(U : topological_space.opens ↥(X.to_LocallyRingedSpace.to_SheafedSpace.to_PresheafedSpace.carrier))
[h : nonempty ↥U],
  X.to_LocallyRingedSpace.to_SheafedSpace.to_PresheafedSpace.presheaf.obj (opposite.op U) ⟶ X.function_field := λ
(X : algebraic_geometry.Scheme)
[_inst_1 : irreducible_space ↥(X.to_LocallyRingedSpace.to_SheafedSpace.to_PresheafedSpace.carrier)]
(U : topological_space.opens ↥(X.to_LocallyRingedSpace.to_SheafedSpace.to_PresheafedSpace.carrier))
[h : nonempty ↥U],
  X.to_LocallyRingedSpace.to_SheafedSpace.to_PresheafedSpace.presheaf.germ
    ⟨generic_point ↥(X.to_LocallyRingedSpace.to_SheafedSpace.to_PresheafedSpace.carrier) _inst_1, _⟩>
WARNING types not equal
<def category_theory.functor.right_derived_obj_injective_zero : Π {C : Type u} [_inst_1 : category_theory.category C]
{D : Type u_1} [_inst_2 : category_theory.category D] [_inst_3 : category_theory.abelian C]
[_inst_4 : category_theory.has_injective_resolutions C] [_inst_5 : category_theory.abelian D] (F : C ⥤ D)
[_inst_6 : F.additive] (X : C) [_inst_7 : category_theory.injective X], (F.right_derived 0).obj X ≅ F.obj X := λ
{C : Type u} [_inst_1 : category_theory.category C] {D : Type u_1} [_inst_2 : category_theory.category D]
[_inst_3 : category_theory.abelian C] [_inst_4 : category_theory.has_injective_resolutions C]
[_inst_5 : category_theory.abelian D] (F : C ⥤ D) [_inst_6 : F.additive] (X : C)
[_inst_7 : category_theory.injective X],
  F.right_derived_obj_iso 0 (category_theory.InjectiveResolution.self X) ≪≫
    (homology_functor D (complex_shape.up ℕ) 0).map_iso
        ((cochain_complex.single₀_map_homological_complex F).app X) ≪≫
      (cochain_complex.homology_functor_0_single₀ D).app (F.obj X)>
WARNING types not equal
<def category_theory.injective_resolution : Π {C : Type u} [_inst_1 : category_theory.category C]
[_inst_2 : category_theory.abelian C] (Z : C) [_inst_3 : category_theory.has_injective_resolution Z],
  cochain_complex C ℕ := λ {C : Type u} [_inst_1 : category_theory.category C] [_inst_2 : category_theory.abelian C]
(Z : C) [_inst_3 : category_theory.has_injective_resolution Z], _.some.cocomplex>
WARNING types not equal
<def is_alg_closure.equiv_of_algebraic : Π (K : Type u_1) (J : Type u_2) [_inst_2 : field K] [_inst_3 : field J]
(L : Type v) (M : Type w) [_inst_5 : field L] [_inst_6 : field M] [_inst_10 : algebra K M]
[_inst_11 : is_alg_closure K M] [_inst_19 : algebra K J] [_inst_20 : algebra J L] [_inst_21 : is_alg_closure J L]
[_inst_22 : algebra K L] [_inst_23 : is_scalar_tower K J L], algebra.is_algebraic K J → (L ≃ₐ[K] M) := λ
(K : Type u_1) (J : Type u_2) [_inst_2 : field K] [_inst_3 : field J] (L : Type v) (M : Type w) [_inst_5 : field L]
[_inst_6 : field M] [_inst_10 : algebra K M] [_inst_11 : is_alg_closure K M] [_inst_19 : algebra K J]
[_inst_20 : algebra J L] [_inst_21 : is_alg_closure J L] [_inst_22 : algebra K L] [_inst_23 : is_scalar_tower K J L]
(hKJ : algebra.is_algebraic K J), is_alg_closure.equiv_of_algebraic' K J L M _>
WARNING types not equal
<def is_alg_closure.equiv_of_algebraic : Π (K : Type u_1) (J : Type u_2) [_inst_2 : field K] [_inst_3 : field J]
(L : Type v) (M : Type w) [_inst_5 : field L] [_inst_6 : field M] [_inst_10 : algebra K M]
[_inst_11 : is_alg_closure K M] [_inst_19 : algebra K J] [_inst_20 : algebra J L] [_inst_21 : is_alg_closure J L]
[_inst_22 : algebra K L] [_inst_23 : is_scalar_tower K J L], algebra.is_algebraic K J → (L ≃ₐ[K] M) := λ
(K : Type u_1) (J : Type u_2) [_inst_2 : field K] [_inst_3 : field J] (L : Type v) (M : Type w) [_inst_5 : field L]
[_inst_6 : field M] [_inst_10 : algebra K M] [_inst_11 : is_alg_closure K M] [_inst_19 : algebra K J]
[_inst_20 : algebra J L] [_inst_21 : is_alg_closure J L] [_inst_22 : algebra K L] [_inst_23 : is_scalar_tower K J L]
(hKJ : algebra.is_algebraic K J), is_alg_closure.equiv_of_algebraic' K J L M _>
WARNING types not equal
<def category_theory.functor.right_derived_obj_injective_succ : Π {C : Type u} [_inst_1 : category_theory.category C]
{D : Type u_1} [_inst_2 : category_theory.category D] [_inst_3 : category_theory.abelian C]
[_inst_4 : category_theory.has_injective_resolutions C] [_inst_5 : category_theory.abelian D] (F : C ⥤ D)
[_inst_6 : F.additive] (n : ℕ) (X : C) [_inst_7 : category_theory.injective X],
  (F.right_derived (n + 1)).obj X ≅ 0 := λ {C : Type u} [_inst_1 : category_theory.category C] {D : Type u_1}
[_inst_2 : category_theory.category D] [_inst_3 : category_theory.abelian C]
[_inst_4 : category_theory.has_injective_resolutions C] [_inst_5 : category_theory.abelian D] (F : C ⥤ D)
[_inst_6 : F.additive] (n : ℕ) (X : C) [_inst_7 : category_theory.injective X],
  F.right_derived_obj_iso (n + 1) (category_theory.InjectiveResolution.self X) ≪≫
    (homology_functor D (complex_shape.up ℕ) (n + 1)).map_iso
        ((cochain_complex.single₀_map_homological_complex F).app X) ≪≫
      (cochain_complex.homology_functor_succ_single₀ D n).app (F.obj X) ≪≫ _.iso_zero>
WARNING types not equal
<def category_theory.injective_resolution.ι : Π {C : Type u} [_inst_1 : category_theory.category C]
[_inst_2 : category_theory.abelian C] (Z : C) [_inst_3 : category_theory.has_injective_resolution Z],
  (cochain_complex.single₀ C).obj Z ⟶ category_theory.injective_resolution Z := λ {C : Type u}
[_inst_1 : category_theory.category C] [_inst_2 : category_theory.abelian C] (Z : C)
[_inst_3 : category_theory.has_injective_resolution Z], _.some.ι>
WARNING types not equal
<def algebraic_geometry.PresheafedSpace.is_open_immersion.to_Scheme : Π
{X : algebraic_geometry.PresheafedSpace CommRing} (Y : algebraic_geometry.Scheme)
(f : X ⟶ Y.to_LocallyRingedSpace.to_SheafedSpace.to_PresheafedSpace)
[H : algebraic_geometry.PresheafedSpace.is_open_immersion f], algebraic_geometry.Scheme := λ
{X : algebraic_geometry.PresheafedSpace CommRing} (Y : algebraic_geometry.Scheme)
(f : X ⟶ Y.to_LocallyRingedSpace.to_SheafedSpace.to_PresheafedSpace)
[H : algebraic_geometry.PresheafedSpace.is_open_immersion f],
  algebraic_geometry.LocallyRingedSpace.is_open_immersion.Scheme
    (algebraic_geometry.PresheafedSpace.is_open_immersion.to_LocallyRingedSpace Y.to_LocallyRingedSpace f)
    _>
WARNING types not equal
<def function_field.class_number : Π (Fq F : Type) [_inst_1 : field Fq] [_inst_2 : fintype Fq] [_inst_3 : field F]
[_inst_4 : algebra (polynomial Fq) F] [_inst_5 : algebra (ratfunc Fq) F]
[_inst_6 : is_scalar_tower (polynomial Fq) (ratfunc Fq) F] [_inst_7 : function_field Fq F]
[_inst_8 : is_separable (ratfunc Fq) F], ℕ := λ (Fq F : Type) [_inst_1 : field Fq] [_inst_2 : fintype Fq]
[_inst_3 : field F] [_inst_4 : algebra (polynomial Fq) F] [_inst_5 : algebra (ratfunc Fq) F]
[_inst_6 : is_scalar_tower (polynomial Fq) (ratfunc Fq) F] [_inst_7 : function_field Fq F]
[_inst_8 : is_separable (ratfunc Fq) F], fintype.card (class_group ↥(function_field.ring_of_integers Fq F) F)>
WARNING types not equal
<def algebraic_geometry.PresheafedSpace.is_open_immersion.to_SheafedSpace_hom : Π {C : Type u}
[_inst_1 : category_theory.category C] [_inst_2 : category_theory.limits.has_products C]
{X : algebraic_geometry.PresheafedSpace C} (Y : algebraic_geometry.SheafedSpace C) (f : X ⟶ Y.to_PresheafedSpace)
[H : algebraic_geometry.PresheafedSpace.is_open_immersion f],
  algebraic_geometry.PresheafedSpace.is_open_immersion.to_SheafedSpace Y f ⟶ Y := λ {C : Type u}
[_inst_1 : category_theory.category C] [_inst_2 : category_theory.limits.has_products C]
{X : algebraic_geometry.PresheafedSpace C} (Y : algebraic_geometry.SheafedSpace C) (f : X ⟶ Y.to_PresheafedSpace)
[H : algebraic_geometry.PresheafedSpace.is_open_immersion f], f>
WARNING types not equal
<def category_theory.preserves_limit_of_Lan_presesrves_limit : Π {C D : Type u}
[_inst_4 : category_theory.small_category C] [_inst_5 : category_theory.small_category D] (F : C ⥤ D) (J : Type u)
[_inst_6 : category_theory.small_category J]
[_inst_7 : category_theory.limits.preserves_limits_of_shape J (category_theory.Lan F.op)],
  category_theory.limits.preserves_limits_of_shape J F := λ {C D : Type u} [_inst_4 : category_theory.small_category C]
[_inst_5 : category_theory.small_category D] (F : C ⥤ D) (J : Type u) [_inst_6 : category_theory.small_category J]
[_inst_7 : category_theory.limits.preserves_limits_of_shape J (category_theory.Lan F.op)],
  category_theory.limits.preserves_limits_of_shape_of_reflects_of_preserves F category_theory.yoneda>
WARNING types not equal
<def algebraic_geometry.Scheme.function_field : Π (X : algebraic_geometry.Scheme)
[_inst_1 : irreducible_space ↥(X.to_LocallyRingedSpace.to_SheafedSpace.to_PresheafedSpace.carrier)], CommRing := λ
(X : algebraic_geometry.Scheme)
[_inst_1 : irreducible_space ↥(X.to_LocallyRingedSpace.to_SheafedSpace.to_PresheafedSpace.carrier)],
  X.to_LocallyRingedSpace.to_SheafedSpace.to_PresheafedSpace.presheaf.stalk
    (generic_point ↥(X.to_LocallyRingedSpace.to_SheafedSpace.to_PresheafedSpace.carrier))>
WARNING types not equal
<def algebraic_geometry.PresheafedSpace.is_open_immersion.to_SheafedSpace : Π {C : Type u}
[_inst_1 : category_theory.category C] [_inst_2 : category_theory.limits.has_products C]
{X : algebraic_geometry.PresheafedSpace C} (Y : algebraic_geometry.SheafedSpace C) (f : X ⟶ Y.to_PresheafedSpace)
[H : algebraic_geometry.PresheafedSpace.is_open_immersion f], algebraic_geometry.SheafedSpace C := λ {C : Type u}
[_inst_1 : category_theory.category C] [_inst_2 : category_theory.limits.has_products C]
{X : algebraic_geometry.PresheafedSpace C} (Y : algebraic_geometry.SheafedSpace C) (f : X ⟶ Y.to_PresheafedSpace)
[H : algebraic_geometry.PresheafedSpace.is_open_immersion f], {to_PresheafedSpace := X, is_sheaf := _}>
WARNING types not equal
<def algebraic_geometry.Scheme.open_cover.finite_subcover : Π {X : algebraic_geometry.Scheme},
  X.open_cover →
  Π [H : compact_space ↥(X.to_LocallyRingedSpace.to_SheafedSpace.to_PresheafedSpace.carrier)], X.open_cover := λ
{X : algebraic_geometry.Scheme} (𝒰 : X.open_cover)
[H : compact_space ↥(X.to_LocallyRingedSpace.to_SheafedSpace.to_PresheafedSpace.carrier)],
  let t : finset ↥(X.to_LocallyRingedSpace.to_SheafedSpace.to_PresheafedSpace.carrier) := _.some
  in {J := ↥t,
      obj := λ (x : ↥t), 𝒰.obj (𝒰.f x.val),
      map := λ (x : ↥t), 𝒰.map (𝒰.f x.val),
      f := λ (x : ↥(X.to_LocallyRingedSpace.to_SheafedSpace.to_PresheafedSpace.carrier)), Exists.some _,
      covers := _,
      is_open := _}>
WARNING types not equal
<def category_theory.exp_terminal_iso_self : Π {C : Type u} [_inst_1 : category_theory.category C] {X : C}
[_inst_2 : category_theory.limits.has_finite_products C] [_inst_4 : category_theory.exponentiable (⊤_ C)],
  (category_theory.exp (⊤_ C)).obj X ≅ X := λ {C : Type u} [_inst_1 : category_theory.category C] {X : C}
[_inst_2 : category_theory.limits.has_finite_products C] [_inst_4 : category_theory.exponentiable (⊤_ C)],
  category_theory.yoneda.ext ((category_theory.exp (⊤_ C)).obj X) X
    (λ (Y : C) (f : Y ⟶ (category_theory.exp (⊤_ C)).obj X),
       (category_theory.limits.prod.left_unitor Y).inv ≫ category_theory.cartesian_closed.uncurry f)
    (λ (Y : C) (f : Y ⟶ X),
       category_theory.cartesian_closed.curry ((category_theory.limits.prod.left_unitor Y).hom ≫ f))
    category_theory.exp_terminal_iso_self._proof_9
    category_theory.exp_terminal_iso_self._proof_10
    category_theory.exp_terminal_iso_self._proof_11>
WARNING types not equal
<def algebraic_geometry.LocallyRingedSpace.hom_of_SheafedSpace_hom_of_is_iso : Π
{X Y : algebraic_geometry.LocallyRingedSpace} (f : X.to_SheafedSpace ⟶ Y.to_SheafedSpace)
[_inst_1 : category_theory.is_iso f], X ⟶ Y := λ {X Y : algebraic_geometry.LocallyRingedSpace}
(f : X.to_SheafedSpace ⟶ Y.to_SheafedSpace) [_inst_1 : category_theory.is_iso f], ⟨f, _⟩>
WARNING types not equal
<def category_theory.functor.right_derived_obj_iso : Π {C : Type u} [_inst_1 : category_theory.category C]
{D : Type u_1} [_inst_2 : category_theory.category D] [_inst_3 : category_theory.abelian C]
[_inst_4 : category_theory.has_injective_resolutions C] [_inst_5 : category_theory.abelian D] (F : C ⥤ D)
[_inst_6 : F.additive] (n : ℕ) {X : C} (P : category_theory.InjectiveResolution X),
  (F.right_derived n).obj X ≅
    (homology_functor D (complex_shape.up ℕ) n).obj
      ((F.map_homological_complex (complex_shape.up ℕ)).obj P.cocomplex) := λ {C : Type u}
[_inst_1 : category_theory.category C] {D : Type u_1} [_inst_2 : category_theory.category D]
[_inst_3 : category_theory.abelian C] [_inst_4 : category_theory.has_injective_resolutions C]
[_inst_5 : category_theory.abelian D] (F : C ⥤ D) [_inst_6 : F.additive] (n : ℕ) {X : C}
(P : category_theory.InjectiveResolution X),
  (homotopy_category.homology_functor D (complex_shape.up ℕ) n).map_iso
      (homotopy_category.iso_of_homotopy_equiv
         (F.map_homotopy_equiv (category_theory.functor.right_derived_obj_iso._proof_14.some.homotopy_equiv P))) ≪≫
    (homotopy_category.homology_factors D (complex_shape.up ℕ) n).app
      ((F.map_homological_complex (complex_shape.up ℕ)).obj P.cocomplex)>
/- Checking 127377 declarations (plus 123531 automatically generated ones) in mathlib (only in imported files) with 1 linters -/

/- The `generalisation_linter` linter reports: -/
/- typeclass generalisations may be possible -/
-- algebra/add_torsor.lean
#check @vsub_eq_sub /- _inst_1: add_group ↝ has_sub has_vsub
 -/

-- algebra/algebra/basic.lean
#check @algebra.smul_mul_assoc /- _inst_4: algebra ↝ has_smul is_scalar_tower
 -/
#check @algebra.bit0_smul_one /- _inst_4: algebra ↝ has_smul module
 -/
#check @algebra.bit0_smul_one' /- _inst_4: algebra ↝ distrib_mul_action has_smul module
 -/
#check @algebra.bit0_smul_bit0 /- _inst_4: algebra ↝ distrib_mul_action has_smul module
 -/
#check @algebra.bit0_smul_bit1 /- _inst_4: algebra ↝ distrib_mul_action has_smul module
 -/
#check @algebra.bit1_smul_one' /- _inst_4: algebra ↝ distrib_mul_action has_smul module mul_action
 -/
#check @algebra.bit1_smul_bit1 /- _inst_4: algebra ↝ distrib_mul_action has_smul module mul_action
 -/
#check @algebra.id.smul_eq_mul /- _inst_1: comm_semiring ↝ has_mul
 -/
#check @alg_hom.map_inv /- _inst_2: division_ring ↝ division_semiring
_inst_3: division_ring ↝ division_semiring
 -/
#check @alg_hom.map_div /- _inst_2: division_ring ↝ division_semiring
_inst_3: division_ring ↝ division_semiring
 -/
#check @alg_equiv.map_inv /- _inst_1: comm_ring ↝ comm_semiring
 -/
#check @alg_equiv.map_div /- _inst_1: comm_ring ↝ comm_semiring
 -/
#check @ring_hom.map_rat_algebra_map /- _inst_1: ring ↝ semiring
_inst_2: ring ↝ semiring
 -/
#check @no_zero_smul_divisors.iff_algebra_map_injective /- _inst_2: ring ↝ euclidean_domain no_zero_divisors
_inst_3: is_domain ↝ no_zero_divisors nontrivial
 -/
#check @algebra_compatible_smul /- _inst_5: module ↝ has_smul mul_action
_inst_6: module ↝ has_smul
 -/
#check @no_zero_smul_divisors.trans /- _inst_16: add_comm_group ↝ add_comm_monoid has_smul
 -/
#check @is_scalar_tower.to_smul_comm_class' /- _inst_3: algebra ↝ has_smul smul_comm_class
_inst_5: module ↝ has_smul smul_comm_class
_inst_6: module ↝ has_smul smul_comm_class
_inst_7: is_scalar_tower ↝ smul_comm_class
 -/
#check @smul_algebra_smul_comm /- _inst_3: algebra ↝ has_smul smul_comm_class
_inst_5: module ↝ has_smul smul_comm_class
_inst_6: module ↝ has_smul smul_comm_class
_inst_7: is_scalar_tower ↝ smul_comm_class
 -/
#check @linear_map.coe_is_scalar_tower /- _inst_3: algebra ↝ has_smul linear_map.compatible_smul
_inst_7: is_scalar_tower ↝ linear_map.compatible_smul
_inst_11: is_scalar_tower ↝ linear_map.compatible_smul
 -/
#check @linear_map.coe_restrict_scalars_eq_coe /- _inst_3: algebra ↝ has_smul linear_map.compatible_smul
_inst_7: is_scalar_tower ↝ linear_map.compatible_smul
_inst_11: is_scalar_tower ↝ linear_map.compatible_smul
 -/
#check @linear_map.ker_restrict_scalars /- _inst_11: is_scalar_tower ↝ linear_map.compatible_smul
 -/

-- algebra/algebra/bilinear.lean
#check @linear_map.mul_left_eq_zero_iff /- _inst_3: algebra ↝ is_scalar_tower module smul_comm_class
 -/
#check @linear_map.mul_right_eq_zero_iff /- _inst_3: algebra ↝ is_scalar_tower module smul_comm_class
 -/
#check @linear_map.mul_left_one /- _inst_3: algebra ↝ is_scalar_tower module smul_comm_class
 -/
#check @linear_map.mul_right_one /- _inst_3: algebra ↝ is_scalar_tower module smul_comm_class
 -/
#check @linear_map.pow_mul_right /- _inst_3: algebra ↝ is_scalar_tower module module smul_comm_class
 -/
#check @linear_map.mul_left_injective /- _inst_2: ring ↝ division_ring is_scalar_tower module smul_comm_class
_inst_3: algebra ↝ is_scalar_tower module smul_comm_class
 -/
#check @linear_map.mul_right_injective /- _inst_2: ring ↝ division_ring is_scalar_tower module smul_comm_class
_inst_3: algebra ↝ is_scalar_tower module smul_comm_class
 -/
#check @linear_map.mul_injective /- _inst_2: ring ↝ division_ring is_scalar_tower module module smul_comm_class
_inst_3: algebra ↝ is_scalar_tower module module smul_comm_class
 -/

-- algebra/algebra/restrict_scalars.lean
#check @restrict_scalars.is_central_scalar /- _inst_5: module ↝ has_smul module no_meet_fake_name
 -/
#check @restrict_scalars_smul_def /- _inst_5: module ↝ has_smul module no_meet_fake_name
 -/
#check @restrict_scalars.add_equiv_map_smul /- _inst_5: module ↝ has_smul module no_meet_fake_name
 -/
#check @restrict_scalars.add_equiv_symm_map_algebra_map_smul /- _inst_5: module ↝ has_smul module no_meet_fake_name
 -/
#check @restrict_scalars.add_equiv_symm_map_smul_smul /- _inst_5: module ↝ has_smul module mul_action no_meet_fake_name
 -/
#check @restrict_scalars.ring_equiv_map_smul /- _inst_3: algebra ↝ has_smul module no_meet_fake_name
 -/

-- algebra/algebra/spectrum.lean
#check @resolvent_set /- _inst_2: ring ↝ has_sub semiring
 -/
#check @resolvent /- _inst_2: ring ↝ has_sub semiring
 -/
#check @spectrum.star_mem_resolvent_set_iff /- _inst_5: star_ring ↝ has_involutive_star star_add_monoid star_semigroup
 -/
#check @spectrum.zero_eq /- _inst_1: field ↝ is_scalar_tower mul_action no_meet_fake_name semifield smul_comm_class smul_with_zero
 -/
#check @spectrum.nonzero_mul_eq_swap_mul /- _inst_1: field ↝ semifield
 -/
#check @spectrum.map_inv /- _inst_1: field ↝ semifield
 -/
#check @alg_hom.mem_resolvent_set_apply /- _inst_1: comm_ring ↝ comm_semiring linear_map_class module no_meet_fake_name non_unital_alg_hom_class
 -/

-- algebra/algebra/subalgebra/basic.lean
#check @subalgebra.is_scalar_tower /- _inst_10: module ↝ has_smul module no_meet_fake_name
 -/
#check @subalgebra.coe_smul /- _inst_10: module ↝ has_smul module no_meet_fake_name
_inst_11: is_scalar_tower ↝ module no_meet_fake_name
 -/
#check @subalgebra.coe_algebra_map /- _inst_11: is_scalar_tower ↝ algebra no_meet_fake_name
 -/
#check @subalgebra.smul_comm_class_right /- _inst_8: smul_comm_class ↝ no_meet_fake_name smul_comm_class
 -/
#check @subalgebra.is_scalar_tower_mid /- _inst_10: module ↝ has_smul
_inst_11: module ↝ has_smul
 -/
#check @subalgebra.mem_of_span_eq_top_of_smul_pow_mem /- _inst_6: comm_ring ↝ comm_semiring
 -/

-- algebra/algebra/tower.lean
#check @submodule.span_algebra_map_image_of_tower /- _inst_11: is_scalar_tower ↝ linear_map.compatible_smul
_inst_12: algebra ↝ has_smul linear_map.compatible_smul module
_inst_14: is_scalar_tower ↝ linear_map.compatible_smul
 -/
#check @submodule.map_mem_span_algebra_map_image /- _inst_10: algebra ↝ has_smul is_scalar_tower linear_map.compatible_smul module
 -/

-- algebra/algebra/unitization.lean
#check @unitization.snd_coe /- _inst_1: has_zero ↝ has_coe_t
 -/
#check @unitization.fst_smul /- _inst_2: has_smul ↝ has_smul
 -/
#check @unitization.snd_smul /- _inst_1: has_smul ↝ has_smul
 -/
#check @unitization.inl_neg /- _inst_2: add_group ↝ subtraction_monoid
 -/
#check @unitization.coe_neg /- _inst_1: add_group ↝ subtraction_monoid
 -/
#check @unitization.coe_mul /- _inst_1: semiring ↝ mul_zero_class
_inst_2: add_comm_monoid ↝ add_zero_class has_smul
 -/
#check @unitization.inl_mul_coe /- _inst_1: semiring ↝ monoid_with_zero
 -/
#check @unitization.coe_mul_inl /- _inst_1: semiring ↝ monoid_with_zero
 -/
#check @unitization.star_module /- _inst_2: star_ring ↝ has_star star_semigroup
_inst_4: star_add_monoid ↝ has_star
_inst_5: module ↝ has_smul
 -/
#check @unitization.algebra_map_eq_inl_comp /- _inst_8: distrib_mul_action ↝ algebra has_smul no_meet_fake_name
_inst_9: is_scalar_tower ↝ algebra no_meet_fake_name
 -/
#check @unitization.algebra_map_eq_inl_ring_hom_comp /- _inst_8: distrib_mul_action ↝ algebra has_smul no_meet_fake_name
_inst_9: is_scalar_tower ↝ algebra no_meet_fake_name
 -/
#check @unitization.alg_hom_ext /- _inst_9: algebra ↝ algebra has_smul no_meet_fake_name
_inst_10: distrib_mul_action ↝ algebra has_smul no_meet_fake_name
_inst_11: is_scalar_tower ↝ algebra no_meet_fake_name
 -/
#check @unitization.alg_hom_ext' /- _inst_12: ring ↝ distrib_mul_action semiring
 -/

-- algebra/algebraic_card.lean
#check @algebraic.aleph_0_le_cardinal_mk_of_char_zero /- _inst_1: comm_ring ↝ euclidean_domain
_inst_2: is_domain ↝ nontrivial
 -/

-- algebra/associated.lean
#check @prime /- _inst_1: comm_monoid_with_zero ↝ monoid_with_zero
 -/
#check @comap_prime /- _inst_3: monoid_with_zero_hom_class ↝ fun_like monoid_hom_class mul_hom_class no_meet_fake_name zero_hom_class
 -/
#check @associates.no_zero_divisors /- _inst_1: cancel_comm_monoid_with_zero ↝ comm_monoid_with_zero no_zero_divisors
 -/

-- algebra/big_operators/associated.lean
#check @associates.rel_associated_iff_map_eq_map /- _inst_1: comm_monoid ↝ monoid
 -/
#check @associates.exists_mem_multiset_le_of_prime /- _inst_1: cancel_comm_monoid_with_zero ↝ comm_monoid_with_zero
 -/
#check @multiset.prod_ne_zero_of_prime /- _inst_1: cancel_comm_monoid_with_zero ↝ comm_monoid_with_zero no_zero_divisors
 -/
#check @prime.dvd_finsupp_prod_iff /- _inst_1: comm_monoid_with_zero ↝ has_zero
 -/

-- algebra/big_operators/basic.lean
#check @finset.sum_erase_lt_of_pos /- _inst_3: ordered_add_comm_monoid ↝ add_comm_monoid covariant_class has_lt
_inst_4: covariant_class ↝ covariant_class
 -/
#check @finset.prod_add_prod_eq /- _inst_1: comm_semiring ↝ comm_monoid has_add right_distrib_class
 -/
#check @finset.sum_unique_nonempty /- _inst_2: unique ↝ inhabited subsingleton
 -/
#check @finset.prod_unique_nonempty /- _inst_2: unique ↝ inhabited subsingleton
 -/

-- algebra/big_operators/fin.lean
#check @fin.partial_sum /- _inst_1: add_monoid ↝ has_add has_zero
 -/
#check @fin.partial_prod /- _inst_1: monoid ↝ has_mul has_one
 -/

-- algebra/big_operators/finprod.lean
#check @finprod_nonneg /- _inst_3: ordered_comm_semiring ↝ linear_ordered_semifield
 -/
#check @one_le_finprod' /- _inst_3: ordered_comm_monoid ↝ comm_monoid covariant_class preorder
 -/
#check @finsum_nonneg /- _inst_3: ordered_add_comm_monoid ↝ add_comm_monoid covariant_class preorder
 -/
#check @smul_finsum /- _inst_3: ring ↝ no_meet_fake_name semiring smul_with_zero
 -/
#check @mul_finsum /- _inst_3: semiring ↝ non_unital_non_assoc_semiring
 -/
#check @finsum_mul /- _inst_3: semiring ↝ non_unital_non_assoc_semiring
 -/

-- algebra/big_operators/finsupp.lean
#check @finsupp.sum_apply' /- _inst_1: add_comm_monoid ↝ has_zero
 -/
#check @finsupp.sum_mul /- _inst_4: non_unital_non_assoc_semiring ↝ has_zero
 -/
#check @finsupp.mul_sum /- _inst_4: non_unital_non_assoc_semiring ↝ has_zero
 -/

-- algebra/big_operators/multiset.lean
#check @multiset.dvd_sum /- _inst_1: semiring ↝ left_distrib_class non_unital_semiring
 -/
#check @multiset.one_le_prod_of_one_le /- _inst_1: ordered_comm_monoid ↝ comm_monoid covariant_class preorder
 -/
#check @multiset.sum_nonneg /- _inst_1: ordered_add_comm_monoid ↝ add_comm_monoid covariant_class preorder
 -/
#check @multiset.sum_le_card_nsmul /- _inst_1: ordered_add_comm_monoid ↝ add_comm_monoid covariant_class covariant_class preorder
 -/
#check @multiset.prod_le_pow_card /- _inst_1: ordered_comm_monoid ↝ comm_monoid covariant_class covariant_class preorder
 -/
#check @multiset.prod_le_prod_of_rel_le /- _inst_1: ordered_comm_monoid ↝ comm_monoid covariant_class covariant_class preorder
 -/
#check @multiset.sum_le_sum_of_rel_le /- _inst_1: ordered_add_comm_monoid ↝ add_comm_monoid covariant_class covariant_class preorder
 -/
#check @multiset.prod_nonneg /- _inst_1: ordered_comm_semiring ↝ linear_ordered_semifield
 -/
#check @multiset.le_prod_of_submultiplicative_on_pred /- _inst_2: ordered_comm_monoid ↝ comm_monoid covariant_class preorder
 -/
#check @multiset.le_sum_of_subadditive_on_pred /- _inst_2: ordered_add_comm_monoid ↝ add_comm_monoid covariant_class preorder
 -/
#check @multiset.le_sum_nonempty_of_subadditive_on_pred /- _inst_2: ordered_add_comm_monoid ↝ add_comm_monoid covariant_class preorder
 -/
#check @multiset.le_prod_nonempty_of_submultiplicative_on_pred /- _inst_2: ordered_comm_monoid ↝ comm_monoid covariant_class preorder
 -/

-- algebra/big_operators/norm_num.lean
#check @tactic.norm_num.list.sum_congr /- _inst_1: add_monoid ↝ has_add has_zero
 -/
#check @tactic.norm_num.list.prod_congr /- _inst_1: monoid ↝ has_mul has_one
 -/

-- algebra/big_operators/order.lean
#check @finset.prod_le_prod'' /- _inst_2: ordered_comm_monoid ↝ comm_monoid covariant_class covariant_class preorder
 -/
#check @finset.sum_le_sum /- _inst_2: ordered_add_comm_monoid ↝ add_comm_monoid covariant_class covariant_class preorder
 -/
#check @finset.sum_lt_sum /- _inst_1: ordered_cancel_add_comm_monoid ↝ covariant_class ordered_add_comm_monoid
 -/
#check @finset.prod_lt_prod' /- _inst_1: ordered_cancel_comm_monoid ↝ covariant_class ordered_comm_monoid
 -/
#check @finset.sum_lt_sum_of_subset /- _inst_1: ordered_cancel_add_comm_monoid ↝ covariant_class ordered_add_comm_monoid
 -/
#check @finset.prod_lt_prod_of_subset' /- _inst_1: ordered_cancel_comm_monoid ↝ covariant_class ordered_comm_monoid
 -/
#check @finset.prod_eq_prod_iff_of_le /- _inst_1: ordered_cancel_comm_monoid ↝ contravariant_class contravariant_class covariant_class ordered_comm_monoid
 -/
#check @finset.sum_eq_sum_iff_of_le /- _inst_1: ordered_cancel_add_comm_monoid ↝ contravariant_class contravariant_class covariant_class ordered_add_comm_monoid
 -/
#check @finset.exists_lt_of_prod_lt' /- _inst_1: linear_ordered_cancel_comm_monoid ↝ canonically_linear_ordered_monoid
 -/
#check @finset.exists_lt_of_sum_lt /- _inst_1: linear_ordered_cancel_add_comm_monoid ↝ linear_ordered_add_comm_monoid
 -/
#check @finset.exists_le_of_sum_le /- _inst_1: linear_ordered_cancel_add_comm_monoid ↝ linear_ordered_semiring
 -/
#check @finset.exists_pos_of_sum_zero_of_exists_nonzero /- _inst_1: linear_ordered_cancel_add_comm_monoid ↝ linear_ordered_semiring
 -/
#check @finset.prod_nonneg /- _inst_1: ordered_comm_semiring ↝ linear_ordered_semifield
 -/
#check @finset.prod_pos /- _inst_1: ordered_comm_semiring ↝ linear_ordered_semifield
 -/
#check @finset.prod_le_prod' /- _inst_1: canonically_ordered_comm_semiring ↝ comm_monoid covariant_class covariant_class preorder
 -/

-- algebra/big_operators/ring.lean
#check @finset.sum_div /- _inst_1: division_ring ↝ division_semiring
 -/
#check @finset.dvd_sum /- _inst_1: comm_semiring ↝ semiring
 -/
#check @finset.sum_range_succ_mul_sum_range_succ /- _inst_1: non_unital_non_assoc_semiring ↝ add_comm_monoid has_mul left_distrib_class right_distrib_class
 -/

-- algebra/category/Algebra/basic.lean
#check @Algebra.id_apply /- _inst_1: comm_ring ↝ module no_meet_fake_name ring
 -/
#check @Algebra.coe_comp /- _inst_1: comm_ring ↝ module no_meet_fake_name ring
 -/

-- algebra/category/FinVect.lean
#check @FinVect /- _inst_1: field ↝ division_ring module no_meet_fake_name
 -/

-- algebra/category/FinVect/limits.lean
#check @FinVect.category_theory.limits.pi_obj.finite_dimensional /- _inst_3: field ↝ division_ring finite_dimensional module no_meet_fake_name
 -/

-- algebra/category/Group/epi_mono.lean
#check @add_monoid_hom.ker_eq_bot_of_cancel /- _inst_2: add_group ↝ add_zero_class
 -/
#check @monoid_hom.ker_eq_bot_of_cancel /- _inst_2: group ↝ mul_one_class
 -/

-- algebra/category/Mon/basic.lean
#check @Mon.assoc_monoid_hom /- _inst_1: monoid ↝ mul_one_class
_inst_2: monoid ↝ mul_one_class
 -/
#check @AddMon.assoc_add_monoid_hom /- _inst_1: add_monoid ↝ add_zero_class
_inst_2: add_monoid ↝ add_zero_class
 -/

-- algebra/category/Ring/basic.lean
#check @SemiRing.assoc_ring_hom /- _inst_1: semiring ↝ non_assoc_semiring
_inst_2: semiring ↝ non_assoc_semiring
 -/

-- algebra/char_p/algebra.lean
#check @algebra.char_p_iff /- _inst_2: comm_semiring ↝ semiring
 -/
#check @is_fraction_ring.char_p_of_is_fraction_ring /- _inst_2: field ↝ comm_ring
 -/
#check @is_fraction_ring.char_zero_of_is_fraction_ring /- _inst_5: char_zero ↝ char_p
 -/

-- algebra/char_p/basic.lean
#check @ring_char.eq_zero /- _inst_2: char_zero ↝ char_p
 -/
#check @eq_iff_modeq_int /- _inst_1: ring ↝ add_group_with_one
 -/
#check @char_p.neg_one_ne_one /- _inst_1: ring ↝ add_group_with_one
 -/
#check @char_p.cast_eq_mod /- _inst_1: non_assoc_ring ↝ non_assoc_semiring
 -/
#check @char_p.char_ne_zero_of_fintype /- _inst_1: non_assoc_ring ↝ add_group_with_one
 -/
#check @char_p.char_is_prime /- _inst_1: ring ↝ non_assoc_ring
 -/
#check @char_p.false_of_nontrivial_of_char_one /- _inst_1: non_assoc_semiring ↝ add_monoid_with_one subsingleton
_inst_3: char_p ↝ subsingleton
 -/
#check @char_p.nontrivial_of_char_ne_one /- _inst_1: non_assoc_semiring ↝ add_monoid_with_one
 -/
#check @nat.lcm.char_p /- _inst_1: semiring ↝ add_monoid_with_one
_inst_2: semiring ↝ add_monoid_with_one
 -/

-- algebra/char_p/exp_char.lean
#check @char_prime_of_ne_zero /- _inst_1: semiring ↝ non_assoc_semiring
 -/

-- algebra/char_p/invertible.lean
#check @not_ring_char_dvd_of_invertible /- _inst_1: field ↝ division_semiring
 -/

-- algebra/char_p/local_ring.lean
#check @char_p_zero_or_prime_power /- _inst_1: comm_ring ↝ char_p euclidean_domain
 -/

-- algebra/char_p/pi.lean
#check @char_p.pi' /- _inst_1: comm_ring ↝ semiring
 -/

-- algebra/char_p/subring.lean
#check @char_p.subsemiring /- _inst_1: semiring ↝ non_assoc_semiring
 -/
#check @char_p.subring' /- _inst_1: comm_ring ↝ ring
 -/

-- algebra/char_p/two.lean
#check @char_two.two_eq_zero /- _inst_1: semiring ↝ add_monoid_with_one
 -/

-- algebra/char_zero.lean
#check @half_add_self /- _inst_1: division_ring ↝ division_semiring left_distrib_class
 -/

-- algebra/continued_fractions/basic.lean
#check @generalized_continued_fraction.pair.has_coe_to_generalized_continued_fraction_pair /- _inst_1: has_coe ↝ has_lift_t
 -/
#check @generalized_continued_fraction.next_numerator /- _inst_1: division_ring ↝ has_add has_mul
 -/
#check @generalized_continued_fraction.next_denominator /- _inst_1: division_ring ↝ has_add has_mul
 -/

-- algebra/continued_fractions/computation/basic.lean
#check @generalized_continued_fraction.int_fract_pair.has_coe_to_int_fract_pair /- _inst_1: has_coe ↝ has_lift_t
 -/
#check @generalized_continued_fraction.int_fract_pair.of /- _inst_1: linear_ordered_field ↝ linear_ordered_ring
 -/

-- algebra/continued_fractions/computation/correctness_terminating.lean
#check @generalized_continued_fraction.comp_exact_value /- _inst_1: linear_ordered_field ↝ division_ring linear_order
 -/

-- algebra/covariant_and_contravariant.lean
#check @covariant_flip_add_iff /- _inst_1: add_comm_semigroup ↝ has_add is_commutative
 -/
#check @covariant_flip_mul_iff /- _inst_1: comm_semigroup ↝ has_mul is_commutative
 -/
#check @contravariant_flip_add_iff /- _inst_1: add_comm_semigroup ↝ has_add is_commutative
 -/
#check @contravariant_flip_mul_iff /- _inst_1: comm_semigroup ↝ has_mul is_commutative
 -/

-- algebra/cubic_discriminant.lean
#check @cubic.map /- _inst_1: semiring ↝ non_assoc_semiring
_inst_2: semiring ↝ non_assoc_semiring
 -/
#check @cubic.map_roots /- _inst_1: comm_ring ↝ semiring
 -/
#check @cubic.disc /- _inst_3: ring ↝ has_add has_mul has_one has_pow has_sub
 -/

-- algebra/direct_limit.lean
#check @module.directed_system.map_self /- _inst_1: ring ↝ semiring
 -/
#check @module.directed_system.map_map /- _inst_1: ring ↝ semiring
 -/
#check @module.direct_limit /- _inst_2: preorder ↝ has_le
 -/
#check @module.direct_limit.totalize /- _inst_1: ring ↝ semiring
_inst_2: preorder ↝ has_le
 -/
#check @ring.direct_limit /- _inst_2: preorder ↝ has_le
 -/

-- algebra/direct_sum/algebra.lean
#check @direct_sum.alg_hom_ext' /- _inst_8: direct_sum.galgebra ↝ algebra no_meet_fake_name
 -/

-- algebra/direct_sum/basic.lean
#check @direct_sum.add_hom_ext /- _inst_2: add_monoid ↝ add_zero_class
 -/
#check @direct_sum.from_add_monoid /- _inst_2: add_comm_monoid ↝ add_zero_class
 -/

-- algebra/direct_sum/finsupp.lean
#check @finsupp_lequiv_direct_sum /- _inst_2: add_comm_group ↝ add_comm_monoid module no_meet_fake_name
 -/

-- algebra/direct_sum/internal.lean
#check @add_comm_monoid.of_submonoid_on_semiring /- _inst_1: semiring ↝ add_comm_monoid
 -/
#check @add_comm_group.of_subgroup_on_ring /- _inst_1: ring ↝ add_comm_group
 -/
#check @set_like.nat_cast_mem_graded /- _inst_4: add_submonoid_class ↝ add_mem_class no_meet_fake_name zero_mem_class
 -/
#check @set_like.int_cast_mem_graded /- _inst_4: add_subgroup_class ↝ add_submonoid_class neg_mem_class no_meet_fake_name
 -/
#check @direct_sum.coe_mul_apply /- _inst_6: set_like.graded_monoid ↝ direct_sum.gnon_unital_non_assoc_semiring direct_sum.gsemiring no_meet_fake_name set_like.has_graded_mul
 -/
#check @set_like.is_homogeneous.smul /- _inst_3: algebra ↝ has_smul module
 -/

-- algebra/direct_sum/ring.lean
#check @direct_sum.mul_eq_sum_support_ghas_mul /- _inst_4: direct_sum.gsemiring ↝ direct_sum.gnon_unital_non_assoc_semiring graded_monoid.ghas_mul no_meet_fake_name
 -/
#check @direct_sum.ring_hom_ext' /- _inst_5: semiring ↝ non_assoc_semiring
 -/
#check @non_unital_non_assoc_semiring.direct_sum_gnon_unital_non_assoc_semiring /- _inst_2: add_monoid ↝ graded_monoid.ghas_mul has_add
 -/

-- algebra/divisibility.lean
#check @semigroup_has_dvd /- _inst_1: semigroup ↝ has_mul
 -/
#check @dvd.intro /- _inst_1: semigroup ↝ has_dvd has_mul
 -/
#check @exists_eq_mul_right_of_dvd /- _inst_1: semigroup ↝ has_dvd has_mul
 -/
#check @dvd.elim /- _inst_1: semigroup ↝ has_dvd has_mul
 -/
#check @map_dvd /- _inst_2: monoid ↝ fun_like has_dvd has_mul
_inst_3: monoid ↝ fun_like has_dvd has_mul
 -/
#check @dvd_not_unit /- _inst_1: comm_monoid_with_zero ↝ monoid_with_zero
 -/
#check @ne_zero_of_dvd_ne_zero /- _inst_1: monoid_with_zero ↝ has_dvd mul_zero_class
 -/

-- algebra/dual_number.lean
#check @dual_number.snd_mul /- _inst_1: semiring ↝ has_add has_mul
 -/

-- algebra/euclidean_domain.lean
#check @euclidean_domain.lcm_dvd /- _inst_1: euclidean_domain ↝ field
 -/
#check @euclidean_domain.mul_div_mul_cancel /- _inst_1: euclidean_domain ↝ field no_zero_divisors
 -/

-- algebra/field/basic.lean
#check @add_div /- _inst_1: division_semiring ↝ div_inv_monoid has_add right_distrib_class
 -/
#check @one_div_mul_add_mul_one_div_eq_one_div_add_one_div /- _inst_1: division_semiring ↝ add_comm_semigroup group_with_zero left_distrib_class right_distrib_class
 -/
#check @add_div_eq_mul_add_div /- _inst_1: division_semiring ↝ group_with_zero has_add right_distrib_class
 -/
#check @one_div_neg_one_eq_neg_one /- _inst_1: division_ring ↝ division_monoid has_distrib_neg has_neg
 -/
#check @neg_div /- _inst_1: division_ring ↝ div_inv_monoid has_distrib_neg has_neg
 -/
#check @field.is_domain /- _inst_1: field ↝ is_domain ring
 -/
#check @field.to_is_field /- _inst_1: field ↝ semifield
 -/
#check @uniq_inv_of_is_field /- _inst_1: ring ↝ semiring
 -/

-- algebra/field_power.lean
#check @ring_hom.map_zpow /- _inst_1: division_ring ↝ division_semiring
_inst_2: division_ring ↝ division_semiring
 -/
#check @zpow_bit1_neg /- _inst_1: division_ring ↝ group_with_zero has_distrib_neg has_neg
 -/

-- algebra/free.lean
#check @free_semigroup.traverse /- _inst_1: applicative ↝ functor has_seq no_meet_fake_name
 -/
#check @free_add_semigroup.traverse /- _inst_1: applicative ↝ functor has_seq no_meet_fake_name
 -/

-- algebra/free_monoid.lean
#check @free_add_monoid.hom_eq /- _inst_1: add_monoid ↝ add_zero_class
 -/
#check @free_monoid.hom_eq /- _inst_1: monoid ↝ mul_one_class
 -/

-- algebra/gcd_monoid/basic.lean
#check @norm_unit_eq_one /- _inst_2: unique ↝ normalization_monoid
 -/
#check @normalize_eq /- _inst_2: unique ↝ normalization_monoid
 -/
#check @gcd_eq_of_dvd_sub_right /- _inst_1: comm_ring ↝ field gcd_monoid normalization_monoid
_inst_2: is_domain ↝ cancel_comm_monoid_with_zero gcd_monoid normalization_monoid
 -/
#check @gcd_eq_of_dvd_sub_left /- _inst_1: comm_ring ↝ field gcd_monoid
 -/

-- algebra/gcd_monoid/finset.lean
#check @finset.lcm /- _inst_2: normalized_gcd_monoid ↝ gcd_monoid is_associative is_commutative
 -/
#check @finset.gcd /- _inst_2: normalized_gcd_monoid ↝ gcd_monoid is_associative is_commutative
 -/
#check @finset.gcd_eq_of_dvd_sub /- _inst_1: comm_ring ↝ field gcd_monoid normalization_monoid
 -/

-- algebra/gcd_monoid/integrally_closed.lean
#check @is_localization.surj_of_gcd_domain /- _inst_1: comm_ring ↝ field
_inst_2: is_domain ↝ cancel_comm_monoid_with_zero
_inst_4: comm_ring ↝ comm_semiring
 -/
#check @gcd_monoid.to_is_integrally_closed /- _inst_1: comm_ring ↝ algebra field
 -/

-- algebra/gcd_monoid/multiset.lean
#check @multiset.lcm /- _inst_2: normalized_gcd_monoid ↝ gcd_monoid is_associative is_commutative
 -/
#check @multiset.gcd /- _inst_2: normalized_gcd_monoid ↝ gcd_monoid is_associative is_commutative
 -/

-- algebra/geom_sum.lean
#check @geom_sum_succ' /- _inst_1: semiring ↝ add_comm_monoid has_pow
 -/
#check @geom_sum_zero /- _inst_1: semiring ↝ add_comm_monoid has_pow
 -/
#check @geom_sum₂_self /- _inst_1: comm_ring ↝ semiring
 -/

-- algebra/graded_monoid.lean
#check @list.dprod_index /- _inst_1: add_monoid ↝ has_add has_zero
 -/
#check @list.dprod /- _inst_2: graded_monoid.gmonoid ↝ graded_monoid.ghas_mul graded_monoid.ghas_one no_meet_fake_name
 -/
#check @monoid.gmonoid_gnpow /- _inst_2: monoid ↝ graded_monoid.gmonoid has_pow
 -/
#check @set_like.coe_ghas_one /- _inst_4: set_like.has_graded_one ↝ graded_monoid.ghas_one no_meet_fake_name
 -/
#check @set_like.coe_ghas_mul /- _inst_4: set_like.has_graded_mul ↝ graded_monoid.ghas_mul no_meet_fake_name
 -/
#check @set_like.pow_mem_graded /- _inst_4: set_like.graded_monoid ↝ no_meet_fake_name set_like.has_graded_mul set_like.has_graded_one
 -/
#check @set_like.list_prod_map_mem_graded /- _inst_4: set_like.graded_monoid ↝ no_meet_fake_name set_like.has_graded_mul set_like.has_graded_one
 -/
#check @set_like.coe_gnpow /- _inst_4: set_like.graded_monoid ↝ graded_monoid.gmonoid no_meet_fake_name
 -/
#check @set_like.coe_list_dprod /- _inst_4: set_like.graded_monoid ↝ graded_monoid.ghas_mul graded_monoid.ghas_one graded_monoid.gmonoid no_meet_fake_name set_like.has_graded_mul set_like.has_graded_one
 -/
#check @set_like.is_homogeneous /- _inst_1: set_like ↝ has_mem
 -/

-- algebra/group/basic.lean
#check @comp_mul_left /- _inst_1: semigroup ↝ has_mul is_associative
 -/
#check @comp_add_left /- _inst_1: add_semigroup ↝ has_add is_associative
 -/
#check @comp_mul_right /- _inst_1: semigroup ↝ has_mul is_associative
 -/
#check @comp_add_right /- _inst_1: add_semigroup ↝ has_add is_associative
 -/
#check @bit0_zero /- _inst_1: add_monoid ↝ add_zero_class
 -/
#check @exists_nsmul_eq_zero_of_zsmul_eq_zero /- _inst_1: add_group ↝ subtraction_monoid
 -/
#check @exists_npow_eq_one_of_zpow_eq_one /- _inst_1: group ↝ division_monoid
 -/
#check @commutator_element /- _inst_1: group ↝ has_inv has_mul
 -/
#check @commutator_element_def /- _inst_1: group ↝ has_bracket has_inv has_mul
 -/

-- algebra/group/conj.lean
#check @is_conj_one_right /- _inst_1: cancel_monoid ↝ right_cancel_monoid
 -/

-- algebra/group/defs.lean
#check @group.to_monoid /- _inst_1: group ↝ monoid
 -/
#check @add_group.to_add_monoid /- _inst_1: add_group ↝ add_monoid
 -/

-- algebra/group/semiconj.lean
#check @add_semiconj_by.add_right /- _inst_1: add_semigroup ↝ has_add is_associative
 -/
#check @semiconj_by.mul_right /- _inst_1: semigroup ↝ has_mul is_associative
 -/

-- algebra/group/with_one.lean
#check @with_zero.coe_zpow /- _inst_1: div_inv_monoid ↝ has_one has_pow
 -/
#check @with_zero.inv_one /- _inst_1: group ↝ division_monoid
 -/

-- algebra/group_power/lemmas.lean
#check @zsmul_pos /- _inst_1: ordered_add_comm_group ↝ covariant_class preorder sub_neg_monoid
 -/
#check @one_lt_zpow' /- _inst_1: ordered_comm_group ↝ covariant_class div_inv_monoid preorder
 -/
#check @zpow_mono_right /- _inst_1: ordered_comm_group ↝ covariant_class group preorder
 -/
#check @zsmul_mono_left /- _inst_1: ordered_add_comm_group ↝ add_group covariant_class preorder
 -/
#check @zsmul_mono_right /- _inst_1: ordered_add_comm_group ↝ add_comm_group covariant_class covariant_class preorder
 -/
#check @zpow_mono_left /- _inst_1: ordered_comm_group ↝ comm_group covariant_class covariant_class preorder
 -/
#check @abs_nsmul /- _inst_1: linear_ordered_add_comm_group ↝ add_group covariant_class linear_order
 -/
#check @bit0_mul /- _inst_1: non_unital_non_assoc_ring ↝ add_group has_mul right_distrib_class
 -/
#check @mul_bit0 /- _inst_1: non_unital_non_assoc_ring ↝ add_group has_mul left_distrib_class
 -/
#check @zsmul_eq_mul /- _inst_1: ring ↝ has_distrib_neg non_assoc_ring
 -/
#check @neg_one_pow_eq_pow_mod_two /- _inst_1: ring ↝ has_distrib_neg has_involutive_neg monoid
 -/

-- algebra/group_power/order.lean
#check @pow_le_pow_iff' /- _inst_2: linear_order ↝ preorder
 -/
#check @nsmul_le_nsmul_iff /- _inst_2: linear_order ↝ preorder
 -/
#check @pow_lt_pow_iff' /- _inst_2: linear_order ↝ preorder
 -/
#check @nsmul_lt_nsmul_iff /- _inst_2: linear_order ↝ preorder
 -/
#check @zero_pow_le_one /- _inst_1: ordered_semiring ↝ monoid_with_zero preorder zero_le_one_class
 -/

-- algebra/group_power/ring.lean
#check @min_pow_dvd_add /- _inst_1: semiring ↝ has_add left_distrib_class monoid
 -/

-- algebra/group_ring_action.lean
#check @smul_inv'' /- _inst_6: division_ring ↝ division_semiring
 -/

-- algebra/group_with_zero/basic.lean
#check @monoid_hom.map_units_inv /- _inst_2: group_with_zero ↝ division_monoid
 -/

-- algebra/hom/equiv.lean
#check @mul_equiv_class.map_eq_one_iff /- _inst_1: mul_one_class ↝ equiv_like has_mul has_one no_meet_fake_name one_hom_class
_inst_2: mul_one_class ↝ equiv_like has_mul has_one no_meet_fake_name one_hom_class
_inst_3: mul_equiv_class ↝ equiv_like no_meet_fake_name one_hom_class
 -/
#check @add_equiv_class.map_eq_zero_iff /- _inst_1: add_zero_class ↝ equiv_like has_add has_zero no_meet_fake_name zero_hom_class
_inst_2: add_zero_class ↝ equiv_like has_add has_zero no_meet_fake_name zero_hom_class
_inst_3: add_equiv_class ↝ equiv_like no_meet_fake_name zero_hom_class
 -/
#check @add_equiv_class.map_ne_zero_iff /- _inst_1: add_zero_class ↝ equiv_like has_add has_zero no_meet_fake_name zero_hom_class
_inst_2: add_zero_class ↝ equiv_like has_add has_zero no_meet_fake_name zero_hom_class
_inst_3: add_equiv_class ↝ equiv_like no_meet_fake_name zero_hom_class
 -/
#check @mul_equiv_class.map_ne_one_iff /- _inst_1: mul_one_class ↝ equiv_like has_mul has_one no_meet_fake_name one_hom_class
_inst_2: mul_one_class ↝ equiv_like has_mul has_one no_meet_fake_name one_hom_class
_inst_3: mul_equiv_class ↝ equiv_like no_meet_fake_name one_hom_class
 -/

-- algebra/hom/group.lean
#check @map_add_eq_zero /- _inst_3: add_monoid_hom_class ↝ add_hom_class fun_like no_meet_fake_name zero_hom_class
 -/
#check @map_mul_eq_one /- _inst_3: monoid_hom_class ↝ fun_like mul_hom_class no_meet_fake_name one_hom_class
 -/
#check @map_sub' /- _inst_5: add_monoid_hom_class ↝ add_hom_class fun_like no_meet_fake_name
 -/
#check @map_div' /- _inst_5: monoid_hom_class ↝ fun_like mul_hom_class no_meet_fake_name
 -/
#check @injective_iff_map_eq_zero /- _inst_5: add_monoid_hom_class ↝ add_hom_class fun_like no_meet_fake_name zero_hom_class
 -/
#check @injective_iff_map_eq_one /- _inst_5: monoid_hom_class ↝ fun_like mul_hom_class no_meet_fake_name one_hom_class
 -/

-- algebra/hom/group_action.lean
#check @distrib_mul_action_hom.map_neg /- _inst_11: add_group ↝ subtraction_monoid
 -/
#check @distrib_mul_action_hom.map_sub /- _inst_11: add_group ↝ subtraction_monoid
 -/

-- algebra/hom/iterate.lean
#check @monoid_hom.coe_pow /- _inst_5: comm_monoid ↝ mul_one_class
 -/
#check @monoid.End.coe_pow /- _inst_1: monoid ↝ mul_one_class
 -/
#check @add_monoid.End.coe_pow /- _inst_1: add_monoid ↝ add_zero_class
 -/
#check @ring_hom.coe_pow /- _inst_1: semiring ↝ non_assoc_semiring
 -/
#check @ring_hom.iterate_map_one /- _inst_1: semiring ↝ non_assoc_semiring
 -/
#check @ring_hom.iterate_map_zero /- _inst_1: semiring ↝ non_assoc_semiring
 -/
#check @ring_hom.iterate_map_add /- _inst_1: semiring ↝ non_assoc_semiring
 -/
#check @ring_hom.iterate_map_mul /- _inst_1: semiring ↝ non_assoc_semiring
 -/
#check @ring_hom.iterate_map_smul /- _inst_1: semiring ↝ non_assoc_semiring
 -/
#check @ring_hom.iterate_map_sub /- _inst_1: ring ↝ non_assoc_ring
 -/
#check @ring_hom.iterate_map_neg /- _inst_1: ring ↝ non_assoc_ring
 -/
#check @ring_hom.iterate_map_zsmul /- _inst_1: ring ↝ non_assoc_ring
 -/

-- algebra/hom/ring.lean
#check @non_unital_ring_hom.coe_coe /- _inst_1: non_unital_ring_hom_class ↝ fun_like has_coe_t
 -/
#check @map_bit1 /- _inst_3: ring_hom_class ↝ add_hom_class fun_like no_meet_fake_name one_hom_class
 -/
#check @ring_hom.coe_coe /- _inst_1: ring_hom_class ↝ fun_like has_coe_t
 -/
#check @function.injective.is_domain /- _inst_1: ring ↝ euclidean_domain no_zero_divisors
_inst_2: is_domain ↝ no_zero_divisors nontrivial
 -/

-- algebra/hom/units.lean
#check @is_add_unit.map /- _inst_3: add_monoid_hom_class ↝ fun_like has_coe_t
 -/
#check @is_unit.map /- _inst_3: monoid_hom_class ↝ fun_like has_coe_t
 -/

-- algebra/homology/additive.lean
#check @homological_complex.cycles_additive /- _inst_3: category_theory.limits.has_equalizers ↝ category_theory.limits.has_kernels
 -/

-- algebra/homology/differential_object.lean
#check @homological_complex.d_eq_to_hom /- _inst_1: add_comm_group ↝ add_right_cancel_semigroup
 -/

-- algebra/homology/exact.lean
#check @category_theory.comp_eq_zero_of_image_eq_kernel /- _inst_2: category_theory.limits.has_images ↝ category_theory.limits.has_image no_meet_fake_name
 -/
#check @category_theory.exact_epi_comp /- _inst_4: category_theory.limits.has_equalizers ↝ category_theory.epi category_theory.epi category_theory.limits.has_kernels no_meet_fake_name
_inst_5: category_theory.epi ↝ category_theory.epi no_meet_fake_name
 -/
#check @category_theory.exact_comp_mono /- _inst_4: category_theory.limits.has_equalizers ↝ category_theory.epi category_theory.limits.has_kernels no_meet_fake_name
 -/
#check @category_theory.exact_comp_iso /- _inst_5: category_theory.is_iso ↝ category_theory.mono
 -/
#check @category_theory.exact_kernel_subobject_arrow /- _inst_4: category_theory.limits.has_equalizers ↝ category_theory.limits.has_kernels
 -/
#check @category_theory.limits.factor_thru_kernel_subobject.epi /- _inst_4: category_theory.limits.has_equalizers ↝ category_theory.epi category_theory.epi category_theory.limits.has_kernels no_meet_fake_name
 -/
#check @category_theory.limits.kernel.lift.epi /- _inst_4: category_theory.limits.has_equalizers ↝ category_theory.epi category_theory.limits.has_kernels no_meet_fake_name
 -/
#check @category_theory.exact_zero_left_of_mono /- _inst_4: category_theory.limits.has_equalizers ↝ category_theory.epi category_theory.limits.has_kernels no_meet_fake_name
_inst_5: category_theory.limits.has_zero_object ↝ category_theory.epi no_meet_fake_name
_inst_6: category_theory.mono ↝ category_theory.epi no_meet_fake_name
 -/
#check @category_theory.epi_iff_exact_zero_right /- _inst_4: category_theory.preadditive ↝ category_theory.epi category_theory.limits.has_kernels category_theory.limits.has_zero_morphisms no_meet_fake_name
 -/

-- algebra/homology/homological_complex.lean
#check @homological_complex.image_eq_image /- _inst_3: category_theory.limits.has_images ↝ category_theory.limits.has_image no_meet_fake_name
 -/
#check @homological_complex.image_to_eq_image /- _inst_3: category_theory.limits.has_images ↝ category_theory.limits.has_image no_meet_fake_name
 -/

-- algebra/homology/homology.lean
#check @homological_complex.boundaries_eq_bot /- _inst_4: category_theory.limits.has_zero_object ↝ category_theory.limits.has_initial category_theory.limits.initial_mono_class
 -/
#check @boundaries_to_cycles_naturality /- _inst_3: category_theory.limits.has_equalizers ↝ category_theory.limits.has_kernels
 -/

-- algebra/homology/image_to_kernel.lean
#check @image_to_kernel_zero_right /- _inst_3: category_theory.limits.has_images ↝ category_theory.limits.has_image no_meet_fake_name
 -/
#check @image_to_kernel_comp_right /- _inst_4: category_theory.limits.has_images ↝ category_theory.limits.has_image no_meet_fake_name
 -/
#check @image_to_kernel_comp_left /- _inst_4: category_theory.limits.has_images ↝ category_theory.limits.has_image no_meet_fake_name
 -/
#check @image_to_kernel_comp_mono /- _inst_4: category_theory.limits.has_images ↝ category_theory.limits.has_image no_meet_fake_name
 -/
#check @image_to_kernel_epi_comp /- _inst_4: category_theory.limits.has_images ↝ category_theory.limits.has_image no_meet_fake_name
 -/
#check @image_to_kernel_comp_hom_inv_comp /- _inst_4: category_theory.limits.has_images ↝ category_theory.limits.has_image no_meet_fake_name
 -/

-- algebra/homology/quasi_iso.lean
#check @quasi_iso_comp /- _inst_8: quasi_iso ↝ category_theory.is_iso no_meet_fake_name
_inst_9: quasi_iso ↝ category_theory.is_iso no_meet_fake_name
 -/
#check @quasi_iso_of_comp_left /- _inst_8: quasi_iso ↝ category_theory.is_iso no_meet_fake_name
 -/
#check @quasi_iso_of_comp_right /- _inst_8: quasi_iso ↝ category_theory.is_iso no_meet_fake_name
 -/

-- algebra/homology/short_exact/preadditive.lean
#check @category_theory.exact_inl_snd /- _inst_5: category_theory.limits.has_binary_biproducts ↝ category_theory.limits.has_binary_biproduct
 -/
#check @category_theory.exact_inr_fst /- _inst_5: category_theory.limits.has_binary_biproducts ↝ category_theory.limits.has_binary_biproduct
 -/

-- algebra/indicator_function.lean
#check @set.indicator_Union_apply /- _inst_3: complete_lattice ↝ no_meet_fake_name
 -/
#check @set.mul_indicator_Union_apply /- _inst_3: complete_lattice ↝ no_meet_fake_name
 -/

-- algebra/invertible.lean
#check @inv_of_two_add_inv_of_two /- _inst_1: non_assoc_semiring ↝ has_add mul_one_class right_distrib_class
 -/

-- algebra/lie/basic.lean
#check @lie_hom.lie_apply /- _inst_7: lie_module ↝ lie_ring_module
_inst_11: lie_module ↝ lie_ring_module
 -/

-- algebra/lie/cartan_subalgebra.lean
#check @lie_algebra.top_is_cartan_subalgebra_of_nilpotent /- _inst_4: lie_algebra.is_nilpotent ↝ lie_algebra.is_nilpotent
 -/

-- algebra/lie/classical.lean
#check @lie_algebra.symplectic.J /- _inst_5: comm_ring ↝ has_neg mul_zero_one_class
 -/
#check @lie_algebra.orthogonal.indefinite_diagonal /- _inst_5: comm_ring ↝ has_neg mul_zero_one_class
 -/
#check @lie_algebra.orthogonal.Pso /- _inst_5: comm_ring ↝ mul_zero_one_class
 -/
#check @lie_algebra.orthogonal.JD /- _inst_5: comm_ring ↝ mul_zero_one_class
 -/
#check @lie_algebra.orthogonal.PD /- _inst_5: comm_ring ↝ has_neg mul_zero_one_class
 -/

-- algebra/lie/free.lean
#check @free_lie_algebra.module /- _inst_4: is_scalar_tower ↝ has_smul no_meet_fake_name
 -/
#check @free_lie_algebra.lift_aux /- _inst_3: lie_algebra ↝ is_scalar_tower module no_meet_fake_name smul_comm_class
 -/

-- algebra/lie/of_associative.lean
#check @ring.has_bracket /- _inst_1: ring ↝ has_mul has_sub
 -/
#check @ring.lie_def /- _inst_1: ring ↝ has_bracket has_mul has_sub
 -/
#check @commute_iff_lie_eq /- _inst_1: ring ↝ add_group has_bracket has_mul
 -/
#check @commute.lie_eq /- _inst_1: ring ↝ add_group has_bracket has_mul
 -/
#check @lie_ring.of_associative_ring_bracket /- _inst_1: ring ↝ has_bracket has_mul has_sub
 -/
#check @module.End.lie_ring_module /- _inst_2: comm_ring ↝ semiring
 -/
#check @lie_algebra.ad_eq_lmul_left_sub_lmul_right /- _inst_9: algebra ↝ algebra is_scalar_tower lie_algebra module no_meet_fake_name smul_comm_class
 -/

-- algebra/lie/quotient.lean
#check @lie_submodule.quotient.module' /- _inst_10: module ↝ has_smul module no_meet_fake_name
_inst_11: is_scalar_tower ↝ module no_meet_fake_name
 -/
#check @lie_submodule.quotient.is_central_scalar /- _inst_10: module ↝ has_smul has_smul is_central_scalar no_meet_fake_name
_inst_11: is_scalar_tower ↝ has_smul is_central_scalar no_meet_fake_name
 -/

-- algebra/lie/solvable.lean
#check @lie_algebra.lie_ideal.solvable_iff_le_radical /- _inst_6: is_noetherian ↝ lie_algebra.is_solvable no_meet_fake_name
 -/

-- algebra/lie/subalgebra.lean
#check @lie_subalgebra.is_central_scalar /- _inst_7: module ↝ has_smul module no_meet_fake_name
 -/
#check @lie_subalgebra.is_scalar_tower /- _inst_6: module ↝ has_smul module no_meet_fake_name
 -/
#check @lie_subalgebra.is_noetherian /- _inst_5: is_noetherian ↝ is_noetherian no_meet_fake_name
 -/

-- algebra/lie/submodule.lean
#check @lie_submodule.is_central_scalar /- _inst_11: module ↝ has_smul module no_meet_fake_name
 -/

-- algebra/lie/weights.lean
#check @lie_module.is_weight /- _inst_8: lie_module ↝ lie_module no_meet_fake_name
 -/

-- algebra/module/basic.lean
#check @module.eq_zero_of_zero_eq_one /- _inst_3: module ↝ has_smul mul_action no_meet_fake_name smul_with_zero
 -/
#check @neg_smul /- _inst_2: add_comm_group ↝ has_smul no_meet_fake_name smul_with_zero subtraction_comm_monoid
 -/
#check @module.subsingleton /- _inst_4: module ↝ has_smul mul_action no_meet_fake_name smul_with_zero
 -/
#check @add_comm_group.int_is_scalar_tower /- _inst_2: add_comm_group ↝ has_smul subtraction_comm_monoid
 -/
#check @smul_eq_zero /- _inst_3: module ↝ distrib_mul_action has_smul no_meet_fake_name smul_with_zero
 -/
#check @division_ring.to_no_zero_smul_divisors /- _inst_1: division_ring ↝ distrib_mul_action division_semiring
_inst_2: add_comm_group ↝ add_comm_monoid distrib_mul_action has_smul
_inst_3: module ↝ distrib_mul_action has_smul
 -/
#check @nat.smul_one_eq_coe /- _inst_1: semiring ↝ non_assoc_semiring
 -/
#check @finset.cast_card /- _inst_1: comm_semiring ↝ semiring
 -/

-- algebra/module/dedekind_domain.lean
#check @submodule.is_internal_prime_power_torsion /- _inst_1: comm_ring ↝ euclidean_domain
_inst_2: is_domain ↝ no_meet_fake_name
 -/

-- algebra/module/equiv.lean
#check @linear_equiv.trans /- _inst_14: ring_hom_comp_triple ↝
 -/

-- algebra/module/hom.lean
#check @add_monoid_hom.coe_smul /- _inst_3: add_monoid ↝ add_zero_class distrib_mul_action
_inst_5: distrib_mul_action ↝ distrib_mul_action has_smul
 -/
#check @add_monoid_hom.smul_apply /- _inst_3: add_monoid ↝ add_zero_class distrib_mul_action
_inst_5: distrib_mul_action ↝ distrib_mul_action has_smul
 -/
#check @add_monoid_hom.smul_comm_class /- _inst_3: add_monoid ↝ add_zero_class distrib_mul_action
_inst_5: distrib_mul_action ↝ distrib_mul_action has_smul
_inst_6: distrib_mul_action ↝ distrib_mul_action has_smul
 -/
#check @add_monoid_hom.is_scalar_tower /- _inst_3: add_monoid ↝ add_zero_class distrib_mul_action
_inst_5: distrib_mul_action ↝ distrib_mul_action has_smul
_inst_6: distrib_mul_action ↝ distrib_mul_action has_smul
 -/
#check @add_monoid_hom.is_central_scalar /- _inst_5: distrib_mul_action ↝ distrib_mul_action has_smul
 -/

-- algebra/module/injective.lean
#check @module.Baer /- _inst_1: ring ↝ module no_meet_fake_name semiring
_inst_2: add_comm_group ↝ add_comm_monoid
 -/

-- algebra/module/linear_map.lean
#check @linear_map.map_neg /- _inst_4: add_comm_group ↝ subtraction_comm_monoid
 -/
#check @linear_map.map_sub /- _inst_4: add_comm_group ↝ subtraction_comm_monoid
 -/
#check @linear_map.smul_apply /- _inst_12: distrib_mul_action ↝ has_smul has_smul
_inst_13: smul_comm_class ↝ has_smul
 -/
#check @linear_map.coe_smul /- _inst_12: distrib_mul_action ↝ has_smul has_smul
_inst_13: smul_comm_class ↝ has_smul
 -/
#check @linear_map.smul_comm_class /- _inst_12: distrib_mul_action ↝ has_smul has_smul
_inst_13: smul_comm_class ↝ has_smul
_inst_18: distrib_mul_action ↝ has_smul has_smul
_inst_19: smul_comm_class ↝ has_smul
 -/
#check @linear_map.is_scalar_tower /- _inst_12: distrib_mul_action ↝ has_smul has_smul
_inst_13: smul_comm_class ↝ has_smul
_inst_18: distrib_mul_action ↝ has_smul has_smul
_inst_19: smul_comm_class ↝ has_smul
 -/
#check @linear_map.is_central_scalar /- _inst_12: distrib_mul_action ↝ has_smul has_smul
_inst_13: smul_comm_class ↝ has_smul
 -/
#check @linear_map.smul_comp /- _inst_15: distrib_mul_action ↝ has_smul has_smul
_inst_16: smul_comm_class ↝ has_smul
 -/
#check @module.End.smul_comm_class /- _inst_10: is_scalar_tower ↝ linear_map.compatible_smul
 -/
#check @module.End.smul_comm_class' /- _inst_10: is_scalar_tower ↝ smul_comm_class
 -/
#check @linear_map.apply_is_scalar_tower /- _inst_6: comm_semiring ↝ distrib_mul_action has_smul no_meet_fake_name semiring smul_comm_class
 -/

-- algebra/module/pid.lean
#check @submodule.is_internal_prime_power_torsion_of_pid /- _inst_1: comm_ring ↝ field is_dedekind_domain no_meet_fake_name submodule.is_principal
_inst_3: is_principal_ideal_ring ↝ is_dedekind_domain no_meet_fake_name submodule.is_principal
 -/
#check @ideal.torsion_of_eq_span_pow_p_order /- _inst_1: comm_ring ↝ distrib_mul_action field no_meet_fake_name submodule.is_principal unique_factorization_monoid
_inst_3: is_principal_ideal_ring ↝ no_meet_fake_name submodule.is_principal unique_factorization_monoid
_inst_4: add_comm_group ↝ add_comm_monoid distrib_mul_action has_smul
 -/

-- algebra/module/projective.lean
#check @module.projective_lifting_property /- _inst_4: add_comm_group ↝ add_comm_monoid has_smul
_inst_6: add_comm_group ↝ add_comm_monoid has_smul
 -/
#check @module.projective_of_basis /- _inst_1: ring ↝ distrib_mul_action has_smul module no_meet_fake_name semiring smul_comm_class
_inst_2: add_comm_group ↝ add_comm_monoid has_smul
 -/

-- algebra/module/submodule/basic.lean
#check @submodule.is_scalar_tower /- _inst_5: is_scalar_tower ↝ has_smul is_scalar_tower no_meet_fake_name
 -/
#check @submodule.is_central_scalar /- _inst_5: is_scalar_tower ↝ has_smul is_central_scalar no_meet_fake_name
 -/
#check @submodule.coe_smul_of_tower /- _inst_5: is_scalar_tower ↝ has_smul no_meet_fake_name
 -/
#check @submodule.not_mem_of_ortho /- _inst_1: ring ↝ euclidean_domain mul_action
_inst_2: is_domain ↝ nontrivial
 -/
#check @submodule.smul_mem_iff /- _inst_1: division_ring ↝ division_semiring mul_action
_inst_6: module ↝ has_smul mul_action
 -/
#check @subspace /- _inst_1: field ↝ semiring
_inst_2: add_comm_group ↝ add_comm_monoid
 -/

-- algebra/module/submodule/pointwise.lean
#check @submodule.smul_le_self_of_tower /- _inst_8: module ↝ has_smul
_inst_9: module ↝ distrib_mul_action has_smul
 -/

-- algebra/module/torsion.lean
#check @module.is_torsion_by /- _inst_1: comm_semiring ↝ semiring
_inst_3: module ↝ has_smul
 -/
#check @module.is_torsion_by_set /- _inst_1: comm_semiring ↝ semiring
_inst_3: module ↝ has_smul
 -/
#check @module.is_torsion' /- _inst_2: add_comm_monoid ↝ has_zero
 -/
#check @module.is_torsion /- _inst_1: comm_semiring ↝ semiring
_inst_3: module ↝ has_smul
 -/
#check @module.is_torsion_by_set.is_scalar_tower /- _inst_7: is_scalar_tower ↝ has_smul no_meet_fake_name
 -/
#check @submodule.quotient_torsion.no_zero_smul_divisors /- _inst_1: comm_ring ↝ euclidean_domain has_quotient module no_meet_fake_name no_zero_divisors
_inst_4: is_domain ↝ no_zero_divisors nontrivial
 -/
#check @submodule.is_torsion'_powers_iff /- _inst_3: distrib_mul_action ↝ has_smul
 -/

-- algebra/monoid_algebra/basic.lean
#check @monoid_algebra /- _inst_1: semiring ↝ has_zero
 -/
#check @monoid_algebra.has_smul /- _inst_3: distrib_mul_action ↝ has_smul
 -/
#check @monoid_algebra.distrib_mul_action /- _inst_3: distrib_mul_action ↝ distrib_mul_action no_meet_fake_name
 -/
#check @monoid_algebra.module /- _inst_3: module ↝ module no_meet_fake_name
 -/
#check @monoid_algebra.has_faithful_smul /- _inst_3: distrib_mul_action ↝ has_faithful_smul has_smul has_smul
_inst_4: has_faithful_smul ↝ has_faithful_smul
_inst_5: nonempty ↝ has_faithful_smul
 -/
#check @monoid_algebra.is_scalar_tower /- _inst_4: distrib_mul_action ↝ has_smul has_smul is_scalar_tower no_meet_fake_name
_inst_5: distrib_mul_action ↝ has_smul has_smul is_scalar_tower no_meet_fake_name
_inst_7: is_scalar_tower ↝ is_scalar_tower no_meet_fake_name
 -/
#check @monoid_algebra.smul_comm_class /- _inst_4: distrib_mul_action ↝ has_smul has_smul no_meet_fake_name smul_comm_class
_inst_5: distrib_mul_action ↝ has_smul has_smul no_meet_fake_name smul_comm_class
_inst_6: smul_comm_class ↝ no_meet_fake_name smul_comm_class
 -/
#check @monoid_algebra.is_central_scalar /- _inst_3: distrib_mul_action ↝ has_smul has_smul is_central_scalar no_meet_fake_name
_inst_5: is_central_scalar ↝ is_central_scalar no_meet_fake_name
 -/
#check @monoid_algebra.comap_distrib_mul_action_self /- _inst_1: group ↝ monoid
 -/
#check @monoid_algebra.smul_comm_class_symm_self /- _inst_3: distrib_mul_action ↝ has_smul has_smul smul_comm_class
 -/
#check @monoid_algebra.ring_hom_ext /- _inst_3: semiring ↝ non_assoc_semiring
 -/
#check @monoid_algebra.induction_on /- _inst_2: monoid ↝ mul_one_class
 -/
#check @monoid_algebra.map_domain_algebra_map /- _inst_11: monoid_hom_class ↝ fun_like no_meet_fake_name one_hom_class
 -/
#check @add_monoid_algebra /- _inst_1: semiring ↝ has_zero
 -/
#check @add_monoid_algebra.has_smul /- _inst_3: distrib_mul_action ↝ has_smul
 -/
#check @add_monoid_algebra.distrib_mul_action /- _inst_3: distrib_mul_action ↝ distrib_mul_action no_meet_fake_name
 -/
#check @add_monoid_algebra.has_faithful_smul /- _inst_3: distrib_mul_action ↝ has_faithful_smul has_smul has_smul
_inst_4: has_faithful_smul ↝ has_faithful_smul
_inst_5: nonempty ↝ has_faithful_smul
 -/
#check @add_monoid_algebra.module /- _inst_3: module ↝ module no_meet_fake_name
 -/
#check @add_monoid_algebra.is_scalar_tower /- _inst_4: distrib_mul_action ↝ has_smul has_smul is_scalar_tower no_meet_fake_name
_inst_5: distrib_mul_action ↝ has_smul has_smul is_scalar_tower no_meet_fake_name
_inst_7: is_scalar_tower ↝ is_scalar_tower no_meet_fake_name
 -/
#check @add_monoid_algebra.smul_comm_class /- _inst_4: distrib_mul_action ↝ has_smul has_smul no_meet_fake_name smul_comm_class
_inst_5: distrib_mul_action ↝ has_smul has_smul no_meet_fake_name smul_comm_class
_inst_6: smul_comm_class ↝ no_meet_fake_name smul_comm_class
 -/
#check @add_monoid_algebra.is_central_scalar /- _inst_3: distrib_mul_action ↝ has_smul has_smul is_central_scalar no_meet_fake_name
_inst_5: is_central_scalar ↝ is_central_scalar no_meet_fake_name
 -/
#check @add_monoid_algebra.induction_on /- _inst_2: add_monoid ↝ add_zero_class
 -/
#check @add_monoid_algebra.ring_hom_ext /- _inst_2: add_monoid ↝ add_zero_class
 -/
#check @add_monoid_algebra.map_domain_algebra_map /- _inst_6: add_monoid_hom_class ↝ fun_like no_meet_fake_name zero_hom_class
 -/

-- algebra/monoid_algebra/grading.lean
#check @add_monoid_algebra.grade_by.is_internal /- _inst_2: add_monoid ↝ add_zero_class direct_sum.decomposition no_meet_fake_name
_inst_4: add_monoid ↝ add_zero_class direct_sum.decomposition no_meet_fake_name
 -/
#check @add_monoid_algebra.grade.is_internal /- _inst_4: add_monoid ↝ direct_sum.decomposition
 -/

-- algebra/ne_zero.lean
#check @ne_zero.ne' /- _inst_1: add_monoid_with_one ↝ has_nat_cast has_zero
 -/
#check @ne_zero.coe_trans /- _inst_2: has_coe ↝ has_lift_t
_inst_3: has_coe_t ↝ has_lift_t
 -/
#check @ne_zero.trans /- _inst_2: has_coe ↝ has_lift_t
_inst_3: has_coe_t ↝ has_lift_t
 -/
#check @ne_zero.nat_of_ne_zero /- _inst_1: semiring ↝ fun_like no_meet_fake_name non_assoc_semiring zero_hom_class
_inst_2: semiring ↝ fun_like no_meet_fake_name non_assoc_semiring zero_hom_class
 -/

-- algebra/order/absolute_value.lean
#check @absolute_value.sub_le /- _inst_2: ordered_ring ↝ ordered_semiring
 -/
#check @absolute_value.map_sub_eq_zero_iff /- _inst_2: ordered_ring ↝ ordered_semiring
 -/
#check @absolute_value.map_one /- _inst_2: linear_ordered_ring ↝ linear_ordered_semifield
 -/
#check @absolute_value.map_neg /- _inst_2: linear_ordered_comm_ring ↝ covariant_class no_zero_divisors ordered_comm_ring
 -/
#check @absolute_value.map_inv /- _inst_1: division_ring ↝ division_semiring
 -/
#check @absolute_value.map_div /- _inst_1: division_ring ↝ division_semiring
 -/
#check @is_absolute_value.abv_one /- _inst_1: linear_ordered_comm_ring ↝ linear_ordered_semifield
 -/
#check @is_absolute_value.abv_neg /- _inst_2: ring ↝ has_distrib_neg has_involutive_neg semiring
 -/
#check @is_absolute_value.abv_sub_le /- _inst_1: linear_ordered_field ↝ ordered_semiring
 -/
#check @is_absolute_value.sub_abv_le_abv_sub /- _inst_1: linear_ordered_field ↝ ordered_ring
 -/
#check @is_absolute_value.abv_inv /- _inst_2: division_ring ↝ division_semiring
 -/
#check @is_absolute_value.abv_div /- _inst_2: division_ring ↝ division_semiring
 -/

-- algebra/order/algebra.lean
#check @linear_ordered_comm_ring.to_ordered_smul /- _inst_1: linear_ordered_comm_ring ↝ linear_ordered_semiring
 -/

-- algebra/order/archimedean.lean
#check @exists_nat_one_div_lt /- _inst_1: linear_ordered_field ↝ covariant_class linear_ordered_semifield
 -/
#check @archimedean_iff_nat_lt /- _inst_1: linear_ordered_field ↝ linear_ordered_semifield
 -/

-- algebra/order/complete_field.lean
#check @linear_ordered_field.cut_map /- _inst_1: linear_ordered_field ↝ has_lt has_rat_cast
_inst_2: division_ring ↝ has_rat_cast
 -/
#check @linear_ordered_field.cut_map_nonempty /- _inst_2: linear_ordered_field ↝ division_ring
 -/
#check @linear_ordered_field.cut_map_add /- _inst_2: linear_ordered_field ↝ char_zero division_ring
 -/

-- algebra/order/field.lean
#check @div_self_le_one /- _inst_1: linear_ordered_semifield ↝ group_with_zero linear_order zero_le_one_class
 -/
#check @is_lub.mul_left /- _inst_1: linear_ordered_field ↝ linear_ordered_semifield
 -/
#check @mul_sub_mul_div_mul_neg_iff /- _inst_1: linear_ordered_field ↝ covariant_class field has_lt
 -/
#check @mul_sub_mul_div_mul_nonpos_iff /- _inst_1: linear_ordered_field ↝ covariant_class field has_le
 -/
#check @mul_self_inj_of_nonneg /- _inst_1: linear_ordered_field ↝ comm_ring covariant_class no_zero_divisors partial_order
 -/

-- algebra/order/floor.lean
#check @nat.le_floor_iff /- _inst_1: linear_ordered_semiring ↝ ordered_semiring
 -/
#check @nat.gc_ceil_coe /- _inst_1: linear_ordered_semiring ↝ ordered_semiring
 -/
#check @int.fract_div_mul_self_mem_Ico /- _inst_3: linear_ordered_field ↝ has_div linear_ordered_ring
 -/
#check @round /- _inst_1: linear_ordered_field ↝ has_div linear_ordered_ring
 -/

-- algebra/order/group.lean
#check @ordered_comm_group.has_exists_mul_of_le /- _inst_1: ordered_comm_group ↝ comm_group has_le
 -/
#check @ordered_add_comm_group.has_exists_add_of_le /- _inst_1: ordered_add_comm_group ↝ add_comm_group has_le
 -/
#check @le_div_iff_mul_le' /- _inst_3: covariant_class ↝ covariant_class
 -/
#check @le_sub_iff_add_le' /- _inst_3: covariant_class ↝ covariant_class
 -/
#check @div_le_iff_le_mul' /- _inst_3: covariant_class ↝ covariant_class
 -/
#check @sub_le_iff_le_add' /- _inst_3: covariant_class ↝ covariant_class
 -/
#check @lt_sub_iff_add_lt' /- _inst_3: covariant_class ↝ covariant_class
 -/
#check @lt_div_iff_mul_lt' /- _inst_3: covariant_class ↝ covariant_class
 -/
#check @sub_lt_iff_lt_add' /- _inst_3: covariant_class ↝ covariant_class
 -/
#check @div_lt_iff_lt_mul' /- _inst_3: covariant_class ↝ covariant_class
 -/
#check @le_of_forall_pos_lt_add /- _inst_3: covariant_class ↝ covariant_class
 -/
#check @le_of_forall_one_lt_lt_mul /- _inst_3: covariant_class ↝ covariant_class
 -/
#check @le_of_forall_pos_le_add /- _inst_3: covariant_class ↝ covariant_class
 -/
#check @le_of_forall_one_lt_le_mul /- _inst_3: covariant_class ↝ covariant_class
 -/
#check @linear_ordered_add_comm_group.add_lt_add_left /- _inst_1: linear_ordered_add_comm_group ↝ covariant_class has_add has_lt
 -/
#check @linear_ordered_comm_group.mul_lt_mul_left' /- _inst_1: linear_ordered_comm_group ↝ covariant_class has_lt has_mul
 -/
#check @min_inv_inv' /- _inst_1: linear_ordered_comm_group ↝ covariant_class covariant_class group linear_order
 -/
#check @min_neg_neg /- _inst_1: linear_ordered_add_comm_group ↝ add_group covariant_class covariant_class linear_order
 -/
#check @max_neg_neg /- _inst_1: linear_ordered_add_comm_group ↝ add_group covariant_class covariant_class linear_order
 -/
#check @max_inv_inv' /- _inst_1: linear_ordered_comm_group ↝ covariant_class covariant_class group linear_order
 -/
#check @min_sub_sub_right /- _inst_1: linear_ordered_add_comm_group ↝ covariant_class linear_order sub_neg_monoid
 -/
#check @min_div_div_right' /- _inst_1: linear_ordered_comm_group ↝ covariant_class div_inv_monoid linear_order
 -/
#check @max_sub_sub_right /- _inst_1: linear_ordered_add_comm_group ↝ covariant_class linear_order sub_neg_monoid
 -/
#check @max_div_div_right' /- _inst_1: linear_ordered_comm_group ↝ covariant_class div_inv_monoid linear_order
 -/
#check @eq_one_of_inv_eq' /- _inst_1: linear_ordered_comm_group ↝ covariant_class group linear_order
 -/
#check @eq_zero_of_neg_eq /- _inst_1: linear_ordered_add_comm_group ↝ add_group covariant_class linear_order
 -/
#check @exists_zero_lt /- _inst_1: linear_ordered_add_comm_group ↝ add_group covariant_class linear_order
 -/
#check @exists_one_lt' /- _inst_1: linear_ordered_comm_group ↝ covariant_class group linear_order
 -/
#check @abs_neg /- _inst_1: add_group ↝ has_abs has_involutive_neg
 -/
#check @eq_or_eq_neg_of_abs_eq /- _inst_1: add_group ↝ has_abs has_involutive_neg
 -/
#check @abs_lt /- _inst_3: covariant_class ↝ covariant_class
_inst_4: covariant_class ↝ covariant_class
 -/
#check @abs_le /- _inst_1: linear_ordered_add_comm_group ↝ add_group covariant_class covariant_class linear_order
 -/
#check @le_abs' /- _inst_1: linear_ordered_add_comm_group ↝ add_group covariant_class covariant_class linear_order
 -/
#check @apply_abs_le_add_of_nonneg' /- _inst_1: linear_ordered_add_comm_group ↝ add_group covariant_class linear_order
_inst_3: preorder ↝ has_le
 -/
#check @apply_abs_le_mul_of_one_le' /- _inst_1: linear_ordered_add_comm_group ↝ add_group covariant_class linear_order
_inst_3: preorder ↝ has_le
 -/
#check @abs_sub_lt_iff /- _inst_1: linear_ordered_add_comm_group ↝ add_comm_group covariant_class covariant_class covariant_class linear_order
 -/
#check @abs_eq /- _inst_1: linear_ordered_add_comm_group ↝ add_group covariant_class linear_order
 -/
#check @abs_le_max_abs_abs /- _inst_1: linear_ordered_add_comm_group ↝ add_group covariant_class covariant_class linear_order
 -/
#check @eq_of_abs_sub_eq_zero /- _inst_1: linear_ordered_add_comm_group ↝ add_group covariant_class linear_order
 -/
#check @max_sub_max_le_max /- _inst_1: linear_ordered_add_comm_group ↝ add_group covariant_class covariant_class linear_order
 -/
#check @inv_le_inv' /- _inst_1: ordered_comm_group ↝ covariant_class covariant_class group has_le
 -/
#check @neg_le_neg /- _inst_1: ordered_add_comm_group ↝ add_group covariant_class covariant_class has_le
 -/
#check @inv_lt_inv' /- _inst_1: ordered_comm_group ↝ covariant_class covariant_class group has_lt
 -/
#check @neg_lt_neg /- _inst_1: ordered_add_comm_group ↝ add_group covariant_class covariant_class has_lt
 -/
#check @neg_neg_of_pos /- _inst_1: ordered_add_comm_group ↝ add_group covariant_class has_lt
 -/
#check @inv_lt_one_of_one_lt /- _inst_1: ordered_comm_group ↝ covariant_class group has_lt
 -/
#check @neg_nonpos_of_nonneg /- _inst_1: ordered_add_comm_group ↝ add_group covariant_class has_le
 -/
#check @inv_le_one_of_one_le /- _inst_1: ordered_comm_group ↝ covariant_class group has_le
 -/
#check @neg_nonneg_of_nonpos /- _inst_1: ordered_add_comm_group ↝ add_group covariant_class has_le
 -/
#check @one_le_inv_of_le_one /- _inst_1: ordered_comm_group ↝ covariant_class group has_le
 -/

-- algebra/order/hom/ring.lean
#check @order_ring_hom.subsingleton /- _inst_1: linear_ordered_field ↝ char_zero division_ring linear_order
 -/

-- algebra/order/lattice_group.lean
#check @mul_sup /- _inst_1: lattice ↝ contravariant_class covariant_class semilattice_sup
_inst_2: comm_group ↝ contravariant_class covariant_class group
 -/
#check @add_sup /- _inst_1: lattice ↝ contravariant_class covariant_class semilattice_sup
_inst_2: add_comm_group ↝ add_group contravariant_class covariant_class
 -/
#check @mul_inf /- _inst_1: lattice ↝ contravariant_class covariant_class semilattice_inf
_inst_2: comm_group ↝ contravariant_class covariant_class group
 -/
#check @add_inf /- _inst_1: lattice ↝ contravariant_class covariant_class semilattice_inf
_inst_2: add_comm_group ↝ add_group contravariant_class covariant_class
 -/
#check @inv_sup_eq_inv_inf_inv /- _inst_2: comm_group ↝ covariant_class group
 -/
#check @neg_sup_eq_neg_inf_neg /- _inst_2: add_comm_group ↝ add_group covariant_class
 -/
#check @lattice_ordered_comm_group.has_zero_lattice_has_pos_part /- _inst_1: lattice ↝ has_sup
_inst_2: add_comm_group ↝ has_zero
 -/
#check @lattice_ordered_comm_group.has_one_lattice_has_pos_part /- _inst_1: lattice ↝ has_sup
_inst_2: comm_group ↝ has_one
 -/
#check @lattice_ordered_comm_group.m_pos_part_def /- _inst_1: lattice ↝ has_pos_part has_sup
_inst_2: comm_group ↝ has_one has_pos_part
 -/
#check @lattice_ordered_comm_group.pos_part_def /- _inst_1: lattice ↝ has_pos_part has_sup
_inst_2: add_comm_group ↝ has_pos_part has_zero
 -/
#check @lattice_ordered_comm_group.has_one_lattice_has_neg_part /- _inst_1: lattice ↝ has_sup
_inst_2: comm_group ↝ has_inv has_one
 -/
#check @lattice_ordered_comm_group.has_zero_lattice_has_neg_part /- _inst_1: lattice ↝ has_sup
_inst_2: add_comm_group ↝ has_neg has_zero
 -/
#check @lattice_ordered_comm_group.neg_part_def /- _inst_1: lattice ↝ has_neg_part has_sup
_inst_2: add_comm_group ↝ has_neg has_neg_part has_zero
 -/
#check @lattice_ordered_comm_group.m_neg_part_def /- _inst_1: lattice ↝ has_neg_part has_sup
_inst_2: comm_group ↝ has_inv has_neg_part has_one
 -/
#check @lattice_ordered_comm_group.pos_zero /- _inst_1: lattice ↝ has_pos_part semilattice_sup
_inst_2: add_comm_group ↝ has_pos_part has_zero
 -/
#check @lattice_ordered_comm_group.pos_one /- _inst_1: lattice ↝ has_pos_part semilattice_sup
_inst_2: comm_group ↝ has_one has_pos_part
 -/
#check @lattice_ordered_comm_group.le_abs /- _inst_1: lattice ↝ semilattice_sup
_inst_2: add_comm_group ↝ has_abs has_neg
 -/
#check @lattice_ordered_comm_group.le_mabs /- _inst_1: lattice ↝ semilattice_sup
_inst_2: comm_group ↝ has_abs has_inv
 -/
#check @lattice_ordered_comm_group.inv_le_abs /- _inst_1: lattice ↝ semilattice_sup
_inst_2: comm_group ↝ has_abs has_inv
 -/
#check @lattice_ordered_comm_group.neg_le_abs /- _inst_1: lattice ↝ semilattice_sup
_inst_2: add_comm_group ↝ has_abs has_neg
 -/
#check @lattice_ordered_comm_group.pos_nonneg /- _inst_1: lattice ↝ has_pos_part semilattice_sup
_inst_2: add_comm_group ↝ has_pos_part has_zero
 -/
#check @lattice_ordered_comm_group.one_le_pos /- _inst_1: lattice ↝ has_pos_part semilattice_sup
_inst_2: comm_group ↝ has_one has_pos_part
 -/
#check @lattice_ordered_comm_group.one_le_neg /- _inst_1: lattice ↝ has_neg_part semilattice_sup
_inst_2: comm_group ↝ has_inv has_neg_part has_one
 -/
#check @lattice_ordered_comm_group.neg_nonneg /- _inst_1: lattice ↝ has_neg_part semilattice_sup
_inst_2: add_comm_group ↝ has_neg has_neg_part has_zero
 -/
#check @lattice_ordered_comm_group.m_le_pos /- _inst_1: lattice ↝ has_pos_part semilattice_sup
_inst_2: comm_group ↝ has_one has_pos_part
 -/
#check @lattice_ordered_comm_group.le_pos /- _inst_1: lattice ↝ has_pos_part semilattice_sup
_inst_2: add_comm_group ↝ has_pos_part has_zero
 -/
#check @lattice_ordered_comm_group.inv_le_neg /- _inst_1: lattice ↝ has_neg_part semilattice_sup
_inst_2: comm_group ↝ has_inv has_neg_part has_one
 -/
#check @lattice_ordered_comm_group.neg_le_neg /- _inst_1: lattice ↝ has_neg_part semilattice_sup
_inst_2: add_comm_group ↝ has_neg has_neg_part has_zero
 -/
#check @lattice_ordered_comm_group.neg_eq_pos_neg /- _inst_1: lattice ↝ has_neg_part has_pos_part
_inst_2: add_comm_group ↝ has_neg has_neg_part has_pos_part
 -/
#check @lattice_ordered_comm_group.neg_eq_pos_inv /- _inst_1: lattice ↝ has_neg_part has_pos_part
_inst_2: comm_group ↝ has_inv has_neg_part has_pos_part
 -/
#check @lattice_ordered_comm_group.mul_inf_eq_mul_inf_mul /- _inst_1: lattice ↝ contravariant_class covariant_class semilattice_inf
_inst_2: comm_group ↝ contravariant_class covariant_class group
 -/
#check @lattice_ordered_comm_group.add_inf_eq_add_inf_add /- _inst_1: lattice ↝ contravariant_class covariant_class semilattice_inf
_inst_2: add_comm_group ↝ add_group contravariant_class covariant_class
 -/
#check @lattice_ordered_comm_group.abs_inv_comm /- _inst_1: lattice ↝ semilattice_sup
_inst_2: comm_group ↝ division_monoid has_abs
 -/
#check @lattice_ordered_comm_group.abs_neg_comm /- _inst_1: lattice ↝ semilattice_sup
_inst_2: add_comm_group ↝ has_abs subtraction_monoid
 -/

-- algebra/order/module.lean
#check @smul_neg_iff_of_pos /- _inst_3: module ↝ distrib_mul_action has_smul no_meet_fake_name smul_with_zero
 -/
#check @smul_add_smul_le_smul_add_smul /- _inst_1: ordered_ring ↝ contravariant_class covariant_class distrib_mul_action has_exists_add_of_le no_meet_fake_name ordered_semiring smul_with_zero
_inst_2: ordered_add_comm_group ↝ covariant_class distrib_mul_action has_exists_add_of_le has_smul no_meet_fake_name ordered_add_comm_monoid smul_with_zero
 -/
#check @smul_add_smul_lt_smul_add_smul /- _inst_1: ordered_ring ↝ covariant_class distrib_mul_action has_exists_add_of_le no_meet_fake_name ordered_semiring smul_with_zero
_inst_2: ordered_add_comm_group ↝ distrib_mul_action has_exists_add_of_le has_smul no_meet_fake_name ordered_add_comm_monoid smul_with_zero
 -/
#check @pi.smul_with_zero'' /- _inst_1: linear_ordered_field ↝ monoid_with_zero mul_action_with_zero no_meet_fake_name
 -/
#check @pi.ordered_smul' /- _inst_1: linear_ordered_field ↝ no_meet_fake_name ordered_semiring ordered_smul smul_with_zero smul_with_zero
 -/

-- algebra/order/monoid.lean
#check @ordered_add_comm_monoid.to_covariant_class_right /- _inst_1: ordered_add_comm_monoid ↝ covariant_class has_add has_le
 -/
#check @ordered_comm_monoid.to_covariant_class_right /- _inst_1: ordered_comm_monoid ↝ covariant_class has_le has_mul
 -/
#check @bit0_pos /- _inst_1: ordered_add_comm_monoid ↝ add_zero_class covariant_class preorder
 -/
#check @with_zero.contravariant_class_mul_lt /- _inst_2: partial_order ↝ preorder
 -/
#check @bot_eq_zero' /- _inst_1: canonically_linear_ordered_add_monoid ↝ canonically_ordered_add_monoid
 -/
#check @bot_eq_one' /- _inst_1: canonically_linear_ordered_monoid ↝ canonically_ordered_monoid
 -/
#check @ordered_cancel_add_comm_monoid.to_contravariant_class_right /- _inst_2: ordered_cancel_add_comm_monoid ↝ contravariant_class has_add has_lt
 -/
#check @ordered_cancel_comm_monoid.to_contravariant_class_right /- _inst_2: ordered_cancel_comm_monoid ↝ contravariant_class has_lt has_mul
 -/
#check @with_top.zero_lt_top /- _inst_1: ordered_add_comm_monoid ↝ has_zero preorder
 -/
#check @with_top.zero_lt_coe /- _inst_1: ordered_add_comm_monoid ↝ has_zero preorder
 -/
#check @additive.of_mul_le /- _inst_1: preorder ↝ has_le
 -/
#check @additive.of_mul_lt /- _inst_1: preorder ↝ has_lt
 -/
#check @additive.to_mul_le /- _inst_1: preorder ↝ has_le
 -/
#check @additive.to_mul_lt /- _inst_1: preorder ↝ has_lt
 -/
#check @multiplicative.of_add_le /- _inst_1: preorder ↝ has_le
 -/
#check @multiplicative.of_add_lt /- _inst_1: preorder ↝ has_lt
 -/
#check @multiplicative.to_add_le /- _inst_1: preorder ↝ has_le
 -/
#check @multiplicative.to_add_lt /- _inst_1: preorder ↝ has_lt
 -/

-- algebra/order/monoid_lemmas.lean
#check @left.add_eq_add_iff_eq_and_eq /- _inst_1: add_semigroup ↝ has_add
 -/
#check @left.mul_eq_mul_iff_eq_and_eq /- _inst_1: semigroup ↝ has_mul
 -/
#check @right.mul_eq_mul_iff_eq_and_eq /- _inst_1: semigroup ↝ has_mul
 -/
#check @right.add_eq_add_iff_eq_and_eq /- _inst_1: add_semigroup ↝ has_add
 -/
#check @add_le_cancellable_zero /- _inst_1: add_monoid ↝ add_zero_class
 -/
#check @mul_le_cancellable_one /- _inst_1: monoid ↝ mul_one_class
 -/

-- algebra/order/monoid_lemmas_zero_lt.lean
#check @zero_lt.left.mul_pos /- _inst_2: preorder ↝ has_lt
 -/
#check @zero_lt.mul_neg_of_pos_of_neg /- _inst_2: preorder ↝ has_lt
 -/
#check @zero_lt.right.mul_pos /- _inst_2: preorder ↝ has_lt
 -/
#check @zero_lt.mul_neg_of_neg_of_pos /- _inst_2: preorder ↝ has_lt
 -/
#check @zero_lt.mul_left_cancel_iff /- _inst_1: mul_zero_class ↝ has_mul has_zero
 -/
#check @zero_lt.mul_right_cancel_iff /- _inst_1: mul_zero_class ↝ has_mul has_zero
 -/
#check @zero_lt.le_mul_iff_one_le_right /- _inst_3: preorder ↝ has_le has_lt
 -/
#check @zero_lt.lt_mul_iff_one_lt_right /- _inst_3: preorder ↝ has_lt
 -/
#check @zero_lt.mul_le_iff_le_one_right /- _inst_3: preorder ↝ has_le has_lt
 -/
#check @zero_lt.mul_lt_iff_lt_one_right /- _inst_3: preorder ↝ has_lt
 -/
#check @zero_lt.le_mul_iff_one_le_left /- _inst_3: preorder ↝ has_le has_lt
 -/
#check @zero_lt.lt_mul_iff_one_lt_left /- _inst_3: preorder ↝ has_lt
 -/
#check @zero_lt.mul_le_iff_le_one_left /- _inst_3: preorder ↝ has_le has_lt
 -/
#check @zero_lt.mul_lt_iff_lt_one_left /- _inst_3: preorder ↝ has_lt
 -/
#check @zero_lt.right.mul_le_one_of_le_of_le /- _inst_2: partial_order ↝ preorder
 -/

-- algebra/order/nonneg.lean
#check @nonneg.no_max_order /- _inst_1: partial_order ↝ preorder
 -/

-- algebra/order/pointwise.lean
#check @Sup_one /- _inst_1: complete_lattice ↝ complete_semilattice_Sup
 -/
#check @Sup_zero /- _inst_1: complete_lattice ↝ complete_semilattice_Sup
 -/
#check @Inf_one /- _inst_1: complete_lattice ↝ complete_semilattice_Inf
 -/
#check @Inf_zero /- _inst_1: complete_lattice ↝ complete_semilattice_Inf
 -/
#check @linear_ordered_field.smul_Ioo /- _inst_1: linear_ordered_field ↝ linear_ordered_semifield
 -/
#check @linear_ordered_field.smul_Icc /- _inst_1: linear_ordered_field ↝ linear_ordered_semifield
 -/
#check @linear_ordered_field.smul_Ico /- _inst_1: linear_ordered_field ↝ linear_ordered_semifield
 -/
#check @linear_ordered_field.smul_Ioc /- _inst_1: linear_ordered_field ↝ linear_ordered_semifield
 -/
#check @linear_ordered_field.smul_Ioi /- _inst_1: linear_ordered_field ↝ linear_ordered_semifield
 -/
#check @linear_ordered_field.smul_Iio /- _inst_1: linear_ordered_field ↝ linear_ordered_semifield
 -/
#check @linear_ordered_field.smul_Ici /- _inst_1: linear_ordered_field ↝ linear_ordered_semifield
 -/
#check @linear_ordered_field.smul_Iic /- _inst_1: linear_ordered_field ↝ linear_ordered_semifield
 -/

-- algebra/order/ring.lean
#check @add_one_le_two_mul /- _inst_2: semiring ↝ has_add mul_one_class right_distrib_class
 -/
#check @zero_lt_one /- _inst_1: ordered_semiring ↝ mul_zero_one_class partial_order zero_le_one_class
 -/
#check @le_iff_exists_nonneg_add /- _inst_1: ordered_ring ↝ add_comm_group contravariant_class covariant_class covariant_class has_le
 -/
#check @abs_mul_abs_self /- _inst_1: linear_ordered_ring ↝ has_distrib_neg has_mul has_neg linear_order
 -/
#check @max_mul_mul_le_max_mul_max /- _inst_1: linear_ordered_comm_ring ↝ linear_ordered_semifield
 -/
#check @abs_dvd /- _inst_1: ring ↝ has_abs has_distrib_neg has_neg semigroup
 -/
#check @dvd_abs /- _inst_1: ring ↝ has_abs has_distrib_neg has_neg semigroup
 -/
#check @canonically_ordered_comm_semiring.to_covariant_mul_le /- _inst_1: canonically_ordered_comm_semiring ↝ canonically_ordered_add_monoid has_mul left_distrib_class
 -/

-- algebra/order/smul.lean
#check @ordered_smul.mk'' /- _inst_3: mul_action_with_zero ↝ has_smul mul_action no_meet_fake_name smul_with_zero
 -/
#check @ordered_smul.mk' /- _inst_1: linear_ordered_field ↝ linear_ordered_semifield no_meet_fake_name smul_with_zero
 -/
#check @smul_le_smul_iff_of_pos /- _inst_1: linear_ordered_field ↝ linear_ordered_semifield mul_action no_meet_fake_name smul_with_zero
_inst_2: ordered_add_comm_group ↝ has_smul mul_action no_meet_fake_name ordered_add_comm_monoid smul_with_zero
_inst_3: mul_action_with_zero ↝ has_smul mul_action no_meet_fake_name smul_with_zero
 -/
#check @smul_lt_iff_of_pos /- _inst_1: linear_ordered_field ↝ linear_ordered_semifield mul_action no_meet_fake_name smul_with_zero
_inst_2: ordered_add_comm_group ↝ has_smul mul_action no_meet_fake_name ordered_add_comm_monoid smul_with_zero
_inst_3: mul_action_with_zero ↝ has_smul mul_action no_meet_fake_name smul_with_zero
 -/
#check @lt_smul_iff_of_pos /- _inst_1: linear_ordered_field ↝ linear_ordered_semifield mul_action no_meet_fake_name smul_with_zero
_inst_2: ordered_add_comm_group ↝ has_smul mul_action no_meet_fake_name ordered_add_comm_monoid smul_with_zero
_inst_3: mul_action_with_zero ↝ has_smul mul_action no_meet_fake_name smul_with_zero
 -/

-- algebra/order/sub.lean
#check @tsub_le_iff_right /- _inst_1: preorder ↝ has_le
 -/
#check @le_tsub_mul /- _inst_5: comm_semiring ↝ non_unital_comm_semiring
 -/
#check @tsub_le_tsub_left /- _inst_5: covariant_class ↝ covariant_class
 -/
#check @tsub_le_tsub_add_tsub /- _inst_5: covariant_class ↝ covariant_class
 -/
#check @add_tsub_add_le_tsub_right /- _inst_5: covariant_class ↝ covariant_class
 -/
#check @add_monoid_hom.le_map_tsub /- _inst_2: add_comm_monoid ↝ add_zero_class
_inst_6: add_comm_monoid ↝ add_zero_class
 -/
#check @add_tsub_add_eq_tsub_right /- _inst_6: contravariant_class ↝ contravariant_class
 -/
#check @lt_tsub_iff_right /- _inst_2: add_comm_semigroup ↝ has_add
 -/
#check @add_le_cancellable.lt_tsub_iff_right /- _inst_1: canonically_linear_ordered_add_monoid ↝ add_comm_semigroup linear_order
 -/
#check @add_le_cancellable.lt_tsub_iff_left /- _inst_1: canonically_linear_ordered_add_monoid ↝ add_comm_semigroup linear_order
 -/

-- algebra/order/with_zero.lean
#check @zero_le' /- _inst_1: linear_ordered_comm_monoid_with_zero ↝ covariant_class has_le mul_zero_one_class zero_le_one_class
 -/
#check @zero_lt_one₀ /- _inst_1: linear_ordered_comm_group_with_zero ↝ group_with_zero partial_order zero_le_one_class
 -/
#check @le_of_le_mul_right /- _inst_1: linear_ordered_comm_group_with_zero ↝ covariant_class group_with_zero has_le
 -/
#check @monoid_hom.map_neg_one /- _inst_1: linear_ordered_comm_group_with_zero ↝ covariant_class linear_order monoid
_inst_2: ring ↝ has_distrib_neg has_involutive_neg mul_one_class
 -/

-- algebra/parity.lean
#check @even.map /- _inst_3: add_monoid_hom_class ↝ add_hom_class fun_like no_meet_fake_name
 -/
#check @is_square.map /- _inst_3: monoid_hom_class ↝ fun_like mul_hom_class no_meet_fake_name
 -/
#check @is_square_zero /- _inst_1: monoid_with_zero ↝ mul_zero_class
 -/
#check @even_iff_exists_two_mul /- _inst_1: semiring ↝ non_assoc_semiring
 -/
#check @even_iff_two_dvd /- _inst_1: semiring ↝ has_add has_dvd mul_one_class right_distrib_class
 -/
#check @range_two_mul /- _inst_3: semiring ↝ has_add mul_one_class right_distrib_class
 -/
#check @even_bit0 /- _inst_1: semiring ↝ has_add
 -/
#check @even_two /- _inst_1: semiring ↝ has_add has_one
 -/
#check @even.mul_left /- _inst_1: semiring ↝ non_unital_non_assoc_semiring
 -/
#check @even.mul_right /- _inst_1: semiring ↝ non_unital_non_assoc_semiring
 -/
#check @even_two_mul /- _inst_1: semiring ↝ has_add mul_one_class right_distrib_class
 -/
#check @odd /- _inst_1: semiring ↝ has_add has_mul has_one
 -/
#check @odd.map /- _inst_3: ring_hom_class ↝ add_hom_class fun_like no_meet_fake_name one_hom_class
 -/
#check @even.zpow_abs /- _inst_1: linear_ordered_field ↝ division_monoid has_distrib_neg has_neg linear_order
 -/

-- algebra/periodic.lean
#check @list.periodic_prod /- _inst_2: comm_monoid ↝ monoid
 -/
#check @list.periodic_sum /- _inst_2: add_comm_monoid ↝ add_monoid
 -/
#check @function.periodic.const_smul₀ /- _inst_2: division_ring ↝ distrib_mul_action division_semiring mul_action no_meet_fake_name smul_with_zero
_inst_3: module ↝ distrib_mul_action has_smul mul_action no_meet_fake_name smul_with_zero
 -/
#check @function.periodic.sub_eq' /- _inst_1: add_comm_group ↝ subtraction_comm_monoid
 -/
#check @function.periodic.nat_mul /- _inst_1: semiring ↝ non_assoc_semiring
 -/
#check @function.periodic.sub_nat_mul_eq /- _inst_1: ring ↝ non_assoc_ring
 -/
#check @function.periodic.nsmul_sub_eq /- _inst_1: add_comm_group ↝ subtraction_comm_monoid
 -/
#check @function.antiperiodic.funext' /- _inst_2: add_group ↝ has_involutive_neg
 -/
#check @function.antiperiodic.periodic /- _inst_1: semiring ↝ add_semigroup mul_one_class right_distrib_class
_inst_2: add_group ↝ has_involutive_neg
 -/
#check @function.antiperiodic.sub_eq /- _inst_2: add_group ↝ has_involutive_neg
 -/
#check @function.antiperiodic.sub_eq' /- _inst_1: add_comm_group ↝ subtraction_comm_monoid
_inst_2: add_group ↝ has_neg
 -/
#check @function.antiperiodic.const_smul₀ /- _inst_3: division_ring ↝ distrib_mul_action division_semiring mul_action
_inst_4: module ↝ distrib_mul_action has_smul mul_action
 -/
#check @function.antiperiodic.add /- _inst_1: add_group ↝ add_semigroup nonempty
_inst_2: add_group ↝ has_involutive_neg
 -/
#check @function.periodic.add_antiperiod /- _inst_1: add_group ↝ add_semigroup nonempty
_inst_2: add_group ↝ has_involutive_neg
 -/
#check @function.antiperiodic.mul /- _inst_2: ring ↝ has_distrib_neg has_involutive_neg has_mul
 -/

-- algebra/polynomial/group_ring_action.lean
#check @prod_X_sub_smul /- _inst_5: mul_semiring_action ↝ mul_action
 -/

-- algebra/quadratic_discriminant.lean
#check @discrim /- _inst_1: ring ↝ has_add has_mul has_one has_pow has_sub
 -/
#check @quadratic_eq_zero_iff_discrim_eq_sq /- _inst_1: comm_ring ↝ field no_zero_divisors
_inst_2: is_domain ↝ cancel_monoid_with_zero no_zero_divisors
 -/

-- algebra/quandle.lean
#check @rack.self_distrib /- _inst_1: rack ↝ shelf
 -/
#check @rack.is_involutory /- _inst_2: rack ↝ shelf
 -/
#check @rack.is_abelian /- _inst_2: rack ↝ shelf
 -/

-- algebra/quaternion.lean
#check @quaternion_algebra.has_coe_t /- _inst_1: comm_ring ↝ has_zero
 -/
#check @quaternion_algebra.coe_re /- _inst_1: comm_ring ↝ has_coe_t no_meet_fake_name
 -/
#check @quaternion_algebra.coe_im_i /- _inst_1: comm_ring ↝ has_coe_t has_zero no_meet_fake_name
 -/
#check @quaternion_algebra.coe_im_j /- _inst_1: comm_ring ↝ has_coe_t has_zero no_meet_fake_name
 -/
#check @quaternion_algebra.coe_im_k /- _inst_1: comm_ring ↝ has_coe_t has_zero no_meet_fake_name
 -/
#check @quaternion_algebra.coe_injective /- _inst_1: comm_ring ↝ has_coe_t no_meet_fake_name
 -/
#check @quaternion_algebra.has_zero /- _inst_1: comm_ring ↝ has_zero
 -/
#check @quaternion_algebra.has_one /- _inst_1: comm_ring ↝ mul_zero_one_class
 -/
#check @quaternion_algebra.has_add /- _inst_1: comm_ring ↝ has_add
 -/
#check @quaternion_algebra.has_neg /- _inst_1: comm_ring ↝ has_neg
 -/
#check @quaternion_algebra.has_sub /- _inst_1: comm_ring ↝ has_sub
 -/
#check @quaternion_algebra.has_mul /- _inst_1: comm_ring ↝ has_add has_mul has_sub
 -/
#check @quaternion.has_coe_t /- _inst_1: comm_ring ↝ has_coe_t has_neg has_one no_meet_fake_name
 -/
#check @quaternion.ext /- _inst_1: comm_ring ↝ has_neg has_one
 -/
#check @quaternion.ext_iff /- _inst_1: comm_ring ↝ has_neg has_one
 -/
#check @quaternion.coe_re /- _inst_1: comm_ring ↝ has_coe_t has_neg has_one
 -/
#check @quaternion.coe_im_i /- _inst_1: comm_ring ↝ has_coe_t has_neg mul_zero_one_class
 -/
#check @quaternion.coe_im_j /- _inst_1: comm_ring ↝ has_coe_t has_neg mul_zero_one_class
 -/
#check @quaternion.coe_im_k /- _inst_1: comm_ring ↝ has_coe_t has_neg mul_zero_one_class
 -/
#check @quaternion.nontrivial /- _inst_1: linear_ordered_comm_ring ↝ euclidean_domain
 -/

-- algebra/ring/basic.lean
#check @map_bit0 /- _inst_1: non_assoc_semiring ↝ fun_like has_add
_inst_2: non_assoc_semiring ↝ fun_like has_add
 -/
#check @two_dvd_bit0 /- _inst_1: semiring ↝ has_add has_dvd mul_one_class right_distrib_class
 -/
#check @has_dvd.dvd.linear_comb /- _inst_1: non_unital_comm_semiring ↝ comm_semigroup has_add left_distrib_class
 -/
#check @add_mul_self_eq /- _inst_1: comm_semiring ↝ add_semigroup comm_monoid left_distrib_class right_distrib_class
 -/
#check @dvd_neg_of_dvd /- _inst_1: semigroup ↝ has_dvd has_involutive_neg has_mul
 -/
#check @neg_dvd_of_dvd /- _inst_1: semigroup ↝ has_dvd has_involutive_neg has_mul
 -/
#check @mul_sub_left_distrib /- _inst_1: non_unital_non_assoc_ring ↝ has_distrib_neg has_mul left_distrib_class sub_neg_monoid
 -/
#check @mul_sub_right_distrib /- _inst_1: non_unital_non_assoc_ring ↝ has_distrib_neg has_mul right_distrib_class sub_neg_monoid
 -/
#check @units.neg_divp /- _inst_1: ring ↝ has_distrib_neg has_neg monoid
 -/
#check @units.divp_add_divp_same /- _inst_1: ring ↝ has_add monoid right_distrib_class
 -/
#check @units.add_divp /- _inst_1: ring ↝ has_add monoid right_distrib_class
 -/
#check @units.divp_add /- _inst_1: ring ↝ has_add monoid right_distrib_class
 -/
#check @dvd_sub /- _inst_1: non_unital_ring ↝ has_distrib_neg left_distrib_class semigroup sub_neg_monoid
 -/
#check @is_domain.to_cancel_monoid_with_zero /- _inst_2: is_domain ↝ no_zero_divisors
 -/
#check @semiconj_by.add_right /- _inst_1: distrib ↝ has_add has_mul left_distrib_class right_distrib_class
 -/
#check @semiconj_by.add_left /- _inst_1: distrib ↝ has_add has_mul left_distrib_class right_distrib_class
 -/
#check @mul_self_sub_mul_self /- _inst_1: comm_ring ↝ non_unital_comm_ring
 -/
#check @mul_self_eq_mul_self_iff /- _inst_1: comm_ring ↝ non_unital_comm_ring
 -/
#check @units.divp_add_divp /- _inst_1: comm_ring ↝ comm_monoid has_add right_distrib_class
 -/

-- algebra/ring/boolean_ring.lean
#check @boolean_ring.has_sup /- _inst_1: boolean_ring ↝ has_add has_mul
 -/
#check @boolean_ring.has_inf /- _inst_1: boolean_ring ↝ has_mul
 -/

-- algebra/ring/equiv.lean
#check @ring_equiv.map_eq_zero_iff /- _inst_1: non_unital_non_assoc_semiring ↝ add_zero_class has_mul
_inst_2: non_unital_non_assoc_semiring ↝ add_zero_class has_mul
 -/
#check @ring_equiv.map_ne_zero_iff /- _inst_1: non_unital_non_assoc_semiring ↝ add_zero_class has_mul
_inst_2: non_unital_non_assoc_semiring ↝ add_zero_class has_mul
 -/
#check @ring_equiv.map_eq_one_iff /- _inst_1: non_assoc_semiring ↝ has_add mul_one_class
_inst_2: non_assoc_semiring ↝ has_add mul_one_class
 -/
#check @ring_equiv.map_ne_one_iff /- _inst_1: non_assoc_semiring ↝ has_add mul_one_class
_inst_2: non_assoc_semiring ↝ has_add mul_one_class
 -/
#check @ring_equiv.to_equiv_commutes /- _inst_1: non_assoc_semiring ↝ has_add has_mul
_inst_2: non_assoc_semiring ↝ has_add has_mul
 -/
#check @ring_equiv.map_inv /- _inst_1: division_ring ↝ division_semiring
_inst_2: division_ring ↝ division_semiring
 -/
#check @ring_equiv.map_div /- _inst_1: division_ring ↝ division_semiring
_inst_2: division_ring ↝ division_semiring
 -/
#check @ring_equiv.is_domain /- _inst_6: ring ↝ euclidean_domain no_zero_divisors
_inst_7: is_domain ↝ no_zero_divisors nontrivial
 -/

-- algebra/ring/idempotents.lean
#check @is_idempotent_elem.iff_eq_one /- _inst_7: group ↝ left_cancel_monoid
 -/

-- algebra/ring/opposite.lean
#check @mul_opposite.is_domain /- _inst_1: ring ↝ euclidean_domain no_zero_divisors
_inst_2: is_domain ↝ no_zero_divisors nontrivial
 -/
#check @add_opposite.is_domain /- _inst_1: ring ↝ euclidean_domain no_zero_divisors
_inst_2: is_domain ↝ no_zero_divisors nontrivial
 -/

-- algebra/ring_quot.lean
#check @ring_quot.rel.neg /- _inst_5: ring ↝ has_distrib_neg has_neg semiring
 -/
#check @ring_quot.ring_quot_ext /- _inst_5: semiring ↝ non_assoc_semiring
 -/
#check @ring_quot.rel.star /- _inst_6: star_ring ↝ has_star star_add_monoid star_semigroup
 -/

-- algebra/smul_with_zero.lean
#check @smul_inv₀ /- _inst_3: mul_action_with_zero ↝ has_smul mul_action no_meet_fake_name smul_with_zero
 -/

-- algebra/squarefree.lean
#check @squarefree.of_mul_left /- _inst_1: comm_monoid ↝ monoid
 -/
#check @squarefree_of_dvd_of_squarefree /- _inst_1: comm_monoid ↝ monoid
 -/

-- algebra/star/basic.lean
#check @star_id_of_comm /- _inst_1: comm_semiring ↝ comm_monoid has_involutive_star
 -/
#check @star_div' /- _inst_1: field ↝ has_star semifield
 -/
#check @star_bit1 /- _inst_2: star_ring ↝ has_star star_add_monoid star_semigroup
 -/
#check @star_semigroup.to_star_module /- _inst_1: comm_monoid ↝ comm_semigroup has_star
 -/
#check @ring.inverse_star /- _inst_2: star_ring ↝ has_star star_add_monoid star_semigroup
 -/
#check @star_inv_of /- _inst_2: star_semigroup ↝ has_star invertible no_meet_fake_name
 -/
#check @star_semigroup.to_opposite_star_module /- _inst_1: comm_monoid ↝ comm_semigroup has_star
 -/

-- algebra/star/pointwise.lean
#check @set.star_mul /- _inst_1: monoid ↝ has_involutive_star semigroup
 -/

-- algebra/star/self_adjoint.lean
#check @self_adjoint.one_mem /- _inst_2: star_ring ↝ has_star star_add_monoid star_semigroup
 -/
#check @self_adjoint.conjugate /- _inst_1: ring ↝ has_involutive_star non_unital_ring star_add_monoid star_semigroup
_inst_2: star_ring ↝ has_involutive_star star_add_monoid star_semigroup
 -/
#check @self_adjoint.conjugate' /- _inst_1: ring ↝ has_involutive_star non_unital_ring star_add_monoid star_semigroup
_inst_2: star_ring ↝ has_involutive_star star_add_monoid star_semigroup
 -/
#check @self_adjoint.is_star_normal_of_mem /- _inst_1: ring ↝ has_star non_unital_ring star_add_monoid
_inst_2: star_ring ↝ has_star star_add_monoid
 -/
#check @self_adjoint.mul_mem /- _inst_1: comm_ring ↝ has_star non_unital_comm_ring star_add_monoid star_semigroup
_inst_2: star_ring ↝ has_star star_add_monoid star_semigroup
 -/
#check @self_adjoint.coe_smul /- _inst_2: has_trivial_star ↝ has_smul
_inst_6: star_module ↝ has_smul
 -/
#check @skew_adjoint.conjugate /- _inst_1: ring ↝ has_distrib_neg has_involutive_star non_unital_ring star_add_monoid star_semigroup
_inst_2: star_ring ↝ has_involutive_star star_add_monoid star_semigroup
 -/
#check @skew_adjoint.conjugate' /- _inst_1: ring ↝ has_distrib_neg has_involutive_star non_unital_ring star_add_monoid star_semigroup
_inst_2: star_ring ↝ has_involutive_star star_add_monoid star_semigroup
 -/
#check @skew_adjoint.is_star_normal_of_mem /- _inst_1: ring ↝ has_distrib_neg has_star non_unital_ring star_add_monoid
_inst_2: star_ring ↝ has_star star_add_monoid
 -/
#check @skew_adjoint.coe_smul /- _inst_2: has_trivial_star ↝ has_smul
_inst_6: distrib_mul_action ↝ has_smul has_smul
_inst_7: star_module ↝ has_smul
 -/
#check @is_star_normal_zero /- _inst_1: semiring ↝ has_star non_unital_semiring star_add_monoid
_inst_2: star_ring ↝ has_star star_add_monoid
 -/
#check @is_star_normal_star_self /- _inst_1: monoid ↝ has_involutive_star semigroup
_inst_2: star_semigroup ↝ has_involutive_star
 -/
#check @has_trivial_star.is_star_normal /- _inst_1: monoid ↝ has_star semigroup
_inst_2: star_semigroup ↝ has_star
 -/
#check @comm_monoid.is_star_normal /- _inst_1: comm_monoid ↝ comm_semigroup has_star
_inst_2: star_semigroup ↝ has_star
 -/

-- algebra/star/unitary.lean
#check @unitary.coe_inv /- _inst_1: group_with_zero ↝ division_monoid
 -/

-- algebra/symmetrized.lean
#check @sym_alg.unsym_mul_self /- _inst_1: semiring ↝ has_add monoid right_distrib_class
 -/
#check @sym_alg.sym_mul_self /- _inst_1: semiring ↝ has_add monoid right_distrib_class
 -/

-- algebra/triv_sq_zero_ext.lean
#check @triv_sq_zero_ext.fst_smul /- _inst_2: has_smul ↝ has_smul
 -/
#check @triv_sq_zero_ext.snd_smul /- _inst_1: has_smul ↝ has_smul
 -/
#check @triv_sq_zero_ext.inl_neg /- _inst_2: add_group ↝ subtraction_monoid
 -/
#check @triv_sq_zero_ext.inr_add /- _inst_2: add_zero_class ↝ has_add
 -/
#check @triv_sq_zero_ext.inr_neg /- _inst_1: add_group ↝ subtraction_monoid
 -/
#check @triv_sq_zero_ext.inr_mul_inr /- _inst_3: module ↝ has_smul no_meet_fake_name smul_with_zero
 -/
#check @triv_sq_zero_ext.inl_mul_inr /- _inst_3: module ↝ distrib_mul_action has_smul
 -/
#check @triv_sq_zero_ext.inr_mul_inl /- _inst_3: module ↝ distrib_mul_action has_smul
 -/
#check @triv_sq_zero_ext.algebra_map_eq_inl' /- _inst_5: module ↝ algebra has_smul no_meet_fake_name
_inst_7: is_scalar_tower ↝ algebra no_meet_fake_name
 -/

-- algebra/tropical/basic.lean
#check @tropical.untrop_zpow /- _inst_1: add_group ↝ sub_neg_monoid
 -/
#check @tropical.trop_zsmul /- _inst_1: add_group ↝ sub_neg_monoid
 -/
#check @tropical.covariant_swap_mul_lt /- _inst_1: preorder ↝ has_lt
 -/
#check @tropical.mul_eq_zero_iff /- _inst_2: linear_ordered_add_comm_monoid ↝ has_add
 -/

-- algebraic_geometry/EllipticCurve.lean
#check @EllipticCurve.Δ_aux /- _inst_1: comm_ring ↝ has_add has_mul has_neg has_one has_pow has_sub
 -/
#check @EllipticCurve.two_torsion_polynomial /- _inst_2: comm_ring ↝ semiring
 -/

-- algebraic_geometry/open_immersion.lean
#check @algebraic_geometry.SheafedSpace.is_open_immersion.has_limit_cospan_forget_of_left /- H: algebraic_geometry.SheafedSpace.is_open_immersion ↝ algebraic_geometry.PresheafedSpace.is_open_immersion no_meet_fake_name
 -/
#check @algebraic_geometry.SheafedSpace.is_open_immersion.has_limit_cospan_forget_of_left' /- H: algebraic_geometry.SheafedSpace.is_open_immersion ↝ algebraic_geometry.PresheafedSpace.is_open_immersion no_meet_fake_name
 -/
#check @algebraic_geometry.SheafedSpace.is_open_immersion.has_limit_cospan_forget_of_right /- H: algebraic_geometry.SheafedSpace.is_open_immersion ↝ algebraic_geometry.PresheafedSpace.is_open_immersion no_meet_fake_name
 -/
#check @algebraic_geometry.SheafedSpace.is_open_immersion.has_limit_cospan_forget_of_right' /- H: algebraic_geometry.SheafedSpace.is_open_immersion ↝ algebraic_geometry.PresheafedSpace.is_open_immersion no_meet_fake_name
 -/

-- algebraic_geometry/prime_spectrum/basic.lean
#check @prime_spectrum /- _inst_1: comm_ring ↝ semiring
 -/
#check @prime_spectrum.t1_space_iff_is_field /- _inst_1: comm_ring ↝ euclidean_domain
_inst_2: is_domain ↝ no_meet_fake_name
 -/

-- algebraic_geometry/prime_spectrum/noetherian.lean
#check @prime_spectrum.exists_prime_spectrum_prod_le /- _inst_2: is_noetherian_ring ↝ is_noetherian
 -/
#check @prime_spectrum.exists_prime_spectrum_prod_le_and_ne_bot_of_domain /- _inst_3: comm_ring ↝ euclidean_domain is_noetherian module no_zero_divisors
_inst_4: is_domain ↝ no_zero_divisors nontrivial
_inst_5: is_noetherian_ring ↝ is_noetherian
 -/

-- algebraic_geometry/projective_spectrum/topology.lean
#check @projective_spectrum /- _inst_2: comm_ring ↝ module semiring
 -/

-- algebraic_topology/dold_kan/faces.lean
#check @algebraic_topology.dold_kan.higher_faces_vanish /- _inst_2: category_theory.preadditive ↝ category_theory.limits.has_zero_morphisms
 -/

-- algebraic_topology/simplicial_object.lean
#check @category_theory.simplicial_object.category_theory.limits.has_limits /- _inst_2: category_theory.limits.has_limits ↝ category_theory.limits.has_limits_of_shape
 -/
#check @category_theory.simplicial_object.category_theory.limits.has_colimits /- _inst_2: category_theory.limits.has_colimits ↝ category_theory.limits.has_colimits_of_shape
 -/
#check @category_theory.simplicial_object.truncated.category_theory.limits.has_limits /- _inst_2: category_theory.limits.has_limits ↝ category_theory.limits.has_limits_of_shape
 -/
#check @category_theory.simplicial_object.truncated.category_theory.limits.has_colimits /- _inst_2: category_theory.limits.has_colimits ↝ category_theory.limits.has_colimits_of_shape
 -/
#check @category_theory.cosimplicial_object.category_theory.limits.has_limits /- _inst_2: category_theory.limits.has_limits ↝ category_theory.limits.has_limits_of_shape
 -/
#check @category_theory.cosimplicial_object.category_theory.limits.has_colimits /- _inst_2: category_theory.limits.has_colimits ↝ category_theory.limits.has_colimits_of_shape
 -/
#check @category_theory.cosimplicial_object.truncated.category_theory.limits.has_limits /- _inst_2: category_theory.limits.has_limits ↝ category_theory.limits.has_limits_of_shape
 -/
#check @category_theory.cosimplicial_object.truncated.category_theory.limits.has_colimits /- _inst_2: category_theory.limits.has_colimits ↝ category_theory.limits.has_colimits_of_shape
 -/

-- analysis/analytic/composition.lean
#check @formal_multilinear_series.apply_composition /- _inst_1: comm_ring ↝ ring
 -/
#check @formal_multilinear_series.comp_id /- _inst_4: normed_add_comm_group ↝ has_continuous_const_smul module seminormed_add_comm_group
_inst_5: normed_space ↝ has_continuous_const_smul module
 -/
#check @formal_multilinear_series.id_comp /- _inst_2: normed_add_comm_group ↝ has_continuous_const_smul module seminormed_add_comm_group
_inst_3: normed_space ↝ has_continuous_const_smul module
 -/
#check @formal_multilinear_series.le_comp_radius_of_summable /- _inst_4: normed_add_comm_group ↝ has_continuous_const_smul module seminormed_add_comm_group
_inst_5: normed_space ↝ has_continuous_const_smul module
 -/
#check @formal_multilinear_series.comp_partial_sum /- _inst_1: nontrivially_normed_field ↝ has_continuous_const_smul module normed_field
_inst_2: normed_add_comm_group ↝ has_continuous_const_smul module seminormed_add_comm_group
_inst_3: normed_space ↝ has_continuous_const_smul module
_inst_4: normed_add_comm_group ↝ has_continuous_const_smul module seminormed_add_comm_group
_inst_5: normed_space ↝ has_continuous_const_smul module
_inst_6: normed_add_comm_group ↝ has_continuous_const_smul module seminormed_add_comm_group
_inst_7: normed_space ↝ has_continuous_const_smul module
 -/
#check @formal_multilinear_series.comp_assoc /- _inst_1: nontrivially_normed_field ↝ has_continuous_const_smul module normed_field
_inst_2: normed_add_comm_group ↝ has_continuous_const_smul module seminormed_add_comm_group
_inst_3: normed_space ↝ has_continuous_const_smul module
_inst_4: normed_add_comm_group ↝ has_continuous_const_smul module seminormed_add_comm_group
_inst_5: normed_space ↝ has_continuous_const_smul module
_inst_6: normed_add_comm_group ↝ has_continuous_add has_continuous_const_smul module seminormed_add_comm_group
_inst_7: normed_space ↝ has_continuous_const_smul module
_inst_8: normed_add_comm_group ↝ has_continuous_add has_continuous_const_smul module seminormed_add_comm_group
_inst_9: normed_space ↝ has_continuous_const_smul module
 -/

-- analysis/analytic/inverse.lean
#check @formal_multilinear_series.comp_right_inv_aux1 /- _inst_1: nontrivially_normed_field ↝ has_continuous_const_smul module normed_field
_inst_2: normed_add_comm_group ↝ has_continuous_const_smul module seminormed_add_comm_group
_inst_3: normed_space ↝ has_continuous_const_smul module
_inst_4: normed_add_comm_group ↝ has_continuous_add has_continuous_const_smul module seminormed_add_comm_group
_inst_5: normed_space ↝ has_continuous_const_smul module
 -/

-- analysis/asymptotics/asymptotic_equivalent.lean
#check @asymptotics.is_equivalent /- _inst_1: normed_add_comm_group ↝ has_norm has_sub
 -/

-- analysis/asymptotics/asymptotics.lean
#check @asymptotics.is_o.not_is_O /- _inst_5: seminormed_add_comm_group ↝ has_norm
 -/
#check @asymptotics.is_O_with.prod_left_same /- _inst_6: seminormed_add_comm_group ↝ has_norm
 -/
#check @asymptotics.is_O_with.prod_left_fst /- _inst_6: seminormed_add_comm_group ↝ has_norm
 -/
#check @asymptotics.is_O_with.prod_left_snd /- _inst_6: seminormed_add_comm_group ↝ has_norm
 -/
#check @asymptotics.is_O.prod_left_fst /- _inst_6: seminormed_add_comm_group ↝ has_norm
 -/
#check @asymptotics.is_O.prod_left_snd /- _inst_6: seminormed_add_comm_group ↝ has_norm
 -/
#check @asymptotics.is_o.prod_left_fst /- _inst_6: seminormed_add_comm_group ↝ has_norm
 -/
#check @asymptotics.is_o.prod_left_snd /- _inst_6: seminormed_add_comm_group ↝ has_norm
 -/
#check @asymptotics.is_O_with.eq_zero_imp /- _inst_8: normed_add_comm_group ↝ seminormed_add_comm_group
 -/
#check @asymptotics.is_O_refl_left /- _inst_5: seminormed_add_comm_group ↝ has_norm
 -/
#check @asymptotics.is_o_top /- _inst_8: normed_add_comm_group ↝ seminormed_add_comm_group
 -/
#check @asymptotics.is_o_const_iff /- _inst_7: normed_add_comm_group ↝ seminormed_add_comm_group
 -/
#check @asymptotics.is_O_const_of_tendsto /- _inst_7: normed_add_comm_group ↝ seminormed_add_comm_group
 -/
#check @asymptotics.is_O.trans_tendsto /- _inst_7: normed_add_comm_group ↝ seminormed_add_comm_group
_inst_8: normed_add_comm_group ↝ seminormed_add_comm_group
 -/
#check @asymptotics.is_O_with_const_mul_self /- _inst_10: semi_normed_ring ↝ non_unital_semi_normed_ring
 -/
#check @asymptotics.is_O_with_self_const_mul /- _inst_12: normed_field ↝ normed_division_ring
 -/
#check @asymptotics.is_O_self_const_mul /- _inst_12: normed_field ↝ normed_division_ring
 -/
#check @asymptotics.is_O_const_mul_left_iff /- _inst_12: normed_field ↝ normed_division_ring
 -/
#check @asymptotics.is_o_const_mul_left_iff /- _inst_12: normed_field ↝ normed_division_ring
 -/
#check @asymptotics.is_O.const_mul_right /- _inst_12: normed_field ↝ normed_division_ring
 -/
#check @asymptotics.is_O_const_mul_right_iff /- _inst_12: normed_field ↝ normed_division_ring
 -/
#check @asymptotics.is_o.const_mul_right /- _inst_12: normed_field ↝ normed_division_ring
 -/
#check @asymptotics.is_o_const_mul_right_iff /- _inst_12: normed_field ↝ normed_division_ring
 -/
#check @asymptotics.is_O_with.mul /- _inst_10: semi_normed_ring ↝ non_unital_semi_normed_ring
_inst_12: normed_field ↝ normed_division_ring
 -/
#check @asymptotics.is_O_with.of_pow /- _inst_12: normed_field ↝ normed_division_ring
 -/
#check @asymptotics.is_O_with.inv_rev /- _inst_12: normed_field ↝ normed_division_ring
_inst_13: normed_field ↝ normed_division_ring
 -/
#check @asymptotics.is_o_const_left /- _inst_8: normed_add_comm_group ↝ seminormed_add_comm_group
 -/
#check @asymptotics.is_O_with.eventually_mul_div_cancel /- _inst_12: normed_field ↝ normed_division_ring
 -/
#check @asymptotics.is_O_with_of_eq_mul /- _inst_12: normed_field ↝ normed_division_ring
 -/
#check @asymptotics.div_is_bounded_under_of_is_O /- _inst_12: normed_field ↝ normed_division_ring
 -/
#check @asymptotics.is_o.tendsto_zero_of_tendsto /- _inst_14: normed_add_comm_group ↝ seminormed_add_comm_group
_inst_15: normed_field ↝ norm_one_class semi_normed_ring
 -/
#check @asymptotics.is_O_cofinite_iff /- _inst_7: normed_add_comm_group ↝ seminormed_add_comm_group
 -/
#check @summable_of_is_O /- _inst_1: normed_add_comm_group ↝ seminormed_add_comm_group
 -/

-- analysis/asymptotics/specific_asymptotics.lean
#check @filter.is_bounded_under.is_o_sub_self_inv /- _inst_1: normed_field ↝ normed_division_ring
 -/
#check @pow_div_pow_eventually_eq_at_top /- _inst_1: linear_ordered_field ↝ group_with_zero no_max_order preorder
 -/
#check @pow_div_pow_eventually_eq_at_bot /- _inst_1: linear_ordered_field ↝ group_with_zero preorder
 -/
#check @tendsto_zpow_at_top_at_top /- _inst_1: linear_ordered_field ↝ linear_ordered_semifield
 -/
#check @asymptotics.is_O.trans_tendsto_norm_at_top /- _inst_1: normed_linear_ordered_field ↝ seminormed_add_comm_group
 -/

-- analysis/asymptotics/superpolynomial_decay.lean
#check @asymptotics.superpolynomial_decay /- _inst_2: comm_semiring ↝ has_mul has_pow has_zero
 -/
#check @asymptotics.superpolynomial_decay.trans_eventually_le /- _inst_2: ordered_comm_semiring ↝ linear_ordered_semifield
 -/
#check @asymptotics.superpolynomial_decay_mul_const_iff /- _inst_2: field ↝ semifield
 -/
#check @asymptotics.superpolynomial_decay_const_mul_iff /- _inst_2: field ↝ semifield
 -/
#check @asymptotics.superpolynomial_decay_iff_norm_tendsto_zero /- _inst_1: normed_linear_ordered_field ↝ semi_normed_comm_ring
 -/

-- analysis/asymptotics/theta.lean
#check @asymptotics.is_Theta.tendsto_zero_iff /- _inst_7: normed_add_comm_group ↝ seminormed_add_comm_group
_inst_8: normed_add_comm_group ↝ seminormed_add_comm_group
 -/

-- analysis/box_integral/basic.lean
#check @box_integral.integral_sum /- _inst_1: normed_add_comm_group ↝ seminormed_add_comm_group
 -/

-- analysis/box_integral/partition/measure.lean
#check @box_integral.box.measurable_set_Ioo /- _inst_1: fintype ↝ finite
 -/

-- analysis/calculus/cont_diff.lean
#check @cont_diff_within_at.div_const /- _inst_14: normed_field ↝ normed_division_ring normed_space
 -/
#check @cont_diff.div_const /- _inst_14: normed_field ↝ normed_division_ring normed_space
 -/
#check @cont_diff_at_inv /- _inst_12: normed_field ↝ normed_division_ring normed_space
 -/

-- analysis/calculus/deriv.lean
#check @deriv_mul_const_field /- _inst_6: normed_field ↝ normed_division_ring normed_space
 -/
#check @has_deriv_at.div_const /- _inst_6: nontrivially_normed_field ↝ normed_division_ring normed_space
 -/
#check @has_deriv_within_at.div_const /- _inst_6: nontrivially_normed_field ↝ normed_division_ring normed_space
 -/
#check @has_strict_deriv_at.div_const /- _inst_6: nontrivially_normed_field ↝ normed_division_ring normed_space
 -/
#check @deriv_within_div_const /- _inst_6: nontrivially_normed_field ↝ normed_field normed_space
 -/
#check @deriv_div_const /- _inst_6: nontrivially_normed_field ↝ normed_field normed_space
 -/

-- analysis/calculus/fderiv.lean
#check @has_fderiv_at_filter /- _inst_1: nontrivially_normed_field ↝ module normed_field
_inst_2: normed_add_comm_group ↝ module seminormed_add_comm_group
_inst_3: normed_space ↝ module
_inst_4: normed_add_comm_group ↝ module seminormed_add_comm_group
_inst_5: normed_space ↝ module
 -/
#check @has_strict_fderiv_at /- _inst_1: nontrivially_normed_field ↝ module normed_field
_inst_2: normed_add_comm_group ↝ module seminormed_add_comm_group
_inst_3: normed_space ↝ module
_inst_4: normed_add_comm_group ↝ module seminormed_add_comm_group
_inst_5: normed_space ↝ module
 -/
#check @has_strict_fderiv_at.const_smul /- _inst_11: module ↝ has_smul module
_inst_12: smul_comm_class ↝ module
_inst_13: has_continuous_const_smul ↝ module
 -/
#check @has_fderiv_at_filter.const_smul /- _inst_11: module ↝ has_smul module
_inst_12: smul_comm_class ↝ module
_inst_13: has_continuous_const_smul ↝ module
 -/
#check @has_strict_fderiv_at.mul_const' /- _inst_12: normed_algebra ↝ is_scalar_tower module module normed_space smul_comm_class
 -/
#check @has_fderiv_within_at.mul_const' /- _inst_12: normed_algebra ↝ is_scalar_tower module module normed_space smul_comm_class
 -/
#check @has_fderiv_at.mul_const' /- _inst_12: normed_algebra ↝ is_scalar_tower module module normed_space smul_comm_class
 -/
#check @has_strict_fderiv_at.const_mul /- _inst_12: normed_algebra ↝ is_scalar_tower module module normed_space smul_comm_class
 -/
#check @has_fderiv_within_at.const_mul /- _inst_12: normed_algebra ↝ is_scalar_tower module module normed_space smul_comm_class
 -/
#check @has_fderiv_at.const_mul /- _inst_12: normed_algebra ↝ is_scalar_tower module module normed_space smul_comm_class
 -/
#check @has_fderiv_at_ring_inverse /- _inst_11: normed_algebra ↝ is_scalar_tower module module normed_space normed_space smul_comm_class
 -/
#check @has_fderiv_at_filter_real_equiv /- _inst_3: normed_add_comm_group ↝ seminormed_add_comm_group
 -/
#check @has_strict_fderiv_at.restrict_scalars /- _inst_3: normed_algebra ↝ has_smul linear_map.compatible_smul
_inst_7: is_scalar_tower ↝ linear_map.compatible_smul
_inst_11: is_scalar_tower ↝ linear_map.compatible_smul
 -/
#check @has_fderiv_at_filter.restrict_scalars /- _inst_3: normed_algebra ↝ has_smul linear_map.compatible_smul
_inst_7: is_scalar_tower ↝ linear_map.compatible_smul
_inst_11: is_scalar_tower ↝ linear_map.compatible_smul
 -/
#check @has_fderiv_at.restrict_scalars /- _inst_3: normed_algebra ↝ has_smul linear_map.compatible_smul
_inst_7: is_scalar_tower ↝ linear_map.compatible_smul
_inst_11: is_scalar_tower ↝ linear_map.compatible_smul
 -/
#check @has_fderiv_within_at.restrict_scalars /- _inst_3: normed_algebra ↝ has_smul linear_map.compatible_smul
_inst_7: is_scalar_tower ↝ linear_map.compatible_smul
_inst_11: is_scalar_tower ↝ linear_map.compatible_smul
 -/
#check @has_fderiv_within_at_of_restrict_scalars /- _inst_3: normed_algebra ↝ has_smul linear_map.compatible_smul
_inst_7: is_scalar_tower ↝ linear_map.compatible_smul
_inst_11: is_scalar_tower ↝ linear_map.compatible_smul
 -/
#check @has_fderiv_at_of_restrict_scalars /- _inst_3: normed_algebra ↝ has_smul linear_map.compatible_smul
_inst_7: is_scalar_tower ↝ linear_map.compatible_smul
_inst_11: is_scalar_tower ↝ linear_map.compatible_smul
 -/

-- analysis/calculus/fderiv_measurable.lean
#check @fderiv_measurable_aux.A /- _inst_1: nontrivially_normed_field ↝ module normed_field
_inst_2: normed_add_comm_group ↝ module seminormed_add_comm_group
_inst_3: normed_space ↝ module
_inst_4: normed_add_comm_group ↝ module seminormed_add_comm_group
_inst_5: normed_space ↝ module
 -/
#check @right_deriv_measurable_aux.A /- _inst_1: normed_add_comm_group ↝ seminormed_add_comm_group
 -/

-- analysis/calculus/formal_multilinear_series.lean
#check @formal_multilinear_series /- _inst_17: ring ↝ semiring
_inst_21: topological_add_group ↝
_inst_22: has_continuous_const_smul ↝
_inst_26: topological_add_group ↝
_inst_27: has_continuous_const_smul ↝
 -/
#check @formal_multilinear_series.inhabited /- _inst_1: comm_ring ↝ ring
 -/
#check @formal_multilinear_series.congr /- _inst_1: comm_ring ↝ ring
 -/
#check @formal_multilinear_series.comp_continuous_linear_map /- _inst_1: comm_ring ↝ ring
 -/
#check @continuous_linear_map.comp_formal_multilinear_series /- _inst_1: comm_ring ↝ ring
 -/

-- analysis/calculus/inverse.lean
#check @approximates_linear_on /- _inst_1: nontrivially_normed_field ↝ module normed_field
_inst_2: normed_add_comm_group ↝ module seminormed_add_comm_group
_inst_3: normed_space ↝ module
_inst_4: normed_add_comm_group ↝ module seminormed_add_comm_group
_inst_5: normed_space ↝ module
 -/

-- analysis/calculus/local_extr.lean
#check @pos_tangent_cone_at /- _inst_1: normed_add_comm_group ↝ seminormed_add_comm_group
 -/

-- analysis/calculus/mean_value.lean
#check @image_norm_le_of_liminf_right_slope_norm_lt_deriv_boundary /- _inst_5: normed_add_comm_group ↝ seminormed_add_comm_group
 -/

-- analysis/calculus/tangent_cone.lean
#check @tangent_cone_at /- _inst_1: nontrivially_normed_field ↝ has_norm semiring
_inst_3: module ↝ has_smul
 -/
#check @tangent_cone_univ /- _inst_2: normed_add_comm_group ↝ has_smul module mul_action seminormed_add_comm_group
_inst_3: normed_space ↝ has_smul module mul_action
 -/
#check @tangent_cone_mono /- _inst_2: normed_add_comm_group ↝ has_smul module seminormed_add_comm_group
_inst_3: normed_space ↝ has_smul module
 -/
#check @tangent_cone_at.lim_zero /- _inst_1: nontrivially_normed_field ↝ normed_field
_inst_2: normed_add_comm_group ↝ has_smul seminormed_add_comm_group
 -/
#check @mem_tangent_cone_of_open_segment_subset /- _inst_6: normed_add_comm_group ↝ seminormed_add_comm_group
 -/
#check @unique_diff_on.unique_diff_within_at /- _inst_2: normed_add_comm_group ↝ module seminormed_add_comm_group
_inst_3: normed_space ↝ module
 -/
#check @unique_diff_on_empty /- _inst_2: normed_add_comm_group ↝ module seminormed_add_comm_group
_inst_3: normed_space ↝ module
 -/

-- analysis/complex/abs_max.lean
#check @complex.exists_mem_frontier_is_max_on_norm /- _inst_5: nontrivial ↝ no_meet_fake_name noncompact_space
 -/

-- analysis/complex/basic.lean
#check @normed_space.complex_to_real /- _inst_1: normed_add_comm_group ↝ seminormed_add_comm_group
 -/

-- analysis/complex/phragmen_lindelof.lean
#check @phragmen_lindelof.is_O_sub_exp_exp /- _inst_1: normed_add_comm_group ↝ seminormed_add_comm_group
 -/
#check @phragmen_lindelof.is_O_sub_exp_rpow /- _inst_1: normed_add_comm_group ↝ seminormed_add_comm_group
 -/

-- analysis/convex/basic.lean
#check @segment /- _inst_1: ordered_semiring ↝ has_add has_le mul_zero_one_class
_inst_2: add_comm_monoid ↝ has_add
 -/
#check @open_segment /- _inst_1: ordered_semiring ↝ has_add has_lt mul_zero_one_class
_inst_2: add_comm_monoid ↝ has_add
 -/
#check @left_mem_segment /- _inst_3: mul_action_with_zero ↝ has_smul mul_action no_meet_fake_name smul_with_zero
 -/
#check @insert_endpoints_open_segment /- _inst_3: module ↝ has_smul mul_action mul_action_with_zero no_meet_fake_name smul_with_zero
 -/
#check @open_segment_same /- _inst_2: add_comm_group ↝ add_comm_monoid has_smul mul_action
 -/
#check @segment_eq_image /- _inst_2: add_comm_group ↝ add_comm_monoid has_smul
_inst_4: module ↝ has_smul
 -/
#check @open_segment_eq_image /- _inst_2: add_comm_group ↝ add_comm_monoid has_smul
_inst_4: module ↝ has_smul
 -/
#check @mem_segment_iff_div /- _inst_1: linear_ordered_field ↝ linear_ordered_semifield
_inst_2: add_comm_group ↝ add_cancel_comm_monoid has_smul
_inst_4: module ↝ has_smul
 -/
#check @mem_open_segment_iff_div /- _inst_1: linear_ordered_field ↝ covariant_class linear_ordered_semifield
_inst_2: add_comm_group ↝ add_comm_monoid has_smul
_inst_4: module ↝ has_smul
 -/
#check @open_segment_subset_Ioo /- _inst_2: ordered_cancel_add_comm_monoid ↝ covariant_class covariant_class has_smul no_meet_fake_name ordered_add_comm_monoid smul_with_zero
 -/
#check @convex /- _inst_1: ordered_semiring ↝ has_add has_le mul_zero_one_class
_inst_2: add_comm_monoid ↝ has_add
 -/
#check @convex_Iio /- _inst_6: ordered_cancel_add_comm_monoid ↝ covariant_class has_smul mul_action no_meet_fake_name ordered_add_comm_monoid smul_with_zero
 -/
#check @monotone_on.convex_le /- _inst_3: ordered_add_comm_monoid ↝ preorder
 -/
#check @monotone_on.convex_lt /- _inst_3: ordered_add_comm_monoid ↝ preorder
 -/
#check @convex.combo_eq_vadd /- _inst_1: ordered_semiring ↝ distrib_mul_action semiring
 -/
#check @convex.smul /- _inst_1: ordered_comm_semiring ↝ linear_ordered_semifield module
 -/
#check @convex.smul_preimage /- _inst_1: ordered_comm_semiring ↝ linear_ordered_semifield module
 -/
#check @convex.add_smul_mem /- _inst_2: add_comm_group ↝ add_comm_monoid distrib_mul_action has_smul mul_action
 -/
#check @convex.neg /- _inst_1: ordered_ring ↝ ordered_semiring
 -/
#check @convex.add_smul /- _inst_1: linear_ordered_field ↝ covariant_class distrib_mul_action linear_ordered_semifield mul_action no_meet_fake_name smul_with_zero
_inst_2: add_comm_group ↝ add_comm_monoid distrib_mul_action has_smul mul_action no_meet_fake_name smul_with_zero
 -/
#check @set.ord_connected.convex /- _inst_2: linear_ordered_add_comm_monoid ↝ has_smul is_trichotomous no_meet_fake_name ordered_add_comm_monoid smul_with_zero
 -/
#check @std_simplex /- _inst_1: ordered_semiring ↝ add_comm_monoid_with_one has_le
 -/

-- analysis/convex/combination.lean
#check @finset.center_mass /- _inst_1: linear_ordered_field ↝ has_inv semiring
_inst_2: add_comm_group ↝ add_comm_monoid has_smul
_inst_4: module ↝ has_smul
 -/
#check @set.finite.convex_hull_eq_image /- _inst_2: add_comm_group ↝ add_comm_monoid has_smul is_scalar_tower
 -/
#check @mem_Icc_of_mem_std_simplex /- _inst_1: linear_ordered_field ↝ ordered_semiring
 -/

-- analysis/convex/cone.lean
#check @convex_cone.smul_mem_iff /- _inst_1: linear_ordered_field ↝ linear_ordered_semifield
 -/
#check @convex_cone.to_ordered_smul /- _inst_3: module ↝ distrib_mul_action has_smul mul_action_with_zero no_meet_fake_name smul_with_zero
 -/
#check @convex_cone.flat /- _inst_2: add_comm_group ↝ add_comm_monoid has_neg
 -/
#check @convex_cone.salient /- _inst_2: add_comm_group ↝ add_comm_monoid has_neg
 -/

-- analysis/convex/contractible.lean
#check @star_convex.contractible_space /- _inst_1: add_comm_group ↝ add_comm_monoid
 -/

-- analysis/convex/exposed.lean
#check @is_exposed /- _inst_1: normed_linear_ordered_field ↝ has_le module normed_field
_inst_2: normed_add_comm_group ↝ module seminormed_add_comm_group
_inst_3: normed_space ↝ module
 -/
#check @continuous_linear_map.to_exposed /- _inst_1: normed_linear_ordered_field ↝ has_le module normed_field
_inst_2: normed_add_comm_group ↝ module seminormed_add_comm_group
_inst_3: normed_space ↝ module
 -/
#check @set.exposed_points /- _inst_1: normed_linear_ordered_field ↝ has_le module normed_field
_inst_2: normed_add_comm_group ↝ module seminormed_add_comm_group
_inst_3: normed_space ↝ module
 -/

-- analysis/convex/extreme.lean
#check @is_extreme.convex_diff /- _inst_2: add_comm_group ↝ add_comm_monoid has_smul
 -/

-- analysis/convex/function.lean
#check @convex_on /- _inst_4: ordered_add_comm_monoid ↝ has_add has_le
 -/
#check @concave_on /- _inst_4: ordered_add_comm_monoid ↝ has_add has_le
 -/
#check @strict_convex_on /- _inst_4: ordered_add_comm_monoid ↝ has_add has_lt
 -/
#check @strict_concave_on /- _inst_4: ordered_add_comm_monoid ↝ has_add has_lt
 -/
#check @convex_on_iff_forall_pos /- _inst_5: module ↝ has_smul mul_action no_meet_fake_name smul_with_zero
_inst_6: module ↝ has_smul mul_action no_meet_fake_name smul_with_zero
 -/
#check @linear_order.strict_convex_on_of_lt /- _inst_5: module ↝ has_smul
_inst_6: module ↝ has_smul
 -/
#check @strict_convex_on.add_convex_on /- _inst_4: ordered_cancel_add_comm_monoid ↝ covariant_class has_smul ordered_add_comm_monoid
 -/
#check @strict_convex_on.add /- _inst_4: ordered_cancel_add_comm_monoid ↝ covariant_class covariant_class has_smul ordered_add_comm_monoid
 -/
#check @convex_on.convex_lt /- _inst_4: ordered_cancel_add_comm_monoid ↝ covariant_class has_smul no_meet_fake_name ordered_add_comm_monoid smul_with_zero
 -/
#check @convex_on.sup /- _inst_6: module ↝ has_smul no_meet_fake_name smul_with_zero
 -/
#check @strict_convex_on.sup /- _inst_6: module ↝ has_smul no_meet_fake_name smul_with_zero
 -/
#check @convex_on.le_left_of_right_le' /- _inst_4: linear_ordered_cancel_add_comm_monoid ↝ covariant_class has_smul linear_ordered_add_comm_monoid no_meet_fake_name smul_with_zero
 -/
#check @strict_convex_on.lt_left_of_right_lt' /- _inst_4: linear_ordered_cancel_add_comm_monoid ↝ covariant_class has_smul linear_ordered_add_comm_monoid no_meet_fake_name smul_with_zero
 -/
#check @neg_convex_on_iff /- _inst_6: module ↝ distrib_mul_action has_smul
 -/
#check @neg_strict_convex_on_iff /- _inst_6: module ↝ distrib_mul_action has_smul
 -/
#check @convex_on.smul /- _inst_1: ordered_comm_semiring ↝ distrib_mul_action no_meet_fake_name ordered_semiring smul_comm_class smul_with_zero
_inst_5: module ↝ distrib_mul_action has_smul no_meet_fake_name smul_comm_class smul_with_zero
 -/
#check @convex_on.comp_affine_map /- _inst_1: linear_ordered_field ↝ ordered_ring
 -/
#check @convex_on_iff_div /- _inst_1: linear_ordered_field ↝ linear_ordered_semifield
 -/
#check @strict_convex_on_iff_div /- _inst_1: linear_ordered_field ↝ covariant_class linear_ordered_semifield
 -/

-- analysis/convex/gauge.lean
#check @gauge /- _inst_1: add_comm_group ↝ add_comm_monoid
 -/
#check @absorbent.gauge_set_nonempty /- _inst_1: add_comm_group ↝ add_comm_monoid
 -/
#check @balanced.star_convex /- _inst_1: add_comm_group ↝ add_comm_monoid
 -/
#check @gauge_smul_of_nonneg /- _inst_6: mul_action_with_zero ↝ has_smul mul_action no_meet_fake_name smul_with_zero
 -/
#check @gauge_smul_left_of_nonneg /- _inst_6: mul_action_with_zero ↝ has_smul mul_action no_meet_fake_name smul_with_zero
 -/

-- analysis/convex/hull.lean
#check @convex_hull_smul /- _inst_1: ordered_comm_semiring ↝ linear_ordered_semifield module
 -/

-- analysis/convex/independent.lean
#check @convex_independent /- _inst_2: add_comm_group ↝ add_comm_monoid
 -/
#check @convex.convex_independent_extreme_points /- _inst_1: linear_ordered_field ↝ densely_ordered linear_ordered_ring no_zero_smul_divisors
 -/

-- analysis/convex/join.lean
#check @convex_join /- _inst_3: module ↝ has_smul
 -/
#check @convex_join_assoc_aux /- _inst_1: linear_ordered_field ↝ covariant_class distrib_mul_action linear_ordered_semifield mul_action mul_action_with_zero no_meet_fake_name smul_with_zero
_inst_2: add_comm_group ↝ add_comm_monoid distrib_mul_action has_smul mul_action mul_action_with_zero no_meet_fake_name smul_with_zero
 -/

-- analysis/convex/quasiconvex.lean
#check @quasiconvex_on /- _inst_4: ordered_add_comm_monoid ↝ has_le
 -/
#check @quasiconcave_on /- _inst_4: ordered_add_comm_monoid ↝ has_le
 -/
#check @convex_on.quasiconvex_on /- _inst_4: linear_ordered_add_comm_monoid ↝ has_smul no_meet_fake_name ordered_add_comm_monoid smul_with_zero
 -/
#check @concave_on.quasiconcave_on /- _inst_4: linear_ordered_add_comm_monoid ↝ has_smul no_meet_fake_name ordered_add_comm_monoid smul_with_zero
 -/

-- analysis/convex/star.lean
#check @star_convex /- _inst_1: ordered_semiring ↝ has_add has_le mul_zero_one_class
_inst_2: add_comm_monoid ↝ has_add
 -/
#check @star_convex.mem /- _inst_4: module ↝ has_smul mul_action no_meet_fake_name smul_with_zero
 -/
#check @star_convex_iff_forall_pos /- _inst_4: module ↝ has_smul mul_action no_meet_fake_name smul_with_zero
 -/
#check @star_convex.smul /- _inst_1: ordered_comm_semiring ↝ linear_ordered_semifield module
 -/
#check @star_convex.preimage_smul /- _inst_1: ordered_comm_semiring ↝ linear_ordered_semifield module
 -/
#check @star_convex.add_smul_mem /- _inst_2: add_comm_group ↝ add_comm_monoid distrib_mul_action has_smul mul_action
 -/
#check @star_convex.neg /- _inst_1: ordered_ring ↝ ordered_semiring
 -/
#check @star_convex_iff_div /- _inst_1: linear_ordered_field ↝ linear_ordered_semifield
_inst_2: add_comm_group ↝ add_comm_monoid has_smul
_inst_3: module ↝ has_smul
 -/

-- analysis/convex/strict.lean
#check @strict_convex /- _inst_1: ordered_semiring ↝ has_add has_lt mul_zero_one_class
_inst_4: add_comm_monoid ↝ has_add
 -/
#check @convex.strict_convex /- _inst_6: module ↝ has_smul
 -/
#check @strict_convex_singleton /- _inst_6: module ↝ has_smul
 -/
#check @set.subsingleton.strict_convex /- _inst_6: module ↝ has_smul
 -/
#check @strict_convex.linear_image /- _inst_6: module ↝ has_smul
_inst_7: module ↝ has_smul
 -/
#check @strict_convex_Iic /- _inst_9: linear_ordered_cancel_add_comm_monoid ↝ covariant_class covariant_class has_smul linear_ordered_add_comm_monoid no_meet_fake_name order_closed_topology smul_with_zero
_inst_10: order_topology ↝ order_closed_topology
 -/
#check @strict_convex_Iio /- _inst_9: linear_ordered_cancel_add_comm_monoid ↝ has_smul linear_ordered_semiring no_meet_fake_name order_closed_topology smul_with_zero
_inst_10: order_topology ↝ order_closed_topology
 -/
#check @strict_convex_Ioi /- _inst_9: linear_ordered_cancel_add_comm_monoid ↝ has_smul linear_ordered_semiring no_meet_fake_name order_closed_topology smul_with_zero
_inst_10: order_topology ↝ order_closed_topology
 -/
#check @strict_convex.smul /- _inst_4: add_comm_group ↝ add_comm_monoid has_smul module mul_action no_meet_fake_name smul_with_zero
_inst_8: linear_ordered_field ↝ module mul_action no_meet_fake_name semifield smul_with_zero
 -/
#check @strict_convex.preimage_smul /- _inst_1: ordered_comm_semiring ↝ linear_ordered_semifield module no_meet_fake_name smul_with_zero
 -/
#check @strict_convex.eq_of_open_segment_subset_frontier /- _inst_4: add_comm_group ↝ add_comm_monoid has_smul
_inst_6: module ↝ has_smul
 -/
#check @strict_convex.add_smul_mem /- _inst_4: add_comm_group ↝ add_cancel_comm_monoid distrib_mul_action has_smul mul_action
 -/
#check @strict_convex.neg /- _inst_1: ordered_ring ↝ ordered_semiring
_inst_8: topological_add_group ↝ has_continuous_neg
 -/
#check @strict_convex_iff_div /- _inst_1: linear_ordered_field ↝ covariant_class linear_ordered_semifield
_inst_3: add_comm_group ↝ add_comm_monoid has_smul
_inst_5: module ↝ has_smul
 -/

-- analysis/convex/strict_convex_space.lean
#check @strict_convex_space.of_norm_add_lt_aux /- _inst_2: normed_add_comm_group ↝ seminormed_add_comm_group
 -/

-- analysis/convex/topology.lean
#check @convex.combo_interior_closure_subset_interior /- _inst_1: linear_ordered_field ↝ linear_ordered_semifield mul_action
_inst_3: module ↝ has_smul mul_action
 -/
#check @convex.closure /- _inst_1: linear_ordered_field ↝ ordered_semiring
_inst_3: module ↝ has_smul
_inst_5: topological_add_group ↝ has_continuous_add
 -/
#check @set.finite.compact_convex_hull /- _inst_4: topological_add_group ↝ has_continuous_add
 -/

-- analysis/convolution.lean
#check @has_compact_support.convolution_integrand_bound_right /- _inst_1: normed_add_comm_group ↝ module seminormed_add_comm_group
_inst_4: normed_add_comm_group ↝ has_continuous_add module module no_meet_fake_name normed_space seminormed_add_comm_group smul_comm_class
 -/
#check @continuous.convolution_integrand_fst /- _inst_10: add_group ↝ has_sub
 -/
#check @convolution_exists_at /- _inst_1: normed_add_comm_group ↝ module seminormed_add_comm_group
_inst_2: normed_add_comm_group ↝ module module seminormed_add_comm_group
_inst_6: normed_space ↝ module
 -/
#check @measure_theory.ae_strongly_measurable.convolution_integrand' /- _inst_11: add_group ↝ has_add has_measurable_sub₂ has_neg has_sub
_inst_12: has_measurable_add₂ ↝ has_measurable_sub₂
_inst_13: has_measurable_neg ↝ has_measurable_sub₂
 -/
#check @measure_theory.ae_strongly_measurable.convolution_integrand_snd' /- _inst_11: add_group ↝ has_add has_measurable_sub has_neg has_sub
_inst_12: has_measurable_add₂ ↝ has_measurable_sub
_inst_13: has_measurable_neg ↝ has_measurable_sub
 -/
#check @measure_theory.ae_strongly_measurable.convolution_integrand_swap_snd' /- _inst_11: add_group ↝ has_add has_measurable_sub has_neg has_sub
_inst_12: has_measurable_add₂ ↝ has_measurable_sub
_inst_13: has_measurable_neg ↝ has_measurable_sub
 -/
#check @has_compact_support.convolution_exists_at /- _inst_15: topological_add_group ↝ has_continuous_add has_continuous_neg
_inst_16: borel_space ↝ opens_measurable_space
_inst_17: topological_space.second_countable_topology ↝ no_meet_fake_name second_countable_topology_either
 -/
#check @convolution_exists_at_flip /- _inst_12: has_measurable_add₂ ↝ has_measurable_add
 -/
#check @convolution_exists_at.integrable_swap /- _inst_12: has_measurable_add₂ ↝ has_measurable_add
 -/
#check @convolution /- _inst_1: normed_add_comm_group ↝ module seminormed_add_comm_group
_inst_2: normed_add_comm_group ↝ module module seminormed_add_comm_group
_inst_6: normed_space ↝ module
 -/
#check @smul_convolution /- _inst_13: add_group ↝ has_sub
 -/
#check @convolution_smul /- _inst_13: add_group ↝ has_sub
 -/
#check @zero_convolution /- _inst_13: add_group ↝ has_sub
 -/
#check @convolution_zero /- _inst_13: add_group ↝ has_sub
 -/
#check @convolution_exists_at.distrib_add /- _inst_13: add_group ↝ has_sub
 -/
#check @convolution_exists_at.add_distrib /- _inst_13: add_group ↝ has_sub
 -/
#check @has_compact_support.convolution /- _inst_15: topological_add_group ↝ has_continuous_add
 -/
#check @has_compact_support.continuous_convolution_right /- _inst_15: topological_add_group ↝ has_continuous_add has_continuous_neg has_continuous_sub has_measurable_add₂ has_measurable_neg sigma_compact_space
_inst_16: borel_space ↝ has_measurable_add₂ has_measurable_neg opens_measurable_space
_inst_17: topological_space.second_countable_topology ↝ has_measurable_add₂ no_meet_fake_name second_countable_topology_either sigma_compact_space topological_space.first_countable_topology
 -/
#check @bdd_above.continuous_convolution_right_of_integrable /- _inst_15: topological_add_group ↝ has_continuous_sub has_measurable_add₂ has_measurable_neg
_inst_16: borel_space ↝ has_measurable_add₂ has_measurable_neg opens_measurable_space
_inst_17: topological_space.second_countable_topology ↝ has_measurable_add₂ no_meet_fake_name second_countable_topology_either topological_space.first_countable_topology
 -/
#check @measure_theory.integrable.integrable_convolution /- _inst_15: topological_add_group ↝ has_measurable_add₂ has_measurable_neg
_inst_16: borel_space ↝ has_measurable_add₂ has_measurable_neg
_inst_17: topological_space.second_countable_topology ↝ has_measurable_add₂
 -/
#check @convolution_flip /- _inst_15: topological_add_group ↝ has_measurable_add has_measurable_neg
_inst_16: borel_space ↝ has_measurable_add has_measurable_neg
 -/
#check @dist_convolution_le' /- _inst_14: borel_space ↝ has_measurable_add₂ has_measurable_neg opens_measurable_space
_inst_15: topological_space.second_countable_topology ↝ has_measurable_add₂
 -/
#check @convolution_precompR_apply /- _inst_13: normed_add_comm_group ↝ add_group has_measurable_add₂ has_measurable_neg topological_add_group topological_space
 -/

-- analysis/hofer.lean
#check @hofer /- _inst_1: metric_space ↝ pseudo_metric_space
 -/

-- analysis/inner_product_space/adjoint.lean
#check @inner_product_space.is_self_adjoint /- _inst_2: inner_product_space ↝ add_comm_monoid has_inner module
 -/

-- analysis/inner_product_space/basic.lean
#check @orthonormal /- _inst_2: inner_product_space ↝ has_inner has_norm
 -/
#check @is_R_or_C.inner_apply /- _inst_1: is_R_or_C ↝ comm_semiring has_inner star_ring
 -/
#check @submodule.coe_inner /- _inst_2: inner_product_space ↝ add_comm_monoid has_inner inner_product_space module no_meet_fake_name
 -/
#check @orthogonal_family /- _inst_2: inner_product_space ↝ has_inner module seminormed_add_comm_group
 -/
#check @has_inner.is_R_or_C_to_real /- _inst_2: inner_product_space ↝ has_inner
 -/
#check @continuous_linear_map.re_apply_inner_self /- _inst_2: inner_product_space ↝ add_comm_monoid has_inner module topological_space
 -/

-- analysis/inner_product_space/pi_L2.lean
#check @euclidean_space /- _inst_6: is_R_or_C ↝
_inst_7: fintype ↝
 -/

-- analysis/inner_product_space/projection.lean
#check @submodule.finrank_add_finrank_orthogonal /- _inst_4: finite_dimensional ↝ finite_dimensional no_meet_fake_name
 -/
#check @orthogonal_family.is_internal_iff /- _inst_5: finite_dimensional ↝ finite_dimensional no_meet_fake_name
 -/
#check @maximal_orthonormal_iff_basis_of_finite_dimensional /- _inst_4: finite_dimensional ↝ finite_dimensional no_meet_fake_name
 -/

-- analysis/inner_product_space/spectrum.lean
#check @inner_product_space.is_self_adjoint.orthogonal_supr_eigenspaces_eq_bot /- _inst_3: finite_dimensional ↝ finite_dimensional no_meet_fake_name
 -/

-- analysis/locally_convex/balanced_core_hull.lean
#check @balanced_core_aux /- _inst_1: semi_normed_ring ↝ has_norm
 -/
#check @balanced_hull /- _inst_1: semi_normed_ring ↝ has_norm
 -/
#check @subset_balanced_hull /- _inst_2: add_comm_group ↝ add_comm_monoid has_smul mul_action
_inst_3: module ↝ has_smul mul_action
 -/
#check @balanced_hull.balanced /- _inst_2: add_comm_group ↝ add_comm_monoid has_smul is_scalar_tower
_inst_3: module ↝ has_smul is_scalar_tower
 -/
#check @balanced_core_aux_empty /- _inst_1: normed_field ↝ norm_one_class semi_normed_ring
_inst_2: add_comm_group ↝ add_comm_monoid has_smul
_inst_3: module ↝ has_smul
 -/
#check @balanced_core_aux_subset /- _inst_1: normed_field ↝ mul_action norm_one_class semi_normed_ring
_inst_2: add_comm_group ↝ add_comm_monoid has_smul mul_action
_inst_3: module ↝ has_smul mul_action
 -/
#check @balanced_core_aux_balanced /- _inst_2: add_comm_group ↝ add_comm_monoid has_smul is_scalar_tower mul_action no_meet_fake_name smul_with_zero
_inst_3: module ↝ has_smul is_scalar_tower mul_action no_meet_fake_name smul_with_zero
 -/
#check @balanced_core_aux_maximal /- _inst_1: normed_field ↝ mul_action normed_division_ring
_inst_2: add_comm_group ↝ add_comm_monoid has_smul mul_action
_inst_3: module ↝ has_smul mul_action
 -/
#check @is_closed.balanced_core /- _inst_1: nontrivially_normed_field ↝ has_continuous_const_smul mul_action normed_field
_inst_5: has_continuous_smul ↝ has_continuous_const_smul
 -/

-- analysis/locally_convex/basic.lean
#check @absorbs /- _inst_1: semi_normed_ring ↝ has_norm
 -/
#check @absorbent /- _inst_1: semi_normed_ring ↝ has_norm
 -/
#check @balanced /- _inst_1: semi_normed_ring ↝ has_norm
 -/
#check @balanced.smul /- _inst_4: smul_comm_class ↝ smul_comm_class
 -/
#check @absorbs.add /- _inst_2: add_comm_group ↝ add_comm_monoid distrib_mul_action has_smul
_inst_3: module ↝ distrib_mul_action has_smul
 -/
#check @balanced.add /- _inst_2: add_comm_group ↝ add_comm_monoid distrib_mul_action has_smul
_inst_3: module ↝ distrib_mul_action has_smul
 -/
#check @balanced_zero /- _inst_2: add_comm_group ↝ add_comm_monoid distrib_mul_action has_smul
_inst_3: module ↝ distrib_mul_action has_smul
 -/
#check @balanced.smul_mono /- _inst_4: add_comm_group ↝ add_comm_monoid has_smul mul_action no_meet_fake_name smul_with_zero
_inst_5: module ↝ has_smul mul_action no_meet_fake_name smul_with_zero
 -/
#check @balanced.absorbs_self /- _inst_1: normed_field ↝ mul_action normed_division_ring
_inst_4: add_comm_group ↝ add_comm_monoid has_smul mul_action
_inst_5: module ↝ has_smul mul_action
 -/
#check @balanced.subset_smul /- _inst_1: normed_field ↝ mul_action normed_division_ring
_inst_4: add_comm_group ↝ add_comm_monoid has_smul mul_action
_inst_5: module ↝ has_smul mul_action
 -/
#check @balanced.mem_smul_iff /- _inst_1: normed_field ↝ normed_division_ring
_inst_4: add_comm_group ↝ add_comm_monoid has_smul is_scalar_tower
_inst_5: module ↝ has_smul is_scalar_tower
 -/
#check @absorbs.inter /- _inst_1: normed_field ↝ mul_action normed_division_ring
_inst_4: add_comm_group ↝ add_comm_monoid has_smul mul_action
_inst_5: module ↝ has_smul mul_action
 -/
#check @absorbent_univ /- _inst_1: normed_field ↝ mul_action normed_division_ring
_inst_4: add_comm_group ↝ add_comm_monoid has_smul mul_action
_inst_5: module ↝ has_smul mul_action
 -/
#check @absorbent_nhds_zero /- _inst_1: normed_field ↝ mul_action no_meet_fake_name normed_division_ring smul_with_zero
_inst_4: add_comm_group ↝ add_comm_monoid has_smul mul_action no_meet_fake_name smul_with_zero
_inst_5: module ↝ has_smul mul_action no_meet_fake_name smul_with_zero
 -/
#check @balanced_zero_union_interior /- _inst_1: normed_field ↝ distrib_mul_action has_continuous_const_smul mul_action no_meet_fake_name normed_division_ring smul_with_zero
_inst_4: add_comm_group ↝ add_comm_monoid distrib_mul_action has_continuous_const_smul has_smul mul_action no_meet_fake_name smul_with_zero
_inst_5: module ↝ distrib_mul_action has_continuous_const_smul has_smul mul_action no_meet_fake_name smul_with_zero
_inst_9: has_continuous_smul ↝ has_continuous_const_smul
 -/
#check @balanced.closure /- _inst_1: normed_field ↝ has_continuous_const_smul semi_normed_ring
_inst_4: add_comm_group ↝ add_comm_monoid has_continuous_const_smul has_smul
_inst_5: module ↝ has_continuous_const_smul has_smul
_inst_9: has_continuous_smul ↝ has_continuous_const_smul
 -/
#check @absorbs_zero_iff /- _inst_2: add_comm_group ↝ add_comm_monoid has_smul no_meet_fake_name no_zero_smul_divisors smul_with_zero
_inst_3: module ↝ has_smul no_meet_fake_name no_zero_smul_divisors smul_with_zero
 -/

-- analysis/locally_convex/bounded.lean
#check @bornology.is_vonN_bounded.of_topological_space_le /- _inst_2: add_comm_group ↝ add_comm_monoid has_smul
_inst_3: module ↝ has_smul
 -/
#check @bornology.is_vonN_bounded.image /- _inst_3: add_comm_group ↝ add_comm_monoid has_smul
_inst_5: add_comm_group ↝ add_comm_monoid has_smul
 -/
#check @normed_space.is_vonN_bounded_ball /- _inst_1: nontrivially_normed_field ↝ module normed_field
 -/

-- analysis/locally_convex/weak_dual.lean
#check @linear_map.to_seminorm_family /- _inst_4: add_comm_group ↝ add_comm_monoid module
 -/

-- analysis/locally_convex/with_seminorms.lean
#check @seminorm_family /- _inst_1: normed_field ↝ semi_normed_ring
_inst_3: module ↝ has_smul
 -/
#check @seminorm.is_bounded /- _inst_1: normed_field ↝ semi_normed_ring
 -/
#check @seminorm.continuous_from_bounded /- _inst_9: uniform_add_group ↝ topological_add_group
_inst_11: uniform_add_group ↝ has_continuous_add
 -/

-- analysis/normed/field/basic.lean
#check @nnnorm_one /- _inst_1: seminormed_add_comm_group ↝ has_nnnorm has_norm
 -/
#check @finset.norm_prod_le' /- _inst_2: normed_comm_ring ↝ semi_normed_comm_ring
 -/
#check @finset.norm_prod_le /- _inst_2: normed_comm_ring ↝ semi_normed_comm_ring
 -/
#check @semi_normed_top_ring /- _inst_1: non_unital_semi_normed_ring ↝ has_continuous_add has_continuous_mul has_continuous_neg non_unital_non_assoc_ring topological_space
 -/
#check @normed_field.nhds_within_is_unit_ne_bot /- _inst_1: nontrivially_normed_field ↝ filter.ne_bot group_with_zero no_meet_fake_name topological_space
 -/
#check @summable.mul_norm /- _inst_1: normed_ring ↝ non_unital_semi_normed_ring
 -/
#check @summable_norm_sum_mul_antidiagonal_of_summable_norm /- _inst_1: normed_ring ↝ non_unital_semi_normed_ring
 -/
#check @ring_hom_isometric.ids /- _inst_1: semi_normed_ring ↝ has_norm semiring
 -/

-- analysis/normed/group/basic.lean
#check @controlled_sum_of_mem_closure_range /- _inst_1: seminormed_add_comm_group ↝ add_group
 -/
#check @coe_nnnorm /- _inst_1: seminormed_add_comm_group ↝ has_nnnorm has_norm
 -/
#check @coe_comp_nnnorm /- _inst_1: seminormed_add_comm_group ↝ has_nnnorm has_norm
 -/
#check @norm_to_nnreal /- _inst_1: seminormed_add_comm_group ↝ has_nnnorm has_norm
 -/
#check @add_monoid_hom_class.bound_of_antilipschitz /- _inst_4: add_monoid_hom_class ↝ fun_like no_meet_fake_name zero_hom_class
 -/
#check @eventually_ne_of_tendsto_norm_at_top /- _inst_1: seminormed_add_comm_group ↝ has_norm
 -/
#check @normed_top_group /- _inst_1: seminormed_add_comm_group ↝ add_group topological_add_group topological_space
 -/
#check @cauchy_seq_sum_of_eventually_eq /- _inst_1: seminormed_add_comm_group ↝ add_comm_group uniform_add_group uniform_space
 -/
#check @norm_eq_zero /- _inst_1: normed_add_comm_group ↝ seminormed_add_comm_group t0_space
 -/
#check @norm_pos_iff /- _inst_1: normed_add_comm_group ↝ seminormed_add_comm_group t0_space
 -/
#check @norm_le_zero_iff /- _inst_1: normed_add_comm_group ↝ seminormed_add_comm_group t0_space
 -/

-- analysis/normed/group/hom.lean
#check @exists_pos_bound_of_bound /- _inst_2: seminormed_add_comm_group ↝ has_norm
 -/
#check @normed_add_group_hom.op_norm_zero_iff /- _inst_5: normed_add_comm_group ↝ seminormed_add_comm_group
 -/
#check @normed_add_group_hom.coe_smul /- _inst_6: distrib_mul_action ↝ has_smul has_smul
_inst_8: has_bounded_smul ↝ has_smul
 -/
#check @normed_add_group_hom.smul_apply /- _inst_6: distrib_mul_action ↝ has_smul has_smul
_inst_8: has_bounded_smul ↝ has_smul
 -/
#check @normed_add_group_hom.smul_comm_class /- _inst_6: distrib_mul_action ↝ has_smul has_smul
_inst_8: has_bounded_smul ↝ has_smul
_inst_10: distrib_mul_action ↝ has_smul has_smul
_inst_12: has_bounded_smul ↝ has_smul
 -/
#check @normed_add_group_hom.is_scalar_tower /- _inst_6: distrib_mul_action ↝ has_smul has_smul
_inst_8: has_bounded_smul ↝ has_smul
_inst_10: distrib_mul_action ↝ has_smul has_smul
_inst_12: has_bounded_smul ↝ has_smul
 -/
#check @normed_add_group_hom.is_central_scalar /- _inst_6: distrib_mul_action ↝ has_smul has_smul
 -/
#check @normed_add_group_hom.is_closed_ker /- _inst_6: normed_add_comm_group ↝ seminormed_add_comm_group t1_space
 -/
#check @controlled_closure_of_complete /- _inst_1: normed_add_comm_group ↝ seminormed_add_comm_group
 -/

-- analysis/normed/group/quotient.lean
#check @image_norm_nonempty /- _inst_1: seminormed_add_comm_group ↝ add_group add_subgroup.normal has_norm no_meet_fake_name
 -/

-- analysis/normed_space/add_torsor.lean
#check @affine_subspace.is_closed_direction_iff /- _inst_4: normed_add_comm_group ↝ add_torsor module seminormed_add_comm_group t1_space
_inst_5: metric_space ↝ add_torsor has_vsub pseudo_metric_space
_inst_9: normed_space ↝ module
 -/
#check @antilipschitz_with_line_map /- _inst_4: normed_add_comm_group ↝ add_torsor module seminormed_add_comm_group
 -/
#check @eventually_homothety_mem_of_mem_interior /- _inst_5: metric_space ↝ add_torsor has_vadd has_vsub pseudo_metric_space
 -/

-- analysis/normed_space/add_torsor_bases.lean
#check @exists_subset_affine_independent_span_eq_top_of_open /- _inst_1: normed_add_comm_group ↝ add_torsor seminormed_add_comm_group
 -/

-- analysis/normed_space/ball_action.lean
#check @is_scalar_tower_closed_ball_closed_ball_closed_ball /- _inst_6: normed_algebra ↝ has_smul normed_space
 -/
#check @is_scalar_tower_closed_ball_closed_ball_ball /- _inst_6: normed_algebra ↝ has_smul normed_space
 -/
#check @is_scalar_tower_sphere_closed_ball_closed_ball /- _inst_6: normed_algebra ↝ has_smul normed_space
 -/
#check @is_scalar_tower_sphere_closed_ball_ball /- _inst_6: normed_algebra ↝ has_smul normed_space
 -/
#check @is_scalar_tower_sphere_sphere_closed_ball /- _inst_6: normed_algebra ↝ has_smul normed_space
 -/
#check @is_scalar_tower_sphere_sphere_ball /- _inst_6: normed_algebra ↝ has_smul normed_space
 -/
#check @is_scalar_tower_sphere_sphere_sphere /- _inst_6: normed_algebra ↝ has_smul normed_space
 -/
#check @is_scalar_tower_sphere_ball_ball /- _inst_2: normed_field ↝ is_scalar_tower normed_space semi_normed_ring
_inst_6: normed_algebra ↝ has_smul is_scalar_tower normed_space
 -/
#check @is_scalar_tower_closed_ball_ball_ball /- _inst_2: normed_field ↝ is_scalar_tower normed_space semi_normed_ring
_inst_6: normed_algebra ↝ has_smul is_scalar_tower normed_space
 -/
#check @smul_comm_class_sphere_ball_ball /- _inst_2: normed_field ↝ normed_space semi_normed_ring smul_comm_class
_inst_7: normed_algebra ↝ has_smul normed_space smul_comm_class
 -/
#check @ne_neg_of_mem_sphere /- _inst_4: normed_space ↝ module no_zero_smul_divisors
 -/

-- analysis/normed_space/banach.lean
#check @continuous_linear_map.exists_approx_preimage_norm_le /- _inst_2: normed_add_comm_group ↝ has_smul module seminormed_add_comm_group
_inst_6: complete_space ↝ baire_space
 -/
#check @affine_map.is_open_map /- _inst_8: metric_space ↝ add_torsor pseudo_metric_space
_inst_10: metric_space ↝ add_torsor pseudo_metric_space
 -/

-- analysis/normed_space/banach_steinhaus.lean
#check @banach_steinhaus /- _inst_8: complete_space ↝ baire_space
 -/

-- analysis/normed_space/basic.lean
#check @eventually_nhds_norm_smul_sub_lt /- _inst_4: normed_space ↝ distrib_mul_action has_continuous_const_smul has_smul
 -/
#check @normed_space.to_module' /- _inst_4: normed_add_comm_group ↝ module seminormed_add_comm_group
_inst_5: normed_space ↝ module
 -/
#check @interior_closed_ball' /- _inst_7: nontrivial ↝ filter.ne_bot no_meet_fake_name
 -/
#check @normed_algebra.to_normed_space' /- _inst_4: normed_ring ↝ no_meet_fake_name normed_space semi_normed_ring
_inst_5: normed_algebra ↝ no_meet_fake_name normed_space
 -/
#check @norm_algebra_map /- _inst_3: normed_algebra ↝ algebra has_smul no_meet_fake_name normed_space
 -/
#check @normed_space.restrict_scalars /- _inst_3: normed_algebra ↝ no_meet_fake_name normed_space
_inst_5: normed_space ↝ no_meet_fake_name normed_space
 -/

-- analysis/normed_space/bounded_linear_maps.lean
#check @is_linear_map.with_bound /- _inst_1: nontrivially_normed_field ↝ module normed_field
 -/
#check @is_bounded_linear_map.tendsto /- _inst_1: nontrivially_normed_field ↝ module normed_field
 -/
#check @is_bounded_linear_map.is_O_id /- _inst_1: nontrivially_normed_field ↝ normed_field
 -/
#check @continuous_linear_map.map_add₂ /- _inst_4: normed_add_comm_group ↝ module module seminormed_add_comm_group
_inst_8: nontrivially_normed_field ↝ module normed_field
_inst_12: normed_add_comm_group ↝ has_continuous_add has_smul module module seminormed_add_comm_group
_inst_14: normed_space ↝ has_smul module
_inst_15: smul_comm_class ↝ module
 -/
#check @continuous_linear_map.map_zero₂ /- _inst_4: normed_add_comm_group ↝ module module seminormed_add_comm_group
_inst_8: nontrivially_normed_field ↝ module normed_field
_inst_12: normed_add_comm_group ↝ has_continuous_add has_smul module module seminormed_add_comm_group
_inst_14: normed_space ↝ has_smul module
_inst_15: smul_comm_class ↝ module
 -/
#check @continuous_linear_map.map_smulₛₗ₂ /- _inst_4: normed_add_comm_group ↝ module module mul_action seminormed_add_comm_group
_inst_8: nontrivially_normed_field ↝ distrib_mul_action has_continuous_const_smul module mul_action normed_field
_inst_12: normed_add_comm_group ↝ distrib_mul_action has_continuous_add has_continuous_const_smul has_smul module module mul_action seminormed_add_comm_group
_inst_14: normed_space ↝ distrib_mul_action has_continuous_const_smul has_smul module mul_action
 -/
#check @continuous_linear_map.map_sub₂ /- _inst_4: normed_add_comm_group ↝ module module seminormed_add_comm_group
_inst_8: nontrivially_normed_field ↝ module normed_field
_inst_12: normed_add_comm_group ↝ has_continuous_add has_smul module module seminormed_add_comm_group
_inst_14: normed_space ↝ has_smul module
_inst_15: smul_comm_class ↝ module
 -/
#check @continuous_linear_map.map_neg₂ /- _inst_4: normed_add_comm_group ↝ module module seminormed_add_comm_group
_inst_8: nontrivially_normed_field ↝ module normed_field
_inst_12: normed_add_comm_group ↝ has_continuous_add has_smul module module seminormed_add_comm_group
_inst_14: normed_space ↝ has_smul module
_inst_15: smul_comm_class ↝ module
 -/
#check @continuous_linear_map.map_smul₂ /- _inst_2: normed_add_comm_group ↝ has_smul module seminormed_add_comm_group
_inst_3: normed_space ↝ has_smul module
_inst_4: normed_add_comm_group ↝ module module seminormed_add_comm_group
_inst_6: normed_add_comm_group ↝ distrib_mul_action has_continuous_add has_continuous_const_smul has_smul module module no_meet_fake_name seminormed_add_comm_group smul_comm_class
 -/
#check @continuous_linear_map.lmul_left_right_is_bounded_bilinear /- _inst_9: normed_algebra ↝ is_scalar_tower module module no_meet_fake_name normed_space normed_space smul_comm_class smul_comm_class
 -/

-- analysis/normed_space/compact_operator.lean
#check @is_compact_operator_iff_exists_mem_nhds_image_subset_compact /- _inst_4: add_comm_monoid ↝ has_zero
 -/
#check @is_compact_operator.image_subset_compact_of_vonN_bounded /- _inst_2: semi_normed_ring ↝ semiring
 -/
#check @is_compact_operator.smul /- _inst_6: add_comm_monoid ↝ has_zero
_inst_8: add_comm_monoid ↝ add_monoid has_smul
_inst_14: distrib_mul_action ↝ has_smul
 -/
#check @is_compact_operator.add /- _inst_6: add_comm_monoid ↝ has_zero
_inst_8: add_comm_monoid ↝ add_monoid
 -/
#check @is_compact_operator.neg /- _inst_6: add_comm_monoid ↝ has_zero
_inst_12: add_comm_group ↝ has_involutive_neg
 -/
#check @is_compact_operator.sub /- _inst_13: topological_add_group ↝ has_continuous_add has_continuous_neg
 -/
#check @is_compact_operator.continuous_comp /- _inst_7: add_comm_monoid ↝ has_zero
 -/
#check @is_compact_operator.cod_restrict /- _inst_5: add_comm_monoid ↝ has_zero
 -/
#check @is_closed_set_of_is_compact_operator /- _inst_5: normed_add_comm_group ↝ has_continuous_const_smul module seminormed_add_comm_group t2_space
 -/

-- analysis/normed_space/complemented.lean
#check @continuous_linear_map.ker_closed_complemented_of_finite_dimensional_range /- _inst_5: normed_space ↝ module module no_meet_fake_name normed_space
 -/

-- analysis/normed_space/completion.lean
#check @uniform_space.completion.normed_space.to_has_uniform_continuous_const_smul /- _inst_2: normed_add_comm_group ↝ has_smul seminormed_add_comm_group
 -/

-- analysis/normed_space/conformal_linear_map.lean
#check @is_conformal_map /- _inst_4: normed_space ↝ module module
 -/

-- analysis/normed_space/dual.lean
#check @normed_space.dual /- _inst_1: nontrivially_normed_field ↝ module normed_field
_inst_3: normed_space ↝ module
 -/
#check @normed_space.dual.finite_dimensional /- _inst_6: finite_dimensional ↝ finite_dimensional
 -/

-- analysis/normed_space/exponential.lean
#check @star_exp /- _inst_7: star_ring ↝ has_star star_add_monoid star_semigroup
 -/
#check @norm_exp_series_summable_of_mem_ball /- _inst_4: normed_algebra ↝ algebra module normed_space
 -/
#check @exp_series_has_sum_exp_of_mem_ball /- _inst_4: normed_algebra ↝ algebra module normed_space
 -/
#check @has_fpower_series_on_ball_exp_of_radius_pos /- _inst_4: normed_algebra ↝ algebra normed_space
 -/
#check @continuous_on_exp /- _inst_4: normed_algebra ↝ algebra normed_space
 -/
#check @map_exp_of_mem_ball /- _inst_3: normed_ring ↝ add_monoid_hom_class algebra fun_like module monoid_hom_class no_meet_fake_name semi_normed_ring t2_space
_inst_5: normed_algebra ↝ algebra has_smul module
_inst_7: ring_hom_class ↝ add_monoid_hom_class fun_like monoid_hom_class no_meet_fake_name
 -/

-- analysis/normed_space/finite_dimension.lean
#check @affine_map.continuous_of_finite_dimensional /- _inst_2: normed_add_comm_group ↝ add_torsor has_continuous_smul module seminormed_add_comm_group t2_space
_inst_4: normed_add_comm_group ↝ add_torsor has_continuous_smul module seminormed_add_comm_group
_inst_12: metric_space ↝ add_torsor pseudo_metric_space
_inst_14: metric_space ↝ add_torsor pseudo_metric_space
 -/
#check @linear_map.exists_antilipschitz_with /- _inst_5: normed_space ↝ has_continuous_smul module module no_meet_fake_name normed_space
 -/
#check @is_open_set_of_nat_le_rank /- _inst_2: normed_add_comm_group ↝ module module normed_space seminormed_add_comm_group
 -/
#check @finite_dimensional.nonempty_continuous_linear_equiv_of_finrank_eq /- _inst_2: normed_add_comm_group ↝ has_continuous_smul module seminormed_add_comm_group t2_space
_inst_3: normed_space ↝ has_continuous_smul module
_inst_4: normed_add_comm_group ↝ has_continuous_smul module seminormed_add_comm_group t2_space
_inst_5: normed_space ↝ has_continuous_smul module
 -/
#check @basis.op_nnnorm_le /- _inst_4: normed_add_comm_group ↝ has_smul module seminormed_add_comm_group
 -/
#check @continuous_linear_map.topological_space.second_countable_topology /- _inst_14: topological_space.second_countable_topology ↝ topological_space.separable_space
 -/
#check @submodule.complete_of_finite_dimensional /- _inst_3: normed_space ↝ module module no_meet_fake_name normed_space
 -/
#check @linear_equiv.closed_embedding_of_injective /- _inst_2: normed_add_comm_group ↝ finite_dimensional has_continuous_smul module no_meet_fake_name seminormed_add_comm_group t2_space
_inst_3: normed_space ↝ finite_dimensional has_continuous_smul module no_meet_fake_name
 -/
#check @continuous_linear_map.exists_right_inverse_of_surjective /- _inst_2: normed_add_comm_group ↝ has_continuous_smul module module module seminormed_add_comm_group
_inst_3: normed_space ↝ has_continuous_smul module module module
_inst_4: normed_add_comm_group ↝ has_continuous_smul module module module seminormed_add_comm_group t2_space
_inst_5: normed_space ↝ has_continuous_smul module module module
 -/
#check @exists_mem_frontier_inf_dist_compl_eq_dist /- _inst_1: normed_add_comm_group ↝ no_meet_fake_name proper_space seminormed_add_comm_group
_inst_3: finite_dimensional ↝ no_meet_fake_name proper_space
 -/
#check @is_compact.exists_mem_frontier_inf_dist_compl_eq_dist /- _inst_3: nontrivial ↝ no_meet_fake_name noncompact_space
 -/

-- analysis/normed_space/hahn_banach/separation.lean
#check @geometric_hahn_banach_open /- _inst_1: normed_add_comm_group ↝ has_continuous_add has_continuous_const_vadd seminormed_add_comm_group
 -/

-- analysis/normed_space/is_R_or_C.lean
#check @is_R_or_C.norm_coe_norm /- _inst_2: normed_add_comm_group ↝ seminormed_add_comm_group
 -/

-- analysis/normed_space/lattice_ordered_group.lean
#check @normed_lattice_add_comm_group_topological_lattice /- _inst_1: normed_lattice_add_comm_group ↝ has_continuous_inf has_continuous_sup lattice topological_space
 -/
#check @is_closed_le_of_is_closed_nonneg /- _inst_2: ordered_add_comm_group ↝ add_group covariant_class has_le
 -/

-- analysis/normed_space/matrix_exponential.lean
#check @function.topological_ring /- _inst_1: non_unital_ring ↝ non_unital_non_assoc_ring
 -/
#check @function.algebra_ring /- _inst_2: ring ↝ semiring
 -/
#check @pi.matrix_topological_ring /- _inst_1: ring ↝ non_unital_non_assoc_ring
 -/
#check @matrix.exp_diagonal /- _inst_11: algebra ↝ algebra algebra distrib_mul_action has_smul has_smul no_meet_fake_name
 -/
#check @matrix.exp_conj_transpose /- _inst_11: algebra ↝ algebra
 -/
#check @matrix.exp_transpose /- _inst_7: algebra ↝ algebra has_smul
 -/

-- analysis/normed_space/mazur_ulam.lean
#check @isometric.midpoint_fixed /- _inst_1: normed_add_comm_group ↝ add_torsor seminormed_add_comm_group
 -/
#check @isometric.map_midpoint /- _inst_5: normed_add_comm_group ↝ add_torsor seminormed_add_comm_group
_inst_7: metric_space ↝ add_torsor pseudo_metric_space
 -/

-- analysis/normed_space/multilinear.lean
#check @multilinear_map.bound_of_shell /- _inst_5: nontrivially_normed_field ↝ module normed_field
_inst_14: normed_add_comm_group ↝ has_smul module seminormed_add_comm_group
 -/
#check @multilinear_map.norm_image_sub_le_of_bound' /- _inst_5: nontrivially_normed_field ↝ module normed_field
_inst_14: normed_add_comm_group ↝ module seminormed_add_comm_group
_inst_15: normed_space ↝ module
 -/
#check @multilinear_map.restr_norm_le /- _inst_5: nontrivially_normed_field ↝ module normed_field
_inst_14: normed_add_comm_group ↝ module seminormed_add_comm_group
_inst_15: normed_space ↝ module
_inst_16: normed_add_comm_group ↝ module seminormed_add_comm_group
_inst_17: normed_space ↝ module
 -/
#check @continuous_multilinear_map.op_norm /- _inst_5: nontrivially_normed_field ↝ module normed_field
_inst_14: normed_add_comm_group ↝ module seminormed_add_comm_group
_inst_15: normed_space ↝ module
 -/
#check @continuous_multilinear_map.bounds_bdd_below /- _inst_5: nontrivially_normed_field ↝ module normed_field
_inst_14: normed_add_comm_group ↝ module seminormed_add_comm_group
_inst_15: normed_space ↝ module
 -/
#check @continuous_multilinear_map.norm_restrict_scalars /- _inst_19: normed_algebra ↝ has_smul
 -/
#check @continuous_multilinear_map.has_continuous_const_smul /- _inst_19: module ↝ distrib_mul_action has_smul module
 -/
#check @continuous_multilinear_map.uncurry0 /- _inst_5: nontrivially_normed_field ↝ module normed_field
_inst_16: normed_add_comm_group ↝ module seminormed_add_comm_group
_inst_17: normed_space ↝ module
 -/
#check @continuous_multilinear_map.curry0 /- _inst_15: normed_space ↝ module
 -/

-- analysis/normed_space/operator_norm.lean
#check @continuous_of_linear_of_boundₛₗ /- _inst_9: normed_space ↝ has_smul module
_inst_10: normed_space ↝ has_smul module
 -/
#check @continuous_of_linear_of_bound /- _inst_9: normed_space ↝ has_smul module
_inst_11: normed_space ↝ has_smul module
 -/
#check @norm_image_of_norm_zero /- _inst_7: nontrivially_normed_field ↝ fun_like module no_meet_fake_name normed_field zero_hom_class
_inst_8: nontrivially_normed_field ↝ fun_like module no_meet_fake_name normed_field zero_hom_class
_inst_10: normed_space ↝ fun_like module no_meet_fake_name zero_hom_class
_inst_12: normed_space ↝ fun_like module no_meet_fake_name zero_hom_class
_inst_17: semilinear_map_class ↝ fun_like no_meet_fake_name zero_hom_class
 -/
#check @semilinear_map_class.bound_of_shell_semi_normed /- _inst_7: nontrivially_normed_field ↝ fun_like module normed_field
_inst_8: nontrivially_normed_field ↝ fun_like module normed_field
 -/
#check @continuous_linear_map.to_span_singleton_homothety /- _inst_7: nontrivially_normed_field ↝ module normed_field
 -/
#check @continuous_linear_map.to_span_singleton_smul' /- _inst_18: normed_space ↝ distrib_mul_action has_continuous_const_smul has_smul module
 -/
#check @continuous_linear_map.op_norm /- _inst_7: nontrivially_normed_field ↝ module normed_field
_inst_8: nontrivially_normed_field ↝ module normed_field
_inst_10: normed_space ↝ module
_inst_12: normed_space ↝ module
 -/
#check @continuous_linear_map.bounds_bdd_below /- _inst_7: nontrivially_normed_field ↝ module normed_field
_inst_8: nontrivially_normed_field ↝ module normed_field
_inst_10: normed_space ↝ module
_inst_12: normed_space ↝ module
 -/
#check @continuous_linear_map.antilipschitz_of_bound /- _inst_7: nontrivially_normed_field ↝ module normed_field
_inst_8: nontrivially_normed_field ↝ module normed_field
_inst_10: normed_space ↝ module
_inst_12: normed_space ↝ module
 -/
#check @continuous_linear_map.bound_of_antilipschitz /- _inst_7: nontrivially_normed_field ↝ module normed_field
_inst_8: nontrivially_normed_field ↝ module normed_field
_inst_10: normed_space ↝ module
_inst_12: normed_space ↝ module
 -/
#check @continuous_linear_map.op_norm_smul_le /- _inst_21: smul_comm_class ↝ module
 -/
#check @continuous_linear_map.precompR /- _inst_10: normed_space ↝ module
 -/
#check @continuous_linear_map.op_norm_lmul_right_apply /- _inst_21: normed_algebra ↝ is_scalar_tower module module no_meet_fake_name normed_space smul_comm_class
 -/
#check @continuous_linear_map.norm_restrict_scalars /- _inst_21: normed_algebra ↝ has_smul linear_map.compatible_smul
_inst_23: is_scalar_tower ↝ linear_map.compatible_smul
_inst_25: is_scalar_tower ↝ linear_map.compatible_smul
 -/
#check @continuous_linear_equiv.homothety_inverse /- _inst_7: nontrivially_normed_field ↝ module normed_field
_inst_8: nontrivially_normed_field ↝ module normed_field
_inst_10: normed_space ↝ module
_inst_12: normed_space ↝ module
 -/
#check @continuous_linear_map.bilinear_comp /- _inst_7: nontrivially_normed_field ↝ module normed_field
_inst_10: normed_space ↝ module
 -/
#check @linear_map.bound_of_shell /- _inst_2: normed_add_comm_group ↝ module seminormed_add_comm_group
 -/
#check @continuous_linear_map.op_norm_zero_iff /- _inst_1: normed_add_comm_group ↝ module seminormed_add_comm_group
 -/
#check @continuous_linear_map.homothety_norm /- _inst_2: normed_add_comm_group ↝ module seminormed_add_comm_group
 -/
#check @continuous_linear_map.uniform_embedding_of_bound /- _inst_2: normed_add_comm_group ↝ module seminormed_add_comm_group
_inst_5: nontrivially_normed_field ↝ module normed_field
_inst_6: nontrivially_normed_field ↝ module normed_field
_inst_8: normed_space ↝ module
_inst_9: normed_space ↝ module
 -/
#check @continuous_linear_map.antilipschitz_of_uniform_embedding /- _inst_1: normed_add_comm_group ↝ has_smul module mul_action seminormed_add_comm_group
 -/
#check @continuous_linear_map.tendsto_of_tendsto_pointwise_of_cauchy_seq /- _inst_2: normed_add_comm_group ↝ has_continuous_sub module seminormed_add_comm_group
 -/
#check @continuous_linear_map.is_compact_closure_image_coe_of_bounded /- _inst_2: normed_add_comm_group ↝ module module normed_space seminormed_add_comm_group t2_space
 -/
#check @continuous_linear_map.is_closed_image_coe_closed_ball /- _inst_1: normed_add_comm_group ↝ module seminormed_add_comm_group
 -/
#check @continuous_linear_map.is_compact_image_coe_closed_ball /- _inst_1: normed_add_comm_group ↝ module seminormed_add_comm_group
 -/
#check @linear_isometry.norm_to_continuous_linear_map_comp /- _inst_1: normed_add_comm_group ↝ module seminormed_add_comm_group
_inst_2: normed_add_comm_group ↝ module seminormed_add_comm_group
_inst_3: normed_add_comm_group ↝ module seminormed_add_comm_group
 -/
#check @continuous_linear_map.op_norm_comp_linear_isometry_equiv /- _inst_3: normed_add_comm_group ↝ module seminormed_add_comm_group
 -/
#check @continuous_linear_map.norm_smul_right_apply /- _inst_1: normed_add_comm_group ↝ module seminormed_add_comm_group
 -/
#check @continuous_linear_equiv.antilipschitz /- _inst_1: normed_add_comm_group ↝ module seminormed_add_comm_group
_inst_2: normed_add_comm_group ↝ module seminormed_add_comm_group
 -/
#check @continuous_linear_equiv.one_le_norm_mul_norm_symm /- _inst_2: normed_add_comm_group ↝ module seminormed_add_comm_group
 -/
#check @is_coercive /- _inst_1: normed_add_comm_group ↝ seminormed_add_comm_group
 -/

-- analysis/normed_space/pointwise.lean
#check @affinity_unit_ball /- _inst_2: normed_add_comm_group ↝ seminormed_add_comm_group
 -/

-- analysis/normed_space/riesz_lemma.lean
#check @riesz_lemma /- _inst_2: normed_add_comm_group ↝ module seminormed_add_comm_group
_inst_3: normed_space ↝ module
 -/

-- analysis/normed_space/spectrum.lean
#check @spectral_radius /- _inst_1: normed_field ↝ comm_semiring has_nnnorm
 -/
#check @spectrum.mem_resolvent_set_of_spectral_radius_lt /- _inst_2: normed_ring ↝ algebra semi_normed_ring
_inst_3: normed_algebra ↝ algebra
 -/
#check @spectrum.norm_resolvent_le_forall /- _inst_1: nontrivially_normed_field ↝ algebra mul_action normed_field normed_space
_inst_3: normed_algebra ↝ algebra has_smul mul_action normed_space
 -/
#check @spectrum.has_fpower_series_on_ball_inverse_one_sub_smul /- _inst_3: normed_algebra ↝ distrib_mul_action has_smul is_scalar_tower module module mul_action normed_space smul_comm_class
 -/
#check @spectrum.is_unit_one_sub_smul_of_lt_inv_radius /- _inst_1: nontrivially_normed_field ↝ algebra distrib_mul_action is_scalar_tower no_meet_fake_name normed_field smul_comm_class smul_with_zero
 -/

-- analysis/normed_space/star/basic.lean
#check @ring_hom_isometric.star_ring_end /- _inst_1: normed_comm_ring ↝ semi_normed_comm_ring star_add_monoid
 -/

-- analysis/seminorm.lean
#check @add_group_seminorm.is_scalar_tower /- _inst_4: is_scalar_tower ↝ has_smul
_inst_7: is_scalar_tower ↝ has_smul
 -/
#check @add_group_seminorm.coe_smul /- _inst_4: is_scalar_tower ↝ has_smul
 -/
#check @add_group_seminorm.smul_apply /- _inst_4: is_scalar_tower ↝ has_smul
 -/
#check @add_group_seminorm.sub_le /- _inst_2: add_comm_group ↝ add_group
 -/
#check @add_group_seminorm.sub_rev /- _inst_2: add_comm_group ↝ add_group
 -/
#check @add_group_seminorm.comp_add_le /- _inst_4: add_comm_group ↝ add_group
 -/
#check @seminorm.is_scalar_tower /- _inst_6: is_scalar_tower ↝ has_smul
_inst_9: is_scalar_tower ↝ has_smul
 -/
#check @seminorm.coe_smul /- _inst_6: is_scalar_tower ↝ has_smul
 -/
#check @seminorm.smul_apply /- _inst_6: is_scalar_tower ↝ has_smul
 -/
#check @seminorm.smul_comp /- _inst_10: is_scalar_tower ↝ has_smul
 -/
#check @seminorm.smul_le_smul /- _inst_5: module ↝ has_smul
 -/
#check @seminorm.comp_smul /- _inst_1: semi_normed_comm_ring ↝ distrib_mul_action has_smul no_meet_fake_name semi_normed_ring smul_comm_class
 -/
#check @seminorm.comp_smul_apply /- _inst_1: semi_normed_comm_ring ↝ distrib_mul_action has_smul no_meet_fake_name semi_normed_ring smul_comm_class
 -/
#check @seminorm.ball /- _inst_2: add_comm_group ↝ add_group
 -/
#check @seminorm.ball_zero_eq_preimage_ball /- _inst_3: module ↝ has_smul
 -/
#check @seminorm.balanced_ball_zero /- _inst_3: module ↝ has_smul
 -/
#check @seminorm.ball_smul_ball /- _inst_3: module ↝ has_smul
 -/
#check @seminorm.ball_eq_emptyset /- _inst_3: module ↝ has_smul
 -/
#check @seminorm.smul_ball_zero /- _inst_1: normed_field ↝ mul_action normed_division_ring
_inst_3: module ↝ has_smul is_scalar_tower mul_action
 -/
#check @seminorm.absorbent_ball_zero /- _inst_1: normed_field ↝ mul_action normed_division_ring
_inst_3: module ↝ has_smul mul_action
 -/
#check @seminorm.symmetric_ball_zero /- _inst_1: normed_field ↝ mul_action norm_one_class semi_normed_ring
 -/
#check @seminorm.neg_ball /- _inst_1: normed_field ↝ semi_normed_ring
 -/
#check @seminorm.smul_ball_preimage /- _inst_1: normed_field ↝ distrib_mul_action mul_action normed_division_ring
_inst_3: module ↝ distrib_mul_action has_smul mul_action
 -/
#check @seminorm.convex_on /- _inst_1: normed_field ↝ mul_action norm_one_class semi_normed_ring
_inst_4: module ↝ has_smul mul_action
 -/

-- analysis/special_functions/polynomials.lean
#check @polynomial.eventually_no_roots /- _inst_1: normed_linear_ordered_field ↝ comm_ring is_domain no_max_order preorder
 -/

-- analysis/specific_limits/basic.lean
#check @tendsto_nat_floor_mul_div_at_top /- _inst_4: floor_ring ↝ floor_semiring
 -/
#check @tendsto_nat_ceil_mul_div_at_top /- _inst_4: floor_ring ↝ floor_semiring
 -/

-- analysis/specific_limits/normed.lean
#check @normed_field.tendsto_norm_inverse_nhds_within_0_at_top /- _inst_1: normed_field ↝ normed_division_ring
 -/
#check @normed_field.tendsto_zero_smul_of_tendsto_zero_of_bounded /- _inst_2: normed_add_comm_group ↝ has_smul seminormed_add_comm_group
 -/
#check @normed_field.continuous_at_zpow /- _inst_1: nontrivially_normed_field ↝ filter.ne_bot no_meet_fake_name normed_field
 -/
#check @is_o_pow_const_const_pow_of_one_lt /- _inst_1: normed_ring ↝ semi_normed_ring
 -/
#check @tendsto_pow_at_top_nhds_0_of_norm_lt_1 /- _inst_1: normed_ring ↝ semi_normed_ring
 -/
#check @has_sum_geometric_of_norm_lt_1 /- _inst_1: normed_field ↝ has_continuous_sub normed_division_ring
 -/
#check @normed_ring.summable_geometric_of_norm_lt_1 /- _inst_1: normed_ring ↝ semi_normed_ring
 -/

-- category_theory/abelian/basic.lean
#check @category_theory.abelian.of_coimage_image_comparison_is_iso.e.category_theory.is_iso /- _inst_5: category_theory.limits.has_zero_object ↝ category_theory.is_iso no_meet_fake_name
 -/
#check @category_theory.abelian.of_coimage_image_comparison_is_iso.m.category_theory.is_iso /- _inst_5: category_theory.limits.has_zero_object ↝ category_theory.is_iso no_meet_fake_name
 -/
#check @category_theory.abelian.has_finite_biproducts /- _inst_2: category_theory.abelian ↝ category_theory.limits.has_finite_products category_theory.preadditive
 -/
#check @category_theory.abelian.has_binary_biproducts /- _inst_2: category_theory.abelian ↝ category_theory.limits.has_finite_biproducts category_theory.limits.has_zero_morphisms
 -/
#check @category_theory.abelian.has_zero_object /- _inst_2: category_theory.abelian ↝ category_theory.limits.has_finite_coproducts category_theory.limits.has_zero_morphisms
 -/
#check @category_theory.abelian.coimage_iso_image /- _inst_2: category_theory.abelian ↝ category_theory.is_iso category_theory.limits.has_cokernels category_theory.limits.has_kernels category_theory.limits.has_zero_morphisms no_meet_fake_name
 -/
#check @category_theory.abelian.has_equalizers /- _inst_2: category_theory.abelian ↝ category_theory.limits.has_kernels category_theory.preadditive
 -/
#check @category_theory.abelian.has_pullbacks /- _inst_2: category_theory.abelian ↝ category_theory.limits.has_equalizers category_theory.limits.has_finite_products
 -/
#check @category_theory.abelian.has_coequalizers /- _inst_2: category_theory.abelian ↝ category_theory.limits.has_cokernels category_theory.preadditive
 -/
#check @category_theory.abelian.has_pushouts /- _inst_2: category_theory.abelian ↝ category_theory.limits.has_coequalizers category_theory.limits.has_finite_coproducts
 -/
#check @category_theory.abelian.has_finite_limits /- _inst_2: category_theory.abelian ↝ category_theory.limits.has_equalizers category_theory.limits.has_finite_products
 -/
#check @category_theory.abelian.has_finite_colimits /- _inst_2: category_theory.abelian ↝ category_theory.limits.has_coequalizers category_theory.limits.has_finite_coproducts
 -/
#check @category_theory.abelian.epi_pullback_of_epi_g /- _inst_4: category_theory.epi ↝ category_theory.epi
 -/
#check @category_theory.abelian.epi_snd_of_is_limit /- _inst_2: category_theory.abelian ↝ category_theory.epi no_meet_fake_name
 -/
#check @category_theory.abelian.epi_fst_of_is_limit /- _inst_2: category_theory.abelian ↝ category_theory.epi no_meet_fake_name
 -/
#check @category_theory.abelian.mono_pushout_of_mono_g /- _inst_4: category_theory.mono ↝ category_theory.mono
 -/
#check @category_theory.abelian.mono_inr_of_is_colimit /- _inst_2: category_theory.abelian ↝ category_theory.mono no_meet_fake_name
 -/
#check @category_theory.abelian.mono_inl_of_is_colimit /- _inst_2: category_theory.abelian ↝ category_theory.mono no_meet_fake_name
 -/

-- category_theory/abelian/diagram_lemmas/four.lean
#check @category_theory.abelian.is_iso_of_is_iso_of_is_iso_of_is_iso_of_is_iso /- _inst_3: category_theory.is_iso ↝ category_theory.epi
_inst_4: category_theory.is_iso ↝ category_theory.epi category_theory.mono
_inst_5: category_theory.is_iso ↝ category_theory.epi category_theory.mono
_inst_6: category_theory.is_iso ↝ category_theory.mono
 -/

-- category_theory/abelian/exact.lean
#check @category_theory.abelian.exact_iff_image_eq_kernel /- _inst_2: category_theory.abelian ↝ category_theory.balanced category_theory.epi category_theory.limits.has_image category_theory.limits.has_images category_theory.limits.has_kernels category_theory.limits.has_zero_morphisms category_theory.mono no_meet_fake_name
 -/
#check @category_theory.abelian.is_equivalence.exact_iff /- _inst_5: category_theory.is_equivalence ↝ category_theory.creates_colimits_of_size category_theory.creates_limits_of_size category_theory.faithful no_meet_fake_name
 -/
#check @category_theory.abelian.category_theory.limits.cokernel.desc.category_theory.is_iso /- _inst_2: category_theory.abelian ↝ category_theory.balanced category_theory.epi category_theory.limits.has_cokernels category_theory.limits.has_images category_theory.limits.has_kernels category_theory.limits.has_zero_morphisms category_theory.mono no_meet_fake_name
 -/
#check @category_theory.abelian.cokernel.desc.inv /- _inst_2: category_theory.abelian ↝ category_theory.is_iso category_theory.limits.has_cokernels category_theory.limits.has_images category_theory.limits.has_kernels category_theory.limits.has_zero_morphisms no_meet_fake_name
_inst_3: category_theory.epi ↝ category_theory.is_iso no_meet_fake_name
 -/
#check @category_theory.abelian.category_theory.limits.kernel.lift.category_theory.is_iso /- _inst_2: category_theory.abelian ↝ category_theory.balanced category_theory.epi category_theory.limits.has_images category_theory.limits.has_kernels category_theory.mono category_theory.preadditive no_meet_fake_name
 -/
#check @category_theory.abelian.kernel.lift.inv /- _inst_2: category_theory.abelian ↝ category_theory.is_iso category_theory.limits.has_images category_theory.limits.has_kernels category_theory.limits.has_zero_morphisms no_meet_fake_name
_inst_3: category_theory.mono ↝ category_theory.is_iso no_meet_fake_name
 -/
#check @category_theory.functor.map_exact /- _inst_5: category_theory.limits.has_zero_object ↝ category_theory.functor.preserves_zero_morphisms
 -/

-- category_theory/abelian/injective_resolution.lean
#check @category_theory.InjectiveResolution.category_theory.has_injective_resolutions /- _inst_2: category_theory.abelian ↝ category_theory.has_injective_resolution category_theory.limits.has_equalizers category_theory.limits.has_images category_theory.limits.has_zero_morphisms category_theory.limits.has_zero_object no_meet_fake_name
_inst_3: category_theory.enough_injectives ↝ category_theory.has_injective_resolution no_meet_fake_name
 -/

-- category_theory/abelian/left_derived.lean
#check @category_theory.abelian.functor.preserves_exact_of_preserves_finite_colimits_of_epi /- _inst_5: category_theory.functor.additive ↝ category_theory.functor.preserves_zero_morphisms no_meet_fake_name
 -/
#check @category_theory.abelian.functor.left_derived_zero_to_self_app /- _inst_6: category_theory.enough_projectives ↝ category_theory.has_projective_resolutions
 -/
#check @category_theory.abelian.functor.left_derived_zero_to_self_app_inv /- _inst_6: category_theory.enough_projectives ↝ category_theory.has_projective_resolutions
 -/

-- category_theory/abelian/non_preadditive.lean
#check @category_theory.non_preadditive_abelian.category_theory.abelian.factor_thru_image.category_theory.epi /- _inst_2: category_theory.non_preadditive_abelian ↝ category_theory.limits.has_cokernels category_theory.limits.has_finite_products category_theory.limits.has_kernels category_theory.limits.has_zero_morphisms category_theory.limits.has_zero_object category_theory.normal_mono_category
 -/
#check @category_theory.non_preadditive_abelian.is_iso_factor_thru_image /- _inst_2: category_theory.non_preadditive_abelian ↝ category_theory.balanced category_theory.epi category_theory.limits.has_cokernels category_theory.limits.has_kernels category_theory.limits.has_zero_morphisms category_theory.mono no_meet_fake_name
_inst_3: category_theory.mono ↝ category_theory.mono no_meet_fake_name
 -/
#check @category_theory.non_preadditive_abelian.category_theory.abelian.factor_thru_coimage.category_theory.mono /- _inst_2: category_theory.non_preadditive_abelian ↝ category_theory.limits.has_cokernels category_theory.limits.has_finite_coproducts category_theory.limits.has_kernels category_theory.limits.has_zero_morphisms category_theory.limits.has_zero_object category_theory.normal_epi_category
 -/
#check @category_theory.non_preadditive_abelian.is_iso_factor_thru_coimage /- _inst_2: category_theory.non_preadditive_abelian ↝ category_theory.balanced category_theory.epi category_theory.limits.has_cokernels category_theory.limits.has_kernels category_theory.limits.has_zero_morphisms category_theory.mono no_meet_fake_name
_inst_3: category_theory.epi ↝ category_theory.epi no_meet_fake_name
 -/
#check @category_theory.non_preadditive_abelian.epi_is_cokernel_of_kernel /- _inst_3: category_theory.epi ↝ category_theory.is_iso no_meet_fake_name
 -/
#check @category_theory.non_preadditive_abelian.mono_is_kernel_of_cokernel /- _inst_3: category_theory.mono ↝ category_theory.is_iso no_meet_fake_name
 -/
#check @category_theory.non_preadditive_abelian.mono_Δ /- _inst_2: category_theory.non_preadditive_abelian ↝ category_theory.limits.has_finite_products
 -/
#check @category_theory.non_preadditive_abelian.lift_map /- _inst_2: category_theory.non_preadditive_abelian ↝ category_theory.limits.has_finite_products category_theory.limits.has_zero_morphisms
 -/

-- category_theory/abelian/projective.lean
#check @category_theory.ProjectiveResolution.category_theory.has_projective_resolutions /- _inst_2: category_theory.abelian ↝ category_theory.has_projective_resolution category_theory.limits.has_equalizers category_theory.limits.has_images category_theory.limits.has_zero_morphisms category_theory.limits.has_zero_object no_meet_fake_name
_inst_3: category_theory.enough_projectives ↝ category_theory.has_projective_resolution no_meet_fake_name
 -/

-- category_theory/abelian/pseudoelements.lean
#check @category_theory.abelian.pseudo_equal_trans /- _inst_2: category_theory.abelian ↝ category_theory.epi category_theory.epi category_theory.limits.has_pullbacks no_meet_fake_name
 -/
#check @category_theory.abelian.pseudoelement.Module.eq_range_of_pseudoequal /- _inst_4: comm_ring ↝ module no_meet_fake_name ring ring_hom_comp_triple
 -/

-- category_theory/abelian/right_derived.lean
#check @category_theory.abelian.functor.preserves_exact_of_preserves_finite_limits_of_mono /- _inst_5: category_theory.functor.additive ↝ category_theory.functor.preserves_zero_morphisms no_meet_fake_name
 -/
#check @category_theory.abelian.functor.right_derived_zero_to_self_app /- _inst_6: category_theory.enough_injectives ↝ category_theory.has_injective_resolutions
 -/
#check @category_theory.abelian.functor.right_derived_zero_to_self_app_inv /- _inst_6: category_theory.enough_injectives ↝ category_theory.has_injective_resolutions
 -/

-- category_theory/abelian/transfer.lean
#check @category_theory.abelian_of_adjunction.has_kernels /- _inst_2: category_theory.preadditive ↝ category_theory.limits.has_kernel category_theory.limits.has_kernel category_theory.limits.has_zero_morphisms no_meet_fake_name
_inst_4: category_theory.abelian ↝ category_theory.limits.has_kernel category_theory.limits.has_kernels category_theory.limits.has_zero_morphisms no_meet_fake_name
_inst_5: category_theory.functor.preserves_zero_morphisms ↝ category_theory.limits.has_kernel no_meet_fake_name
 -/
#check @category_theory.abelian_of_adjunction.has_cokernels /- _inst_2: category_theory.preadditive ↝ category_theory.limits.has_cokernel category_theory.limits.has_cokernel category_theory.limits.has_zero_morphisms no_meet_fake_name
_inst_4: category_theory.abelian ↝ category_theory.limits.has_cokernel category_theory.limits.has_cokernels category_theory.limits.has_zero_morphisms no_meet_fake_name
_inst_5: category_theory.functor.preserves_zero_morphisms ↝ category_theory.limits.has_cokernel no_meet_fake_name
 -/

-- category_theory/adjunction/lifting.lean
#check @category_theory.adjoint_square_lift /- _inst_5: category_theory.is_right_adjoint ↝ category_theory.is_right_adjoint
_inst_7: category_theory.is_right_adjoint ↝ category_theory.is_right_adjoint
 -/
#check @category_theory.monadic_adjoint_square_lift /- _inst_5: category_theory.is_right_adjoint ↝ category_theory.is_right_adjoint
_inst_7: category_theory.is_right_adjoint ↝ category_theory.is_right_adjoint
 -/

-- category_theory/adjunction/limits.lean
#check @category_theory.adjunction.has_colimit_comp_equivalence /- _inst_4: category_theory.is_equivalence ↝ category_theory.limits.preserves_colimits_of_size no_meet_fake_name
 -/
#check @category_theory.adjunction.has_colimits_of_shape_of_equivalence /- _inst_5: category_theory.limits.has_colimits_of_shape ↝ category_theory.limits.has_colimit no_meet_fake_name
 -/
#check @category_theory.adjunction.has_colimits_of_equivalence /- _inst_5: category_theory.limits.has_colimits_of_size ↝ category_theory.limits.has_colimits_of_shape
 -/
#check @category_theory.adjunction.has_limit_comp_equivalence /- _inst_4: category_theory.is_equivalence ↝ category_theory.limits.preserves_limits_of_size no_meet_fake_name
 -/
#check @category_theory.adjunction.has_limits_of_shape_of_equivalence /- _inst_5: category_theory.limits.has_limits_of_shape ↝ category_theory.limits.has_limit no_meet_fake_name
 -/
#check @category_theory.adjunction.has_limits_of_equivalence /- _inst_5: category_theory.limits.has_limits_of_size ↝ category_theory.limits.has_limits_of_shape
 -/

-- category_theory/adjunction/reflective.lean
#check @category_theory.unit_obj_eq_map_unit /- _inst_4: category_theory.reflective ↝ category_theory.faithful category_theory.full category_theory.is_right_adjoint category_theory.mono no_meet_fake_name
 -/
#check @category_theory.is_iso_unit_obj /- _inst_4: category_theory.reflective ↝ category_theory.faithful category_theory.full category_theory.is_right_adjoint
 -/
#check @category_theory.functor.ess_image.unit_is_iso /- _inst_4: category_theory.reflective ↝ category_theory.is_iso category_theory.is_right_adjoint no_meet_fake_name
 -/
#check @category_theory.unit_comp_partial_bijective_aux /- _inst_4: category_theory.reflective ↝ category_theory.faithful category_theory.full category_theory.is_right_adjoint
 -/

-- category_theory/bicategory/End.lean
#check @category_theory.End_monoidal /- _inst_1: category_theory.bicategory ↝ quiver
 -/

-- category_theory/bicategory/coherence_tactic.lean
#check @category_theory.bicategory.bicategorical_coherence.whisker_left /- _inst_2: category_theory.bicategory.lift_hom ↝ category_theory.bicategory.lift_hom no_meet_fake_name
 -/
#check @category_theory.bicategory.bicategorical_coherence.whisker_left_hom /- _inst_2: category_theory.bicategory.lift_hom ↝ category_theory.bicategory.bicategorical_coherence category_theory.bicategory.lift_hom no_meet_fake_name
 -/
#check @category_theory.bicategory.bicategorical_coherence.whisker_right /- _inst_4: category_theory.bicategory.lift_hom ↝ category_theory.bicategory.lift_hom no_meet_fake_name
 -/
#check @category_theory.bicategory.bicategorical_coherence.whisker_right_hom /- _inst_4: category_theory.bicategory.lift_hom ↝ category_theory.bicategory.bicategorical_coherence category_theory.bicategory.lift_hom no_meet_fake_name
 -/
#check @category_theory.bicategory.bicategorical_coherence.assoc_hom /- _inst_3: category_theory.bicategory.lift_hom ↝ category_theory.bicategory.bicategorical_coherence category_theory.bicategory.lift_hom no_meet_fake_name
 -/
#check @category_theory.bicategory.bicategorical_coherence.assoc'_hom /- _inst_3: category_theory.bicategory.lift_hom ↝ category_theory.bicategory.bicategorical_coherence category_theory.bicategory.lift_hom no_meet_fake_name
 -/
#check @tactic.bicategory.coherence.assoc_lift_hom₂ /- _inst_5: category_theory.bicategory.lift_hom₂ ↝
_inst_6: category_theory.bicategory.lift_hom₂ ↝
 -/

-- category_theory/bicategory/locally_discrete.lean
#check @category_theory.functor.to_oplax_functor_map /- _inst_3: category_theory.bicategory ↝ no_meet_fake_name
 -/
#check @category_theory.functor.to_oplax_functor_map_comp /- _inst_3: category_theory.bicategory ↝ no_meet_fake_name
 -/
#check @category_theory.functor.to_oplax_functor /- _inst_3: category_theory.bicategory ↝ no_meet_fake_name
 -/
#check @category_theory.functor.to_oplax_functor_map₂ /- _inst_3: category_theory.bicategory ↝ no_meet_fake_name
 -/
#check @category_theory.functor.to_oplax_functor_obj /- _inst_3: category_theory.bicategory ↝ no_meet_fake_name
 -/
#check @category_theory.functor.to_oplax_functor_map_id /- _inst_3: category_theory.bicategory ↝ no_meet_fake_name
 -/

-- category_theory/bicategory/single_obj.lean
#check @category_theory.monoidal_single_obj /- _inst_4: category_theory.monoidal_category ↝
 -/

-- category_theory/category/basic.lean
#check @category_theory.eq_whisker /- _inst_1: category_theory.category ↝ category_theory.category_struct
 -/
#check @category_theory.whisker_eq /- _inst_1: category_theory.category ↝ category_theory.category_struct
 -/
#check @category_theory.comp_ite /- _inst_1: category_theory.category ↝ category_theory.category_struct
 -/
#check @category_theory.ite_comp /- _inst_1: category_theory.category ↝ category_theory.category_struct
 -/
#check @category_theory.comp_dite /- _inst_1: category_theory.category ↝ category_theory.category_struct
 -/
#check @category_theory.dite_comp /- _inst_1: category_theory.category ↝ category_theory.category_struct
 -/

-- category_theory/category/preorder.lean
#check @category_theory.hom_of_le /- _inst_1: preorder ↝ has_le quiver
 -/
#check @category_theory.le_of_hom /- _inst_1: preorder ↝ has_le quiver
 -/

-- category_theory/category/ulift.lean
#check @category_theory.as_small /- _inst_2: category_theory.category ↝
 -/

-- category_theory/closed/ideal.lean
#check @category_theory.exponential_ideal.mk_of_iso /- _inst_5: category_theory.reflective ↝ category_theory.is_right_adjoint
 -/

-- category_theory/concrete_category/bundled_hom.lean
#check @category_theory.bundled_hom.bundled_hom_of_parent_projection /- _inst_1: category_theory.bundled_hom.parent_projection ↝
 -/

-- category_theory/core.lean
#check @category_theory.core.forget_functor_to_core /- _inst_2: category_theory.groupoid ↝ category_theory.category
 -/

-- category_theory/endomorphism.lean
#check @category_theory.End /- _inst_1: category_theory.category_struct ↝ quiver
 -/

-- category_theory/enriched/basic.lean
#check @category_theory.forget_enrichment /- _inst_9: category_theory.enriched_category ↝
 -/

-- category_theory/equivalence.lean
#check @category_theory.equivalence.fully_faithful_to_ess_image /- _inst_3: category_theory.full ↝ category_theory.full no_meet_fake_name
_inst_4: category_theory.faithful ↝ category_theory.faithful no_meet_fake_name
 -/

-- category_theory/filtered.lean
#check @category_theory.is_filtered_of_semilattice_sup_nonempty /- _inst_2: semilattice_sup ↝ category_theory.is_filtered_or_empty category_theory.small_category
 -/
#check @category_theory.is_filtered_of_directed_le_nonempty /- _inst_2: preorder ↝ category_theory.is_filtered_or_empty category_theory.small_category has_le
_inst_3: is_directed ↝ category_theory.is_filtered_or_empty
 -/
#check @category_theory.is_cofiltered_of_semilattice_inf_nonempty /- _inst_2: semilattice_inf ↝ category_theory.is_cofiltered_or_empty category_theory.small_category
 -/
#check @category_theory.is_cofiltered_of_directed_ge_nonempty /- _inst_2: preorder ↝ category_theory.is_cofiltered_or_empty category_theory.small_category has_le
_inst_3: is_directed ↝ category_theory.is_cofiltered_or_empty
 -/

-- category_theory/fin_category.lean
#check @category_theory.fin_category.obj_as_type /- _inst_3: category_theory.fin_category ↝
 -/
#check @category_theory.fin_category.as_type /- _inst_3: category_theory.fin_category ↝
 -/

-- category_theory/full_subcategory.lean
#check @category_theory.induced_category /- _inst_1: category_theory.category ↝
 -/

-- category_theory/functor/epi_mono.lean
#check @category_theory.functor.preserves_monomorphisms_comp /- _inst_4: category_theory.functor.preserves_monomorphisms ↝ category_theory.mono no_meet_fake_name
_inst_5: category_theory.functor.preserves_monomorphisms ↝ category_theory.mono no_meet_fake_name
 -/
#check @category_theory.functor.preserves_epimorphisms_comp /- _inst_4: category_theory.functor.preserves_epimorphisms ↝ category_theory.epi no_meet_fake_name
_inst_5: category_theory.functor.preserves_epimorphisms ↝ category_theory.epi no_meet_fake_name
 -/
#check @category_theory.functor.preserves_monomorphisms.of_iso /- _inst_4: category_theory.functor.preserves_monomorphisms ↝ category_theory.mono no_meet_fake_name
 -/
#check @category_theory.functor.preserves_epimorphisms.of_iso /- _inst_4: category_theory.functor.preserves_epimorphisms ↝ category_theory.epi no_meet_fake_name
 -/

-- category_theory/functor/flat.lean
#check @category_theory.flat_of_preserves_finite_limits /- _inst_3: category_theory.limits.has_finite_limits ↝ category_theory.limits.has_limit no_meet_fake_name
_inst_4: category_theory.limits.preserves_finite_limits ↝ category_theory.limits.preserves_limits_of_shape
 -/

-- category_theory/generator.lean
#check @category_theory.is_separating /- _inst_1: category_theory.category ↝ category_theory.category_struct
 -/
#check @category_theory.is_coseparating /- _inst_1: category_theory.category ↝ category_theory.category_struct
 -/

-- category_theory/graded_object.lean
#check @category_theory.graded_object_with_shift /- _inst_1: add_comm_group ↝
 -/

-- category_theory/idempotents/basic.lean
#check @category_theory.idempotents.is_idempotent_complete_of_abelian /- _inst_3: category_theory.abelian ↝ category_theory.limits.has_kernels category_theory.preadditive
 -/

-- category_theory/idempotents/karoubi.lean
#check @category_theory.idempotents.to_karoubi_is_equivalence /- _inst_2: category_theory.is_idempotent_complete ↝ category_theory.ess_surj
 -/

-- category_theory/is_connected.lean
#check @category_theory.ulift_hom.is_connected /- hc: category_theory.is_connected ↝ category_theory.is_preconnected nonempty
 -/
#check @category_theory.is_connected_of_equivalent /- _inst_4: category_theory.is_connected ↝ category_theory.is_preconnected nonempty
 -/
#check @category_theory.is_connected_op /- _inst_3: category_theory.is_connected ↝ category_theory.is_preconnected nonempty
 -/
#check @category_theory.zag /- _inst_1: category_theory.category ↝ quiver
 -/
#check @category_theory.equiv_relation /- _inst_3: category_theory.is_connected ↝ category_theory.is_preconnected nonempty
 -/
#check @category_theory.nonempty_hom_of_connected_groupoid /- _inst_4: category_theory.groupoid ↝ category_theory.category category_theory.is_iso no_meet_fake_name
 -/

-- category_theory/limits/comma.lean
#check @category_theory.comma.has_limits_of_shape /- _inst_5: category_theory.limits.has_limits_of_shape ↝ category_theory.limits.has_limit no_meet_fake_name
_inst_6: category_theory.limits.has_limits_of_shape ↝ category_theory.limits.has_limit no_meet_fake_name
 -/
#check @category_theory.comma.has_limits /- _inst_5: category_theory.limits.has_limits ↝ category_theory.limits.has_limits_of_shape
_inst_6: category_theory.limits.has_limits ↝ category_theory.limits.has_limits_of_shape
 -/
#check @category_theory.comma.has_colimits_of_shape /- _inst_5: category_theory.limits.has_colimits_of_shape ↝ category_theory.limits.has_colimit no_meet_fake_name
_inst_6: category_theory.limits.has_colimits_of_shape ↝ category_theory.limits.has_colimit no_meet_fake_name
 -/
#check @category_theory.comma.has_colimits /- _inst_5: category_theory.limits.has_colimits ↝ category_theory.limits.has_colimits_of_shape
_inst_6: category_theory.limits.has_colimits ↝ category_theory.limits.has_colimits_of_shape
 -/
#check @category_theory.arrow.has_limits_of_shape /- _inst_5: category_theory.limits.has_limits_of_shape ↝ category_theory.limits.has_limit no_meet_fake_name
 -/
#check @category_theory.arrow.has_limits /- _inst_5: category_theory.limits.has_limits ↝ category_theory.limits.has_limits_of_shape
 -/
#check @category_theory.arrow.has_colimits_of_shape /- _inst_5: category_theory.limits.has_colimits_of_shape ↝ category_theory.limits.has_colimit no_meet_fake_name
 -/
#check @category_theory.arrow.has_colimits /- _inst_5: category_theory.limits.has_colimits ↝ category_theory.limits.has_colimits_of_shape
 -/
#check @category_theory.structured_arrow.has_limits_of_shape /- _inst_5: category_theory.limits.has_limits_of_shape ↝ category_theory.limits.has_limit no_meet_fake_name
 -/
#check @category_theory.structured_arrow.has_limits /- _inst_5: category_theory.limits.has_limits ↝ category_theory.limits.has_limits_of_shape
 -/
#check @category_theory.costructured_arrow.has_colimits_of_shape /- _inst_5: category_theory.limits.has_colimits_of_shape ↝ category_theory.limits.has_colimit no_meet_fake_name
 -/
#check @category_theory.costructured_arrow.has_colimits /- _inst_5: category_theory.limits.has_colimits ↝ category_theory.limits.has_colimits_of_shape
 -/

-- category_theory/limits/constructions/over/connected.lean
#check @category_theory.over.has_connected_limits /- _inst_4: category_theory.limits.has_limits_of_shape ↝ category_theory.limits.has_limit no_meet_fake_name
 -/

-- category_theory/limits/creates.lean
#check @category_theory.has_limits_of_shape_of_has_limits_of_shape_creates_limits_of_shape /- _inst_4: category_theory.limits.has_limits_of_shape ↝ category_theory.limits.has_limit no_meet_fake_name
 -/
#check @category_theory.has_limits_of_has_limits_creates_limits /- _inst_4: category_theory.limits.has_limits_of_size ↝ category_theory.limits.has_limits_of_shape
 -/
#check @category_theory.has_colimits_of_shape_of_has_colimits_of_shape_creates_colimits_of_shape /- _inst_4: category_theory.limits.has_colimits_of_shape ↝ category_theory.limits.has_colimit no_meet_fake_name
 -/
#check @category_theory.has_colimits_of_has_colimits_creates_colimits /- _inst_4: category_theory.limits.has_colimits_of_size ↝ category_theory.limits.has_colimits_of_shape
 -/
#check @category_theory.preserves_limits_of_creates_limits_and_has_limits /- _inst_5: category_theory.limits.has_limits_of_size ↝ category_theory.limits.has_limits_of_shape
 -/
#check @category_theory.preserves_colimits_of_creates_colimits_and_has_colimits /- _inst_5: category_theory.limits.has_colimits_of_size ↝ category_theory.limits.has_colimits_of_shape
 -/

-- category_theory/limits/filtered_colimit_commutes_finite_limit.lean
#check @category_theory.limits.colim.preserves_finite_limits /- _inst_9: category_theory.limits.has_finite_limits ↝ category_theory.limits.has_limits_of_shape
 -/

-- category_theory/limits/final.lean
#check @category_theory.functor.final.colimit_iso /- _inst_3: category_theory.functor.final ↝ category_theory.is_iso category_theory.limits.has_colimit no_meet_fake_name
 -/
#check @category_theory.functor.final.cofinal_of_colimit_comp_coyoneda_iso_punit /- _inst_3: category_theory.functor.final ↝ category_theory.limits.has_colimit no_meet_fake_name
 -/
#check @category_theory.functor.initial.limit_iso /- _inst_3: category_theory.functor.initial ↝ category_theory.is_iso category_theory.limits.has_limit no_meet_fake_name
 -/

-- category_theory/limits/functor_category.lean
#check @category_theory.limits.functor_category_has_limits_of_shape /- _inst_5: category_theory.limits.has_limits_of_shape ↝ category_theory.limits.has_limit no_meet_fake_name
 -/
#check @category_theory.limits.functor_category_has_colimits_of_shape /- _inst_5: category_theory.limits.has_colimits_of_shape ↝ category_theory.limits.has_colimit no_meet_fake_name
 -/
#check @category_theory.limits.functor_category_has_limits_of_size /- _inst_5: category_theory.limits.has_limits_of_size ↝ category_theory.limits.has_limits_of_shape
 -/
#check @category_theory.limits.functor_category_has_colimits_of_size /- _inst_5: category_theory.limits.has_colimits_of_size ↝ category_theory.limits.has_colimits_of_shape
 -/
#check @category_theory.limits.evaluation_preserves_limits /- _inst_5: category_theory.limits.has_limits ↝ category_theory.limits.has_limits_of_shape
 -/
#check @category_theory.limits.evaluation_preserves_colimits /- _inst_5: category_theory.limits.has_colimits ↝ category_theory.limits.has_colimits_of_shape
 -/

-- category_theory/limits/has_limits.lean
#check @category_theory.limits.limit.map_pre' /- _inst_4: category_theory.limits.has_limits_of_shape ↝ category_theory.limits.has_limit no_meet_fake_name
 -/
#check @category_theory.limits.limit.map_post /- _inst_4: category_theory.limits.has_limits_of_shape ↝ category_theory.limits.has_limit no_meet_fake_name
_inst_6: category_theory.limits.has_limits_of_shape ↝ category_theory.limits.has_limit no_meet_fake_name
 -/
#check @category_theory.limits.has_limits_of_shape_of_equivalence /- _inst_5: category_theory.limits.has_limits_of_shape ↝ category_theory.limits.has_limit no_meet_fake_name
 -/
#check @category_theory.limits.colimit.pre_map' /- _inst_4: category_theory.limits.has_colimits_of_shape ↝ category_theory.limits.has_colimit no_meet_fake_name
 -/
#check @category_theory.limits.has_colimits_of_shape_of_equivalence /- _inst_5: category_theory.limits.has_colimits_of_shape ↝ category_theory.limits.has_colimit no_meet_fake_name
 -/

-- category_theory/limits/lattice.lean
#check @category_theory.limits.complete_lattice.category_theory.limits.has_binary_products /- _inst_3: semilattice_inf ↝ category_theory.limits.has_finite_limits category_theory.limits.has_limit category_theory.limits.has_limits_of_shape category_theory.small_category has_le no_meet_fake_name
_inst_4: order_top ↝ category_theory.limits.has_finite_limits
 -/
#check @category_theory.limits.complete_lattice.category_theory.limits.has_binary_coproducts /- _inst_3: semilattice_sup ↝ category_theory.limits.has_colimit category_theory.limits.has_colimits_of_shape category_theory.limits.has_finite_colimits category_theory.small_category has_le no_meet_fake_name
_inst_4: order_bot ↝ category_theory.limits.has_finite_colimits
 -/

-- category_theory/limits/over.lean
#check @category_theory.over.category_theory.limits.has_colimits_of_shape /- _inst_3: category_theory.limits.has_colimits_of_shape ↝ category_theory.limits.has_colimit no_meet_fake_name
 -/
#check @category_theory.over.category_theory.limits.has_colimits /- _inst_3: category_theory.limits.has_colimits ↝ category_theory.limits.has_colimits_of_shape
 -/
#check @category_theory.under.category_theory.limits.has_limits_of_shape /- _inst_3: category_theory.limits.has_limits_of_shape ↝ category_theory.limits.has_limit no_meet_fake_name
 -/
#check @category_theory.under.category_theory.limits.has_limits /- _inst_3: category_theory.limits.has_limits ↝ category_theory.limits.has_limits_of_shape
 -/

-- category_theory/limits/preserves/basic.lean
#check @category_theory.limits.comp_reflects_limits_of_shape /- _inst_4: category_theory.limits.reflects_limits_of_shape ↝ category_theory.limits.reflects_limit no_meet_fake_name
 -/
#check @category_theory.limits.comp_reflects_limits /- _inst_4: category_theory.limits.reflects_limits_of_size ↝ category_theory.limits.reflects_limits_of_shape no_meet_fake_name
_inst_5: category_theory.limits.reflects_limits_of_size ↝ category_theory.limits.reflects_limits_of_shape no_meet_fake_name
 -/
#check @category_theory.limits.comp_reflects_colimits_of_shape /- _inst_4: category_theory.limits.reflects_colimits_of_shape ↝ category_theory.limits.reflects_colimit no_meet_fake_name
 -/
#check @category_theory.limits.comp_reflects_colimits /- _inst_4: category_theory.limits.reflects_colimits_of_size ↝ category_theory.limits.reflects_colimits_of_shape no_meet_fake_name
_inst_5: category_theory.limits.reflects_colimits_of_size ↝ category_theory.limits.reflects_colimits_of_shape no_meet_fake_name
 -/
#check @category_theory.limits.preserves_limits_of_reflects_of_preserves /- _inst_5: category_theory.limits.reflects_limits_of_size ↝ category_theory.limits.reflects_limits_of_shape no_meet_fake_name
 -/
#check @category_theory.limits.reflects_limits_of_shape_of_nat_iso /- _inst_4: category_theory.limits.reflects_limits_of_shape ↝ category_theory.limits.reflects_limit
 -/
#check @category_theory.limits.reflects_limits_of_nat_iso /- _inst_4: category_theory.limits.reflects_limits_of_size ↝ category_theory.limits.reflects_limits_of_shape no_meet_fake_name
 -/
#check @category_theory.limits.reflects_limits_of_shape_of_reflects_isomorphisms /- _inst_5: category_theory.limits.has_limits_of_shape ↝ category_theory.limits.has_limit no_meet_fake_name
 -/
#check @category_theory.limits.reflects_limits_of_reflects_isomorphisms /- _inst_5: category_theory.limits.has_limits_of_size ↝ category_theory.limits.has_limits_of_shape
 -/
#check @category_theory.limits.preserves_colimits_of_reflects_of_preserves /- _inst_5: category_theory.limits.reflects_colimits_of_size ↝ category_theory.limits.reflects_colimits_of_shape no_meet_fake_name
 -/
#check @category_theory.limits.reflects_colimits_of_shape_of_nat_iso /- _inst_4: category_theory.limits.reflects_colimits_of_shape ↝ category_theory.limits.reflects_colimit
 -/
#check @category_theory.limits.reflects_colimits_of_nat_iso /- _inst_4: category_theory.limits.reflects_colimits_of_size ↝ category_theory.limits.reflects_colimits_of_shape no_meet_fake_name
 -/
#check @category_theory.limits.reflects_colimits_of_shape_of_reflects_isomorphisms /- _inst_5: category_theory.limits.has_colimits_of_shape ↝ category_theory.limits.has_colimit no_meet_fake_name
 -/
#check @category_theory.limits.reflects_colimits_of_reflects_isomorphisms /- _inst_5: category_theory.limits.has_colimits_of_size ↝ category_theory.limits.has_colimits_of_shape
 -/

-- category_theory/limits/preserves/filtered.lean
#check @category_theory.limits.comp_preserves_filtered_colimits /- _inst_5: category_theory.limits.preserves_filtered_colimits ↝ category_theory.limits.preserves_colimits_of_shape no_meet_fake_name
_inst_6: category_theory.limits.preserves_filtered_colimits ↝ category_theory.limits.preserves_colimits_of_shape no_meet_fake_name
 -/
#check @category_theory.limits.comp_preserves_cofiltered_limits /- _inst_5: category_theory.limits.preserves_cofiltered_limits ↝ category_theory.limits.preserves_limits_of_shape no_meet_fake_name
_inst_6: category_theory.limits.preserves_cofiltered_limits ↝ category_theory.limits.preserves_limits_of_shape no_meet_fake_name
 -/

-- category_theory/limits/preserves/finite.lean
#check @category_theory.limits.preserves_limits.preserves_finite_limits /- _inst_5: category_theory.limits.preserves_limits ↝ category_theory.limits.preserves_finite_limits no_meet_fake_name
 -/

-- category_theory/limits/preserves/functor_category.lean
#check @category_theory.functor_category.prod_preserves_colimits /- _inst_5: category_theory.limits.has_colimits ↝ category_theory.limits.has_colimits_of_shape
 -/
#check @category_theory.whiskering_left_preserves_limits /- _inst_4: category_theory.limits.has_limits ↝ category_theory.limits.has_limits_of_shape
 -/
#check @category_theory.whiskering_right_preserves_limits /- _inst_7: category_theory.limits.has_limits ↝ category_theory.limits.has_limits_of_shape
 -/

-- category_theory/limits/preserves/shapes/biproducts.lean
#check @category_theory.limits.preserves_biproducts_shrink /- hp: category_theory.limits.preserves_biproducts ↝ category_theory.limits.preserves_biproducts_of_shape
 -/
#check @category_theory.functor.section_biproduct_comparison /- _inst_7: category_theory.functor.preserves_zero_morphisms ↝ category_theory.split_epi no_meet_fake_name
 -/
#check @category_theory.functor.retraction_biproduct_comparison' /- _inst_7: category_theory.functor.preserves_zero_morphisms ↝ category_theory.split_mono no_meet_fake_name
 -/
#check @category_theory.functor.section_biprod_comparison /- _inst_7: category_theory.functor.preserves_zero_morphisms ↝ category_theory.split_epi no_meet_fake_name
 -/
#check @category_theory.functor.retraction_biprod_comparison' /- _inst_7: category_theory.functor.preserves_zero_morphisms ↝ category_theory.split_mono no_meet_fake_name
 -/
#check @category_theory.limits.preserves_products_of_shape_of_preserves_biproducts_of_shape /- _inst_7: category_theory.limits.preserves_biproducts_of_shape ↝ category_theory.limits.preserves_biproduct no_meet_fake_name
 -/
#check @category_theory.limits.preserves_coproducts_of_shape_of_preserves_biproducts_of_shape /- _inst_7: category_theory.limits.preserves_biproducts_of_shape ↝ category_theory.limits.preserves_biproduct no_meet_fake_name
 -/

-- category_theory/limits/shapes/biproducts.lean
#check @category_theory.limits.has_finite_products_of_has_finite_biproducts /- _inst_3: category_theory.limits.has_finite_biproducts ↝ category_theory.limits.has_biproduct no_meet_fake_name
 -/
#check @category_theory.limits.has_finite_coproducts_of_has_finite_biproducts /- _inst_3: category_theory.limits.has_finite_biproducts ↝ category_theory.limits.has_biproduct no_meet_fake_name
 -/
#check @category_theory.limits.has_zero_object_of_has_finite_biproducts /- _inst_3: category_theory.limits.has_finite_biproducts ↝ category_theory.limits.has_biproducts_of_shape no_meet_fake_name
 -/
#check @category_theory.limits.has_binary_biproducts_of_finite_biproducts /- _inst_3: category_theory.limits.has_finite_biproducts ↝ category_theory.limits.has_biproducts_of_shape no_meet_fake_name
 -/
#check @category_theory.limits.has_binary_products_of_has_binary_biproducts /- _inst_3: category_theory.limits.has_binary_biproducts ↝ category_theory.limits.has_binary_biproduct
 -/
#check @category_theory.limits.has_binary_coproducts_of_has_binary_biproducts /- _inst_3: category_theory.limits.has_binary_biproducts ↝ category_theory.limits.has_binary_biproduct
 -/
#check @category_theory.limits.biprod.symmetry' /- _inst_3: category_theory.limits.has_binary_biproducts ↝ category_theory.limits.has_binary_biproduct
 -/
#check @category_theory.limits.biproduct.map_eq /- _inst_5: category_theory.limits.has_finite_biproducts ↝ category_theory.limits.has_biproduct no_meet_fake_name
 -/
#check @category_theory.limits.biproduct.matrix_map /- _inst_2: category_theory.preadditive ↝ category_theory.limits.has_zero_morphisms
 -/
#check @category_theory.limits.biproduct.map_matrix /- _inst_2: category_theory.preadditive ↝ category_theory.limits.has_zero_morphisms
 -/
#check @category_theory.limits.inl_of_is_limit /- _inst_2: category_theory.preadditive ↝ category_theory.limits.has_zero_morphisms
 -/
#check @category_theory.limits.inr_of_is_limit /- _inst_2: category_theory.preadditive ↝ category_theory.limits.has_zero_morphisms
 -/
#check @category_theory.limits.fst_of_is_colimit /- _inst_2: category_theory.preadditive ↝ category_theory.limits.has_zero_morphisms
 -/
#check @category_theory.limits.snd_of_is_colimit /- _inst_2: category_theory.preadditive ↝ category_theory.limits.has_zero_morphisms
 -/
#check @category_theory.limits.biprod.map_eq /- _inst_5: category_theory.limits.has_binary_biproducts ↝ category_theory.limits.has_binary_biproduct
 -/
#check @category_theory.subsingleton_preadditive_of_has_binary_biproducts /- _inst_3: category_theory.limits.has_binary_biproducts ↝ category_theory.limits.has_binary_biproduct
 -/
#check @category_theory.indecomposable /- _inst_3: category_theory.limits.has_binary_biproducts ↝ category_theory.limits.has_binary_biproduct
 -/

-- category_theory/limits/shapes/disjoint_coproduct.lean
#check @category_theory.limits.initial_mono_class_of_disjoint_coproducts /- _inst_2: category_theory.limits.coproducts_disjoint ↝ category_theory.limits.coproduct_disjoint
 -/

-- category_theory/limits/shapes/finite_limits.lean
#check @category_theory.limits.has_finite_limits_of_has_limits /- _inst_2: category_theory.limits.has_limits ↝ category_theory.limits.has_finite_limits
 -/

-- category_theory/limits/shapes/functor_category.lean
#check @category_theory.limits.functor_category_has_finite_limits /- _inst_3: category_theory.limits.has_finite_limits ↝ category_theory.limits.has_limits_of_shape
 -/
#check @category_theory.limits.functor_category_has_finite_colimits /- _inst_3: category_theory.limits.has_finite_colimits ↝ category_theory.limits.has_colimits_of_shape
 -/

-- category_theory/limits/shapes/images.lean
#check @category_theory.limits.image.map_hom_mk'_ι /- _inst_5: category_theory.limits.has_image ↝ category_theory.limits.has_image no_meet_fake_name
_inst_6: category_theory.limits.has_image ↝ category_theory.limits.has_image no_meet_fake_name
 -/

-- category_theory/limits/shapes/normal_mono/equalizers.lean
#check @category_theory.normal_mono_category.epi_of_zero_cokernel /- _inst_3: category_theory.limits.has_finite_products ↝ category_theory.limits.has_equalizers
_inst_4: category_theory.limits.has_kernels ↝ category_theory.limits.has_equalizers
 -/
#check @category_theory.normal_epi_category.mono_of_zero_kernel /- _inst_3: category_theory.limits.has_finite_coproducts ↝ category_theory.limits.has_coequalizers
_inst_4: category_theory.limits.has_cokernels ↝ category_theory.limits.has_coequalizers
 -/

-- category_theory/limits/shapes/reflexive.lean
#check @category_theory.limits.has_coequalizer_of_common_section /- _inst_3: category_theory.limits.has_reflexive_coequalizers ↝ category_theory.limits.has_coequalizer
 -/
#check @category_theory.limits.has_equalizer_of_common_retraction /- _inst_3: category_theory.limits.has_coreflexive_equalizers ↝ category_theory.limits.has_equalizer
 -/

-- category_theory/limits/shapes/regular_mono.lean
#check @category_theory.is_iso_of_regular_mono_of_epi /- _inst_2: category_theory.regular_mono ↝ category_theory.strong_mono no_meet_fake_name
 -/
#check @category_theory.is_iso_of_regular_epi_of_mono /- _inst_2: category_theory.regular_epi ↝ category_theory.strong_epi no_meet_fake_name
 -/

-- category_theory/limits/shapes/strong_epi.lean
#check @category_theory.strong_epi_comp /- _inst_2: category_theory.strong_epi ↝ category_theory.arrow.has_lift category_theory.epi no_meet_fake_name
_inst_3: category_theory.strong_epi ↝ category_theory.arrow.has_lift category_theory.epi no_meet_fake_name
 -/
#check @category_theory.strong_mono_comp /- _inst_2: category_theory.strong_mono ↝ category_theory.arrow.has_lift category_theory.mono no_meet_fake_name
_inst_3: category_theory.strong_mono ↝ category_theory.arrow.has_lift category_theory.mono no_meet_fake_name
 -/
#check @category_theory.is_iso_of_mono_of_strong_epi /- _inst_3: category_theory.strong_epi ↝ category_theory.arrow.has_lift no_meet_fake_name
 -/
#check @category_theory.is_iso_of_epi_of_strong_mono /- _inst_3: category_theory.strong_mono ↝ category_theory.arrow.has_lift no_meet_fake_name
 -/

-- category_theory/monad/adjunction.lean
#check @category_theory.μ_iso_of_reflective /- _inst_3: category_theory.reflective ↝ category_theory.faithful category_theory.full category_theory.is_right_adjoint
 -/
#check @category_theory.reflective.comparison_ess_surj /- _inst_3: category_theory.reflective ↝ category_theory.is_iso category_theory.is_right_adjoint no_meet_fake_name
 -/

-- category_theory/monad/limits.lean
#check @category_theory.comp_comparison_forget_has_limit /- _inst_4: category_theory.monadic_right_adjoint ↝ category_theory.is_right_adjoint
 -/
#check @category_theory.comp_comparison_has_limit /- _inst_4: category_theory.monadic_right_adjoint ↝ category_theory.is_right_adjoint category_theory.limits.has_limit no_meet_fake_name
_inst_5: category_theory.limits.has_limit ↝ category_theory.limits.has_limit no_meet_fake_name
 -/
#check @category_theory.monadic_creates_limits /- _inst_4: category_theory.monadic_right_adjoint ↝ category_theory.is_equivalence category_theory.is_right_adjoint
 -/
#check @category_theory.monadic_creates_colimit_of_preserves_colimit /- _inst_4: category_theory.monadic_right_adjoint ↝ category_theory.is_equivalence category_theory.is_right_adjoint
 -/
#check @category_theory.has_limit_of_reflective /- _inst_5: category_theory.reflective ↝ category_theory.monadic_right_adjoint
 -/
#check @category_theory.has_limits_of_shape_of_reflective /- _inst_4: category_theory.limits.has_limits_of_shape ↝ category_theory.limits.has_limit no_meet_fake_name
 -/
#check @category_theory.has_limits_of_reflective /- _inst_4: category_theory.limits.has_limits_of_size ↝ category_theory.limits.has_limits_of_shape
 -/
#check @category_theory.has_colimits_of_shape_of_reflective /- _inst_4: category_theory.reflective ↝ category_theory.faithful category_theory.full category_theory.is_right_adjoint
_inst_5: category_theory.limits.has_colimits_of_shape ↝ category_theory.limits.has_colimit no_meet_fake_name
 -/
#check @category_theory.has_colimits_of_reflective /- _inst_5: category_theory.limits.has_colimits_of_size ↝ category_theory.limits.has_colimits_of_shape
 -/

-- category_theory/monoidal/coherence.lean
#check @category_theory.monoidal_category.monoidal_coherence.tensor_hom /- _inst_3: category_theory.monoidal_category.lift_obj ↝ category_theory.monoidal_category.lift_obj category_theory.monoidal_category.monoidal_coherence no_meet_fake_name
 -/
#check @category_theory.monoidal_category.monoidal_coherence.assoc_hom /- _inst_5: category_theory.monoidal_category.lift_obj ↝ category_theory.monoidal_category.lift_obj category_theory.monoidal_category.monoidal_coherence no_meet_fake_name
 -/
#check @category_theory.monoidal_category.monoidal_coherence.assoc'_hom /- _inst_5: category_theory.monoidal_category.lift_obj ↝ category_theory.monoidal_category.lift_obj category_theory.monoidal_category.monoidal_coherence no_meet_fake_name
 -/
#check @tactic.coherence.assoc_lift_hom /- _inst_6: category_theory.monoidal_category.lift_hom ↝
_inst_7: category_theory.monoidal_category.lift_hom ↝
 -/

-- category_theory/monoidal/preadditive.lean
#check @category_theory.tensor_sum /- _inst_4: category_theory.monoidal_preadditive ↝ category_theory.functor.additive no_meet_fake_name
 -/
#check @category_theory.sum_tensor /- _inst_4: category_theory.monoidal_preadditive ↝ category_theory.functor.additive no_meet_fake_name
 -/

-- category_theory/monoidal/rigid/basic.lean
#check @category_theory.monoidal_closed_of_left_rigid_category /- _inst_5: category_theory.left_rigid_category ↝ category_theory.closed no_meet_fake_name
 -/

-- category_theory/monoidal/rigid/functor_category.lean
#check @category_theory.monoidal.rigid_functor_category /- _inst_4: category_theory.rigid_category ↝ category_theory.left_rigid_category category_theory.right_rigid_category
 -/

-- category_theory/monoidal/rigid/of_equivalence.lean
#check @category_theory.left_rigid_category_of_equivalence /- _inst_6: category_theory.left_rigid_category ↝ category_theory.has_left_dual
 -/
#check @category_theory.right_rigid_category_of_equivalence /- _inst_6: category_theory.right_rigid_category ↝ category_theory.has_right_dual
 -/
#check @category_theory.rigid_category_of_equivalence /- _inst_6: category_theory.rigid_category ↝ category_theory.has_left_dual category_theory.has_right_dual
 -/

-- category_theory/monoidal/transport.lean
#check @category_theory.monoidal.transported /- _inst_2: category_theory.monoidal_category ↝
 -/

-- category_theory/morphism_property.lean
#check @category_theory.morphism_property /- _inst_1: category_theory.category ↝ quiver
 -/

-- category_theory/preadditive/additive_functor.lean
#check @category_theory.functor.additive_of_preserves_binary_biproducts /- _inst_5: category_theory.limits.has_binary_biproducts ↝ category_theory.limits.has_binary_biproduct category_theory.limits.has_binary_biproduct no_meet_fake_name
 -/

-- category_theory/preadditive/biproducts.lean
#check @category_theory.is_iso_left_of_is_iso_biprod_map /- _inst_3: category_theory.limits.has_binary_biproducts ↝ category_theory.limits.has_binary_biproduct
 -/
#check @category_theory.biprod.column_nonzero_of_iso /- _inst_3: category_theory.limits.has_binary_biproducts ↝ category_theory.limits.has_binary_biproduct
 -/

-- category_theory/preadditive/default.lean
#check @category_theory.preadditive.is_iso.comp_left_eq_zero /- _inst_2: category_theory.preadditive ↝ category_theory.limits.has_zero_morphisms
 -/
#check @category_theory.preadditive.is_iso.comp_right_eq_zero /- _inst_2: category_theory.preadditive ↝ category_theory.limits.has_zero_morphisms
 -/

-- category_theory/preadditive/functor_category.lean
#check @category_theory.nat_trans.app_zero /- _inst_3: category_theory.preadditive ↝ category_theory.limits.has_zero_morphisms
 -/

-- category_theory/preadditive/hom_orthogonal.lean
#check @category_theory.hom_orthogonal /- _inst_1: category_theory.category ↝ quiver
 -/

-- category_theory/preadditive/of_biproducts.lean
#check @category_theory.semiadditive_of_binary_biproducts.left_add /- _inst_3: category_theory.limits.has_binary_biproducts ↝ category_theory.limits.has_binary_biproduct
 -/
#check @category_theory.semiadditive_of_binary_biproducts.right_add /- _inst_3: category_theory.limits.has_binary_biproducts ↝ category_theory.limits.has_binary_biproduct
 -/

-- category_theory/preadditive/opposite.lean
#check @category_theory.unop_zero /- _inst_2: category_theory.preadditive ↝ category_theory.limits.has_zero_morphisms
 -/
#check @category_theory.op_zero /- _inst_2: category_theory.preadditive ↝ category_theory.limits.has_zero_morphisms
 -/

-- category_theory/shift.lean
#check @category_theory.shift_functor_inv /- _inst_2: add_group ↝ add_monoid category_theory.is_equivalence has_neg no_meet_fake_name
 -/
#check @category_theory.shift_zero_eq_zero /- _inst_2: add_group ↝ add_monoid category_theory.full no_meet_fake_name
 -/
#check @category_theory.has_shift_of_fully_faithful_comm /- _inst_5: category_theory.full ↝
_inst_6: category_theory.faithful ↝
 -/

-- category_theory/simple.lean
#check @category_theory.simple_of_cosimple /- _inst_2: category_theory.abelian ↝ category_theory.balanced category_theory.limits.has_cokernels category_theory.limits.has_zero_object category_theory.preadditive
 -/
#check @category_theory.is_iso_of_epi_of_nonzero /- _inst_2: category_theory.abelian ↝ category_theory.balanced category_theory.limits.has_kernels category_theory.preadditive
 -/
#check @category_theory.biprod.is_iso_inl_iff_is_zero /- _inst_3: category_theory.limits.has_binary_biproducts ↝ category_theory.limits.has_binary_biproduct
 -/

-- category_theory/sites/dense_subsite.lean
#check @category_theory.cover_dense.types.pushforward_family /- _inst_5: category_theory.full ↝
 -/

-- category_theory/sites/grothendieck.lean
#check @category_theory.grothendieck_topology.right_ore_condition /- _inst_2: category_theory.category ↝ category_theory.category_struct
 -/

-- category_theory/sites/left_exact.lean
#check @category_theory.grothendieck_topology.diagram_functor.category_theory.limits.preserves_limits /- _inst_4: category_theory.limits.has_limits ↝ category_theory.limits.has_limits_of_shape
 -/
#check @category_theory.grothendieck_topology.plus_functor.category_theory.limits.preserves_finite_limits /- _inst_7: category_theory.limits.has_finite_limits ↝ category_theory.limits.has_limits_of_shape
 -/
#check @category_theory.presheaf_to_Sheaf.limits.preserves_finite_limits /- _inst_12: category_theory.limits.has_finite_limits ↝ category_theory.limits.has_limits_of_shape
 -/

-- category_theory/sites/limits.lean
#check @category_theory.Sheaf.category_theory.Sheaf_to_presheaf.category_theory.creates_limits /- _inst_4: category_theory.limits.has_limits ↝ category_theory.limits.has_limits_of_shape
 -/
#check @category_theory.Sheaf.category_theory.limits.has_colimits /- _inst_6: category_theory.limits.preserves_limits ↝ category_theory.limits.has_colimits_of_shape
_inst_9: category_theory.reflects_isomorphisms ↝ category_theory.limits.has_colimits_of_shape
_inst_10: category_theory.limits.has_colimits ↝ category_theory.limits.has_colimits_of_shape
 -/

-- category_theory/sites/sieves.lean
#check @category_theory.presieve /- _inst_1: category_theory.category ↝ quiver
 -/

-- category_theory/subobject/limits.lean
#check @category_theory.limits.image_subobject_comp_le_epi_of_epi /- _inst_3: category_theory.limits.has_equalizers ↝ category_theory.epi no_meet_fake_name
_inst_4: category_theory.epi ↝ category_theory.epi no_meet_fake_name
 -/
#check @category_theory.limits.image_subobject_iso_comp /- _inst_3: category_theory.limits.has_equalizers ↝ category_theory.is_iso category_theory.limits.has_image no_meet_fake_name
_inst_4: category_theory.is_iso ↝ category_theory.is_iso category_theory.limits.has_image no_meet_fake_name
 -/

-- category_theory/subterminal.lean
#check @category_theory.is_subterminal /- _inst_1: category_theory.category ↝ quiver
 -/

-- combinatorics/additive/salem_spencer.lean
#check @mul_salem_spencer /- _inst_1: monoid ↝ has_mul
 -/
#check @add_salem_spencer /- _inst_1: add_monoid ↝ has_add
 -/
#check @add_salem_spencer.image /- _inst_1: add_comm_monoid ↝ add_monoid fun_like
_inst_2: add_comm_monoid ↝ add_monoid fun_like
 -/
#check @mul_salem_spencer.image /- _inst_1: comm_monoid ↝ fun_like monoid
_inst_2: comm_monoid ↝ fun_like monoid
 -/
#check @mul_salem_spencer_insert_of_lt /- _inst_1: ordered_cancel_comm_monoid ↝ cancel_comm_monoid covariant_class covariant_class preorder
 -/
#check @add_salem_spencer_insert_of_lt /- _inst_1: ordered_cancel_add_comm_monoid ↝ add_cancel_comm_monoid covariant_class covariant_class preorder
 -/
#check @add_salem_spencer_frontier /- _inst_1: linear_ordered_field ↝ distrib_mul_action linear_ordered_semifield mul_action
 -/

-- combinatorics/configuration.lean
#check @configuration.projective_plane.card_points_eq_card_lines /- _inst_4: configuration.projective_plane ↝ no_meet_fake_name
 -/
#check @configuration.projective_plane.line_count_eq_line_count /- _inst_4: configuration.projective_plane ↝ no_meet_fake_name
 -/
#check @configuration.projective_plane.line_count_eq_point_count /- _inst_4: configuration.projective_plane ↝ no_meet_fake_name
 -/

-- combinatorics/hindman.lean
#check @ultrafilter.continuous_mul_left /- _inst_1: semigroup ↝ has_mul
 -/
#check @ultrafilter.continuous_add_left /- _inst_1: add_semigroup ↝ has_add
 -/

-- combinatorics/set_family/compression/uv.lean
#check @uv.compress /- _inst_1: generalized_boolean_algebra ↝ has_sdiff has_sup order_bot semilattice_inf
 -/

-- combinatorics/set_family/intersecting.lean
#check @set.intersecting.is_max_iff_card_eq /- _inst_1: boolean_algebra ↝ no_meet_fake_name
 -/

-- combinatorics/set_family/lym.lean
#check @finset.card_div_choose_le_card_shadow_div_choose /- _inst_1: linear_ordered_field ↝ linear_ordered_semifield
 -/

-- combinatorics/simple_graph/adj_matrix.lean
#check @simple_graph.adj_matrix_mul_vec_const_apply /- _inst_3: semiring ↝ non_assoc_semiring
 -/
#check @matrix.is_adj_matrix.adj_matrix_to_graph_eq /- _inst_3: decidable_eq ↝ decidable_rel no_meet_fake_name
 -/

-- combinatorics/simple_graph/basic.lean
#check @simple_graph.dart.fintype /- _inst_2: decidable_rel ↝ decidable_pred no_meet_fake_name
 -/
#check @simple_graph.decidable_mem_common_neighbors /- _inst_1: decidable_rel ↝ decidable_pred no_meet_fake_name
 -/
#check @simple_graph.is_regular_of_degree.compl /- _inst_3: decidable_eq ↝ decidable_rel no_meet_fake_name
_inst_4: decidable_rel ↝ decidable_pred decidable_rel no_meet_fake_name
 -/

-- combinatorics/simple_graph/inc_matrix.lean
#check @simple_graph.inc_matrix_mul_transpose_apply_of_adj /- _inst_2: semiring ↝ non_assoc_semiring
 -/

-- combinatorics/simple_graph/regularity/uniform.lean
#check @simple_graph.is_uniform /- _inst_1: linear_ordered_field ↝ has_abs has_le has_lt has_mul has_nat_cast has_rat_cast has_sub
 -/

-- combinatorics/simple_graph/subgraph.lean
#check @simple_graph.subgraph.finite_at /- _inst_1: decidable_rel ↝ decidable_pred no_meet_fake_name
 -/
#check @simple_graph.subgraph.finite_at_of_subgraph /- _inst_1: decidable_rel ↝ decidable_pred no_meet_fake_name
 -/

-- computability/partrec.lean
#check @partrec /- _inst_1: primcodable ↝ encodable
_inst_2: primcodable ↝ encodable
 -/

-- computability/primrec.lean
#check @primrec /- _inst_1: primcodable ↝ encodable
_inst_2: primcodable ↝ encodable
 -/

-- computability/reduce.lean
#check @to_nat /- _inst_1: primcodable ↝ encodable
 -/

-- computability/turing_machine.lean
#check @turing.TM0.machine /- _inst_2: inhabited ↝
 -/
#check @turing.TM1to0.Λ' /- _inst_2: inhabited ↝
_inst_3: inhabited ↝
 -/
#check @turing.TM2to1.Γ' /- _inst_1: decidable_eq ↝
 -/
#check @turing.TM2to1.st_run /- _inst_2: inhabited ↝
 -/

-- control/basic.lean
#check @fish /- _inst_3: monad ↝ has_bind no_meet_fake_name
 -/
#check @succeeds /- _inst_1: alternative ↝ functor has_orelse has_pure no_meet_fake_name
 -/
#check @mtry /- _inst_1: alternative ↝ functor has_orelse has_pure no_meet_fake_name
 -/

-- control/bitraversable/instances.lean
#check @const.bitraverse /- _inst_2: applicative ↝
 -/

-- control/functor.lean
#check @functor.comp.has_pure /- _inst_1: applicative ↝ has_pure no_meet_fake_name
_inst_2: applicative ↝ has_pure no_meet_fake_name
 -/

-- control/monad/cont.lean
#check @cont_t.monad_lift /- _inst_1: monad ↝ has_bind no_meet_fake_name
 -/
#check @writer_t.monad_cont /- _inst_1: monad ↝
 -/
#check @state_t.mk_label /- _inst_1: monad ↝
 -/

-- control/monad/writer.lean
#check @writer_t.ext /- _inst_1: monad ↝
 -/
#check @writer_t.tell /- _inst_1: monad ↝ has_pure no_meet_fake_name
 -/
#check @writer_t.pure /- _inst_1: monad ↝ has_pure no_meet_fake_name
 -/
#check @writer_t.bind /- _inst_1: monad ↝ has_bind has_pure no_meet_fake_name
 -/
#check @writer_t.lift /- _inst_1: monad ↝ functor no_meet_fake_name
 -/
#check @writer_t.monad_map /- _inst_2: monad ↝
_inst_3: monad ↝
 -/
#check @writer_t.adapt /- _inst_1: monad ↝ functor no_meet_fake_name
 -/
#check @writer_t.monad_except /- _inst_1: monad ↝
 -/
#check @reader_t.monad_writer /- _inst_1: monad ↝ has_monad_lift no_meet_fake_name
 -/

-- control/traversable/instances.lean
#check @option.comp_traverse /- _inst_3: is_lawful_applicative ↝
 -/
#check @list.comp_traverse /- _inst_3: is_lawful_applicative ↝
 -/
#check @sum.comp_traverse /- _inst_3: is_lawful_applicative ↝
 -/

-- control/uliftable.lean
#check @uliftable.adapt_up /- _inst_2: monad ↝ has_bind no_meet_fake_name
 -/
#check @uliftable.adapt_down /- _inst_1: monad ↝ has_bind no_meet_fake_name
 -/

-- data/buffer/parser/basic.lean
#check @parser.and_then_eq_bind /- _inst_1: monad ↝ has_bind no_meet_fake_name
 -/
#check @parser.mono.seq /- _inst_2: parser.mono ↝ no_meet_fake_name parser.mono
 -/
#check @parser.mono.foldr /- _inst_1: parser.mono ↝ no_meet_fake_name parser.mono
 -/
#check @parser.mono.foldl /- _inst_1: parser.mono ↝ no_meet_fake_name parser.mono
 -/
#check @parser.static.seq /- _inst_2: parser.static ↝ no_meet_fake_name parser.static
 -/
#check @parser.static.foldr /- _inst_1: parser.static ↝ no_meet_fake_name parser.static
 -/
#check @parser.static.foldl /- _inst_1: parser.static ↝ no_meet_fake_name parser.static
 -/
#check @parser.unfailing.seq /- _inst_2: parser.unfailing ↝ no_meet_fake_name parser.unfailing
 -/
#check @parser.err_static.seq /- _inst_3: parser.err_static ↝ no_meet_fake_name parser.err_static
 -/
#check @parser.err_static.seq_of_unfailing /- _inst_2: parser.unfailing ↝ no_meet_fake_name parser.unfailing
 -/
#check @parser.step.seq /- _inst_2: parser.static ↝ no_meet_fake_name parser.static
 -/
#check @parser.step.seq' /- _inst_2: parser.step ↝ no_meet_fake_name parser.step
 -/
#check @parser.prog.seq /- _inst_2: parser.mono ↝ no_meet_fake_name parser.mono
 -/

-- data/complex/exponential.lean
#check @abv_sum_le_sum_abv /- _inst_1: linear_ordered_field ↝ covariant_class ordered_semiring
 -/

-- data/complex/is_R_or_C.lean
#check @is_R_or_C.conj_bit0 /- _inst_1: is_R_or_C ↝ comm_semiring star_ring
 -/
#check @is_R_or_C.star_def /- _inst_1: is_R_or_C ↝ comm_semiring has_star star_ring
 -/
#check @is_R_or_C.conj_to_ring_equiv /- _inst_1: is_R_or_C ↝ non_unital_semiring star_ring
 -/
#check @is_R_or_C.conj_inv /- _inst_1: is_R_or_C ↝ field star_ring
 -/
#check @finite_dimensional.proper_is_R_or_C /- _inst_2: normed_add_comm_group ↝ has_continuous_smul module no_meet_fake_name proper_space seminormed_add_comm_group t2_space
 -/
#check @finite_dimensional.is_R_or_C.proper_space_submodule /- _inst_3: normed_space ↝ module module no_meet_fake_name normed_space
 -/
#check @is_R_or_C.continuous_conj /- _inst_1: is_R_or_C ↝ comm_semiring has_continuous_star has_star star_ring topological_space
 -/

-- data/complex/module.lean
#check @module.complex_to_real /- _inst_1: add_comm_group ↝ add_comm_monoid
 -/

-- data/dfinsupp/basic.lean
#check @dfinsupp.prod_inv /- _inst_3: comm_group ↝ division_comm_monoid
 -/
#check @dfinsupp.sum_neg /- _inst_3: add_comm_group ↝ subtraction_comm_monoid
 -/
#check @monoid_hom.coe_dfinsupp_prod /- _inst_4: monoid ↝ mul_one_class
 -/
#check @add_monoid_hom.coe_dfinsupp_sum /- _inst_4: add_monoid ↝ add_zero_class
 -/
#check @add_monoid_hom.dfinsupp_sum_apply /- _inst_4: add_monoid ↝ add_zero_class
 -/
#check @monoid_hom.dfinsupp_prod_apply /- _inst_4: monoid ↝ mul_one_class
 -/

-- data/fin/basic.lean
#check @fin.order_iso_subsingleton /- _inst_1: preorder ↝ has_le
 -/

-- data/fin_enum.lean
#check @fin_enum.mem_pi /- _inst_1: fin_enum ↝ decidable_eq
 -/

-- data/finset/lattice.lean
#check @finset.sup /- _inst_1: semilattice_sup ↝ has_bot has_le has_sup is_associative is_commutative
_inst_2: order_bot ↝ has_bot
 -/
#check @finset.sup_eq_supr /- _inst_1: complete_lattice ↝ no_meet_fake_name
 -/
#check @finset.sup_id_eq_Sup /- _inst_1: complete_lattice ↝ no_meet_fake_name
 -/
#check @finset.sup_eq_Sup_image /- _inst_1: complete_lattice ↝ no_meet_fake_name
 -/
#check @finset.inf /- _inst_1: semilattice_inf ↝ has_inf has_le has_top is_associative is_commutative
_inst_2: order_top ↝ has_top
 -/
#check @finset.sup_sdiff_left /- _inst_3: boolean_algebra ↝ no_meet_fake_name
 -/
#check @finset.inf_sdiff_left /- _inst_3: boolean_algebra ↝ no_meet_fake_name
 -/
#check @finset.inf_sdiff_right /- _inst_3: boolean_algebra ↝ no_meet_fake_name
 -/
#check @finset.inf_eq_infi /- _inst_1: complete_lattice ↝ no_meet_fake_name
 -/
#check @finset.inf_id_eq_Inf /- _inst_1: complete_lattice ↝ no_meet_fake_name
 -/
#check @finset.inf_eq_Inf_image /- _inst_1: complete_lattice ↝ no_meet_fake_name
 -/
#check @finset.exists_mem_eq_sup' /- _inst_1: linear_order ↝ is_total semilattice_sup
 -/
#check @finset.max /- _inst_1: linear_order ↝ semilattice_sup
 -/
#check @finset.min /- _inst_1: linear_order ↝ semilattice_inf
 -/
#check @finset.min' /- _inst_1: linear_order ↝ semilattice_inf
 -/
#check @finset.max' /- _inst_1: linear_order ↝ semilattice_sup
 -/
#check @finset.supr_option_to_finset /- _inst_1: complete_lattice ↝ has_Sup
 -/

-- data/finset/locally_finite.lean
#check @finset.Ico_inter_Ico_consecutive /- _inst_1: partial_order ↝ preorder
 -/
#check @finset.Ici_erase /- _inst_3: order_top ↝ has_top locally_finite_order_top
 -/
#check @finset.Iic_erase /- _inst_3: order_bot ↝ has_bot locally_finite_order_bot
 -/
#check @finset.image_add_left_Icc /- _inst_1: ordered_cancel_add_comm_monoid ↝ add_semigroup contravariant_class covariant_class preorder
 -/
#check @finset.image_add_left_Ico /- _inst_1: ordered_cancel_add_comm_monoid ↝ add_semigroup contravariant_class contravariant_class covariant_class covariant_class preorder
 -/
#check @finset.image_add_left_Ioc /- _inst_1: ordered_cancel_add_comm_monoid ↝ add_semigroup contravariant_class contravariant_class covariant_class covariant_class preorder
 -/
#check @finset.image_add_left_Ioo /- _inst_1: ordered_cancel_add_comm_monoid ↝ add_semigroup contravariant_class covariant_class preorder
 -/

-- data/finset/noncomm_prod.lean
#check @multiset.nocomm_prod_map_aux /- _inst_1: monoid ↝ fun_like mul_hom_class mul_one_class no_meet_fake_name
_inst_2: monoid ↝ fun_like mul_hom_class mul_one_class no_meet_fake_name
_inst_3: monoid_hom_class ↝ fun_like mul_hom_class no_meet_fake_name
 -/
#check @multiset.nocomm_sum_map_aux /- _inst_1: add_monoid ↝ add_hom_class add_zero_class fun_like no_meet_fake_name
_inst_2: add_monoid ↝ add_hom_class add_zero_class fun_like no_meet_fake_name
_inst_3: add_monoid_hom_class ↝ add_hom_class fun_like no_meet_fake_name
 -/
#check @finset.noncomm_sum_add_distrib_aux /- _inst_1: add_monoid ↝ add_semigroup
 -/
#check @finset.noncomm_prod_mul_distrib_aux /- _inst_1: monoid ↝ semigroup
 -/

-- data/finset/order.lean
#check @finset.exists_le /- _inst_2: preorder ↝ has_le is_trans
 -/

-- data/finset/pointwise.lean
#check @finset.add_univ_of_zero_mem /- _inst_3: add_monoid ↝ add_zero_class
 -/
#check @finset.mul_univ_of_one_mem /- _inst_3: monoid ↝ mul_one_class
 -/
#check @finset.univ_add_of_zero_mem /- _inst_3: add_monoid ↝ add_zero_class
 -/
#check @finset.univ_mul_of_one_mem /- _inst_3: monoid ↝ mul_one_class
 -/
#check @finset.coe_zpow /- _inst_3: division_monoid ↝ has_involutive_inv monoid
 -/
#check @finset.coe_zsmul /- _inst_3: subtraction_monoid ↝ add_monoid has_involutive_neg
 -/
#check @finset.mul_add_subset /- _inst_3: distrib ↝ has_add has_mul left_distrib_class
 -/
#check @finset.add_mul_subset /- _inst_3: distrib ↝ has_add has_mul right_distrib_class
 -/
#check @finset.smul_comm_class_finset' /- _inst_4: smul_comm_class ↝ smul_comm_class
 -/
#check @finset.vadd_comm_class_finset' /- _inst_4: vadd_comm_class ↝ vadd_comm_class
 -/
#check @finset.is_scalar_tower' /- _inst_6: is_scalar_tower ↝ is_scalar_tower
 -/
#check @finset.is_central_scalar /- _inst_5: is_central_scalar ↝ is_central_scalar
 -/
#check @finset.no_zero_smul_divisors_finset /- _inst_6: no_zero_smul_divisors ↝ no_zero_smul_divisors
 -/

-- data/finsupp/basic.lean
#check @ring_hom.map_finsupp_sum /- _inst_2: semiring ↝ non_assoc_semiring
_inst_3: semiring ↝ non_assoc_semiring
 -/
#check @monoid_hom.coe_finsupp_prod /- _inst_2: monoid ↝ mul_one_class
 -/
#check @add_monoid_hom.coe_finsupp_sum /- _inst_2: add_monoid ↝ add_zero_class
 -/
#check @add_monoid_hom.finsupp_sum_apply /- _inst_2: add_monoid ↝ add_zero_class
 -/
#check @monoid_hom.finsupp_prod_apply /- _inst_2: monoid ↝ mul_one_class
 -/
#check @finsupp.sum_sub /- _inst_2: add_comm_group ↝ subtraction_comm_monoid
 -/
#check @finsupp.lift_add_hom_apply /- _inst_1: add_comm_monoid ↝ add_zero_class
 -/
#check @finsupp.lift_add_hom_symm_apply /- _inst_1: add_comm_monoid ↝ add_zero_class
 -/
#check @finsupp.lift_add_hom_symm_apply_apply /- _inst_1: add_comm_monoid ↝ add_zero_class
 -/
#check @finsupp.lift_add_hom_apply_single /- _inst_1: add_comm_monoid ↝ add_zero_class
 -/
#check @finsupp.sum_sub_index /- _inst_1: add_comm_group ↝ add_group
 -/
#check @finsupp.prod_sum_index /- _inst_1: add_comm_monoid ↝ has_zero
 -/
#check @finsupp.sum_sum_index /- _inst_1: add_comm_monoid ↝ has_zero
 -/
#check @finsupp.sum_update_add /- _inst_2: add_comm_monoid ↝ add_zero_class
 -/
#check @finsupp.eq_zero_of_comap_domain_eq_zero /- _inst_1: add_comm_monoid ↝ has_zero
 -/
#check @finsupp.some_add /- _inst_1: add_comm_monoid ↝ add_zero_class
 -/
#check @finsupp.single_smul /- _inst_3: mul_action_with_zero ↝ has_smul no_meet_fake_name smul_with_zero
 -/
#check @finsupp.comap_has_smul /- _inst_2: mul_action ↝ has_smul
 -/
#check @finsupp.coe_smul /- _inst_2: distrib_mul_action ↝ has_smul has_smul
 -/
#check @finsupp.smul_apply /- _inst_2: distrib_mul_action ↝ has_smul has_smul
 -/
#check @is_smul_regular.finsupp /- _inst_2: distrib_mul_action ↝ has_smul has_smul
 -/
#check @finsupp.is_scalar_tower /- _inst_4: distrib_mul_action ↝ has_smul has_smul
_inst_5: distrib_mul_action ↝ has_smul has_smul
 -/
#check @finsupp.smul_comm_class /- _inst_4: distrib_mul_action ↝ has_smul has_smul
_inst_5: distrib_mul_action ↝ has_smul has_smul
 -/
#check @finsupp.is_central_scalar /- _inst_3: distrib_mul_action ↝ has_smul has_smul
 -/
#check @finsupp.distrib_mul_action_hom_ext /- _inst_1: semiring ↝ distrib_mul_action monoid no_meet_fake_name
_inst_2: add_comm_monoid ↝ add_monoid distrib_mul_action no_meet_fake_name
_inst_3: add_comm_monoid ↝ add_monoid
_inst_4: distrib_mul_action ↝ distrib_mul_action no_meet_fake_name
 -/
#check @nat.cast_finsupp_sum /- _inst_2: comm_semiring ↝ add_comm_monoid_with_one
 -/
#check @int.cast_finsupp_sum /- _inst_2: comm_ring ↝ add_comm_group_with_one
 -/

-- data/finsupp/order.lean
#check @finsupp.has_le.le.contravariant_class /- _inst_1: ordered_add_comm_monoid ↝ add_zero_class has_le
 -/

-- data/fintype/basic.lean
#check @finset.univ_unique /- _inst_2: unique ↝ inhabited subsingleton
 -/
#check @finset.sup_univ_eq_supr /- _inst_2: complete_lattice ↝ no_meet_fake_name
 -/
#check @finset.inf_univ_eq_infi /- _inst_2: complete_lattice ↝ no_meet_fake_name
 -/
#check @fintype.card_unique /- _inst_1: unique ↝ inhabited subsingleton
 -/
#check @fintype.univ_of_is_empty /- _inst_1: is_empty ↝ fintype
 -/
#check @fintype.card_of_is_empty /- _inst_1: is_empty ↝ fintype
 -/
#check @unique.fintype /- _inst_1: unique ↝ inhabited subsingleton
 -/
#check @fintype.preorder.well_founded_lt /- _inst_2: preorder ↝ has_lt is_irrefl is_trans
 -/
#check @fintype.preorder.well_founded_gt /- _inst_2: preorder ↝ has_lt is_irrefl is_trans
 -/
#check @fintype.linear_order.is_well_order_lt /- _inst_2: linear_order ↝ is_trichotomous preorder
 -/
#check @fintype.linear_order.is_well_order_gt /- _inst_2: linear_order ↝ is_trichotomous preorder
 -/
#check @infinite.nonempty /- _inst_1: infinite ↝ nonempty
 -/

-- data/fintype/order.lean
#check @fintype.exists_le /- _inst_2: preorder ↝ has_le is_trans
 -/

-- data/fp/basic.lean
#check @fp.div_nat_lt_two_pow /- C: fp.float_cfg ↝
 -/

-- data/fun_like/basic.lean
#check @fun_like.congr_fun /- i: fun_like ↝ has_coe_to_fun
 -/

-- data/fun_like/equiv.lean
#check @equiv_like.injective /- iE: equiv_like ↝ embedding_like
 -/
#check @equiv_like.apply_eq_iff_eq /- iE: equiv_like ↝ embedding_like
 -/
#check @equiv_like.comp_injective /- iF: equiv_like ↝ embedding_like
 -/

-- data/holor.lean
#check @holor.mul_left_distrib /- _inst_1: distrib ↝ has_add has_mul left_distrib_class
 -/
#check @holor.mul_right_distrib /- _inst_1: distrib ↝ has_add has_mul right_distrib_class
 -/
#check @holor.zero_mul /- _inst_1: ring ↝ mul_zero_class
 -/
#check @holor.mul_zero /- _inst_1: ring ↝ mul_zero_class
 -/
#check @holor.mul_scalar_mul /- _inst_1: monoid ↝ has_mul
 -/
#check @holor.unit_vec /- _inst_1: monoid ↝ has_one
_inst_2: add_monoid ↝ has_zero
 -/
#check @holor.slice_unit_vec_mul /- _inst_1: ring ↝ semiring
 -/
#check @holor.cprank_max_nil /- _inst_1: monoid ↝ has_mul
 -/
#check @holor.cprank_max_1 /- _inst_1: monoid ↝ has_mul
 -/
#check @holor.cprank_max_sum /- _inst_1: ring ↝ semiring
 -/

-- data/int/cast.lean
#check @int.cast_ite /- _inst_1: add_group_with_one ↝ has_int_cast
 -/
#check @int.coe_int_dvd /- _inst_1: comm_ring ↝ ring
 -/
#check @monoid_hom.ext_int /- _inst_1: monoid ↝ mul_one_class
 -/

-- data/int/cast_field.lean
#check @int.cast_neg_nat_cast /- _inst_1: field ↝ add_group_with_one
 -/

-- data/int/log.lean
#check @int.log /- _inst_1: linear_ordered_semifield ↝ has_inv linear_ordered_semiring
 -/
#check @int.clog /- _inst_1: linear_ordered_semifield ↝ has_inv linear_ordered_semiring
 -/

-- data/list/big_operators.lean
#check @list.prod_nil /- _inst_1: monoid ↝ has_mul has_one
 -/
#check @list.sum_nil /- _inst_1: add_monoid ↝ has_add has_zero
 -/
#check @list.prod_singleton /- _inst_1: monoid ↝ mul_one_class
 -/
#check @list.sum_singleton /- _inst_1: add_monoid ↝ add_zero_class
 -/
#check @list.prod_cons /- _inst_1: monoid ↝ is_associative mul_one_class
 -/
#check @list.sum_cons /- _inst_1: add_monoid ↝ add_zero_class is_associative
 -/
#check @list.sum_append /- _inst_1: add_monoid ↝ add_zero_class is_associative
 -/
#check @list.prod_append /- _inst_1: monoid ↝ is_associative mul_one_class
 -/
#check @list.prod_hom /- _inst_1: monoid ↝ fun_like mul_hom_class mul_one_class no_meet_fake_name one_hom_class
_inst_2: monoid ↝ fun_like mul_hom_class mul_one_class no_meet_fake_name one_hom_class
_inst_4: monoid_hom_class ↝ fun_like mul_hom_class no_meet_fake_name one_hom_class
 -/
#check @list.sum_hom /- _inst_1: add_monoid ↝ add_hom_class add_zero_class fun_like no_meet_fake_name zero_hom_class
_inst_2: add_monoid ↝ add_hom_class add_zero_class fun_like no_meet_fake_name zero_hom_class
_inst_4: add_monoid_hom_class ↝ add_hom_class fun_like no_meet_fake_name zero_hom_class
 -/
#check @list.sum_hom₂ /- _inst_1: add_monoid ↝ has_add has_zero
_inst_2: add_monoid ↝ has_add has_zero
_inst_3: add_monoid ↝ has_add has_zero
 -/
#check @list.prod_hom₂ /- _inst_1: monoid ↝ has_mul has_one
_inst_2: monoid ↝ has_mul has_one
_inst_3: monoid ↝ has_mul has_one
 -/
#check @list.single_le_prod /- _inst_1: ordered_comm_monoid ↝ covariant_class covariant_class monoid preorder
 -/
#check @list.single_le_sum /- _inst_1: ordered_add_comm_monoid ↝ add_monoid covariant_class covariant_class preorder
 -/
#check @list.sum_le_foldr_max /- _inst_2: add_monoid ↝ has_zero
 -/
#check @list.dvd_sum /- _inst_1: semiring ↝ left_distrib_class non_unital_semiring
 -/

-- data/list/defs.lean
#check @list.mfoldl_with_index /- _inst_1: monad ↝ has_bind has_pure no_meet_fake_name
 -/
#check @list.mfoldr_with_index /- _inst_1: monad ↝ has_bind has_pure no_meet_fake_name
 -/

-- data/list/forall2.lean
#check @list.rel_sum /- _inst_1: add_monoid ↝ has_add has_zero
_inst_2: add_monoid ↝ has_add has_zero
 -/
#check @list.rel_prod /- _inst_1: monoid ↝ has_mul has_one
_inst_2: monoid ↝ has_mul has_one
 -/

-- data/list/func.lean
#check @list.func.get_neg /- _inst_1: add_group ↝ subtraction_monoid
 -/
#check @list.func.get_add /- _inst_1: add_monoid ↝ add_zero_class
 -/
#check @list.func.nil_add /- _inst_1: add_monoid ↝ add_zero_class
 -/
#check @list.func.add_nil /- _inst_1: add_monoid ↝ add_zero_class
 -/
#check @list.func.get_sub /- _inst_1: add_group ↝ subtraction_monoid
 -/
#check @list.func.nil_sub /- _inst_1: add_group ↝ sub_neg_monoid
 -/
#check @list.func.sub_nil /- _inst_1: add_group ↝ subtraction_monoid
 -/

-- data/list/infix.lean
#check @list.insert_nil /- _inst_1: decidable_eq ↝ has_insert
 -/

-- data/list/lex.lean
#check @list.lex.is_strict_total_order /- _inst_1: is_strict_total_order' ↝ is_asymm is_order_connected is_trichotomous
 -/

-- data/list/min_max.lean
#check @list.argmax /- _inst_1: preorder ↝ has_lt
 -/
#check @list.argmin /- _inst_1: preorder ↝ has_lt
 -/
#check @list.le_max_of_le /- _inst_2: order_bot ↝ has_bot
 -/

-- data/list/perm.lean
#check @list.perm.sum_eq' /- _inst_1: add_monoid ↝ add_semigroup has_zero
 -/
#check @list.perm.prod_eq' /- _inst_1: monoid ↝ has_one semigroup
 -/
#check @list.perm.sum_eq /- _inst_1: add_comm_monoid ↝ has_add has_zero is_associative is_commutative
 -/
#check @list.perm.prod_eq /- _inst_1: comm_monoid ↝ has_mul has_one is_associative is_commutative
 -/

-- data/list/zip.lean
#check @list.sum_zip_with_distrib_left /- _inst_1: semiring ↝ left_distrib_class non_unital_non_assoc_semiring
 -/

-- data/matrix/basic.lean
#check @matrix.has_smul /- _inst_1: has_smul ↝ has_smul
 -/
#check @matrix.smul_comm_class /- _inst_3: smul_comm_class ↝ smul_comm_class
 -/
#check @matrix.module /- _inst_3: module ↝ module no_meet_fake_name
 -/
#check @matrix.smul_of /- _inst_1: has_smul ↝ has_smul has_smul
 -/
#check @matrix.diag_smul /- _inst_1: has_smul ↝ has_smul has_smul
 -/
#check @matrix.diag_conj_transpose /- _inst_2: star_add_monoid ↝ has_star
 -/
#check @matrix.add_dot_product /- _inst_3: non_unital_non_assoc_semiring ↝ add_comm_monoid has_mul right_distrib_class
 -/
#check @matrix.dot_product_add /- _inst_3: non_unital_non_assoc_semiring ↝ add_comm_monoid has_mul left_distrib_class
 -/
#check @matrix.sum_elim_dot_product_sum_elim /- _inst_3: non_unital_non_assoc_semiring ↝ add_comm_monoid has_mul
 -/
#check @matrix.neg_dot_product /- _inst_3: non_unital_non_assoc_ring ↝ has_distrib_neg has_mul subtraction_comm_monoid
 -/
#check @matrix.dot_product_neg /- _inst_3: non_unital_non_assoc_ring ↝ has_distrib_neg has_mul subtraction_comm_monoid
 -/
#check @matrix.star_dot_product_star /- _inst_4: star_ring ↝ has_star star_add_monoid star_semigroup
 -/
#check @matrix.star_dot_product /- _inst_4: star_ring ↝ has_involutive_star star_add_monoid star_semigroup
 -/
#check @matrix.dot_product_star /- _inst_4: star_ring ↝ has_involutive_star star_add_monoid star_semigroup
 -/
#check @matrix.diag_col_mul_row /- _inst_1: non_unital_non_assoc_semiring ↝ add_comm_monoid has_mul
 -/
#check @matrix.semiring.is_scalar_tower /- _inst_1: non_unital_non_assoc_semiring ↝ add_comm_monoid has_mul
 -/
#check @matrix.semiring.smul_comm_class /- _inst_1: non_unital_non_assoc_semiring ↝ add_comm_monoid has_mul
 -/
#check @matrix.mul_mul_right /- _inst_1: comm_semiring ↝ distrib_mul_action no_meet_fake_name semiring smul_comm_class
 -/
#check @matrix.scalar.commute /- _inst_1: comm_semiring ↝ distrib_mul_action is_scalar_tower no_meet_fake_name semiring smul_comm_class
 -/
#check @matrix.mul_vec_smul_assoc /- _inst_1: comm_semiring ↝ distrib_mul_action no_meet_fake_name semiring smul_comm_class
 -/
#check @matrix.transpose_smul /- _inst_1: has_smul ↝ has_smul
 -/
#check @matrix.conj_transpose_one /- _inst_3: star_ring ↝ has_star star_add_monoid star_semigroup
 -/
#check @matrix.conj_transpose_mul /- _inst_3: star_ring ↝ has_star star_add_monoid star_semigroup
 -/
#check @matrix.minor_smul /- _inst_1: has_smul ↝ has_smul
 -/

-- data/matrix/basis.lean
#check @matrix.std_basis_matrix /- _inst_4: semiring ↝ has_zero
 -/

-- data/matrix/block.lean
#check @matrix.from_blocks_multiply /- _inst_3: non_unital_non_assoc_semiring ↝ add_comm_monoid has_mul
 -/
#check @matrix.block_diag_conj_transpose /- _inst_2: star_add_monoid ↝ has_star
 -/
#check @matrix.block_diag_add /- _inst_1: add_zero_class ↝ has_add
 -/
#check @matrix.block_diag_smul /- _inst_3: distrib_mul_action ↝ has_smul
 -/
#check @matrix.block_diagonal'_smul /- _inst_4: module ↝ distrib_mul_action has_smul
 -/
#check @matrix.block_diag'_conj_transpose /- _inst_2: star_add_monoid ↝ has_star
 -/
#check @matrix.block_diag'_add /- _inst_1: add_zero_class ↝ has_add
 -/
#check @matrix.block_diag'_smul /- _inst_3: distrib_mul_action ↝ has_smul
 -/

-- data/matrix/dmatrix.lean
#check @dmatrix /- _inst_1: fintype ↝
_inst_2: fintype ↝
 -/

-- data/matrix/hadamard.lean
#check @matrix.hadamard_add /- _inst_1: distrib ↝ has_add has_mul left_distrib_class
 -/
#check @matrix.add_hadamard /- _inst_1: distrib ↝ has_add has_mul right_distrib_class
 -/
#check @matrix.sum_hadamard_eq /- _inst_3: semiring ↝ add_comm_monoid has_mul
 -/

-- data/matrix/kronecker.lean
#check @matrix.kronecker_map_bilinear_mul_mul /- _inst_4: non_unital_non_assoc_semiring ↝ add_comm_monoid has_mul module
_inst_5: non_unital_non_assoc_semiring ↝ add_comm_monoid has_mul module module
_inst_6: non_unital_non_assoc_semiring ↝ add_comm_monoid has_mul module no_meet_fake_name smul_comm_class
 -/
#check @matrix.add_kronecker /- _inst_1: distrib ↝ has_add has_mul right_distrib_class
 -/
#check @matrix.kronecker_add /- _inst_1: distrib ↝ has_add has_mul left_distrib_class
 -/
#check @matrix.smul_kronecker /- _inst_2: monoid ↝ has_mul
_inst_3: mul_action ↝ has_smul
 -/
#check @matrix.kronecker_smul /- _inst_2: monoid ↝ has_mul
_inst_3: mul_action ↝ has_smul
 -/

-- data/matrix/notation.lean
#check @matrix.empty_mul /- _inst_1: semiring ↝ add_comm_monoid has_mul
 -/
#check @matrix.empty_mul_empty /- _inst_1: semiring ↝ add_comm_monoid has_mul
 -/
#check @matrix.mul_empty /- _inst_1: semiring ↝ add_comm_monoid has_mul
 -/
#check @matrix.mul_val_succ /- _inst_1: semiring ↝ add_comm_monoid has_mul
 -/
#check @matrix.empty_vec_mul /- _inst_1: semiring ↝ non_unital_non_assoc_semiring
 -/
#check @matrix.vec_mul_empty /- _inst_1: semiring ↝ non_unital_non_assoc_semiring
 -/
#check @matrix.cons_vec_mul /- _inst_1: semiring ↝ non_unital_non_assoc_semiring
 -/
#check @matrix.vec_mul_cons /- _inst_1: semiring ↝ non_unital_non_assoc_semiring
 -/
#check @matrix.empty_mul_vec /- _inst_1: semiring ↝ non_unital_non_assoc_semiring
 -/
#check @matrix.mul_vec_empty /- _inst_1: semiring ↝ non_unital_non_assoc_semiring
 -/
#check @matrix.cons_mul_vec /- _inst_1: semiring ↝ non_unital_non_assoc_semiring
 -/
#check @matrix.empty_vec_mul_vec /- _inst_1: semiring ↝ has_mul
 -/
#check @matrix.vec_mul_vec_empty /- _inst_1: semiring ↝ has_mul
 -/
#check @matrix.cons_vec_mul_vec /- _inst_1: semiring ↝ has_mul
 -/
#check @matrix.vec_mul_vec_cons /- _inst_1: semiring ↝ has_mul
 -/
#check @matrix.smul_mat_empty /- _inst_1: semiring ↝ has_smul
 -/
#check @matrix.smul_mat_cons /- _inst_1: semiring ↝ has_mul
 -/

-- data/matrix/pequiv.lean
#check @pequiv.mul_matrix_apply /- _inst_3: semiring ↝ non_assoc_semiring
 -/
#check @pequiv.matrix_mul_apply /- _inst_2: semiring ↝ non_assoc_semiring
 -/
#check @pequiv.to_matrix_injective /- _inst_2: monoid_with_zero ↝ mul_zero_one_class
 -/
#check @pequiv.to_matrix_swap /- _inst_2: ring ↝ add_group_with_one
 -/

-- data/matrix/rank.lean
#check @matrix.rank_eq_finrank_range_to_lin /- _inst_7: add_comm_group ↝ add_comm_monoid module
 -/

-- data/multiset/lattice.lean
#check @multiset.sup /- _inst_1: semilattice_sup ↝ has_bot has_le has_sup is_associative is_commutative
_inst_2: order_bot ↝ has_bot
 -/
#check @multiset.inf /- _inst_1: semilattice_inf ↝ has_inf has_le has_top is_associative is_commutative
_inst_2: order_top ↝ has_top
 -/

-- data/multiset/locally_finite.lean
#check @multiset.Ico_disjoint_Ico /- _inst_1: partial_order ↝ preorder
 -/

-- data/mv_polynomial/basic.lean
#check @mv_polynomial /- _inst_1: comm_semiring ↝ semiring
 -/
#check @mv_polynomial.is_scalar_tower' /- _inst_3: algebra ↝ algebra module
 -/
#check @mv_polynomial.alg_hom_ext' /- _inst_4: comm_semiring ↝ semiring
 -/

-- data/mv_polynomial/comm_ring.lean
#check @mv_polynomial.hom_C /- _inst_2: comm_ring ↝ non_assoc_ring
 -/

-- data/mv_polynomial/variables.lean
#check @mv_polynomial.vars_C_mul /- _inst_3: is_domain ↝ no_zero_divisors
 -/

-- data/nat/cast.lean
#check @nat.mono_cast /- _inst_1: ordered_semiring ↝ add_monoid_with_one covariant_class preorder zero_le_one_class
 -/
#check @ext_nat' /- _inst_2: add_monoid ↝ add_zero_class
 -/
#check @map_nat_cast /- _inst_3: ring_hom_class ↝ add_monoid_hom_class fun_like no_meet_fake_name one_hom_class
 -/

-- data/nat/cast/defs.lean
#check @nat.cast_ite /- _inst_1: add_monoid_with_one ↝ has_nat_cast
 -/

-- data/nat/cast_field.lean
#check @nat.cast_div /- _inst_1: field ↝ semifield
 -/

-- data/nat/choose/bounds.lean
#check @nat.choose_le_pow /- _inst_1: linear_ordered_field ↝ linear_ordered_semifield
 -/
#check @nat.pow_le_choose /- _inst_1: linear_ordered_field ↝ linear_ordered_semifield
 -/

-- data/nat/choose/cast.lean
#check @nat.cast_choose /- _inst_1: division_ring ↝ division_semiring no_zero_divisors
 -/
#check @nat.cast_choose_eq_pochhammer_div /- _inst_1: division_ring ↝ division_semiring
 -/

-- data/nat/prime.lean
#check @nat.monoid.prime_pow /- _inst_1: monoid ↝ has_pow
 -/

-- data/num/lemmas.lean
#check @pos_num.cast_mul /- _inst_1: semiring ↝ non_assoc_semiring
 -/
#check @num.cast_add /- _inst_1: semiring ↝ add_monoid_with_one
 -/
#check @num.cast_to_znum_neg /- _inst_1: add_group ↝ subtraction_monoid
 -/
#check @num.cast_inj /- _inst_1: linear_ordered_semiring ↝ add_monoid_with_one char_zero
 -/
#check @znum.cast_zneg /- _inst_1: add_group ↝ subtraction_monoid
 -/
#check @num.cast_of_znum /- _inst_1: add_group_with_one ↝ add_monoid_with_one
 -/
#check @znum.cast_mul /- _inst_1: ring ↝ non_assoc_ring
 -/
#check @znum.cast_inj /- _inst_1: linear_ordered_ring ↝ add_group_with_one char_zero
 -/
#check @znum.cast_sub /- _inst_1: ring ↝ add_comm_group_with_one
 -/

-- data/option/defs.lean
#check @option.melim /- _inst_1: monad ↝ has_bind no_meet_fake_name
 -/

-- data/ordmap/ordnode.lean
#check @ordnode.of_list /- _inst_2: decidable_rel ↝ has_insert
 -/

-- data/polynomial/algebra_map.lean
#check @polynomial.aeval_eq_sum_range /- _inst_8: comm_semiring ↝ semiring
 -/
#check @polynomial.aeval_eq_sum_range' /- _inst_8: comm_semiring ↝ semiring
 -/
#check @polynomial.is_root_of_eval₂_map_eq_zero /- _inst_3: comm_semiring ↝ semiring
_inst_8: comm_semiring ↝ semiring
 -/
#check @polynomial.aeval_endomorphism /- _inst_3: comm_ring ↝ algebra algebra comm_semiring module no_meet_fake_name
_inst_4: add_comm_group ↝ add_comm_monoid algebra has_smul module no_meet_fake_name
 -/

-- data/polynomial/basic.lean
#check @polynomial.add_hom_ext /- _inst_2: add_monoid ↝ add_zero_class
 -/

-- data/polynomial/denoms_clearable.lean
#check @denoms_clearable /- _inst_2: comm_semiring ↝ semiring
 -/

-- data/polynomial/derivative.lean
#check @polynomial.derivative_smul /- _inst_3: distrib_mul_action ↝ has_smul has_smul is_scalar_tower
_inst_4: is_scalar_tower ↝ is_scalar_tower
 -/

-- data/polynomial/div.lean
#check @polynomial.sum_mod_by_monic_coeff /- _inst_1: comm_ring ↝ module ring
 -/

-- data/polynomial/eval.lean
#check @polynomial.eval₂ /- _inst_2: semiring ↝ has_pow non_assoc_semiring
 -/
#check @polynomial.eval_smul /- _inst_3: distrib_mul_action ↝ has_smul has_smul is_scalar_tower
 -/
#check @polynomial.smul_comp /- _inst_3: distrib_mul_action ↝ has_smul has_smul is_scalar_tower
_inst_4: is_scalar_tower ↝ is_scalar_tower
 -/
#check @polynomial.is_root_prod /- _inst_3: comm_ring ↝ euclidean_domain no_zero_divisors
_inst_4: is_domain ↝ no_zero_divisors nontrivial
 -/
#check @polynomial.is_root.map /- _inst_1: comm_semiring ↝ semiring
_inst_2: comm_semiring ↝ semiring
 -/
#check @polynomial.is_root.of_map /- _inst_2: comm_semiring ↝ semiring
_inst_3: comm_ring ↝ ring
 -/

-- data/polynomial/expand.lean
#check @polynomial.contract /- _inst_1: comm_semiring ↝ module semiring
 -/

-- data/polynomial/field_division.lean
#check @polynomial.derivative_root_multiplicity_of_root /- _inst_1: comm_ring ↝ euclidean_domain module no_zero_divisors
 -/
#check @polynomial.normalization_monoid /- _inst_1: comm_ring ↝ field
 -/
#check @polynomial.coe_norm_unit /- _inst_1: comm_ring ↝ field
 -/
#check @polynomial.leading_coeff_normalize /- _inst_1: comm_ring ↝ field no_zero_divisors
 -/
#check @polynomial.monic.normalize_eq_self /- _inst_1: comm_ring ↝ field
 -/
#check @polynomial.roots_normalize /- _inst_1: comm_ring ↝ field
_inst_2: is_domain ↝ no_meet_fake_name
 -/
#check @polynomial.monic_mul_leading_coeff_inv /- _inst_1: division_ring ↝ division_semiring no_zero_divisors
 -/
#check @polynomial.degree_mul_leading_coeff_inv /- _inst_1: division_ring ↝ division_semiring no_zero_divisors
 -/
#check @polynomial.map_eq_zero /- _inst_1: division_ring ↝ division_semiring
 -/
#check @polynomial.div /- _inst_1: field ↝ has_inv ring
 -/
#check @polynomial.mod /- _inst_1: field ↝ has_inv ring
 -/
#check @polynomial.degree_map /- _inst_1: field ↝ division_ring
_inst_2: division_ring ↝ division_semiring
 -/
#check @polynomial.mem_roots_map /- _inst_1: field ↝ division_ring
_inst_2: field ↝ euclidean_domain is_domain
 -/

-- data/polynomial/integral_normalization.lean
#check @polynomial.support_integral_normalization /- _inst_1: ring ↝ euclidean_domain no_zero_divisors
_inst_2: is_domain ↝ no_zero_divisors nontrivial
 -/

-- data/polynomial/lifts.lean
#check @polynomial.map_alg /- _inst_6: algebra ↝ algebra
 -/

-- data/polynomial/ring_division.lean
#check @polynomial.nat_degree_pos_of_aeval_root /- _inst_1: comm_ring ↝ algebra comm_semiring
 -/
#check @polynomial.is_domain /- _inst_1: ring ↝ euclidean_domain no_zero_divisors
_inst_2: is_domain ↝ no_zero_divisors nontrivial
 -/
#check @polynomial.degree_eq_zero_of_is_unit /- _inst_1: comm_ring ↝ euclidean_domain no_zero_divisors
_inst_2: is_domain ↝ no_zero_divisors nontrivial
 -/
#check @polynomial.prime_X_sub_C /- _inst_1: comm_ring ↝ euclidean_domain no_zero_divisors
_inst_2: is_domain ↝ no_zero_divisors nontrivial
 -/
#check @polynomial.root_multiplicity_X_sub_C_self /- _inst_1: comm_ring ↝ euclidean_domain
_inst_2: is_domain ↝ no_meet_fake_name
 -/
#check @polynomial.root_multiplicity_X_sub_C_pow /- _inst_1: comm_ring ↝ euclidean_domain no_zero_divisors
_inst_2: is_domain ↝ no_meet_fake_name no_zero_divisors
 -/
#check @polynomial.roots_list_prod /- _inst_1: comm_ring ↝ euclidean_domain no_zero_divisors
_inst_2: is_domain ↝ no_meet_fake_name no_zero_divisors
 -/
#check @polynomial.roots_prod /- _inst_1: comm_ring ↝ euclidean_domain no_zero_divisors
_inst_2: is_domain ↝ no_meet_fake_name no_zero_divisors
 -/
#check @polynomial.roots_prod_X_sub_C /- _inst_1: comm_ring ↝ euclidean_domain no_zero_divisors
_inst_2: is_domain ↝ no_meet_fake_name no_zero_divisors
 -/
#check @polynomial.roots_multiset_prod_X_sub_C /- _inst_1: comm_ring ↝ euclidean_domain
_inst_2: is_domain ↝ no_meet_fake_name
 -/
#check @polynomial.nat_degree_multiset_prod_X_sub_C_eq_card /- _inst_1: comm_ring ↝ euclidean_domain
_inst_2: is_domain ↝ nontrivial
 -/
#check @polynomial.card_roots_X_pow_sub_C /- _inst_1: comm_ring ↝ euclidean_domain
_inst_2: is_domain ↝ no_meet_fake_name
 -/
#check @polynomial.mem_nth_roots /- _inst_1: comm_ring ↝ euclidean_domain
_inst_2: is_domain ↝ no_meet_fake_name
 -/
#check @polynomial.card_nth_roots /- _inst_1: comm_ring ↝ euclidean_domain
_inst_2: is_domain ↝ no_meet_fake_name
 -/
#check @polynomial.monic.comp /- _inst_1: comm_ring ↝ no_zero_divisors ring
_inst_2: is_domain ↝ no_zero_divisors
 -/
#check @polynomial.monic.comp_X_add_C /- _inst_1: comm_ring ↝ euclidean_domain
_inst_2: is_domain ↝ no_meet_fake_name
 -/
#check @polynomial.comp_eq_zero_iff /- _inst_1: comm_ring ↝ no_zero_divisors ring
_inst_2: is_domain ↝ no_zero_divisors
 -/
#check @polynomial.root_set /- _inst_3: comm_ring ↝ comm_semiring
 -/
#check @polynomial.mem_root_set_iff /- _inst_4: comm_ring ↝ euclidean_domain
 -/
#check @polynomial.coeff_coe_units_zero_ne_zero /- _inst_1: comm_ring ↝ euclidean_domain
_inst_2: is_domain ↝ no_meet_fake_name
 -/
#check @polynomial.degree_eq_one_of_irreducible_of_root /- _inst_1: comm_ring ↝ euclidean_domain no_zero_divisors
_inst_2: is_domain ↝ no_meet_fake_name no_zero_divisors
 -/
#check @polynomial.leading_coeff_div_by_monic_X_sub_C /- _inst_1: comm_ring ↝ euclidean_domain
_inst_2: is_domain ↝ nontrivial
 -/
#check @polynomial.exists_prod_multiset_X_sub_C_mul /- _inst_1: comm_ring ↝ euclidean_domain no_zero_divisors
_inst_2: is_domain ↝ no_meet_fake_name no_zero_divisors
 -/
#check @polynomial.is_unit_of_is_unit_leading_coeff_of_is_unit_map /- _inst_2: comm_ring ↝ euclidean_domain
 -/
#check @polynomial.monic.irreducible_of_irreducible_map /- _inst_2: is_domain ↝ no_zero_divisors
 -/

-- data/rat/cast.lean
#check @map_rat_cast /- _inst_4: ring_hom_class ↝ fun_like has_coe_t
 -/

-- data/rbmap/default.lean
#check @rbmap.eq_of_find_entry_some /- _inst_2: is_strict_total_order ↝ is_strict_weak_order is_trichotomous
 -/
#check @rbmap.eq_or_mem_of_mem_ins /- _inst_2: is_strict_total_order ↝ is_strict_weak_order is_trichotomous
 -/
#check @rbmap.find_entry_insert_of_ne /- _inst_2: is_strict_total_order ↝ is_strict_weak_order is_trichotomous
 -/
#check @rbmap.mem_of_min_eq /- _inst_1: is_strict_total_order ↝ is_strict_weak_order
 -/
#check @rbmap.mem_of_max_eq /- _inst_1: is_strict_total_order ↝ is_strict_weak_order
 -/
#check @rbmap.min_is_minimal_of_total /- _inst_1: is_strict_total_order ↝ is_strict_weak_order is_trichotomous
 -/
#check @rbmap.max_is_maximal_of_total /- _inst_1: is_strict_total_order ↝ is_strict_weak_order is_trichotomous
 -/

-- data/rbtree/insert.lean
#check @rbnode.mem_ins_of_mem /- _inst_2: is_strict_weak_order ↝ is_incomp_trans is_strict_order
 -/
#check @rbnode.equiv_or_mem_of_mem_ins /- _inst_2: is_strict_weak_order ↝ is_strict_order
 -/
#check @rbnode.find_balance1_gt /- _inst_1: is_strict_weak_order ↝ is_strict_order
 -/
#check @rbnode.find_balance2_lt /- _inst_1: is_strict_weak_order ↝ is_trans
 -/

-- data/rbtree/main.lean
#check @rbtree.mem_of_mem_of_eqv /- _inst_1: is_strict_weak_order ↝ is_incomp_trans
 -/
#check @rbtree.find_correct_of_total /- _inst_2: is_strict_total_order ↝ is_strict_weak_order is_trichotomous
 -/
#check @rbtree.find_correct_exact /- _inst_2: is_strict_total_order ↝ is_strict_weak_order
 -/
#check @rbtree.find_insert_of_ne /- _inst_2: is_strict_total_order ↝ is_strict_weak_order is_trichotomous
 -/
#check @rbtree.eq_of_find_some /- _inst_2: is_strict_total_order ↝ is_strict_weak_order is_trichotomous
 -/
#check @rbtree.eq_or_mem_of_mem_ins /- _inst_2: is_strict_total_order ↝ is_strict_weak_order is_trichotomous
 -/

-- data/real/cau_seq.lean
#check @rat_add_continuous_lemma /- _inst_1: linear_ordered_field ↝ covariant_class covariant_class linear_ordered_semifield
 -/
#check @rat_mul_continuous_lemma /- _inst_1: linear_ordered_field ↝ covariant_class covariant_class linear_ordered_semifield
 -/
#check @is_cau_seq /- _inst_1: linear_ordered_field ↝ has_lt has_zero
_inst_2: ring ↝ has_sub
 -/
#check @cau_seq.one_not_equiv_zero /- _inst_2: ring ↝ euclidean_domain
_inst_3: is_domain ↝ nontrivial
 -/

-- data/real/cau_seq_completion.lean
#check @cau_seq.completion.Cauchy /- _inst_2: comm_ring ↝ ring
 -/
#check @cau_seq.completion.Cauchy.has_rat_cast /- _inst_2: field ↝ comm_ring has_rat_cast
 -/
#check @cau_seq.completion.cau_seq_zero_ne_one /- _inst_2: field ↝ euclidean_domain
 -/

-- data/set/basic.lean
#check @set.univ_unique /- _inst_1: unique ↝ inhabited subsingleton
 -/

-- data/set/equitable.lean
#check @set.subsingleton.equitable_on /- _inst_1: ordered_semiring ↝ add_monoid_with_one covariant_class has_le zero_le_one_class
 -/

-- data/set/finite.lean
#check @set.finite.of_subsingleton /- _inst_1: subsingleton ↝ finite
 -/
#check @supr_infi_of_monotone /- _inst_1: fintype ↝ finite
 -/
#check @set.Union_pi_of_monotone /- _inst_1: linear_order ↝ is_directed preorder
 -/
#check @set.Union_univ_pi_of_monotone /- _inst_3: fintype ↝ finite
 -/

-- data/set/intervals/basic.lean
#check @set.Ioo /- _inst_1: preorder ↝ has_lt
 -/
#check @set.Ico /- _inst_1: preorder ↝ has_le has_lt
 -/
#check @set.Iio /- _inst_1: preorder ↝ has_lt
 -/
#check @set.Icc /- _inst_1: preorder ↝ has_le
 -/
#check @set.Iic /- _inst_1: preorder ↝ has_le
 -/
#check @set.Ioc /- _inst_1: preorder ↝ has_le has_lt
 -/
#check @set.Ici /- _inst_1: preorder ↝ has_le
 -/
#check @set.Ioi /- _inst_1: preorder ↝ has_lt
 -/
#check @set.Icc_bot_top /- _inst_1: partial_order ↝ bounded_order preorder
_inst_2: bounded_order ↝ bounded_order
 -/
#check @set.inv_mem_Icc_iff /- _inst_1: ordered_comm_group ↝ covariant_class covariant_class group preorder
 -/
#check @set.neg_mem_Icc_iff /- _inst_1: ordered_add_comm_group ↝ add_group covariant_class covariant_class preorder
 -/
#check @set.inv_mem_Ico_iff /- _inst_1: ordered_comm_group ↝ covariant_class covariant_class covariant_class covariant_class group preorder
 -/
#check @set.neg_mem_Ico_iff /- _inst_1: ordered_add_comm_group ↝ add_group covariant_class covariant_class covariant_class covariant_class preorder
 -/
#check @set.neg_mem_Ioc_iff /- _inst_1: ordered_add_comm_group ↝ add_group covariant_class covariant_class covariant_class covariant_class preorder
 -/
#check @set.inv_mem_Ioc_iff /- _inst_1: ordered_comm_group ↝ covariant_class covariant_class covariant_class covariant_class group preorder
 -/
#check @set.neg_mem_Ioo_iff /- _inst_1: ordered_add_comm_group ↝ add_group covariant_class covariant_class preorder
 -/
#check @set.inv_mem_Ioo_iff /- _inst_1: ordered_comm_group ↝ covariant_class covariant_class group preorder
 -/
#check @set.add_mem_Icc_iff_left /- _inst_1: ordered_add_comm_group ↝ add_group covariant_class preorder
 -/
#check @set.add_mem_Ico_iff_left /- _inst_1: ordered_add_comm_group ↝ add_group covariant_class covariant_class preorder
 -/
#check @set.add_mem_Ioc_iff_left /- _inst_1: ordered_add_comm_group ↝ add_group covariant_class covariant_class preorder
 -/
#check @set.add_mem_Ioo_iff_left /- _inst_1: ordered_add_comm_group ↝ add_group covariant_class preorder
 -/
#check @set.add_mem_Icc_iff_right /- _inst_1: ordered_add_comm_group ↝ add_comm_group covariant_class preorder
 -/
#check @set.add_mem_Ico_iff_right /- _inst_1: ordered_add_comm_group ↝ add_comm_group covariant_class covariant_class preorder
 -/
#check @set.add_mem_Ioc_iff_right /- _inst_1: ordered_add_comm_group ↝ add_comm_group covariant_class covariant_class preorder
 -/
#check @set.add_mem_Ioo_iff_right /- _inst_1: ordered_add_comm_group ↝ add_comm_group covariant_class preorder
 -/
#check @set.sub_mem_Icc_iff_left /- _inst_1: ordered_add_comm_group ↝ add_group covariant_class preorder
 -/
#check @set.sub_mem_Ico_iff_left /- _inst_1: ordered_add_comm_group ↝ add_group covariant_class covariant_class preorder
 -/
#check @set.sub_mem_Ioc_iff_left /- _inst_1: ordered_add_comm_group ↝ add_group covariant_class covariant_class preorder
 -/
#check @set.sub_mem_Ioo_iff_left /- _inst_1: ordered_add_comm_group ↝ add_group covariant_class preorder
 -/
#check @set.sub_mem_Icc_iff_right /- _inst_1: ordered_add_comm_group ↝ add_comm_group covariant_class preorder
 -/
#check @set.sub_mem_Ico_iff_right /- _inst_1: ordered_add_comm_group ↝ add_comm_group covariant_class covariant_class preorder
 -/
#check @set.sub_mem_Ioc_iff_right /- _inst_1: ordered_add_comm_group ↝ add_comm_group covariant_class covariant_class preorder
 -/
#check @set.sub_mem_Ioo_iff_right /- _inst_1: ordered_add_comm_group ↝ add_comm_group covariant_class preorder
 -/
#check @set.nonempty_Ico_sdiff /- _inst_1: linear_ordered_add_comm_group ↝ add_zero_class contravariant_class contravariant_class contravariant_class covariant_class covariant_class covariant_class linear_order
 -/

-- data/set/intervals/disjoint.lean
#check @set.Union_Ico_eq_Iio_self_iff /- _inst_1: linear_order ↝ preorder
 -/
#check @set.Union_Ioc_eq_Ioi_self_iff /- _inst_1: linear_order ↝ preorder
 -/
#check @set.bUnion_Ico_eq_Iio_self_iff /- _inst_1: linear_order ↝ preorder
 -/
#check @set.bUnion_Ioc_eq_Ioi_self_iff /- _inst_1: linear_order ↝ preorder
 -/

-- data/set/intervals/image_preimage.lean
#check @set.Icc_add_bij /- _inst_1: ordered_cancel_add_comm_monoid ↝ add_cancel_comm_monoid contravariant_class covariant_class preorder
 -/
#check @set.Ioo_add_bij /- _inst_1: ordered_cancel_add_comm_monoid ↝ add_cancel_comm_monoid contravariant_class covariant_class preorder
 -/
#check @set.Ioc_add_bij /- _inst_1: ordered_cancel_add_comm_monoid ↝ add_cancel_comm_monoid contravariant_class contravariant_class covariant_class covariant_class preorder
 -/
#check @set.Ico_add_bij /- _inst_1: ordered_cancel_add_comm_monoid ↝ add_cancel_comm_monoid contravariant_class contravariant_class covariant_class covariant_class preorder
 -/
#check @set.Ici_add_bij /- _inst_1: ordered_cancel_add_comm_monoid ↝ add_cancel_comm_monoid contravariant_class covariant_class preorder
 -/
#check @set.Ioi_add_bij /- _inst_1: ordered_cancel_add_comm_monoid ↝ add_cancel_comm_monoid contravariant_class covariant_class preorder
 -/
#check @set.preimage_const_add_Ici /- _inst_1: ordered_add_comm_group ↝ add_comm_group covariant_class preorder
 -/
#check @set.preimage_const_add_Ioi /- _inst_1: ordered_add_comm_group ↝ add_comm_group covariant_class preorder
 -/
#check @set.preimage_const_add_Iic /- _inst_1: ordered_add_comm_group ↝ add_comm_group covariant_class preorder
 -/
#check @set.preimage_const_add_Iio /- _inst_1: ordered_add_comm_group ↝ add_comm_group covariant_class preorder
 -/
#check @set.preimage_add_const_Ici /- _inst_1: ordered_add_comm_group ↝ add_group covariant_class preorder
 -/
#check @set.preimage_add_const_Ioi /- _inst_1: ordered_add_comm_group ↝ add_group covariant_class preorder
 -/
#check @set.preimage_add_const_Iic /- _inst_1: ordered_add_comm_group ↝ add_group covariant_class preorder
 -/
#check @set.preimage_add_const_Iio /- _inst_1: ordered_add_comm_group ↝ add_group covariant_class preorder
 -/
#check @set.preimage_neg_Ici /- _inst_1: ordered_add_comm_group ↝ add_group covariant_class covariant_class preorder
 -/
#check @set.preimage_neg_Iic /- _inst_1: ordered_add_comm_group ↝ add_group covariant_class covariant_class preorder
 -/
#check @set.preimage_neg_Ioi /- _inst_1: ordered_add_comm_group ↝ add_group covariant_class covariant_class preorder
 -/
#check @set.preimage_neg_Iio /- _inst_1: ordered_add_comm_group ↝ add_group covariant_class covariant_class preorder
 -/
#check @set.preimage_const_sub_Ici /- _inst_1: ordered_add_comm_group ↝ add_comm_group covariant_class preorder
 -/
#check @set.preimage_const_sub_Iic /- _inst_1: ordered_add_comm_group ↝ add_comm_group covariant_class preorder
 -/
#check @set.preimage_const_sub_Ioi /- _inst_1: ordered_add_comm_group ↝ add_comm_group covariant_class preorder
 -/
#check @set.preimage_const_sub_Iio /- _inst_1: ordered_add_comm_group ↝ add_comm_group covariant_class preorder
 -/
#check @set.preimage_mul_const_Iio /- _inst_1: linear_ordered_field ↝ linear_ordered_semifield
 -/
#check @set.preimage_mul_const_Ioi /- _inst_1: linear_ordered_field ↝ linear_ordered_semifield
 -/
#check @set.preimage_mul_const_Iic /- _inst_1: linear_ordered_field ↝ linear_ordered_semifield
 -/
#check @set.preimage_mul_const_Ici /- _inst_1: linear_ordered_field ↝ linear_ordered_semifield
 -/
#check @set.preimage_const_mul_Iio /- _inst_1: linear_ordered_field ↝ linear_ordered_semifield
 -/
#check @set.preimage_const_mul_Ioi /- _inst_1: linear_ordered_field ↝ linear_ordered_semifield
 -/
#check @set.preimage_const_mul_Iic /- _inst_1: linear_ordered_field ↝ linear_ordered_semifield
 -/
#check @set.preimage_const_mul_Ici /- _inst_1: linear_ordered_field ↝ linear_ordered_semifield
 -/
#check @set.inv_Ioo_0_left /- _inst_1: linear_ordered_field ↝ linear_ordered_semifield
 -/

-- data/set/intervals/monotone.lean
#check @strict_mono_of_odd_strict_mono_on_nonneg /- _inst_2: ordered_add_comm_group ↝ add_group covariant_class covariant_class preorder
 -/
#check @monotone_of_odd_of_monotone_on_nonneg /- _inst_2: ordered_add_comm_group ↝ add_group covariant_class covariant_class preorder
 -/
#check @Union_Ioo_of_mono_of_is_glb_of_is_lub /- _inst_1: semilattice_sup ↝ is_directed preorder
 -/

-- data/set/intervals/ord_connected.lean
#check @set.ord_connected_range /- _inst_1: preorder ↝ has_le no_meet_fake_name order_hom_class set.ord_connected set.ord_connected
_inst_3: order_iso_class ↝ no_meet_fake_name order_hom_class set.ord_connected
 -/

-- data/set/intervals/surj_on.lean
#check @surj_on_Ioo_of_monotone_surjective /- _inst_2: partial_order ↝ preorder
 -/
#check @surj_on_Ioi_of_monotone_surjective /- _inst_2: partial_order ↝ preorder
 -/

-- data/set/intervals/unordered_interval.lean
#check @set.abs_sub_le_of_subinterval /- _inst_1: linear_ordered_add_comm_group ↝ add_comm_group covariant_class covariant_class linear_order
 -/

-- data/set/intervals/with_bot_top.lean
#check @with_top.preimage_coe_Ioi /- _inst_1: partial_order ↝ preorder
 -/
#check @with_top.preimage_coe_Ici /- _inst_1: partial_order ↝ preorder
 -/
#check @with_top.preimage_coe_Iio /- _inst_1: partial_order ↝ preorder
 -/
#check @with_top.preimage_coe_Iic /- _inst_1: partial_order ↝ preorder
 -/
#check @with_bot.preimage_coe_Ioi /- _inst_1: partial_order ↝ preorder
 -/
#check @with_bot.preimage_coe_Ici /- _inst_1: partial_order ↝ preorder
 -/
#check @with_bot.preimage_coe_Iio /- _inst_1: partial_order ↝ preorder
 -/
#check @with_bot.preimage_coe_Iic /- _inst_1: partial_order ↝ preorder
 -/

-- data/set/lattice.lean
#check @sup_closed.inter /- _inst_1: semilattice_sup ↝ has_sup
 -/

-- data/set/pairwise.lean
#check @set.nonempty.pairwise_iff_exists_forall /- _inst_1: is_equiv ↝ is_refl is_symm is_trans
 -/
#check @set.pairwise_disjoint.bUnion /- _inst_1: complete_lattice ↝ no_meet_fake_name
 -/

-- data/set/pointwise.lean
#check @set.add_univ_of_zero_mem /- _inst_1: add_monoid ↝ add_zero_class
 -/
#check @set.mul_univ_of_one_mem /- _inst_1: monoid ↝ mul_one_class
 -/
#check @set.univ_mul_of_one_mem /- _inst_1: monoid ↝ mul_one_class
 -/
#check @set.univ_add_of_zero_mem /- _inst_1: add_monoid ↝ add_zero_class
 -/
#check @set.mul_add_subset /- _inst_1: distrib ↝ has_add has_mul left_distrib_class
 -/
#check @set.add_mul_subset /- _inst_1: distrib ↝ has_add has_mul right_distrib_class
 -/
#check @set.bdd_above_mul /- _inst_1: ordered_comm_monoid ↝ covariant_class covariant_class has_mul preorder
 -/
#check @set.bdd_above_add /- _inst_1: ordered_add_comm_monoid ↝ covariant_class covariant_class has_add preorder
 -/
#check @set.list_prod_mem_list_prod /- _inst_1: comm_monoid ↝ monoid
 -/
#check @set.list_sum_mem_list_sum /- _inst_1: add_comm_monoid ↝ add_monoid
 -/
#check @set.list_prod_subset_list_prod /- _inst_1: comm_monoid ↝ monoid
 -/
#check @set.list_sum_subset_list_sum /- _inst_1: add_comm_monoid ↝ add_monoid
 -/
#check @set.list_prod_singleton /- _inst_2: comm_monoid ↝ monoid
 -/
#check @set.list_sum_singleton /- _inst_2: add_comm_monoid ↝ add_monoid
 -/
#check @set.no_zero_divisors /- _inst_3: no_zero_divisors ↝ no_zero_smul_divisors
 -/
#check @set.smul_set_neg /- _inst_1: ring ↝ distrib_mul_action semiring
_inst_3: module ↝ distrib_mul_action has_smul
 -/
#check @set.smul_neg /- _inst_1: ring ↝ distrib_mul_action semiring
_inst_3: module ↝ distrib_mul_action has_smul
 -/
#check @add_submonoid.add_subset /- _inst_1: add_monoid ↝ add_zero_class
 -/
#check @submonoid.mul_subset /- _inst_1: monoid ↝ mul_one_class
 -/
#check @submonoid.coe_mul_self_eq /- _inst_1: monoid ↝ mul_one_class
 -/
#check @add_submonoid.coe_add_self_eq /- _inst_1: add_monoid ↝ add_zero_class
 -/
#check @submonoid.closure_mul_le /- _inst_1: monoid ↝ mul_one_class
 -/
#check @add_submonoid.closure_add_le /- _inst_1: add_monoid ↝ add_zero_class
 -/

-- data/set_like/basic.lean
#check @set_like.has_mem /- i: set_like ↝ has_coe_t
 -/
#check @set_like.has_coe_to_sort /- i: set_like ↝ has_mem
 -/
#check @set_like.coe_sort_coe /- i: set_like ↝ has_coe_t has_coe_to_sort
 -/
#check @set_like.exists /- i: set_like ↝ has_coe_t has_coe_to_sort has_mem
 -/
#check @set_like.forall /- i: set_like ↝ has_coe_t has_coe_to_sort has_mem
 -/
#check @set_like.mem_coe /- i: set_like ↝ has_coe_t has_mem
 -/
#check @set_like.coe_eq_coe /- i: set_like ↝ has_coe_to_sort has_mem
 -/
#check @set_like.coe_mk /- i: set_like ↝ has_mem
 -/
#check @set_like.coe_mem /- i: set_like ↝ has_coe_to_sort has_mem
 -/
#check @set_like.eta /- i: set_like ↝ has_coe_to_sort has_mem
 -/
#check @set_like.le_def /- i: set_like ↝ has_le has_mem
 -/
#check @set_like.coe_subset_coe /- i: set_like ↝ has_coe_t has_le
 -/
#check @set_like.coe_ssubset_coe /- i: set_like ↝ has_coe_t has_lt
 -/
#check @set_like.not_le_iff_exists /- i: set_like ↝ has_coe_t has_le has_mem
 -/
#check @set_like.exists_of_lt /- i: set_like ↝ has_coe_t has_lt has_mem
 -/

-- data/vector/basic.lean
#check @vector.comp_traverse /- _inst_3: is_lawful_applicative ↝
 -/

-- data/zmod/algebra.lean
#check @zmod.algebra.subsingleton /- _inst_1: ring ↝ semiring
 -/

-- data/zmod/basic.lean
#check @zmod.nat_cast_comp_val /- _inst_1: ring ↝ add_group_with_one
 -/
#check @zmod.int_cast_comp_cast /- _inst_1: ring ↝ add_group_with_one
 -/
#check @zmod.cast_one /- _inst_1: ring ↝ add_group_with_one subsingleton
 -/
#check @zmod.cast_add /- _inst_1: ring ↝ add_group_with_one
 -/
#check @zmod.cast_mul /- _inst_1: ring ↝ non_assoc_ring
 -/
#check @ring_hom.ext_zmod /- _inst_1: semiring ↝ non_assoc_semiring
 -/
#check @zmod.ring_hom_map_cast /- _inst_1: ring ↝ non_assoc_ring
 -/
#check @zmod.ring_hom_eq_of_ker_eq /- _inst_1: comm_ring ↝ ring
 -/

-- deprecated/group.lean
#check @is_add_hom.add /- _inst_4: add_semigroup ↝ has_add
 -/
#check @is_mul_hom.mul /- _inst_4: semigroup ↝ has_mul
 -/
#check @is_add_hom.neg /- _inst_5: add_comm_group ↝ subtraction_comm_monoid
 -/
#check @is_mul_hom.inv /- _inst_5: comm_group ↝ division_comm_monoid
 -/
#check @add_equiv.is_add_hom /- _inst_1: add_zero_class ↝ has_add
_inst_2: add_zero_class ↝ has_add
 -/
#check @mul_equiv.is_mul_hom /- _inst_1: mul_one_class ↝ has_mul
_inst_2: mul_one_class ↝ has_mul
 -/
#check @is_add_monoid_hom.neg /- _inst_4: add_comm_group ↝ subtraction_comm_monoid
 -/
#check @is_monoid_hom.inv /- _inst_4: comm_group ↝ division_comm_monoid
 -/
#check @is_add_hom.to_is_add_monoid_hom /- _inst_2: add_group ↝ add_left_cancel_monoid
 -/
#check @is_mul_hom.to_is_monoid_hom /- _inst_2: group ↝ left_cancel_monoid
 -/
#check @ring_hom.to_is_add_group_hom /- _inst_1: ring ↝ non_assoc_ring
_inst_2: ring ↝ non_assoc_ring
 -/

-- deprecated/subfield.lean
#check @field.closure /- _inst_1: field ↝ has_div ring
 -/

-- deprecated/subgroup.lean
#check @is_subgroup.trivial /- _inst_2: group ↝ has_one
 -/
#check @is_add_subgroup.trivial /- _inst_2: add_group ↝ has_zero
 -/
#check @is_subgroup.center /- _inst_2: group ↝ has_mul
 -/
#check @is_add_subgroup.add_center /- _inst_2: add_group ↝ has_add
 -/
#check @is_subgroup.normalizer /- _inst_1: group ↝ has_inv has_mul
 -/
#check @is_add_subgroup.add_normalizer /- _inst_1: add_group ↝ has_add has_neg
 -/

-- deprecated/submonoid.lean
#check @powers /- _inst_1: monoid ↝ has_pow
 -/

-- dynamics/flow.lean
#check @is_fw_invariant /- _inst_1: preorder ↝ has_le
 -/
#check @flow.is_invariant_iff_image_eq /- _inst_1: add_comm_group ↝ add_group has_continuous_add
_inst_3: topological_add_group ↝ has_continuous_add
 -/

-- dynamics/omega_limit.lean
#check @flow.omega_limit_image_eq /- _inst_2: add_comm_group ↝ add_group has_continuous_add
_inst_3: topological_add_group ↝ has_continuous_add
 -/
#check @flow.omega_limit_omega_limit /- _inst_2: add_comm_group ↝ add_group has_continuous_add
_inst_3: topological_add_group ↝ has_continuous_add
 -/

-- dynamics/periodic_pts.lean
#check @mul_action.pow_smul_eq_iff_minimal_period_dvd /- _inst_1: group ↝ monoid
 -/
#check @add_action.nsmul_vadd_eq_iff_minimal_period_dvd /- _inst_1: add_group ↝ add_monoid
 -/

-- field_theory/adjoin.lean
#check @intermediate_field.fintype_of_alg_hom_adjoin_integral /- _inst_4: field ↝ comm_ring is_domain
 -/
#check @intermediate_field.lifts /- _inst_3: field ↝ semiring
 -/

-- field_theory/cardinality.lean
#check @fintype.is_prime_pow_card_of_field /- _inst_2: field ↝ euclidean_domain no_zero_divisors
 -/

-- field_theory/finite/basic.lean
#check @finite_field.prod_univ_units_id_eq_neg_one /- _inst_2: is_domain ↝ no_zero_divisors
 -/
#check @finite_field.card /- _inst_1: field ↝ euclidean_domain no_zero_divisors
 -/
#check @finite_field.X_pow_card_sub_X_nat_degree_eq /- _inst_3: field ↝ euclidean_domain
 -/
#check @finite_field.frobenius_pow /- _inst_1: field ↝ semifield
 -/
#check @char_p.sq_add_sq /- _inst_1: comm_ring ↝ euclidean_domain no_zero_divisors
_inst_2: is_domain ↝ no_zero_divisors nontrivial
 -/
#check @finite_field.is_square_of_char_two /- _inst_1: field ↝ comm_ring is_reduced
 -/
#check @finite_field.exists_nonsquare /- _inst_1: field ↝ euclidean_domain
 -/

-- field_theory/finite/galois_field.lean
#check @galois_poly_separable /- _inst_1: field ↝ comm_ring module
 -/

-- field_theory/fixed.lean
#check @linear_independent_to_linear_map /- _inst_7: ring ↝ module module semiring
_inst_10: is_domain ↝ no_zero_divisors
 -/
#check @cardinal_mk_alg_hom /- _inst_7: field ↝ finite_dimensional module module no_meet_fake_name ring
_inst_9: finite_dimensional ↝ finite_dimensional no_meet_fake_name
_inst_12: finite_dimensional ↝ finite_dimensional no_meet_fake_name
 -/

-- field_theory/galois.lean
#check @is_galois.integral /- _inst_4: is_galois ↝ normal
 -/
#check @is_galois.separable /- _inst_4: is_galois ↝ is_separable
 -/
#check @is_galois.splits /- _inst_4: is_galois ↝ normal
 -/
#check @is_galois.tower_top_of_is_galois /- _inst_10: is_galois ↝ is_separable normal
 -/
#check @is_galois.of_alg_equiv /- h: is_galois ↝ is_separable normal
 -/

-- field_theory/intermediate_field.lean
#check @intermediate_field.coe_smul /- _inst_6: module ↝ has_smul module no_meet_fake_name
_inst_7: is_scalar_tower ↝ module no_meet_fake_name
 -/
#check @intermediate_field.is_scalar_tower_mid /- _inst_6: algebra ↝ has_smul is_scalar_tower no_meet_fake_name
_inst_7: is_scalar_tower ↝ is_scalar_tower no_meet_fake_name
 -/
#check @intermediate_field.aeval_coe /- _inst_6: comm_ring ↝ algebra algebra comm_semiring module no_meet_fake_name
_inst_7: algebra ↝ algebra has_smul no_meet_fake_name
_inst_9: is_scalar_tower ↝ algebra no_meet_fake_name
 -/
#check @intermediate_field.eq_of_le_of_finrank_le /- _inst_6: finite_dimensional ↝ finite_dimensional no_meet_fake_name
 -/

-- field_theory/is_alg_closed/algebraic_closure.lean
#check @algebraic_closure.monic_irreducible /- _inst_1: field ↝ ring
 -/

-- field_theory/is_alg_closed/basic.lean
#check @is_alg_closed.exists_eval₂_eq_zero_of_injective /- _inst_2: ring ↝ semiring
 -/
#check @is_alg_closed.exists_eval₂_eq_zero /- _inst_2: field ↝ division_ring
 -/
#check @is_alg_closure_iff /- _inst_1: field ↝ comm_ring no_zero_smul_divisors
 -/

-- field_theory/is_alg_closed/classification.lean
#check @algebra.is_algebraic.cardinal_mk_le_sigma_polynomial /- _inst_2: comm_ring ↝ euclidean_domain
_inst_3: is_domain ↝ no_meet_fake_name
 -/

-- field_theory/minpoly.lean
#check @minpoly.aeval_ne_zero_of_dvd_not_unit_minpoly /- _inst_1: comm_ring ↝ algebra euclidean_domain no_zero_divisors
_inst_2: is_domain ↝ no_zero_divisors nontrivial
 -/
#check @minpoly.irreducible /- _inst_1: comm_ring ↝ algebra euclidean_domain no_zero_divisors
_inst_3: ring ↝ euclidean_domain no_zero_divisors
_inst_5: is_domain ↝ no_zero_divisors nontrivial
 -/
#check @minpoly.dvd_map_of_is_scalar_tower /- _inst_6: comm_ring ↝ ring
 -/
#check @minpoly.eq_of_algebra_map_eq /- _inst_6: comm_ring ↝ ring
 -/
#check @minpoly.gcd_domain_eq_field_fractions /- _inst_4: comm_ring ↝ algebra field
_inst_13: field ↝ euclidean_domain
 -/
#check @minpoly.gcd_domain_eq_field_fractions' /- _inst_4: comm_ring ↝ field is_scalar_tower
 -/
#check @minpoly.gcd_domain_dvd /- _inst_4: comm_ring ↝ algebra algebra field is_localization is_scalar_tower is_scalar_tower no_meet_fake_name no_zero_smul_divisors
 -/
#check @minpoly.gcd_domain_degree_le_of_ne_zero /- _inst_4: comm_ring ↝ algebra field no_zero_divisors
 -/
#check @minpoly.gcd_domain_unique /- _inst_4: comm_ring ↝ algebra field module
 -/
#check @minpoly.prime /- _inst_2: ring ↝ distrib_mul_action euclidean_domain no_zero_divisors
_inst_3: is_domain ↝ no_zero_divisors nontrivial
 -/
#check @minpoly.root /- _inst_1: field ↝ algebra comm_ring is_domain
 -/
#check @minpoly.coeff_zero_eq_zero /- _inst_2: ring ↝ euclidean_domain
 -/

-- field_theory/mv_polynomial.lean
#check @mv_polynomial.dim_mv_polynomial /- _inst_1: field ↝ comm_ring module strong_rank_condition
 -/

-- field_theory/perfect_closure.lean
#check @perfect_closure.eq_iff /- _inst_2: is_domain ↝ is_reduced
 -/

-- field_theory/primitive_element.lean
#check @field.primitive_element_inf_aux_exists_c /- _inst_1: field ↝ division_ring
_inst_3: field ↝ euclidean_domain has_div is_domain
 -/

-- field_theory/ratfunc.lean
#check @ratfunc.mk_def_of_ne /- hring: comm_ring ↝ euclidean_domain no_zero_divisors
hdomain: is_domain ↝ no_meet_fake_name no_zero_divisors
 -/
#check @ratfunc.mk_eq_localization_mk /- hring: comm_ring ↝ euclidean_domain no_zero_divisors
hdomain: is_domain ↝ no_meet_fake_name no_zero_divisors
 -/
#check @ratfunc.mk_eq_mk /- hring: comm_ring ↝ euclidean_domain no_zero_divisors
hdomain: is_domain ↝ no_meet_fake_name no_zero_divisors
 -/
#check @ratfunc.lift_on_mk /- hring: comm_ring ↝ euclidean_domain no_zero_divisors
hdomain: is_domain ↝ no_meet_fake_name no_zero_divisors
 -/
#check @ratfunc.lift_on_condition_of_lift_on'_condition /- hdomain: is_domain ↝ no_zero_divisors
 -/
#check @ratfunc.lift_on'_mk /- hring: comm_ring ↝ euclidean_domain
hdomain: is_domain ↝ no_meet_fake_name
 -/
#check @ratfunc.induction_on' /- hring: comm_ring ↝ euclidean_domain no_zero_divisors
hdomain: is_domain ↝ no_meet_fake_name no_zero_divisors
 -/
#check @ratfunc.mk_smul /- hring: comm_ring ↝ euclidean_domain has_smul no_zero_divisors
hdomain: is_domain ↝ no_meet_fake_name no_zero_divisors
 -/
#check @ratfunc.map_apply_div_ne_zero /- hring: comm_ring ↝ algebra euclidean_domain no_meet_fake_name no_zero_divisors
hdomain: is_domain ↝ algebra no_meet_fake_name no_zero_divisors
_inst_1: comm_ring ↝ algebra euclidean_domain no_meet_fake_name no_zero_divisors
 -/
#check @ratfunc.map_apply_div /- hring: comm_ring ↝ algebra euclidean_domain no_meet_fake_name
hdomain: is_domain ↝ algebra no_meet_fake_name
 -/
#check @ratfunc.lift_monoid_with_zero_hom_apply_div /- hring: comm_ring ↝ algebra euclidean_domain no_meet_fake_name no_zero_divisors
hdomain: is_domain ↝ algebra no_meet_fake_name no_zero_divisors
 -/
#check @ratfunc.lift_alg_hom_injective /- hring: comm_ring ↝ algebra euclidean_domain no_meet_fake_name
hdomain: is_domain ↝ algebra no_meet_fake_name
 -/
#check @ratfunc.lift_on_div /- hring: comm_ring ↝ algebra euclidean_domain no_meet_fake_name
hdomain: is_domain ↝ algebra no_meet_fake_name
 -/
#check @ratfunc.lift_on'_div /- hring: comm_ring ↝ algebra euclidean_domain no_meet_fake_name
hdomain: is_domain ↝ algebra no_meet_fake_name
 -/
#check @ratfunc.X_ne_zero /- hfield: field ↝ euclidean_domain is_domain
 -/
#check @ratfunc.eval /- _inst_1: field ↝ has_div semiring
 -/

-- field_theory/separable.lean
#check @polynomial.count_roots_le_one /- _inst_1: comm_ring ↝ euclidean_domain
_inst_2: is_domain ↝ no_meet_fake_name
 -/
#check @polynomial.is_unit_or_eq_zero_of_separable_expand /- _inst_1: field ↝ algebra comm_ring is_domain module
 -/
#check @is_separable_tower_top_of_is_separable /- _inst_1: field ↝ comm_ring
_inst_3: field ↝ comm_ring
 -/
#check @is_separable_tower_bot_of_is_separable /- _inst_3: field ↝ euclidean_domain
 -/

-- field_theory/splitting_field.lean
#check @polynomial.splits /- _inst_1: field ↝ semiring
_inst_2: field ↝ comm_ring
 -/
#check @polynomial.roots_map /- _inst_2: field ↝ euclidean_domain is_domain
 -/
#check @lift_of_splits /- _inst_3: field ↝ algebra euclidean_domain is_domain is_scalar_tower module module no_meet_fake_name
 -/
#check @polynomial.factor /- _inst_1: field ↝ comm_ring
 -/

-- field_theory/subfield.lean
#check @subfield_class.coe_rat_mem /- h: subfield_class ↝ no_meet_fake_name subgroup_class subring_class subsemiring_class
 -/
#check @ring_hom.eq_of_eq_on_subfield_top /- _inst_2: field ↝ non_assoc_semiring
 -/

-- field_theory/tower.lean
#check @dim_mul_dim' /- _inst_2: field ↝ division_ring module strong_rank_condition
 -/
#check @finite_dimensional.trans /- _inst_2: field ↝ division_ring module
 -/
#check @finite_dimensional.right /- _inst_2: field ↝ division_ring
_inst_4: algebra ↝ has_smul
 -/
#check @finite_dimensional.linear_map' /- _inst_11: finite_dimensional ↝ finite_dimensional no_meet_fake_name
_inst_14: finite_dimensional ↝ finite_dimensional no_meet_fake_name
 -/

-- geometry/euclidean/basic.lean
#check @euclidean_geometry.angle /- _inst_2: metric_space ↝ pseudo_metric_space
 -/
#check @euclidean_geometry.dist_left_midpoint_eq_dist_right_midpoint /- _inst_2: metric_space ↝ pseudo_metric_space
 -/
#check @euclidean_geometry.inner_weighted_vsub /- _inst_2: metric_space ↝ pseudo_metric_space
 -/
#check @euclidean_geometry.inner_vsub_vsub_of_dist_eq_of_dist_eq /- _inst_2: metric_space ↝ pseudo_metric_space
 -/
#check @euclidean_geometry.dist_smul_vadd_sq /- _inst_2: metric_space ↝ pseudo_metric_space
 -/
#check @euclidean_geometry.dist_sq_smul_orthogonal_vadd_smul_orthogonal_vadd /- _inst_2: metric_space ↝ pseudo_metric_space
 -/
#check @euclidean_geometry.cospherical /- _inst_2: metric_space ↝ has_dist
 -/

-- geometry/euclidean/inversion.lean
#check @euclidean_geometry.inversion /- _inst_2: metric_space ↝ pseudo_metric_space
 -/

-- geometry/euclidean/monge_point.lean
#check @affine.simplex.monge_plane /- _inst_2: metric_space ↝ pseudo_metric_space
 -/
#check @affine.simplex.altitude /- _inst_2: metric_space ↝ pseudo_metric_space
 -/

-- geometry/euclidean/sphere.lean
#check @euclidean_geometry.mul_dist_eq_abs_sub_sq_dist /- _inst_2: metric_space ↝ pseudo_metric_space
 -/

-- geometry/manifold/algebra/monoid.lean
#check @smooth_left_mul_one /- _inst_14: monoid ↝ mul_one_class
 -/
#check @smooth_right_mul_one /- _inst_14: monoid ↝ mul_one_class
 -/

-- geometry/manifold/algebra/smooth_functions.lean
#check @smooth_map.has_zero /- _inst_15: add_monoid ↝ has_zero
 -/
#check @smooth_map.has_one /- _inst_15: monoid ↝ has_one
 -/

-- geometry/manifold/algebra/structures.lean
#check @smooth_ring.to_lie_add_group /- _inst_8: smooth_ring ↝ has_groupoid has_smooth_add has_smooth_mul no_meet_fake_name
 -/
#check @topological_semiring_of_smooth /- _inst_8: smooth_ring ↝ has_smooth_add has_smooth_mul no_meet_fake_name
 -/

-- geometry/manifold/cont_mdiff.lean
#check @cont_mdiff_within_at_iff_of_mem_source /- Is: smooth_manifold_with_corners ↝ has_groupoid
I's: smooth_manifold_with_corners ↝ has_groupoid
 -/
#check @cont_mdiff_on_of_mem_maximal_atlas /- Is: smooth_manifold_with_corners ↝ has_groupoid
 -/
#check @cont_mdiff_on_symm_of_mem_maximal_atlas /- Is: smooth_manifold_with_corners ↝ has_groupoid
 -/

-- geometry/manifold/diffeomorph.lean
#check @diffeomorph.smooth_manifold_with_corners_trans_diffeomorph /- _inst_20: smooth_manifold_with_corners ↝ has_groupoid
 -/

-- geometry/manifold/instances/units_of_normed_algebra.lean
#check @units.chart_at_apply /- _inst_1: normed_ring ↝ charted_space monoid uniform_space
_inst_2: complete_space ↝ charted_space
 -/
#check @units.chart_at_source /- _inst_1: normed_ring ↝ charted_space monoid uniform_space
_inst_2: complete_space ↝ charted_space
 -/
#check @units.smooth_manifold_with_corners /- _inst_4: normed_algebra ↝ normed_space
 -/

-- geometry/manifold/metrizable.lean
#check @manifold_with_corners.metrizable_space /- _inst_3: finite_dimensional ↝ locally_compact_space topological_space.second_countable_topology
 -/

-- geometry/manifold/mfderiv.lean
#check @mdifferentiable_within_at_iff_of_mem_source /- Is: smooth_manifold_with_corners ↝ has_groupoid
I's: smooth_manifold_with_corners ↝ has_groupoid
 -/
#check @mdifferentiable_at_atlas /- _inst_7: smooth_manifold_with_corners ↝ has_groupoid
 -/
#check @mdifferentiable_at_atlas_symm /- _inst_7: smooth_manifold_with_corners ↝ has_groupoid
 -/

-- geometry/manifold/partition_of_unity.lean
#check @smooth_partition_of_unity.finsum_smul_mem_convex /- _inst_4: normed_add_comm_group ↝ seminormed_add_comm_group
 -/

-- geometry/manifold/smooth_manifold_with_corners.lean
#check @smooth_manifold_with_corners.mem_maximal_atlas_of_mem_atlas /- _inst_7: smooth_manifold_with_corners ↝ has_groupoid
 -/
#check @smooth_manifold_with_corners.chart_mem_maximal_atlas /- _inst_7: smooth_manifold_with_corners ↝ has_groupoid
 -/
#check @smooth_manifold_with_corners.prod /- _inst_16: smooth_manifold_with_corners ↝ has_groupoid
_inst_19: smooth_manifold_with_corners ↝ has_groupoid
 -/
#check @topological_space.opens.smooth_manifold_with_corners /- _inst_7: smooth_manifold_with_corners ↝ has_groupoid
 -/

-- geometry/manifold/tangent_bundle.lean
#check @tangent_space /- _inst_7: smooth_manifold_with_corners ↝
 -/

-- group_theory/abelianization.lean
#check @abelianization.hom_ext /- _inst_2: monoid ↝ mul_one_class
 -/

-- group_theory/commutator.lean
#check @subgroup.commutator_def' /- _inst_4: subgroup.normal ↝ no_meet_fake_name subgroup.normal
_inst_5: subgroup.normal ↝ no_meet_fake_name subgroup.normal
 -/

-- group_theory/complement.lean
#check @subgroup.is_complement /- _inst_1: group ↝ has_mul
 -/
#check @add_subgroup.is_complement /- _inst_1: add_group ↝ has_add
 -/
#check @add_subgroup.vadd_to_fun /- _inst_2: add_group ↝ add_action add_monoid
 -/
#check @subgroup.smul_to_fun /- _inst_2: group ↝ monoid mul_action
 -/

-- group_theory/congruence.lean
#check @con.quotient.inhabited /- _inst_1: mul_one_class ↝ has_coe_t has_mul has_one no_meet_fake_name
 -/
#check @add_con.quotient.inhabited /- _inst_1: add_zero_class ↝ has_add has_coe_t has_zero no_meet_fake_name
 -/
#check @add_con.quotient.has_zero /- _inst_1: add_zero_class ↝ has_add has_coe_t has_zero no_meet_fake_name
 -/
#check @con.quotient.has_one /- _inst_1: mul_one_class ↝ has_coe_t has_mul has_one no_meet_fake_name
 -/

-- group_theory/coset.lean
#check @one_left_coset /- _inst_1: monoid ↝ mul_one_class
 -/
#check @zero_left_add_coset /- _inst_1: add_monoid ↝ add_zero_class
 -/
#check @right_coset_one /- _inst_1: monoid ↝ mul_one_class
 -/
#check @right_add_coset_zero /- _inst_1: add_monoid ↝ add_zero_class
 -/
#check @mem_own_left_add_coset /- _inst_1: add_monoid ↝ add_zero_class
 -/
#check @mem_own_left_coset /- _inst_1: monoid ↝ mul_one_class
 -/
#check @mem_own_right_add_coset /- _inst_1: add_monoid ↝ add_zero_class
 -/
#check @mem_own_right_coset /- _inst_1: monoid ↝ mul_one_class
 -/
#check @subgroup.card_eq_card_quotient_mul_card_subgroup /- _inst_4: decidable_pred ↝ decidable_rel no_meet_fake_name
 -/
#check @add_subgroup.card_eq_card_quotient_add_card_add_subgroup /- _inst_4: decidable_pred ↝ decidable_rel no_meet_fake_name
 -/

-- group_theory/double_coset.lean
#check @doset.setoid /- _inst_1: group ↝ has_mul
 -/

-- group_theory/eckmann_hilton.lean
#check @eckmann_hilton.mul_one_class.is_unital /- G: mul_one_class ↝ has_mul has_one is_left_id is_right_id
 -/
#check @eckmann_hilton.add_zero_class.is_unital /- G: add_zero_class ↝ has_add has_zero is_left_id is_right_id
 -/

-- group_theory/exponent.lean
#check @monoid.exponent_exists /- _inst_1: monoid ↝ has_one has_pow
 -/

-- group_theory/finiteness.lean
#check @submonoid.fg /- _inst_1: monoid ↝ mul_one_class
 -/
#check @add_submonoid.fg /- _inst_1: add_monoid ↝ add_zero_class
 -/

-- group_theory/free_abelian_group.lean
#check @free_abelian_group.one_def /- _inst_1: monoid ↝ has_one
 -/
#check @free_abelian_group.of_one /- _inst_1: monoid ↝ has_one
 -/

-- group_theory/free_group.lean
#check @free_group.lift.aux /- _inst_1: group ↝ has_inv has_mul has_one
 -/

-- group_theory/group_action/basic.lean
#check @add_action.orbit /- _inst_2: add_action ↝ has_vadd
 -/
#check @mul_action.orbit /- _inst_2: mul_action ↝ has_smul
 -/
#check @mul_action.fixed_points /- _inst_2: mul_action ↝ has_smul
 -/
#check @add_action.fixed_points /- _inst_2: add_action ↝ has_vadd
 -/
#check @mul_action.fixed_by /- _inst_2: mul_action ↝ has_smul
 -/
#check @add_action.fixed_by /- _inst_2: add_action ↝ has_vadd
 -/
#check @smul_cancel_of_non_zero_divisor /- _inst_2: non_unital_non_assoc_ring ↝ add_group has_smul
 -/

-- group_theory/group_action/defs.lean
#check @smul_mul_smul /- _inst_2: mul_action ↝ has_smul is_scalar_tower
 -/
#check @is_scalar_tower.of_smul_one_mul /- _inst_1: monoid ↝ has_one semigroup
 -/
#check @vadd_comm_class.of_add_vadd_zero /- _inst_1: add_monoid ↝ add_semigroup has_zero
 -/
#check @smul_comm_class.of_mul_smul_one /- _inst_1: monoid ↝ has_one semigroup
 -/

-- group_theory/group_action/embedding.lean
#check @function.embedding.vadd_apply /- _inst_1: add_group ↝ add_monoid has_vadd
_inst_2: add_action ↝ has_vadd has_vadd
 -/
#check @function.embedding.smul_apply /- _inst_1: group ↝ has_smul monoid
_inst_2: mul_action ↝ has_smul has_smul
 -/
#check @function.embedding.coe_vadd /- _inst_1: add_group ↝ add_monoid has_vadd
_inst_2: add_action ↝ has_vadd has_vadd
 -/
#check @function.embedding.coe_smul /- _inst_1: group ↝ has_smul monoid
_inst_2: mul_action ↝ has_smul has_smul
 -/
#check @function.embedding.is_scalar_tower /- _inst_1: group ↝ has_smul monoid
_inst_2: group ↝ has_smul monoid
_inst_4: mul_action ↝ has_smul has_smul
_inst_5: mul_action ↝ has_smul has_smul
 -/
#check @function.embedding.smul_comm_class /- _inst_1: group ↝ has_smul monoid
_inst_2: group ↝ has_smul monoid
_inst_3: mul_action ↝ has_smul has_smul
_inst_4: mul_action ↝ has_smul has_smul
 -/
#check @function.embedding.vadd_comm_class /- _inst_1: add_group ↝ add_monoid has_vadd
_inst_2: add_group ↝ add_monoid has_vadd
_inst_3: add_action ↝ has_vadd has_vadd
_inst_4: add_action ↝ has_vadd has_vadd
 -/
#check @function.embedding.is_central_scalar /- _inst_2: mul_action ↝ has_smul has_smul
 -/

-- group_theory/group_action/group.lean
#check @add_right_cancel_monoid.to_has_faithful_vadd /- _inst_1: add_right_cancel_monoid ↝ add_right_cancel_semigroup has_zero
 -/
#check @right_cancel_monoid.to_has_faithful_smul /- _inst_1: right_cancel_monoid ↝ has_one right_cancel_semigroup
 -/

-- group_theory/group_action/opposite.lean
#check @mul_opposite.op_smul_eq_op_smul_op /- _inst_3: is_central_scalar ↝ is_central_scalar no_meet_fake_name
 -/
#check @add_left_cancel_monoid.to_has_faithful_opposite_scalar /- _inst_1: add_left_cancel_monoid ↝ add_left_cancel_semigroup has_zero
 -/
#check @left_cancel_monoid.to_has_faithful_opposite_scalar /- _inst_1: left_cancel_monoid ↝ has_one left_cancel_semigroup
 -/

-- group_theory/group_action/option.lean
#check @option.smul_none /- _inst_1: has_smul ↝ has_smul
 -/
#check @option.vadd_none /- _inst_1: has_vadd ↝ has_vadd
 -/

-- group_theory/group_action/quotient.lean
#check @add_action.quotient.vadd_mk /- _inst_4: add_action.quotient_action ↝ add_action no_meet_fake_name
 -/
#check @mul_action.quotient.smul_mk /- _inst_4: mul_action.quotient_action ↝ mul_action no_meet_fake_name
 -/
#check @add_action.quotient.vadd_coe /- _inst_4: add_action.quotient_action ↝ add_action no_meet_fake_name
 -/
#check @mul_action.quotient.smul_coe /- _inst_4: mul_action.quotient_action ↝ mul_action no_meet_fake_name
 -/

-- group_theory/group_action/sub_mul_action.lean
#check @sub_mul_action.is_scalar_tower /- _inst_2: mul_action ↝ has_smul has_smul no_meet_fake_name
 -/
#check @sub_mul_action.coe_smul_of_tower /- _inst_2: mul_action ↝ has_smul has_smul no_meet_fake_name
_inst_5: is_scalar_tower ↝ has_smul no_meet_fake_name
 -/
#check @sub_mul_action.is_central_scalar /- _inst_5: is_scalar_tower ↝ has_smul no_meet_fake_name
 -/
#check @sub_mul_action.mul_action /- _inst_2: mul_action ↝ has_smul mul_action no_meet_fake_name
 -/
#check @sub_mul_action.zero_mem /- _inst_3: module ↝ has_smul no_meet_fake_name smul_with_zero
 -/

-- group_theory/group_action/sum.lean
#check @sum.vadd_inl /- _inst_2: has_vadd ↝ has_vadd
 -/
#check @sum.smul_inl /- _inst_2: has_smul ↝ has_smul
 -/
#check @sum.smul_inr /- _inst_1: has_smul ↝ has_smul
 -/
#check @sum.vadd_inr /- _inst_1: has_vadd ↝ has_vadd
 -/
#check @sum.vadd_swap /- _inst_1: has_vadd ↝ has_vadd
_inst_2: has_vadd ↝ has_vadd
 -/
#check @sum.smul_swap /- _inst_1: has_smul ↝ has_smul
_inst_2: has_smul ↝ has_smul
 -/
#check @sum.has_faithful_vadd_left /- _inst_2: has_vadd ↝ has_vadd
 -/
#check @sum.has_faithful_smul_left /- _inst_2: has_smul ↝ has_smul
 -/
#check @sum.has_faithful_vadd_right /- _inst_1: has_vadd ↝ has_vadd
 -/
#check @sum.has_faithful_smul_right /- _inst_1: has_smul ↝ has_smul
 -/

-- group_theory/group_action/units.lean
#check @units.coe_smul /- _inst_1: group ↝ monoid mul_action
_inst_3: mul_action ↝ has_smul mul_action
_inst_4: smul_comm_class ↝ mul_action
_inst_5: is_scalar_tower ↝ mul_action
 -/
#check @units.smul_inv /- _inst_1: group ↝ has_inv monoid mul_action
_inst_3: mul_action ↝ has_smul mul_action
_inst_4: smul_comm_class ↝ mul_action
_inst_5: is_scalar_tower ↝ mul_action
 -/
#check @units.smul_comm_class' /- _inst_1: group ↝ monoid mul_action
_inst_2: group ↝ monoid mul_action
_inst_4: mul_action ↝ has_smul mul_action
_inst_5: smul_comm_class ↝ mul_action
_inst_6: mul_action ↝ has_smul mul_action
_inst_7: smul_comm_class ↝ mul_action
_inst_8: is_scalar_tower ↝ mul_action
_inst_9: is_scalar_tower ↝ mul_action
 -/
#check @units.is_scalar_tower' /- _inst_2: group ↝ monoid mul_action
_inst_3: group ↝ monoid mul_action
_inst_5: mul_action ↝ has_smul mul_action
_inst_6: smul_comm_class ↝ mul_action
_inst_7: mul_action ↝ has_smul mul_action
_inst_8: smul_comm_class ↝ mul_action
_inst_9: is_scalar_tower ↝ mul_action
_inst_10: is_scalar_tower ↝ mul_action
 -/
#check @units.is_scalar_tower'_left /- _inst_1: group ↝ monoid mul_action
_inst_3: mul_action ↝ has_smul mul_action
_inst_6: smul_comm_class ↝ mul_action
_inst_7: is_scalar_tower ↝ mul_action
 -/

-- group_theory/monoid_localization.lean
#check @localization.r /- _inst_1: comm_monoid ↝ mul_one_class
 -/
#check @add_localization.r /- _inst_1: add_comm_monoid ↝ add_zero_class
 -/
#check @submonoid.localization_map.mul_inv_left /- _inst_1: comm_monoid ↝ monoid
 -/
#check @add_submonoid.localization_map.add_neg_left /- _inst_1: add_comm_monoid ↝ add_monoid
 -/
#check @add_submonoid.localization_map.is_add_unit_comp /- _inst_3: add_comm_monoid ↝ add_monoid
 -/
#check @submonoid.localization_map.is_unit_comp /- _inst_3: comm_monoid ↝ monoid
 -/
#check @submonoid.localization_map.sec_zero_fst /- _inst_1: comm_monoid_with_zero ↝ comm_monoid
 -/

-- group_theory/nielsen_schreier.lean
#check @is_free_groupoid.generators /- _inst_1: category_theory.groupoid ↝
 -/

-- group_theory/order_of_element.lean
#check @is_of_fin_add_order /- _inst_2: add_monoid ↝ has_add has_zero
 -/
#check @is_of_fin_order /- _inst_1: monoid ↝ has_mul has_one
 -/
#check @add_order_of /- _inst_1: add_monoid ↝ has_add has_zero
 -/
#check @order_of /- _inst_1: monoid ↝ has_mul has_one
 -/
#check @pow_injective_of_lt_order_of /- _inst_1: left_cancel_monoid ↝ monoid
 -/
#check @nsmul_injective_of_lt_add_order_of /- _inst_1: add_left_cancel_monoid ↝ add_monoid
 -/
#check @mem_multiples_iff_mem_range_add_order_of' /- _inst_1: add_left_cancel_monoid ↝ add_monoid
 -/
#check @mem_powers_iff_mem_range_order_of' /- _inst_1: left_cancel_monoid ↝ monoid
 -/
#check @pow_eq_one_iff_modeq /- _inst_1: left_cancel_monoid ↝ monoid
 -/
#check @is_of_fin_add_order.neg /- _inst_1: add_group ↝ subtraction_monoid
 -/
#check @is_of_fin_order.inv /- _inst_1: group ↝ division_monoid
 -/
#check @add_order_of_dvd_iff_zsmul_eq_zero /- _inst_1: add_group ↝ subtraction_monoid
 -/
#check @order_of_dvd_iff_zpow_eq_one /- _inst_1: group ↝ division_monoid
 -/
#check @order_of_inv /- _inst_1: group ↝ division_monoid
 -/
#check @order_of_neg /- _inst_1: add_group ↝ subtraction_monoid
 -/
#check @nsmul_inj_iff_of_add_order_of_eq_zero /- _inst_1: add_group ↝ add_left_cancel_monoid
 -/
#check @pow_inj_iff_of_order_of_eq_zero /- _inst_1: group ↝ left_cancel_monoid
 -/
#check @order_eq_card_powers /- _inst_5: decidable_eq ↝ decidable_pred
 -/
#check @add_order_of_eq_card_multiples /- _inst_5: decidable_eq ↝ decidable_pred
 -/
#check @decidable_zpowers /- _inst_5: decidable_eq ↝ decidable_pred
 -/
#check @decidable_zmultiples /- _inst_5: decidable_eq ↝ decidable_pred
 -/
#check @order_eq_card_zpowers /- _inst_5: decidable_eq ↝ decidable_pred
 -/
#check @add_order_eq_card_zmultiples /- _inst_5: decidable_eq ↝ decidable_pred
 -/

-- group_theory/p_group.lean
#check @is_p_group /- _inst_1: group ↝ has_one has_pow
 -/

-- group_theory/perm/cycle/basic.lean
#check @equiv.perm.cycle_of /- _inst_1: decidable_eq ↝ decidable_rel no_meet_fake_name
_inst_2: fintype ↝ decidable_rel no_meet_fake_name
 -/

-- group_theory/perm/cycle/type.lean
#check @equiv.perm.vectors_prod_eq_one /- _inst_2: group ↝ has_mul has_one
 -/

-- group_theory/quotient_group.lean
#check @quotient_group.monoid_hom_ext /- _inst_2: group ↝ mul_one_class
 -/
#check @quotient_add_group.add_monoid_hom_ext /- _inst_2: add_group ↝ add_zero_class
 -/

-- group_theory/specific_groups/cyclic.lean
#check @is_simple_group.prime_card /- _inst_1: comm_group ↝ is_cyclic no_meet_fake_name
 -/
#check @is_simple_add_group.prime_card /- _inst_1: add_comm_group ↝ euclidean_domain is_add_cyclic
 -/

-- group_theory/subgroup/basic.lean
#check @sub_mem /- hSM: add_subgroup_class ↝ add_mem_class neg_mem_class no_meet_fake_name
 -/
#check @div_mem /- hSM: subgroup_class ↝ inv_mem_class mul_mem_class no_meet_fake_name
 -/
#check @zsmul_mem /- hSM: add_subgroup_class ↝ add_submonoid_class neg_mem_class no_meet_fake_name
 -/
#check @zpow_mem /- hSM: subgroup_class ↝ inv_mem_class no_meet_fake_name submonoid_class
 -/
#check @inv_mem_iff /- _inst_1: group ↝ division_monoid inv_mem_class no_meet_fake_name
hSG: subgroup_class ↝ inv_mem_class no_meet_fake_name
 -/
#check @neg_mem_iff /- _inst_1: add_group ↝ neg_mem_class no_meet_fake_name subtraction_monoid
hSG: add_subgroup_class ↝ neg_mem_class no_meet_fake_name
 -/
#check @exists_inv_mem_iff_exists_mem /- _inst_1: group ↝ division_monoid inv_mem_class no_meet_fake_name
hSG: subgroup_class ↝ inv_mem_class no_meet_fake_name
 -/
#check @exists_neg_mem_iff_exists_mem /- _inst_1: add_group ↝ neg_mem_class no_meet_fake_name subtraction_monoid
hSG: add_subgroup_class ↝ neg_mem_class no_meet_fake_name
 -/
#check @mul_mem_cancel_right /- hSG: subgroup_class ↝ inv_mem_class mul_mem_class no_meet_fake_name
 -/
#check @add_mem_cancel_right /- hSG: add_subgroup_class ↝ add_mem_class neg_mem_class no_meet_fake_name
 -/
#check @mul_mem_cancel_left /- hSG: subgroup_class ↝ inv_mem_class mul_mem_class no_meet_fake_name
 -/
#check @add_mem_cancel_left /- hSG: add_subgroup_class ↝ add_mem_class neg_mem_class no_meet_fake_name
 -/
#check @group.conjugates_of_set /- _inst_1: group ↝ monoid
 -/
#check @monoid_hom.comap_ker /- _inst_4: group ↝ mul_one_class
 -/
#check @add_monoid_hom.comap_ker /- _inst_4: add_group ↝ add_zero_class
 -/
#check @monoid_hom.eq_of_eq_on_top /- _inst_3: group ↝ mul_one_class
 -/
#check @add_monoid_hom.eq_of_eq_on_top /- _inst_3: add_group ↝ add_zero_class
 -/
#check @monoid_hom.fintype_mrange /- _inst_5: monoid ↝ mul_one_class
_inst_6: monoid ↝ mul_one_class
 -/
#check @add_monoid_hom.fintype_mrange /- _inst_5: add_monoid ↝ add_zero_class
_inst_6: add_monoid ↝ add_zero_class
 -/
#check @is_simple_group.subgroup.is_simple_order /- _inst_4: comm_group ↝ no_meet_fake_name subgroup.normal
 -/
#check @is_simple_add_group.subgroup.is_simple_order /- _inst_4: add_comm_group ↝ add_subgroup.normal euclidean_domain no_meet_fake_name
 -/
#check @add_subgroup.vadd_comm_class_right /- _inst_6: vadd_comm_class ↝ no_meet_fake_name vadd_comm_class
 -/
#check @subgroup.smul_comm_class_right /- _inst_6: smul_comm_class ↝ no_meet_fake_name smul_comm_class
 -/
#check @add_subgroup.ker_saturated /- _inst_4: add_comm_group ↝ add_group
_inst_5: add_comm_group ↝ add_comm_monoid
 -/

-- group_theory/submonoid/pointwise.lean
#check @add_submonoid.mem_smul_pointwise_iff_exists /- _inst_3: group ↝ monoid
 -/

-- group_theory/subsemigroup/center.lean
#check @set.neg_mem_add_center /- _inst_1: add_group ↝ subtraction_monoid
 -/
#check @set.inv_mem_center /- _inst_1: group ↝ division_monoid
 -/
#check @set.add_mem_center /- _inst_1: distrib ↝ has_add has_mul left_distrib_class right_distrib_class
 -/
#check @set.neg_mem_center /- _inst_1: ring ↝ has_distrib_neg has_mul has_neg
 -/

-- group_theory/subsemigroup/centralizer.lean
#check @set.add_mem_centralizer /- _inst_1: distrib ↝ has_add has_mul left_distrib_class right_distrib_class
 -/

-- group_theory/sylow.lean
#check @sylow.pointwise_smul_def /- _inst_2: group ↝ monoid mul_action no_meet_fake_name
 -/
#check @sylow.orbit_eq_top /- _inst_2: fact ↝ mul_action.is_pretransitive no_meet_fake_name
_inst_3: fintype ↝ mul_action.is_pretransitive no_meet_fake_name
 -/
#check @sylow.subsingleton_of_normal /- _inst_2: fact ↝ mul_action.is_pretransitive no_meet_fake_name
_inst_3: fintype ↝ mul_action.is_pretransitive no_meet_fake_name
 -/

-- group_theory/torsion.lean
#check @add_is_torsion.of_surjective /- _inst_1: add_group ↝ add_monoid
_inst_2: add_group ↝ add_monoid
 -/
#check @is_torsion.of_surjective /- _inst_1: group ↝ monoid
_inst_2: group ↝ monoid
 -/
#check @add_is_torsion.extension_closed /- _inst_2: add_group ↝ add_monoid
 -/
#check @is_torsion.extension_closed /- _inst_2: group ↝ monoid
 -/
#check @exponent_exists.is_add_torsion /- _inst_1: add_group ↝ add_monoid
 -/
#check @exponent_exists.is_torsion /- _inst_1: group ↝ monoid
 -/
#check @is_torsion.exponent_exists /- _inst_1: group ↝ monoid
 -/
#check @is_add_torsion.exponent_exists /- _inst_1: add_group ↝ add_monoid
 -/
#check @is_torsion.not_torsion_free /- _inst_1: group ↝ monoid
 -/
#check @add_monoid.is_torsion.not_torsion_free /- _inst_1: add_group ↝ add_monoid
 -/
#check @add_monoid.is_torsion_free.not_torsion /- _inst_1: add_group ↝ add_monoid
 -/
#check @is_torsion_free.not_torsion /- _inst_1: group ↝ monoid
 -/

-- group_theory/transfer.lean
#check @add_subgroup.left_transversals.diff /- _inst_2: add_comm_group ↝ add_comm_monoid
 -/
#check @subgroup.left_transversals.diff /- _inst_2: comm_group ↝ comm_monoid
 -/

-- linear_algebra/adic_completion.lean
#check @Hausdorffification /- _inst_1: comm_ring ↝ comm_semiring has_quotient
_inst_2: add_comm_group ↝ add_comm_monoid has_quotient
 -/
#check @is_adic_complete.of_subsingleton /- _inst_6: subsingleton ↝ is_Hausdorff is_precomplete
 -/
#check @is_adic_complete.le_jacobson_bot /- _inst_6: is_adic_complete ↝ is_Hausdorff is_precomplete
 -/

-- linear_algebra/affine_space/affine_map.lean
#check @affine_map.coe_smul /- _inst_15: distrib_mul_action ↝ has_smul mul_action
_inst_16: smul_comm_class ↝ mul_action
 -/
#check @affine_map.is_central_scalar /- _inst_15: distrib_mul_action ↝ has_smul mul_action smul_comm_class
 -/

-- linear_algebra/affine_space/affine_subspace.lean
#check @vector_span /- _inst_1: ring ↝ semiring
_inst_4: add_torsor ↝ has_vsub
 -/

-- linear_algebra/affine_space/combination.lean
#check @finset.weighted_vsub_of_point /- S: add_torsor ↝ has_vsub
 -/
#check @finset.centroid_weights /- _inst_1: division_ring ↝ has_inv has_nat_cast
 -/

-- linear_algebra/affine_space/finite_dimensional.lean
#check @finite_dimensional_vector_span_of_fintype /- _inst_5: fintype ↝ finite
 -/
#check @finite_dimensional_vector_span_image_of_fintype /- _inst_5: fintype ↝ finite
 -/
#check @finite_dimensional_direction_affine_span_of_fintype /- _inst_5: fintype ↝ finite
 -/
#check @finite_dimensional_direction_affine_span_image_of_fintype /- _inst_5: fintype ↝ finite
 -/
#check @affine_independent.affine_span_eq_top_iff_card_eq_finrank_add_one /- _inst_5: finite_dimensional ↝ finite_dimensional no_meet_fake_name
 -/
#check @collinear /- _inst_1: division_ring ↝ module no_meet_fake_name ring
 -/

-- linear_algebra/affine_space/independent.lean
#check @affine_independent_of_ne /- _inst_1: division_ring ↝ euclidean_domain no_zero_smul_divisors
 -/

-- linear_algebra/affine_space/midpoint.lean
#check @line_map_inv_two /- _inst_1: division_ring ↝ has_inv invertible ring
_inst_2: char_zero ↝ invertible
 -/
#check @homothety_inv_two /- _inst_1: field ↝ comm_ring has_inv invertible
_inst_2: char_zero ↝ invertible
 -/
#check @pi_midpoint_apply /- _inst_1: field ↝ module no_meet_fake_name ring
 -/

-- linear_algebra/affine_space/slope.lean
#check @slope /- _inst_1: field ↝ has_inv has_sub semiring
_inst_3: module ↝ has_smul
_inst_4: add_torsor ↝ has_vsub
 -/

-- linear_algebra/alternating.lean
#check @alternating_map.smul_apply /- _inst_14: distrib_mul_action ↝ has_smul has_smul
_inst_15: smul_comm_class ↝ has_smul
 -/
#check @alternating_map.coe_fn_smul /- _inst_14: distrib_mul_action ↝ has_smul has_smul
_inst_15: smul_comm_class ↝ has_smul
 -/
#check @alternating_map.is_central_scalar /- _inst_14: distrib_mul_action ↝ has_smul has_smul smul_comm_class
 -/
#check @alternating_map.map_swap /- _inst_8: add_comm_group ↝ subtraction_comm_monoid
 -/
#check @alternating_map.map_linear_dependent /- _inst_17: ring ↝ distrib_mul_action semiring
 -/

-- linear_algebra/basic.lean
#check @pi_eq_sum_univ /- _inst_3: semiring ↝ non_assoc_semiring
 -/
#check @submodule.comap_smul /- _inst_1: field ↝ distrib_mul_action division_ring has_smul no_meet_fake_name smul_comm_class
_inst_2: add_comm_group ↝ add_comm_monoid has_smul
_inst_4: add_comm_group ↝ add_comm_monoid distrib_mul_action has_smul has_smul is_scalar_tower no_meet_fake_name smul_comm_class
 -/
#check @linear_map.ker_eq_bot_of_inverse /- _inst_12: ring_hom_inv_pair ↝ ring_hom_comp_triple
 -/
#check @linear_map.range_to_add_subgroup /- _inst_1: ring ↝ semiring
 -/
#check @linear_map.ker_to_add_subgroup /- _inst_2: ring ↝ semiring
_inst_5: add_comm_group ↝ add_comm_monoid
 -/
#check @linear_map.sub_mem_ker_iff /- _inst_1: ring ↝ semiring
_inst_2: ring ↝ semiring
 -/
#check @linear_map.disjoint_ker' /- _inst_2: ring ↝ semiring
 -/
#check @linear_map.ker_le_iff /- _inst_2: ring ↝ semiring
_inst_5: add_comm_group ↝ add_comm_monoid
 -/
#check @linear_map.submodule_image_apply_of_le /- _inst_11: add_comm_group ↝ add_comm_monoid
 -/
#check @linear_equiv.smul_of_ne_zero /- _inst_2: add_comm_group ↝ add_comm_monoid
 -/
#check @submodule.mem_map_equiv /- _inst_1: comm_semiring ↝ ring_hom_surjective semiring
_inst_2: comm_semiring ↝ ring_hom_surjective semiring
 -/
#check @submodule.comap_le_comap_smul /- _inst_1: comm_semiring ↝ distrib_mul_action has_smul no_meet_fake_name semiring smul_comm_class
 -/
#check @submodule.inf_comap_le_comap_add /- _inst_1: comm_semiring ↝ semiring
_inst_2: comm_semiring ↝ semiring
 -/

-- linear_algebra/basis.lean
#check @basis.no_zero_smul_divisors /- _inst_6: no_zero_divisors ↝ no_zero_smul_divisors
 -/
#check @basis.group_smul_span_eq_top /- _inst_1: ring ↝ mul_action semiring
_inst_2: add_comm_group ↝ add_comm_monoid mul_action mul_action
_inst_9: distrib_mul_action ↝ has_smul
_inst_10: distrib_mul_action ↝ mul_action
 -/
#check @nonzero_span_atom /- _inst_1: division_ring ↝ division_semiring mul_action no_meet_fake_name smul_with_zero
_inst_2: add_comm_group ↝ add_comm_monoid has_smul mul_action no_meet_fake_name smul_with_zero
 -/
#check @linear_map.exists_left_inverse_of_injective /- _inst_1: field ↝ division_ring module no_meet_fake_name ring_hom_comp_triple smul_comm_class
 -/
#check @linear_map.exists_right_inverse_of_surjective /- _inst_1: field ↝ division_ring module no_meet_fake_name ring_hom_comp_triple smul_comm_class
_inst_2: add_comm_group ↝ add_comm_monoid module no_meet_fake_name smul_comm_class
 -/
#check @linear_map.exists_extend /- _inst_3: add_comm_group ↝ add_comm_monoid
 -/

-- linear_algebra/bilinear_form.lean
#check @bilin_form.coe_smul /- _inst_17: distrib_mul_action ↝ has_smul has_smul
_inst_18: smul_comm_class ↝ has_smul
 -/
#check @bilin_form.smul_apply /- _inst_17: distrib_mul_action ↝ has_smul has_smul
_inst_18: smul_comm_class ↝ has_smul
 -/
#check @bilin_form.ne_zero_of_not_is_ortho_self /- _inst_13: field ↝ semiring
_inst_14: add_comm_group ↝ add_comm_monoid
 -/
#check @bilin_form.is_ortho_smul_left /- _inst_21: is_domain ↝ no_zero_divisors
_inst_22: add_comm_group ↝ add_comm_monoid has_smul
 -/
#check @bilin_form.is_ortho_smul_right /- _inst_21: is_domain ↝ no_zero_divisors
_inst_22: add_comm_group ↝ add_comm_monoid has_smul
 -/
#check @bilin_form.linear_independent_of_is_Ortho /- _inst_13: field ↝ no_zero_divisors semiring
_inst_14: add_comm_group ↝ add_comm_monoid has_smul
 -/
#check @bilin_form.sum_repr_mul_repr_mul /- _inst_7: comm_semiring ↝ module no_meet_fake_name semiring
 -/
#check @bilin_form.is_alt.neg /- _inst_5: add_comm_group ↝ add_comm_monoid
 -/
#check @bilin_form.is_adjoint_pair.smul /- _inst_7: comm_semiring ↝ distrib_mul_action has_smul no_meet_fake_name semiring smul_comm_class
 -/
#check @bilin_form.is_skew_adjoint /- _inst_4: ring ↝ semiring
 -/
#check @bilin_form.span_singleton_inf_orthogonal_eq_bot /- _inst_13: field ↝ no_meet_fake_name no_zero_divisors semiring smul_with_zero
_inst_14: add_comm_group ↝ add_comm_monoid has_smul no_meet_fake_name smul_with_zero
 -/
#check @bilin_form.orthogonal_span_singleton_eq_to_lin_ker /- _inst_13: field ↝ comm_semiring module module mul_action no_zero_divisors
_inst_14: add_comm_group ↝ add_comm_monoid has_smul module module mul_action
 -/
#check @bilin_form.nondegenerate_restrict_of_disjoint_orthogonal /- _inst_4: ring ↝ module no_meet_fake_name semiring
_inst_5: add_comm_group ↝ add_comm_monoid module no_meet_fake_name
 -/

-- linear_algebra/bilinear_map.lean
#check @linear_map.ext₂ /- _inst_18: module ↝ has_smul module
_inst_30: smul_comm_class ↝ module
 -/
#check @linear_map.congr_fun₂ /- _inst_18: module ↝ has_smul module
_inst_30: smul_comm_class ↝ module
 -/
#check @linear_map.lcompₛₗ /- _inst_1: comm_semiring ↝ module semiring
_inst_2: comm_semiring ↝ module semiring
 -/
#check @linear_map.lsmul_injective /- _inst_1: comm_ring ↝ comm_semiring module
 -/
#check @linear_map.ext_basis /- _inst_1: comm_ring ↝ semiring
_inst_2: comm_ring ↝ module semiring
_inst_3: comm_ring ↝ module semiring
_inst_4: comm_ring ↝ module semiring
_inst_5: add_comm_group ↝ add_comm_monoid
_inst_6: add_comm_group ↝ add_comm_monoid module
_inst_7: add_comm_group ↝ add_comm_monoid has_smul module
_inst_10: module ↝ has_smul module
_inst_12: smul_comm_class ↝ module
 -/
#check @linear_map.sum_repr_mul_repr_mul /- _inst_1: comm_ring ↝ module no_meet_fake_name semiring
_inst_2: comm_ring ↝ module module no_meet_fake_name semiring
_inst_3: comm_ring ↝ module semiring
_inst_4: comm_ring ↝ module semiring
_inst_5: add_comm_group ↝ add_comm_monoid has_smul
_inst_6: add_comm_group ↝ add_comm_monoid has_smul module
_inst_7: add_comm_group ↝ add_comm_monoid has_smul module
 -/

-- linear_algebra/determinant.lean
#check @equiv_of_pi_lequiv_pi /- _inst_12: nontrivial ↝ invariant_basis_number
 -/
#check @linear_map.det_to_matrix_eq_det_to_matrix /- _inst_2: add_comm_group ↝ add_comm_monoid module
 -/
#check @linear_equiv.is_unit_det /- _inst_2: add_comm_group ↝ add_comm_monoid module
_inst_4: add_comm_group ↝ add_comm_monoid module
 -/
#check @linear_map.associated_det_comp_equiv /- _inst_8: add_comm_group ↝ add_comm_monoid
 -/

-- linear_algebra/dimension.lean
#check @dim_le /- _inst_1: ring ↝ semiring
_inst_2: add_comm_group ↝ add_comm_monoid
 -/
#check @lift_dim_range_le /- _inst_1: ring ↝ module no_meet_fake_name semiring
_inst_2: add_comm_group ↝ add_comm_monoid
_inst_4: add_comm_group ↝ add_comm_monoid module no_meet_fake_name
 -/
#check @dim_range_of_surjective /- _inst_2: add_comm_group ↝ add_comm_monoid
 -/
#check @dim_punit /- _inst_1: ring ↝ semiring
 -/
#check @basis.le_span'' /- _inst_1: ring ↝ module no_meet_fake_name ring_hom_comp_triple semiring
_inst_3: add_comm_group ↝ add_comm_monoid
 -/
#check @ideal.rank_eq /- _inst_8: is_domain ↝ no_meet_fake_name no_zero_smul_divisors
 -/
#check @exists_mem_ne_zero_of_dim_pos /- _inst_1: field ↝ euclidean_domain module no_meet_fake_name
 -/
#check @rank /- _inst_2: add_comm_group ↝ add_comm_monoid
_inst_6: add_comm_group ↝ add_comm_monoid module no_meet_fake_name
 -/

-- linear_algebra/dual.lean
#check @module.dual /- _inst_1: comm_semiring ↝ semiring
 -/
#check @module.dual.add_comm_group /- _inst_5: add_comm_group ↝ add_comm_monoid
 -/
#check @basis.eval_ker /- _inst_1: comm_ring ↝ comm_semiring module no_meet_fake_name
_inst_2: add_comm_group ↝ add_comm_monoid module no_meet_fake_name
 -/
#check @basis.dual_dim_eq /- _inst_1: field ↝ comm_ring module no_meet_fake_name
 -/
#check @dual_pair.lc /- _inst_1: comm_ring ↝ semiring
_inst_2: add_comm_group ↝ add_comm_monoid has_smul
_inst_3: module ↝ has_smul
 -/
#check @subspace.module.dual.finite_dimensional /- H: finite_dimensional ↝ module.finite
 -/
#check @subspace.quot_dual_equiv_annihilator /- _inst_6: finite_dimensional ↝ finite_dimensional
 -/
#check @linear_map.dual_map_comp_dual_map /- _inst_6: add_comm_group ↝ add_comm_monoid module no_meet_fake_name
 -/
#check @linear_equiv.dual_map_trans /- _inst_6: add_comm_group ↝ add_comm_monoid module no_meet_fake_name
 -/

-- linear_algebra/eigenspace.lean
#check @module.End.eigenspace /- _inst_1: comm_ring ↝ algebra comm_semiring no_meet_fake_name
 -/
#check @module.End.aeval_apply_of_has_eigenvector /- _inst_4: field ↝ algebra algebra comm_ring mul_action no_meet_fake_name
 -/
#check @module.End.eigenspaces_independent /- _inst_4: field ↝ algebra comm_ring has_smul module no_meet_fake_name no_zero_smul_divisors no_zero_smul_divisors ring_hom_comp_triple smul_comm_class
 -/
#check @module.End.map_generalized_eigenrange_le /- _inst_4: field ↝ algebra comm_ring no_meet_fake_name
 -/

-- linear_algebra/exterior_algebra/of_alternating.lean
#check @alternating_map.module_add_comm_group /- _inst_2: add_comm_group ↝ add_comm_monoid module
 -/

-- linear_algebra/finite_dimensional.lean
#check @finite_dimensional /- _inst_1: division_ring ↝ semiring
_inst_2: add_comm_group ↝ add_comm_monoid
 -/
#check @finite_dimensional.finrank /- _inst_7: add_comm_group ↝ add_comm_monoid
 -/
#check @finite_dimensional.finrank_eq_of_dim_eq /- _inst_1: division_ring ↝ semiring
 -/
#check @finite_dimensional.finite_dimensional_of_finrank_eq_succ /- _inst_6: field ↝ division_ring
 -/
#check @finite_dimensional.fact_finite_dimensional_of_finrank_eq_succ /- _inst_6: field ↝ division_ring
 -/
#check @finite_dimensional.finite_dimensional_iff_of_rank_eq_nsmul /- _inst_6: field ↝ division_ring
 -/
#check @finite_dimensional.finrank_map_subtype_eq /- _inst_1: division_ring ↝ module no_meet_fake_name ring
 -/
#check @linear_map.finite_dimensional_range /- h: finite_dimensional ↝ finite_dimensional no_meet_fake_name
 -/
#check @linear_map.finrank_range_of_inj /- _inst_1: division_ring ↝ module no_meet_fake_name ring ring_hom_surjective
 -/
#check @finrank_top /- _inst_1: division_ring ↝ module no_meet_fake_name ring
 -/
#check @alg_hom.bijective /- _inst_2: field ↝ division_ring module
 -/
#check @submodule.lt_of_le_of_finrank_lt_finrank /- _inst_1: division_ring ↝ module no_meet_fake_name ring
 -/
#check @submodule.finrank_mono /- _inst_6: finite_dimensional ↝ finite_dimensional no_meet_fake_name
 -/
#check @submodule.finrank_lt_finrank_of_lt /- _inst_6: finite_dimensional ↝ finite_dimensional no_meet_fake_name
 -/
#check @submodule.finrank_add_eq_of_is_compl /- _inst_6: finite_dimensional ↝ finite_dimensional no_meet_fake_name
 -/
#check @set.finrank /- _inst_1: division_ring ↝ module no_meet_fake_name ring
 -/
#check @set.finrank_mono /- _inst_1: field ↝ division_ring
 -/
#check @surjective_of_nonzero_of_finrank_eq_one /- _inst_2: add_comm_group ↝ add_comm_monoid distrib_mul_action has_smul
 -/
#check @subalgebra.dim_eq_one_of_eq_bot /- _inst_1: field ↝ euclidean_domain module module module no_meet_fake_name no_zero_smul_divisors strong_rank_condition
_inst_2: field ↝ euclidean_domain module module module no_meet_fake_name no_zero_smul_divisors
 -/
#check @subalgebra_top_dim_eq_submodule_top_dim /- _inst_1: field ↝ comm_ring module module module no_meet_fake_name
_inst_2: field ↝ module module module no_meet_fake_name ring
 -/
#check @subalgebra_top_finrank_eq_submodule_top_finrank /- _inst_1: field ↝ comm_ring module module module no_meet_fake_name
_inst_2: field ↝ module module module no_meet_fake_name ring
 -/
#check @subalgebra.eq_bot_of_finrank_one /- _inst_2: field ↝ euclidean_domain module module no_meet_fake_name no_zero_smul_divisors
 -/

-- linear_algebra/finsupp.lean
#check @finsupp.lhom_ext /- _inst_4: module ↝ module no_meet_fake_name
 -/

-- linear_algebra/finsupp_vector_space.lean
#check @finsupp.basis_single_one /- _inst_1: ring ↝ module no_meet_fake_name semiring
 -/
#check @finsupp.dim_eq /- _inst_1: field ↝ division_ring module no_meet_fake_name strong_rank_condition
 -/
#check @equiv_of_dim_eq_lift_dim /- _inst_1: field ↝ division_ring ring_hom_comp_triple strong_rank_condition
 -/
#check @cardinal_mk_eq_cardinal_mk_field_pow_dim /- _inst_1: field ↝ division_ring strong_rank_condition
 -/
#check @cardinal_lt_aleph_0_of_finite_dimensional /- _inst_4: fintype ↝ finite
 -/

-- linear_algebra/free_algebra.lean
#check @free_algebra.dim_eq /- _inst_1: field ↝ algebra comm_ring no_meet_fake_name strong_rank_condition
 -/

-- linear_algebra/free_module/basic.lean
#check @module.free.tensor /- _inst_2: add_comm_group ↝ add_comm_monoid module
_inst_5: add_comm_group ↝ add_comm_monoid module
 -/

-- linear_algebra/free_module/finite/basic.lean
#check @module.finite.of_basis /- _inst_8: comm_ring ↝ semiring
_inst_9: add_comm_group ↝ add_comm_monoid
 -/

-- linear_algebra/free_module/pid.lean
#check @eq_bot_of_generator_maximal_map_eq_zero /- _inst_2: add_comm_group ↝ add_comm_monoid
 -/
#check @eq_bot_of_generator_maximal_submodule_image_eq_zero /- _inst_2: add_comm_group ↝ add_comm_monoid module no_meet_fake_name
 -/
#check @dvd_generator_iff /- _inst_1: comm_ring ↝ field
 -/
#check @generator_maximal_submodule_image_dvd /- _inst_3: is_principal_ideal_ring ↝ no_meet_fake_name submodule.is_principal
_inst_4: add_comm_group ↝ add_comm_monoid module no_meet_fake_name
 -/
#check @submodule.basis_of_pid_aux /- _inst_1: comm_ring ↝ field has_smul is_noetherian module module mul_action no_meet_fake_name no_zero_divisors ring_hom_comp_triple submodule.is_principal
 -/

-- linear_algebra/general_linear_group.lean
#check @matrix.general_linear_group /- _inst_3: comm_ring ↝ ring
 -/

-- linear_algebra/invariant_basis_number.lean
#check @noetherian_ring_strong_rank_condition /- _inst_3: is_noetherian_ring ↝ is_noetherian
 -/

-- linear_algebra/lagrange.lean
#check @lagrange.basis_divisor /- _inst_1: field ↝ has_inv ring
 -/
#check @lagrange.nodal /- _inst_1: field ↝ comm_ring
 -/
#check @lagrange.nodal_weight /- _inst_1: field ↝ comm_monoid has_inv has_sub
 -/

-- linear_algebra/linear_independent.lean
#check @linear_independent_iff_injective_total /- _inst_2: add_comm_group ↝ add_comm_monoid
 -/
#check @linear_independent.group_smul /- _inst_1: ring ↝ semiring
_inst_2: add_comm_group ↝ add_comm_monoid has_smul
_inst_9: distrib_mul_action ↝ has_smul
 -/
#check @linear_independent.units_smul /- _inst_1: ring ↝ semiring
_inst_2: add_comm_group ↝ add_comm_monoid has_smul is_scalar_tower
 -/
#check @exists_maximal_independent' /- _inst_1: ring ↝ module no_meet_fake_name semiring
_inst_2: add_comm_group ↝ add_comm_monoid
 -/
#check @linear_independent.image_subtype /- _inst_2: add_comm_group ↝ add_comm_monoid
 -/
#check @linear_independent_monoid_hom /- _inst_8: monoid ↝ mul_one_class
 -/
#check @linear_independent_unique_iff /- _inst_1: ring ↝ module no_meet_fake_name semiring
_inst_3: add_comm_group ↝ add_comm_monoid has_smul
 -/

-- linear_algebra/linear_pmap.lean
#check @linear_pmap.smul_apply /- _inst_9: distrib_mul_action ↝ has_smul has_smul
_inst_10: smul_comm_class ↝ has_smul
 -/
#check @linear_pmap.coe_smul /- _inst_9: distrib_mul_action ↝ has_smul has_smul
_inst_10: smul_comm_class ↝ has_smul
 -/

-- linear_algebra/matrix/basis.lean
#check @basis.to_matrix_map_vec_mul /- _inst_7: ring ↝ module semiring
 -/

-- linear_algebra/matrix/bilinear_form.lean
#check @matrix.is_adjoint_pair /- _inst_10: comm_ring ↝ add_comm_monoid has_mul
 -/
#check @is_adjoint_pair_to_bilin /- _inst_11: add_comm_group ↝ add_comm_monoid module module
 -/
#check @matrix.nondegenerate.to_bilin /- _inst_11: add_comm_group ↝ add_comm_monoid module
 -/
#check @matrix.nondegenerate_to_bilin_iff /- _inst_11: add_comm_group ↝ add_comm_monoid module
 -/

-- linear_algebra/matrix/block.lean
#check @matrix.block_triangular_matrix' /- _inst_5: comm_ring ↝ has_zero
 -/
#check @matrix.block_triangular_matrix /- _inst_5: comm_ring ↝ has_zero
 -/

-- linear_algebra/matrix/charpoly/basic.lean
#check @charmatrix /- _inst_1: comm_ring ↝ ring
 -/

-- linear_algebra/matrix/charpoly/coeff.lean
#check @mat_poly_equiv_eq_X_pow_sub_C /- _inst_6: field ↝ algebra algebra comm_ring
 -/

-- linear_algebra/matrix/circulant.lean
#check @matrix.circulant_col_zero_eq /- _inst_1: add_group ↝ subtraction_monoid
 -/
#check @matrix.transpose_circulant /- _inst_1: add_group ↝ subtraction_monoid
 -/
#check @matrix.conj_transpose_circulant /- _inst_2: add_group ↝ subtraction_monoid
 -/
#check @matrix.circulant_mul /- _inst_1: semiring ↝ non_unital_non_assoc_semiring
 -/

-- linear_algebra/matrix/determinant.lean
#check @matrix.det_smul_of_tower /- _inst_7: distrib_mul_action ↝ is_scalar_tower mul_action
 -/
#check @alg_hom.map_det /- _inst_5: comm_ring ↝ algebra comm_semiring
 -/

-- linear_algebra/matrix/diagonal.lean
#check @matrix.proj_diagonal /- _inst_3: comm_ring ↝ comm_semiring distrib_mul_action module module no_meet_fake_name ring_hom_comp_triple smul_comm_class
 -/
#check @matrix.diagonal_to_lin' /- _inst_3: comm_ring ↝ comm_semiring distrib_mul_action module module no_meet_fake_name smul_comm_class
 -/

-- linear_algebra/matrix/dual.lean
#check @linear_map.to_matrix_transpose /- _inst_1: field ↝ comm_ring module module module module no_meet_fake_name ring_hom_comp_triple
 -/

-- linear_algebra/matrix/finite_dimensional.lean
#check @matrix.finite_dimensional /- _inst_3: field ↝ division_ring finite_dimensional module no_meet_fake_name
 -/
#check @matrix.finrank_matrix /- _inst_3: field ↝ division_ring module module no_meet_fake_name
 -/

-- linear_algebra/matrix/hermitian.lean
#check @matrix.is_hermitian /- _inst_2: star_ring ↝ has_star
 -/
#check @matrix.is_hermitian.neg /- _inst_1: ring ↝ has_star non_unital_ring star_add_monoid
 -/
#check @matrix.is_hermitian.sub /- _inst_1: ring ↝ has_star non_unital_ring star_add_monoid
 -/

-- linear_algebra/matrix/is_diag.lean
#check @matrix.is_diag.neg /- _inst_1: add_group ↝ subtraction_monoid
 -/
#check @matrix.is_diag.conj_transpose /- _inst_1: semiring ↝ has_star non_unital_semiring star_add_monoid
_inst_2: star_ring ↝ has_star star_add_monoid
 -/

-- linear_algebra/matrix/nondegenerate.lean
#check @matrix.nondegenerate /- _inst_2: comm_ring ↝ non_unital_non_assoc_semiring
 -/
#check @matrix.nondegenerate_of_det_ne_zero /- _inst_4: is_domain ↝ no_zero_divisors
 -/

-- linear_algebra/matrix/nonsingular_inverse.lean
#check @matrix.inv_of_mul_self /- _inst_3: comm_ring ↝ add_comm_monoid_with_one has_mul
 -/
#check @matrix.mul_inv_of_self /- _inst_3: comm_ring ↝ add_comm_monoid_with_one has_mul
 -/

-- linear_algebra/matrix/reindex.lean
#check @matrix.reindex_linear_equiv_mul /- _inst_2: semiring ↝ add_comm_monoid has_mul module
 -/
#check @matrix.mul_reindex_linear_equiv_one /- _inst_2: semiring ↝ module non_assoc_semiring
 -/

-- linear_algebra/matrix/symmetric.lean
#check @matrix.is_symm_mul_transpose_self /- _inst_2: comm_semiring ↝ add_comm_monoid comm_semigroup
 -/
#check @matrix.is_symm_transpose_mul_self /- _inst_2: comm_semiring ↝ add_comm_monoid comm_semigroup
 -/

-- linear_algebra/matrix/to_lin.lean
#check @algebra.to_matrix_lmul' /- _inst_1: comm_ring ↝ algebra comm_semiring is_scalar_tower module module module module no_meet_fake_name smul_comm_class
_inst_2: comm_ring ↝ algebra is_scalar_tower module module no_meet_fake_name semiring smul_comm_class
 -/
#check @algebra.to_matrix_lsmul /- _inst_1: comm_ring ↝ algebra comm_semiring distrib_mul_action has_smul module module module module no_meet_fake_name
_inst_2: comm_ring ↝ algebra module module no_meet_fake_name semiring
_inst_4: algebra ↝ algebra has_smul is_scalar_tower module module no_meet_fake_name
 -/
#check @linear_map.finite_dimensional' /- _inst_4: finite_dimensional ↝ finite_dimensional
_inst_7: finite_dimensional ↝ finite_dimensional
_inst_8: ring ↝ linear_map.compatible_smul module semiring smul_comm_class
 -/

-- linear_algebra/matrix/to_linear_equiv.lean
#check @matrix.exists_mul_vec_eq_zero_iff /- _inst_6: comm_ring ↝ algebra euclidean_domain is_localization
 -/

-- linear_algebra/matrix/trace.lean
#check @matrix.trace_sub /- _inst_4: add_comm_group ↝ subtraction_comm_monoid
 -/
#check @matrix.trace_neg /- _inst_4: add_comm_group ↝ subtraction_comm_monoid
 -/

-- linear_algebra/matrix/transvection.lean
#check @matrix.transvection /- _inst_4: comm_ring ↝ semiring
 -/
#check @matrix.transvection_struct.det_to_matrix_prod /- _inst_1: field ↝ comm_ring
 -/
#check @matrix.pivot.list_transvec_col /- _inst_1: field ↝ comm_ring has_div
 -/
#check @matrix.pivot.list_transvec_row /- _inst_1: field ↝ comm_ring has_div
 -/
#check @matrix.pivot.reindex_exists_list_transvec_mul_mul_list_transvec_eq_diagonal /- _inst_1: field ↝ algebra comm_ring
 -/

-- linear_algebra/multilinear/basic.lean
#check @multilinear_map.smul_apply /- _inst_16: distrib_mul_action ↝ has_smul has_smul
_inst_18: smul_comm_class ↝ has_smul
 -/
#check @multilinear_map.coe_smul /- _inst_16: distrib_mul_action ↝ has_smul has_smul
_inst_18: smul_comm_class ↝ has_smul
 -/
#check @multilinear_map.map_neg /- _inst_4: add_comm_group ↝ subtraction_comm_monoid
 -/

-- linear_algebra/orientation.lean
#check @basis.adjust_to_orientation /- _inst_1: linear_ordered_comm_ring ↝ ordered_comm_ring
 -/

-- linear_algebra/pi_tensor_product.lean
#check @pi_tensor_product.smul_tprod_coeff' /- _inst_13: distrib_mul_action ↝ has_smul has_smul
_inst_14: smul_comm_class ↝ has_smul
 -/

-- linear_algebra/prod.lean
#check @linear_map.ker_prod_ker_le_ker_coprod /- _inst_12: add_comm_group ↝ add_comm_monoid
 -/

-- linear_algebra/projection.lean
#check @linear_map.ker_id_sub_eq_of_proj /- _inst_1: ring ↝ module no_meet_fake_name ring_hom_comp_triple semiring
 -/
#check @linear_map.range_eq_of_proj /- _inst_1: ring ↝ module no_meet_fake_name semiring
_inst_2: add_comm_group ↝ add_comm_monoid module no_meet_fake_name
 -/
#check @linear_map.of_is_compl /- _inst_4: add_comm_group ↝ add_comm_monoid
 -/
#check @linear_map.of_is_compl_smul /- _inst_11: comm_ring ↝ distrib_mul_action has_smul module no_meet_fake_name ring smul_comm_class
 -/

-- linear_algebra/projective_space/basic.lean
#check @projectivization_setoid /- _inst_1: field ↝ mul_action semiring
_inst_2: add_comm_group ↝ add_comm_monoid mul_action
_inst_3: module ↝ mul_action
 -/

-- linear_algebra/quadratic_form/basic.lean
#check @quadratic_form.polar /- _inst_1: ring ↝ has_sub
_inst_3: add_comm_group ↝ has_add
 -/
#check @quadratic_form.map_smul_of_tower /- _inst_6: module ↝ has_smul
 -/
#check @quadratic_form.polar_smul_left_of_tower /- _inst_7: module ↝ has_smul
 -/
#check @quadratic_form.polar_smul_right_of_tower /- _inst_7: module ↝ has_smul
 -/
#check @quadratic_form.coe_fn_smul /- _inst_5: distrib_mul_action ↝ has_smul has_smul
_inst_6: smul_comm_class ↝ has_smul
 -/
#check @quadratic_form.smul_apply /- _inst_5: distrib_mul_action ↝ has_smul has_smul
_inst_6: smul_comm_class ↝ has_smul
 -/
#check @quadratic_form.pos_def /- _inst_1: ordered_ring ↝ has_lt semiring
 -/
#check @quadratic_form.pos_def.smul /- _inst_4: linear_ordered_comm_ring ↝ has_smul ordered_ring
 -/

-- linear_algebra/quadratic_form/prod.lean
#check @quadratic_form.anisotropic_of_pi /- _inst_15: ordered_ring ↝ module no_meet_fake_name semiring
 -/
#check @quadratic_form.nonneg_pi_iff /- _inst_15: ordered_ring ↝ module no_meet_fake_name ordered_semiring
 -/

-- linear_algebra/quotient.lean
#check @submodule.quotient.mk_smul /- _inst_6: is_scalar_tower ↝ has_smul no_meet_fake_name
 -/
#check @submodule.quotient.smul_comm_class /- _inst_6: is_scalar_tower ↝ has_smul no_meet_fake_name
_inst_9: is_scalar_tower ↝ has_smul no_meet_fake_name
 -/
#check @submodule.quotient.is_scalar_tower /- _inst_6: is_scalar_tower ↝ has_smul no_meet_fake_name
_inst_9: is_scalar_tower ↝ has_smul no_meet_fake_name
 -/
#check @submodule.quotient.is_central_scalar /- _inst_6: is_scalar_tower ↝ has_smul no_meet_fake_name
 -/
#check @submodule.quot_hom_ext /- _inst_4: add_comm_group ↝ add_comm_monoid
 -/
#check @submodule.linear_map_qext /- _inst_4: ring ↝ ring_hom_comp_triple semiring
_inst_5: add_comm_group ↝ add_comm_monoid
 -/
#check @linear_map.range_mkq_comp /- _inst_1: ring ↝ ring_hom_comp_triple semiring
 -/
#check @linear_map.ker_le_range_iff /- _inst_1: ring ↝ semiring
_inst_3: ring ↝ semiring
 -/

-- linear_algebra/ray.lean
#check @same_ray /- _inst_1: ordered_comm_semiring ↝ has_lt semiring
_inst_3: module ↝ has_smul
 -/
#check @smul_ray_of_ne_zero /- _inst_9: smul_comm_class ↝ mul_action
 -/
#check @same_ray_neg_iff /- _inst_1: ordered_comm_ring ↝ distrib_mul_action ordered_comm_semiring
 -/
#check @same_ray_of_mem_orbit /- _inst_2: add_comm_group ↝ add_comm_monoid has_smul mul_action
 -/
#check @units_inv_smul /- _inst_2: add_comm_group ↝ add_comm_monoid distrib_mul_action mul_action smul_comm_class
 -/
#check @same_ray.exists_pos_left /- _inst_2: add_comm_group ↝ add_comm_monoid has_smul mul_action
 -/
#check @same_ray.exists_eq_smul_add /- _inst_2: add_comm_group ↝ add_comm_monoid distrib_mul_action has_smul mul_action no_meet_fake_name smul_with_zero
 -/

-- linear_algebra/sesquilinear_form.lean
#check @linear_map.is_ortho /- _inst_2: comm_semiring ↝ semiring
_inst_5: comm_semiring ↝ module semiring
 -/
#check @linear_map.ortho_smul_left /- _inst_1: field ↝ distrib_mul_action module no_meet_fake_name no_zero_smul_divisors semifield smul_comm_class
_inst_2: field ↝ semifield
_inst_3: add_comm_group ↝ add_comm_monoid has_smul
_inst_5: field ↝ comm_semiring module
_inst_6: add_comm_group ↝ add_comm_monoid module
 -/
#check @linear_map.ortho_smul_right /- _inst_1: field ↝ distrib_mul_action module no_zero_smul_divisors semifield
_inst_2: field ↝ comm_semiring
_inst_3: add_comm_group ↝ add_comm_monoid
_inst_5: field ↝ module semifield
_inst_6: add_comm_group ↝ add_comm_monoid has_smul module
 -/
#check @linear_map.linear_independent_of_is_Ortho /- _inst_1: field ↝ module no_meet_fake_name no_zero_divisors semifield smul_comm_class
_inst_2: field ↝ module semifield
_inst_3: add_comm_group ↝ add_comm_monoid has_smul module
 -/
#check @linear_map.is_refl /- _inst_2: comm_semiring ↝ module semiring
 -/
#check @linear_map.is_alt /- _inst_2: comm_semiring ↝ module semiring
 -/
#check @linear_map.span_singleton_inf_orthogonal_eq_bot /- _inst_1: field ↝ euclidean_domain module no_zero_divisors
 -/
#check @linear_map.orthogonal_span_singleton_eq_to_lin_ker /- _inst_1: field ↝ comm_ring module mul_action no_meet_fake_name no_zero_smul_divisors smul_comm_class
 -/
#check @linear_map.is_adjoint_pair.smul /- _inst_1: comm_ring ↝ comm_semiring distrib_mul_action has_smul module no_meet_fake_name smul_comm_class
_inst_2: add_comm_group ↝ add_comm_monoid distrib_mul_action has_smul has_smul module no_meet_fake_name smul_comm_class
_inst_4: add_comm_group ↝ add_comm_monoid distrib_mul_action has_smul has_smul module no_meet_fake_name smul_comm_class
 -/
#check @linear_map.is_pair_self_adjoint_equiv /- _inst_1: comm_ring ↝ comm_semiring module no_meet_fake_name ring_hom_comp_triple smul_comm_class
_inst_2: add_comm_group ↝ add_comm_monoid module
_inst_4: add_comm_group ↝ add_comm_monoid module
 -/
#check @linear_map.separating_left /- _inst_2: comm_semiring ↝ semiring
_inst_5: comm_semiring ↝ module semiring
 -/
#check @linear_map.separating_right /- _inst_2: comm_semiring ↝ semiring
_inst_5: comm_semiring ↝ module semiring
 -/
#check @linear_map.is_refl.nondegenerate_of_separating_left /- _inst_1: comm_ring ↝ comm_semiring module no_meet_fake_name smul_comm_class
_inst_2: add_comm_group ↝ add_comm_monoid module
 -/
#check @linear_map.is_refl.nondegenerate_of_separating_right /- _inst_1: comm_ring ↝ comm_semiring module no_meet_fake_name smul_comm_class
_inst_2: add_comm_group ↝ add_comm_monoid module
 -/
#check @linear_map.is_Ortho.not_is_ortho_basis_self_of_separating_left /- _inst_1: comm_ring ↝ comm_semiring module module no_meet_fake_name
_inst_2: add_comm_group ↝ add_comm_monoid has_smul module
 -/
#check @linear_map.is_Ortho.separating_left_of_not_is_ortho_basis_self /- _inst_1: comm_ring ↝ comm_semiring module module no_meet_fake_name smul_comm_class
_inst_2: add_comm_group ↝ add_comm_monoid has_smul module
 -/

-- linear_algebra/span.lean
#check @submodule.span_singleton_smul_le /- _inst_9: mul_action ↝ has_smul
 -/
#check @submodule.disjoint_span_singleton /- _inst_8: add_comm_group ↝ add_comm_monoid distrib_mul_action has_smul is_scalar_tower no_meet_fake_name smul_with_zero
 -/
#check @linear_map.span_singleton_sup_ker_eq_top /- _inst_1: field ↝ division_ring
 -/
#check @linear_map.ker_to_span_singleton /- _inst_1: field ↝ distrib_mul_action division_semiring mul_action no_meet_fake_name smul_with_zero
_inst_2: add_comm_group ↝ add_comm_monoid distrib_mul_action has_smul mul_action no_meet_fake_name smul_with_zero
 -/

-- linear_algebra/tensor_product.lean
#check @tensor_product.zero_smul /- _inst_15: module ↝ distrib_mul_action has_smul has_smul no_meet_fake_name smul_with_zero
 -/
#check @tensor_product.smul_tmul' /- _inst_14: distrib_mul_action ↝ has_smul has_smul
_inst_16: smul_comm_class ↝ has_smul
 -/
#check @tensor_product.tmul_smul /- _inst_16: smul_comm_class ↝ has_smul
 -/
#check @tensor_product.is_central_scalar /- _inst_15: module ↝ distrib_mul_action distrib_mul_action has_smul has_smul smul_comm_class
 -/
#check @tensor_product.is_scalar_tower /- _inst_14: distrib_mul_action ↝ has_smul has_smul is_scalar_tower
_inst_16: smul_comm_class ↝ has_smul is_scalar_tower
_inst_19: is_scalar_tower ↝ is_scalar_tower
 -/
#check @tensor_product.neg.aux /- _inst_2: add_comm_group ↝ add_comm_monoid has_neg
_inst_3: add_comm_group ↝ add_comm_monoid
 -/
#check @linear_map.ltensor_sub /- _inst_3: add_comm_group ↝ add_comm_monoid module module
 -/
#check @linear_map.rtensor_sub /- _inst_3: add_comm_group ↝ add_comm_monoid module module
 -/
#check @linear_map.ltensor_neg /- _inst_3: add_comm_group ↝ add_comm_monoid module module
 -/
#check @linear_map.rtensor_neg /- _inst_3: add_comm_group ↝ add_comm_monoid module module
 -/

-- linear_algebra/tensor_product_basis.lean
#check @basis.tensor_product /- _inst_2: add_comm_group ↝ add_comm_monoid module
_inst_4: add_comm_group ↝ add_comm_monoid module
 -/

-- linear_algebra/unitary_group.lean
#check @matrix.unitary_group /- _inst_3: comm_ring ↝ ring
 -/

-- linear_algebra/vandermonde.lean
#check @matrix.vandermonde /- _inst_1: comm_ring ↝ has_pow
 -/
#check @matrix.det_vandermonde_eq_zero_iff /- _inst_1: comm_ring ↝ euclidean_domain no_zero_divisors
_inst_2: is_domain ↝ no_zero_divisors nontrivial
 -/

-- logic/basic.lean
#check @coe_coe /- _inst_1: has_coe ↝ has_lift_t
_inst_2: has_coe_t ↝ has_lift_t
 -/
#check @coe_fn_coe_trans /- _inst_1: has_coe ↝ has_coe_t_aux has_lift_t
_inst_3: has_coe_to_fun ↝ has_coe_to_fun
 -/
#check @coe_fn_coe_trans' /- _inst_1: has_coe ↝ has_coe_t_aux has_lift_t
 -/
#check @coe_fn_coe_base /- _inst_1: has_coe ↝ has_coe_t_aux has_lift_t
 -/
#check @coe_fn_coe_base' /- _inst_1: has_coe ↝ has_coe_t_aux has_lift_t
 -/
#check @coe_sort_coe_trans /- _inst_1: has_coe ↝ has_coe_to_sort has_lift_t
_inst_2: has_coe_t_aux ↝ has_coe_to_sort
 -/
#check @coe_sort_coe_base /- _inst_1: has_coe ↝ has_coe_to_sort has_lift_t
 -/

-- logic/encodable/basic.lean
#check @directed.le_sequence /- _inst_3: preorder ↝ has_le
 -/

-- logic/equiv/basic.lean
#check @equiv.fun_unique /- _inst_1: unique ↝ inhabited subsingleton
 -/

-- logic/equiv/transfer_instance.lean
#check @ring_equiv.local_ring /- _inst_1: comm_semiring ↝ is_local_ring_hom no_meet_fake_name semifield
 -/

-- logic/unique.lean
#check @eq_const_of_unique /- _inst_1: unique ↝ inhabited subsingleton
 -/
#check @heq_const_of_unique /- _inst_1: unique ↝ inhabited subsingleton
 -/
#check @unique.bijective /- _inst_1: unique ↝ inhabited subsingleton
_inst_2: unique ↝ subsingleton
 -/

-- measure_theory/constructions/borel_space.lean
#check @borel_eq_top_of_encodable /- _inst_3: encodable ↝ countable
 -/
#check @measurable_set_of_continuous_at /- _inst_14: emetric_space ↝ pseudo_emetric_space
 -/
#check @measurable_set.nhds_within_is_measurably_generated /- _inst_3: opens_measurable_space ↝ filter.is_measurably_generated no_meet_fake_name
 -/
#check @pi.opens_measurable_space_encodable /- _inst_14: encodable ↝ countable
 -/
#check @nhds_within_Icc_is_measurably_generated /- _inst_3: opens_measurable_space ↝ filter.is_measurably_generated filter.is_measurably_generated no_meet_fake_name
_inst_17: order_closed_topology ↝ filter.is_measurably_generated filter.is_measurably_generated no_meet_fake_name
 -/
#check @measurable_set_le' /- _inst_16: partial_order ↝ preorder
 -/
#check @nhds_within_interval_is_measurably_generated /- _inst_3: opens_measurable_space ↝ filter.is_measurably_generated no_meet_fake_name
_inst_17: order_closed_topology ↝ filter.is_measurably_generated no_meet_fake_name
 -/
#check @dense.borel_eq_generate_from_Ico_mem /- _inst_23: no_min_order ↝ no_bot_order
 -/
#check @dense.borel_eq_generate_from_Ioc_mem /- _inst_23: no_max_order ↝ no_top_order
 -/
#check @measure_theory.measure.ext_of_Ico /- _inst_20: conditionally_complete_linear_order ↝ compact_Icc_space linear_order
 -/
#check @measure_theory.measure.ext_of_Ioc /- _inst_20: conditionally_complete_linear_order ↝ compact_Icc_space linear_order
 -/
#check @topological_group.has_measurable_inv /- _inst_17: topological_group ↝ has_continuous_inv
 -/
#check @topological_add_group.has_measurable_neg /- _inst_17: topological_add_group ↝ has_continuous_neg
 -/
#check @measurable_of_continuous_on_compl_singleton /- _inst_16: t1_space ↝ measurable_singleton_class
 -/
#check @has_continuous_inv₀.has_measurable_inv /- _inst_16: group_with_zero ↝ has_inv has_zero
 -/
#check @monotone.measurable /- _inst_6: borel_space ↝ opens_measurable_space
 -/
#check @measurable_set_of_mem_nhds_within_Ioi_aux /- _inst_3: borel_space ↝ measurable_singleton_class opens_measurable_space
 -/
#check @is_R_or_C.measurable_space /- _inst_1: is_R_or_C ↝ topological_space
 -/
#check @is_R_or_C.borel_space /- _inst_1: is_R_or_C ↝ measurable_space topological_space
 -/
#check @tendsto_measure_cthickening /- _inst_1: pseudo_metric_space ↝ pseudo_emetric_space
 -/
#check @tendsto_measure_cthickening_of_is_compact /- _inst_1: metric_space ↝ pseudo_metric_space t2_space
 -/
#check @measurable_norm /- _inst_2: normed_add_comm_group ↝ seminormed_add_comm_group
 -/
#check @measurable_nnnorm /- _inst_2: normed_add_comm_group ↝ seminormed_add_comm_group
 -/
#check @continuous_linear_map.measurable /- _inst_3: normed_add_comm_group ↝ module seminormed_add_comm_group
_inst_4: normed_space ↝ module
_inst_7: normed_add_comm_group ↝ module seminormed_add_comm_group
_inst_8: normed_space ↝ module
 -/
#check @continuous_linear_map.measurable_space /- _inst_3: normed_add_comm_group ↝ module seminormed_add_comm_group
_inst_5: normed_add_comm_group ↝ module seminormed_add_comm_group
 -/
#check @continuous_linear_map.measurable_apply' /- _inst_2: nontrivially_normed_field ↝ module normed_field
 -/

-- measure_theory/constructions/polish.lean
#check @measurable.exists_continuous /- _inst_7: borel_space ↝ opens_measurable_space
 -/
#check @measure_theory.measurably_separable_range_of_disjoint /- _inst_4: borel_space ↝ opens_measurable_space
 -/

-- measure_theory/constructions/prod.lean
#check @measure_theory.measure.prod_restrict /- _inst_8: measure_theory.sigma_finite ↝ measure_theory.sigma_finite no_meet_fake_name
 -/
#check @measure_theory.measure.prod_sum /- _inst_9: fintype ↝ measure_theory.sigma_finite no_meet_fake_name
 -/
#check @measure_theory.measure.sum_prod /- _inst_9: fintype ↝ measure_theory.sigma_finite no_meet_fake_name
 -/
#check @measure_theory.measure.add_prod /- _inst_8: measure_theory.sigma_finite ↝ measure_theory.sigma_finite no_meet_fake_name
_inst_9: measure_theory.sigma_finite ↝ measure_theory.sigma_finite no_meet_fake_name
 -/

-- measure_theory/covering/besicovitch.lean
#check @besicovitch.exist_finset_disjoint_balls_large_measure /- _inst_2: topological_space.second_countable_topology ↝ topological_space.separable_space
 -/

-- measure_theory/covering/besicovitch_vector_space.lean
#check @besicovitch.multiplicity /- _inst_2: normed_add_comm_group ↝ has_norm has_sub
 -/

-- measure_theory/covering/differentiation.lean
#check @vitali_family.measure_le_of_frequently_le /- _inst_3: borel_space ↝ measure_theory.measure.outer_regular
_inst_4: measure_theory.is_locally_finite_measure ↝ measure_theory.measure.outer_regular
 -/
#check @vitali_family.ae_tendsto_rn_deriv /- _inst_5: measure_theory.is_locally_finite_measure ↝ measure_theory.is_locally_finite_measure measure_theory.is_locally_finite_measure measure_theory.measure.have_lebesgue_decomposition no_meet_fake_name
 -/

-- measure_theory/covering/vitali.lean
#check @vitali.exists_disjoint_subfamily_covering_enlargment_closed_ball /- _inst_1: metric_space ↝ pseudo_metric_space
 -/
#check @vitali.exists_disjoint_covering_ae /- _inst_1: metric_space ↝ pseudo_metric_space topological_space.separable_space
 -/

-- measure_theory/covering/vitali_family.lean
#check @vitali_family.fine_subfamily_on.index_countable /- _inst_2: topological_space.second_countable_topology ↝ topological_space.separable_space
 -/

-- measure_theory/decomposition/lebesgue.lean
#check @measure_theory.signed_measure.have_lebesgue_decomposition_neg /- _inst_1: measure_theory.signed_measure.have_lebesgue_decomposition ↝ measure_theory.measure.have_lebesgue_decomposition measure_theory.measure.have_lebesgue_decomposition
 -/
#check @measure_theory.signed_measure.have_lebesgue_decomposition_smul /- _inst_1: measure_theory.signed_measure.have_lebesgue_decomposition ↝ measure_theory.measure.have_lebesgue_decomposition measure_theory.measure.have_lebesgue_decomposition
 -/
#check @measure_theory.signed_measure.have_lebesgue_decomposition_smul_real /- _inst_1: measure_theory.signed_measure.have_lebesgue_decomposition ↝ measure_theory.measure.have_lebesgue_decomposition measure_theory.measure.have_lebesgue_decomposition measure_theory.signed_measure.have_lebesgue_decomposition no_meet_fake_name
 -/
#check @measure_theory.signed_measure.singular_part_add_with_density_rn_deriv_eq /- _inst_1: measure_theory.signed_measure.have_lebesgue_decomposition ↝ measure_theory.measure.have_lebesgue_decomposition measure_theory.measure.have_lebesgue_decomposition
 -/
#check @measure_theory.signed_measure.singular_part_sub /- _inst_2: measure_theory.signed_measure.have_lebesgue_decomposition ↝ measure_theory.signed_measure.have_lebesgue_decomposition no_meet_fake_name
 -/
#check @measure_theory.complex_measure.singular_part_add_with_density_rn_deriv_eq /- _inst_1: measure_theory.complex_measure.have_lebesgue_decomposition ↝ measure_theory.signed_measure.have_lebesgue_decomposition measure_theory.signed_measure.have_lebesgue_decomposition
 -/

-- measure_theory/decomposition/radon_nikodym.lean
#check @measure_theory.signed_measure.with_densityᵥ_rn_deriv_eq /- _inst_1: measure_theory.sigma_finite ↝ measure_theory.measure.have_lebesgue_decomposition measure_theory.measure.have_lebesgue_decomposition
 -/

-- measure_theory/function/ae_eq_fun.lean
#check @measure_theory.ae_eq_fun.smul_comm_class /- _inst_9: smul_comm_class ↝ smul_comm_class
 -/
#check @measure_theory.ae_eq_fun.coe_fn_abs /- _inst_7: topological_lattice ↝ has_continuous_sup
 -/

-- measure_theory/function/ae_eq_of_integral.lean
#check @measure_theory.ae_eq_zero_of_forall_inner /- _inst_3: topological_space.second_countable_topology ↝ topological_space.separable_space
 -/
#check @measure_theory.ae_eq_zero_of_forall_dual /- _inst_4: topological_space.second_countable_topology ↝ topological_space.separable_space
 -/
#check @measure_theory.ae_const_le_iff_forall_lt_measure_zero /- _inst_7: topological_space.first_countable_topology ↝ filter.is_countably_generated no_meet_fake_name
 -/

-- measure_theory/function/ae_measurable_order.lean
#check @measure_theory.ae_measurable_of_exist_almost_disjoint_supersets /- _inst_1: complete_linear_order ↝ no_meet_fake_name order_closed_topology
 -/

-- measure_theory/function/ae_measurable_sequence.lean
#check @ae_seq.supr /- _inst_3: complete_lattice ↝ has_Sup
 -/

-- measure_theory/function/conditional_expectation.lean
#check @measure_theory.ae_strongly_measurable'.sub /- _inst_3: topological_add_group ↝ has_continuous_sub
 -/
#check @measure_theory.Lp_meas.ae_eq_zero_of_forall_set_integral_eq_zero /- _inst_4: inner_product_space ↝ module normed_add_comm_group normed_space
 -/
#check @measure_theory.condexp_ind_smul_smul' /- _inst_1: is_R_or_C ↝ has_continuous_const_smul module normed_field
 -/
#check @measure_theory.condexp_ind_smul_nonneg /- _inst_24: normed_lattice_add_comm_group ↝ normed_linear_ordered_group
 -/
#check @measure_theory.condexp_strongly_measurable_mul_of_bound /- _inst_18: measure_theory.is_finite_measure ↝ measure_theory.is_finite_measure no_meet_fake_name
 -/

-- measure_theory/function/convergence_in_measure.lean
#check @measure_theory.exists_seq_tendsto_ae.exists_nat_measure_lt_two_inv /- _inst_1: metric_space ↝ has_dist
 -/
#check @measure_theory.tendsto_in_measure.exists_seq_tendsto_in_measure_at_top /- _inst_1: metric_space ↝ has_dist
 -/
#check @measure_theory.tendsto_in_measure.ae_measurable /- _inst_2: normed_add_comm_group ↝ metric_space topological_space.pseudo_metrizable_space
 -/

-- measure_theory/function/egorov.lean
#check @measure_theory.egorov.not_convergent_seq /- _inst_1: metric_space ↝ has_dist
_inst_2: preorder ↝ has_le
 -/

-- measure_theory/function/ess_sup.lean
#check @ess_sup_measure_zero /- _inst_1: complete_lattice ↝ no_meet_fake_name
 -/
#check @ess_sup_mono_ae /- _inst_1: complete_lattice ↝ no_meet_fake_name
 -/
#check @ess_inf_mono_ae /- _inst_1: complete_lattice ↝ no_meet_fake_name
 -/
#check @ess_sup_const /- _inst_1: complete_lattice ↝ conditionally_complete_lattice
 -/
#check @ess_sup_le_of_ae_le /- _inst_1: complete_lattice ↝ no_meet_fake_name
 -/
#check @order_iso.ess_sup_apply /- _inst_1: complete_lattice ↝ no_meet_fake_name
_inst_2: complete_lattice ↝ no_meet_fake_name
 -/
#check @ess_sup_mono_measure /- _inst_1: complete_lattice ↝ no_meet_fake_name
 -/
#check @ess_inf_antitone_measure /- _inst_1: complete_lattice ↝ no_meet_fake_name
 -/
#check @ess_sup_smul_measure /- _inst_1: complete_lattice ↝ conditionally_complete_lattice
 -/
#check @ess_sup_comp_le_ess_sup_map_measure /- _inst_1: complete_lattice ↝ no_meet_fake_name
 -/
#check @measurable_embedding.ess_sup_map_measure /- _inst_1: complete_lattice ↝ no_meet_fake_name
 -/
#check @ess_sup_map_measure_of_measurable /- _inst_1: complete_lattice ↝ no_meet_fake_name
 -/
#check @ae_lt_of_ess_sup_lt /- _inst_1: complete_linear_order ↝ no_meet_fake_name
 -/
#check @ess_sup_indicator_eq_ess_sup_restrict /- _inst_1: complete_linear_order ↝ no_meet_fake_name order_bot
 -/
#check @ennreal.ess_sup_liminf_le /- _inst_2: linear_order ↝ preorder
 -/

-- measure_theory/function/floor.lean
#check @int.measurable_floor /- _inst_5: order_topology ↝ order_closed_topology
 -/
#check @int.measurable_ceil /- _inst_5: order_topology ↝ order_closed_topology
 -/
#check @measurable_fract /- _inst_5: order_topology ↝ has_measurable_sub order_closed_topology
_inst_7: borel_space ↝ has_measurable_sub opens_measurable_space
 -/
#check @measurable_set.image_fract /- _inst_5: order_topology ↝ has_measurable_add order_closed_topology
_inst_7: borel_space ↝ has_measurable_add opens_measurable_space
 -/
#check @nat.measurable_floor /- _inst_5: order_topology ↝ order_closed_topology
 -/
#check @nat.measurable_ceil /- _inst_5: order_topology ↝ order_closed_topology
 -/

-- measure_theory/function/jacobian.lean
#check @exists_partition_approximates_linear_on_of_has_fderiv_within_at /- _inst_7: borel_space ↝ opens_measurable_space
 -/
#check @measure_theory.measurable_image_of_fderiv_within /- _inst_3: finite_dimensional ↝ polish_space t2_space
 -/
#check @measure_theory.measurable_embedding_of_fderiv_within /- _inst_3: finite_dimensional ↝ polish_space t2_space
 -/

-- measure_theory/function/l1_space.lean
#check @measure_theory.lintegral_nnnorm_eq_lintegral_edist /- _inst_2: normed_add_comm_group ↝ seminormed_add_comm_group
 -/
#check @measure_theory.lintegral_norm_eq_lintegral_edist /- _inst_2: normed_add_comm_group ↝ seminormed_add_comm_group
 -/
#check @measure_theory.lintegral_edist_triangle /- _inst_2: normed_add_comm_group ↝ seminormed_add_comm_group
 -/
#check @measure_theory.lintegral_nnnorm_zero /- _inst_2: normed_add_comm_group ↝ seminormed_add_comm_group
 -/
#check @measure_theory.lintegral_nnnorm_add_left /- _inst_2: normed_add_comm_group ↝ seminormed_add_comm_group
_inst_3: normed_add_comm_group ↝ has_nnnorm
 -/
#check @measure_theory.lintegral_nnnorm_add_right /- _inst_2: normed_add_comm_group ↝ has_nnnorm
_inst_3: normed_add_comm_group ↝ seminormed_add_comm_group
 -/
#check @measure_theory.lintegral_nnnorm_neg /- _inst_2: normed_add_comm_group ↝ seminormed_add_comm_group
 -/
#check @measure_theory.has_finite_integral /- _inst_2: normed_add_comm_group ↝ has_nnnorm
 -/
#check @measure_theory.all_ae_of_real_F_le_bound /- _inst_2: normed_add_comm_group ↝ has_norm
 -/
#check @measure_theory.all_ae_tendsto_of_real_norm /- _inst_2: normed_add_comm_group ↝ seminormed_add_comm_group
 -/

-- measure_theory/function/l2_space.lean
#check @measure_theory.L2.inner_def /- _inst_3: inner_product_space ↝ has_inner has_inner normed_add_comm_group
 -/
#check @measure_theory.bounded_continuous_function.inner_to_Lp /- _inst_2: measure_theory.measure_space ↝ has_inner measurable_space module
 -/
#check @measure_theory.continuous_map.inner_to_Lp /- _inst_2: measure_theory.measure_space ↝ has_inner measurable_space module
 -/

-- measure_theory/function/locally_integrable.lean
#check @monotone_on.integrable_on_compact /- _inst_9: conditionally_complete_linear_order ↝ compact_Icc_space linear_order
 -/

-- measure_theory/function/lp_order.lean
#check @measure_theory.Lp.coe_fn_le /- _inst_1: normed_lattice_add_comm_group ↝ normed_add_comm_group preorder
 -/

-- measure_theory/function/lp_space.lean
#check @measure_theory.snorm' /- _inst_2: normed_add_comm_group ↝ has_nnnorm
 -/
#check @measure_theory.snorm_ess_sup /- _inst_2: normed_add_comm_group ↝ has_nnnorm
 -/
#check @continuous_linear_map.smul_comp_Lp /- _inst_9: smul_comm_class ↝ module
 -/
#check @measure_theory.Lp.snorm'_lim_eq_lintegral_liminf /- _inst_4: nonempty ↝ filter.ne_bot
_inst_5: linear_order ↝ filter.ne_bot preorder
 -/
#check @measure_theory.Lp.snorm_exponent_top_lim_eq_ess_sup_liminf /- _inst_4: nonempty ↝ filter.ne_bot
_inst_5: linear_order ↝ filter.ne_bot preorder
 -/

-- measure_theory/function/simple_func_dense_lp.lean
#check @measure_theory.simple_func.nnnorm_approx_on_le /- _inst_3: normed_add_comm_group ↝ seminormed_add_comm_group
 -/
#check @measure_theory.simple_func.norm_approx_on_y₀_le /- _inst_3: normed_add_comm_group ↝ seminormed_add_comm_group
 -/
#check @measure_theory.simple_func.norm_approx_on_zero_le /- _inst_3: normed_add_comm_group ↝ seminormed_add_comm_group
 -/
#check @measure_theory.simple_func.mem_ℒp_approx_on /- _inst_5: borel_space ↝ opens_measurable_space
 -/
#check @measure_theory.simple_func.tendsto_approx_on_range_Lp_snorm /- _inst_5: borel_space ↝ opens_measurable_space
 -/
#check @measure_theory.simple_func.exists_forall_norm_le /- _inst_3: normed_add_comm_group ↝ has_norm
 -/
#check @measure_theory.Lp.simple_func.coe_fn_zero /- _inst_4: normed_lattice_add_comm_group ↝ normed_add_comm_group
 -/

-- measure_theory/function/strongly_measurable.lean
#check @measure_theory.strongly_measurable.measurable_set_support /- _inst_4: topological_space.metrizable_space ↝ t1_space topological_space.pseudo_metrizable_space
 -/
#check @measure_theory.strongly_measurable.measurable_set_mul_support /- _inst_4: topological_space.metrizable_space ↝ t1_space topological_space.pseudo_metrizable_space
 -/
#check @measure_theory.strongly_measurable.neg /- _inst_4: topological_add_group ↝ has_continuous_neg
 -/
#check @measure_theory.strongly_measurable.inv /- _inst_4: topological_group ↝ has_continuous_inv
 -/
#check @measurable.strongly_measurable /- _inst_5: topological_space.second_countable_topology ↝ topological_space.separable_space
 -/
#check @strongly_measurable_iff_measurable /- _inst_4: topological_space.metrizable_space ↝ topological_space.pseudo_metrizable_space
 -/
#check @measure_theory.strongly_measurable.measurable_set_eq_fun /- _inst_3: topological_space.metrizable_space ↝ t2_space topological_space.pseudo_metrizable_space
 -/
#check @measure_theory.fin_strongly_measurable.mul /- _inst_3: monoid_with_zero ↝ mul_zero_class
 -/
#check @measure_theory.fin_strongly_measurable.add /- _inst_3: add_monoid ↝ add_zero_class
 -/
#check @measure_theory.fin_strongly_measurable.neg /- _inst_4: topological_add_group ↝ has_continuous_neg
 -/
#check @measure_theory.fin_strongly_measurable.sub /- _inst_3: add_group ↝ subtraction_monoid
 -/
#check @measure_theory.fin_strongly_measurable.const_smul /- _inst_7: has_continuous_smul ↝ has_continuous_const_smul
 -/
#check @measure_theory.ae_strongly_measurable.div /- _inst_5: topological_group ↝ has_continuous_div
 -/
#check @measure_theory.ae_strongly_measurable.sub /- _inst_5: topological_add_group ↝ has_continuous_sub
 -/
#check @measure_theory.ae_strongly_measurable.sup /- _inst_4: semilattice_sup ↝ has_sup
 -/
#check @measure_theory.ae_strongly_measurable.inf /- _inst_4: semilattice_inf ↝ has_inf
 -/
#check @measure_theory.ae_strongly_measurable.edist /- _inst_4: seminormed_add_comm_group ↝ pseudo_emetric_space
 -/
#check @strongly_measurable.apply_continuous_linear_map /- _inst_5: normed_add_comm_group ↝ module module normed_space seminormed_add_comm_group
_inst_7: normed_add_comm_group ↝ module module normed_space seminormed_add_comm_group
 -/
#check @measure_theory.ae_strongly_measurable.apply_continuous_linear_map /- _inst_5: normed_add_comm_group ↝ module module normed_space seminormed_add_comm_group
_inst_7: normed_add_comm_group ↝ module module normed_space seminormed_add_comm_group
 -/
#check @ae_strongly_measurable_with_density_iff /- _inst_4: normed_add_comm_group ↝ seminormed_add_comm_group
 -/
#check @measure_theory.fin_strongly_measurable_iff_measurable /- _inst_2: seminormed_add_comm_group ↝ has_zero opens_measurable_space topological_space topological_space.pseudo_metrizable_space
 -/
#check @measure_theory.measurable_uncurry_of_continuous_of_measurable /- _inst_3: topological_space.metrizable_space ↝ measurable_singleton_class topological_space.pseudo_metrizable_space
 -/
#check @measure_theory.strongly_measurable_uncurry_of_continuous_of_strongly_measurable /- _inst_3: topological_space.metrizable_space ↝ measurable_singleton_class topological_space.pseudo_metrizable_space
 -/

-- measure_theory/function/uniform_integrable.lean
#check @measure_theory.tendsto_indicator_ge /- _inst_1: normed_add_comm_group ↝ seminormed_add_comm_group
 -/
#check @measure_theory.uniform_integrable_subsingleton /- _inst_2: subsingleton ↝ finite
 -/

-- measure_theory/group/action.lean
#check @measure_theory.smul_invariant_measure.smul_nnreal /- _inst_2: measure_theory.smul_invariant_measure ↝ measure_theory.smul_invariant_measure no_meet_fake_name
 -/
#check @measure_theory.vadd_invariant_measure.vadd_nnreal /- _inst_2: measure_theory.vadd_invariant_measure ↝ measure_theory.vadd_invariant_measure no_meet_fake_name
 -/

-- measure_theory/group/arithmetic.lean
#check @measurable_neg_iff /- _inst_4: add_group ↝ has_involutive_neg
 -/
#check @measurable_inv_iff /- _inst_4: group ↝ has_involutive_inv
 -/
#check @ae_measurable_neg_iff /- _inst_4: add_group ↝ has_involutive_neg
 -/
#check @ae_measurable_inv_iff /- _inst_4: group ↝ has_involutive_inv
 -/
#check @measurable_inv_iff₀ /- _inst_4: group_with_zero ↝ has_involutive_inv
 -/
#check @ae_measurable_inv_iff₀ /- _inst_4: group_with_zero ↝ has_involutive_inv
 -/
#check @add_submonoid.has_measurable_vadd /- _inst_4: add_action ↝ has_vadd
 -/
#check @submonoid.has_measurable_smul /- _inst_4: mul_action ↝ has_smul
 -/
#check @add_units.has_measurable_vadd /- _inst_4: add_action ↝ has_vadd
 -/
#check @units.has_measurable_smul /- _inst_4: mul_action ↝ has_smul
 -/

-- measure_theory/group/fundamental_domain.lean
#check @measure_theory.is_add_fundamental_domain.mk' /- _inst_1: add_group ↝ add_monoid
 -/
#check @measure_theory.is_fundamental_domain.mk' /- _inst_1: group ↝ monoid
 -/
#check @measure_theory.is_fundamental_domain.mono /- _inst_1: group ↝ monoid
_inst_2: mul_action ↝ has_smul
 -/
#check @measure_theory.is_add_fundamental_domain.mono /- _inst_1: add_group ↝ add_monoid
_inst_2: add_action ↝ has_vadd
 -/

-- measure_theory/group/integration.lean
#check @measure_theory.integrable.comp_inv /- _inst_6: group ↝ has_inv
 -/
#check @measure_theory.integrable.comp_neg /- _inst_6: add_group ↝ has_neg
 -/
#check @measure_theory.integral_neg_eq_self /- _inst_6: add_group ↝ has_involutive_neg
 -/
#check @measure_theory.integral_inv_eq_self /- _inst_6: group ↝ has_involutive_inv
 -/
#check @measure_theory.integrable.comp_add_left /- _inst_6: add_group ↝ has_add
 -/
#check @measure_theory.integrable.comp_mul_left /- _inst_6: group ↝ has_mul
 -/
#check @measure_theory.integrable.comp_add_right /- _inst_6: add_group ↝ has_add
 -/
#check @measure_theory.integrable.comp_mul_right /- _inst_6: group ↝ has_mul
 -/

-- measure_theory/group/measure.lean
#check @measure_theory.map_div_right_eq_self /- _inst_2: group ↝ div_inv_monoid
 -/
#check @measure_theory.map_sub_right_eq_self /- _inst_2: add_group ↝ sub_neg_monoid
 -/
#check @measure_theory.measure.neg.is_add_right_invariant /- _inst_2: add_group ↝ subtraction_monoid
 -/
#check @measure_theory.measure.inv.is_mul_right_invariant /- _inst_2: group ↝ division_monoid
 -/
#check @measure_theory.measure.neg.is_add_left_invariant /- _inst_2: add_group ↝ subtraction_monoid
 -/
#check @measure_theory.measure.inv.is_mul_left_invariant /- _inst_2: group ↝ division_monoid
 -/
#check @measure_theory.measure.map_sub_left_eq_self /- _inst_2: add_group ↝ sub_neg_monoid
 -/
#check @measure_theory.measure.map_div_left_eq_self /- _inst_2: group ↝ div_inv_monoid
 -/
#check @measure_theory.measure.map_add_right_neg_eq_self /- _inst_2: add_group ↝ has_add has_neg
 -/
#check @measure_theory.measure.map_mul_right_inv_eq_self /- _inst_2: group ↝ has_inv has_mul
 -/
#check @measure_theory.measure.regular.inv /- _inst_5: topological_group ↝ has_continuous_inv
 -/
#check @measure_theory.measure.regular.neg /- _inst_5: topological_add_group ↝ has_continuous_neg
 -/
#check @measure_theory.regular_neg_iff /- _inst_3: borel_space ↝ has_measurable_neg measure_theory.measure.regular
 -/
#check @measure_theory.regular_inv_iff /- _inst_3: borel_space ↝ has_measurable_inv measure_theory.measure.regular
 -/
#check @measure_theory.is_open_pos_measure_of_mul_left_invariant_of_compact /- _inst_3: borel_space ↝ has_measurable_mul
 -/
#check @measure_theory.is_open_pos_measure_of_add_left_invariant_of_compact /- _inst_3: borel_space ↝ has_measurable_add
 -/
#check @measure_theory.measure_lt_top_of_is_compact_of_is_add_left_invariant /- _inst_3: borel_space ↝ has_measurable_add
 -/
#check @measure_theory.measure_lt_top_of_is_compact_of_is_mul_left_invariant /- _inst_3: borel_space ↝ has_measurable_mul
 -/
#check @measure_theory.is_mul_left_invariant.is_mul_right_invariant /- _inst_2: comm_group ↝ comm_semigroup
 -/
#check @measure_theory.is_mul_left_invariant.is_add_right_invariant /- _inst_2: add_comm_group ↝ add_comm_semigroup
 -/
#check @measure_theory.measure.is_locally_finite_measure_of_is_add_haar_measure /- _inst_6: measure_theory.measure.is_add_haar_measure ↝ measure_theory.is_finite_measure_on_compacts
 -/
#check @measure_theory.measure.is_locally_finite_measure_of_is_haar_measure /- _inst_6: measure_theory.measure.is_haar_measure ↝ measure_theory.is_finite_measure_on_compacts
 -/
#check @measure_theory.measure.add_haar_singleton /- _inst_4: measure_theory.measure.is_add_haar_measure ↝ measure_theory.measure.is_add_left_invariant
_inst_5: topological_add_group ↝ has_measurable_add
_inst_6: borel_space ↝ has_measurable_add
 -/
#check @measure_theory.measure.haar_singleton /- _inst_4: measure_theory.measure.is_haar_measure ↝ measure_theory.measure.is_mul_left_invariant
_inst_5: topological_group ↝ has_measurable_mul
_inst_6: borel_space ↝ has_measurable_mul
 -/
#check @measure_theory.measure.is_add_haar_measure.smul /- _inst_4: measure_theory.measure.is_add_haar_measure ↝ measure_theory.is_finite_measure_on_compacts measure_theory.measure.is_add_left_invariant measure_theory.measure.is_open_pos_measure no_meet_fake_name
 -/
#check @measure_theory.measure.is_haar_measure.smul /- _inst_4: measure_theory.measure.is_haar_measure ↝ measure_theory.is_finite_measure_on_compacts measure_theory.measure.is_mul_left_invariant measure_theory.measure.is_open_pos_measure no_meet_fake_name
 -/
#check @measure_theory.measure.is_add_haar_measure_map /- _inst_4: measure_theory.measure.is_add_haar_measure ↝ measure_theory.is_finite_measure_on_compacts measure_theory.measure.is_add_left_invariant measure_theory.measure.is_open_pos_measure
_inst_6: topological_add_group ↝ has_continuous_add
_inst_12: topological_add_group ↝ has_continuous_add
 -/
#check @measure_theory.measure.is_haar_measure_map /- _inst_4: measure_theory.measure.is_haar_measure ↝ measure_theory.is_finite_measure_on_compacts measure_theory.measure.is_mul_left_invariant measure_theory.measure.is_open_pos_measure
_inst_6: topological_group ↝ has_continuous_mul
_inst_12: topological_group ↝ has_continuous_mul
 -/
#check @measure_theory.measure.is_add_haar_measure.sigma_finite /- _inst_4: measure_theory.measure.is_add_haar_measure ↝ measure_theory.is_finite_measure_on_compacts
 -/
#check @measure_theory.measure.is_haar_measure.sigma_finite /- _inst_4: measure_theory.measure.is_haar_measure ↝ measure_theory.is_finite_measure_on_compacts
 -/
#check @measure_theory.measure.prod.is_add_haar_measure /- _inst_9: measure_theory.measure.is_add_haar_measure ↝ measure_theory.is_finite_measure_on_compacts measure_theory.measure.is_add_left_invariant measure_theory.measure.is_open_pos_measure
_inst_10: measure_theory.measure.is_add_haar_measure ↝ measure_theory.is_finite_measure_on_compacts measure_theory.measure.is_add_left_invariant measure_theory.measure.is_open_pos_measure
 -/
#check @measure_theory.measure.prod.is_haar_measure /- _inst_9: measure_theory.measure.is_haar_measure ↝ measure_theory.is_finite_measure_on_compacts measure_theory.measure.is_mul_left_invariant measure_theory.measure.is_open_pos_measure
_inst_10: measure_theory.measure.is_haar_measure ↝ measure_theory.is_finite_measure_on_compacts measure_theory.measure.is_mul_left_invariant measure_theory.measure.is_open_pos_measure
 -/

-- measure_theory/group/pointwise.lean
#check @measurable_set.const_smul₀ /- _inst_3: mul_action_with_zero ↝ has_smul mul_action no_meet_fake_name smul_with_zero
 -/

-- measure_theory/group/prod.lean
#check @measure_theory.map_prod_mul_eq /- _inst_2: group ↝ has_mul
 -/
#check @measure_theory.map_prod_sum_eq /- _inst_2: add_group ↝ has_add
 -/
#check @measure_theory.measurable_measure_mul_right /- _inst_2: group ↝ has_mul has_one
 -/
#check @measure_theory.measurable_measure_add_right /- _inst_2: add_group ↝ has_add has_zero
 -/
#check @measure_theory.quasi_measure_preserving_div /- _inst_2: group ↝ div_inv_monoid has_measurable_div₂ has_measurable_mul
_inst_3: has_measurable_mul₂ ↝ has_measurable_div₂ has_measurable_mul
_inst_6: has_measurable_inv ↝ has_measurable_div₂
 -/
#check @measure_theory.quasi_measure_preserving_sub /- _inst_2: add_group ↝ has_measurable_add has_measurable_sub₂ sub_neg_monoid
_inst_3: has_measurable_add₂ ↝ has_measurable_add has_measurable_sub₂
_inst_6: has_measurable_neg ↝ has_measurable_sub₂
 -/

-- measure_theory/integral/bochner.lean
#check @measure_theory.weighted_smul_smul /- _inst_4: normed_space ↝ has_smul
 -/
#check @measure_theory.integral_norm_eq_lintegral_nnnorm /- _inst_12: normed_add_comm_group ↝ seminormed_add_comm_group
 -/
#check @measure_theory.ae_le_trim_of_strongly_measurable /- _inst_11: linear_order ↝ preorder
 -/

-- measure_theory/integral/circle_integral_transform.lean
#check @complex.circle_transform /- _inst_1: normed_add_comm_group ↝ seminormed_add_comm_group
 -/
#check @complex.circle_transform_deriv /- _inst_1: normed_add_comm_group ↝ seminormed_add_comm_group
 -/

-- measure_theory/integral/divergence_theorem.lean
#check @measure_theory.integral_divergence_of_has_fderiv_within_at_off_countable_of_equiv /- _inst_6: partial_order ↝ preorder
 -/

-- measure_theory/integral/integrable_on.lean
#check @continuous_at.strongly_measurable_at_filter /- _inst_2: normed_add_comm_group ↝ topological_space topological_space.pseudo_metrizable_space
 -/

-- measure_theory/integral/integral_eq_improper.lean
#check @measure_theory.ae_cover.bUnion_Iic_ae_cover /- _inst_1: encodable ↝ countable
 -/
#check @measure_theory.ae_cover.bInter_Ici_ae_cover /- _inst_1: encodable ↝ countable
 -/

-- measure_theory/integral/interval_integral.lean
#check @interval_integral.continuous_within_at_of_dominated_interval /- _inst_5: topological_space.first_countable_topology ↝ filter.is_countably_generated no_meet_fake_name
 -/
#check @interval_integral.continuous_at_of_dominated_interval /- _inst_5: topological_space.first_countable_topology ↝ filter.is_countably_generated no_meet_fake_name
 -/

-- measure_theory/integral/lebesgue.lean
#check @measure_theory.simple_func.coe_le /- _inst_2: preorder ↝ has_le
 -/
#check @measure_theory.simple_func.coe_smul /- _inst_2: has_smul ↝ has_smul has_smul
 -/
#check @measure_theory.simple_func.has_nat_pow /- _inst_2: monoid ↝ has_pow
 -/
#check @measure_theory.simple_func.has_int_pow /- _inst_2: div_inv_monoid ↝ has_pow
 -/
#check @measure_theory.simple_func.supr_approx_apply /- _inst_3: complete_lattice ↝ no_meet_fake_name
 -/
#check @measure_theory.simple_func.fin_meas_supp.add /- _inst_3: add_monoid ↝ add_zero_class
 -/
#check @measure_theory.simple_func.fin_meas_supp.mul /- _inst_3: monoid_with_zero ↝ mul_zero_class
 -/
#check @measure_theory.set_lintegral_const_lt_top /- _inst_1: measure_theory.is_finite_measure ↝ measure_theory.is_finite_measure no_meet_fake_name
 -/
#check @measure_theory.ae_measurable_with_density_iff /- _inst_1: normed_add_comm_group ↝ seminormed_add_comm_group
 -/

-- measure_theory/integral/set_integral.lean
#check @continuous_at.integral_sub_linear_is_o_ae /- _inst_4: opens_measurable_space ↝ filter.is_measurably_generated no_meet_fake_name
 -/
#check @continuous_linear_map.integral_comp_Lp /- _inst_3: is_R_or_C ↝ module nontrivially_normed_field
 -/
#check @continuous_linear_map.set_integral_comp_Lp /- _inst_3: is_R_or_C ↝ module nontrivially_normed_field
 -/

-- measure_theory/integral/set_to_l1.lean
#check @measure_theory.fin_meas_additive /- _inst_8: add_monoid ↝ has_add
 -/
#check @measure_theory.fin_meas_additive.zero /- _inst_8: add_comm_monoid ↝ add_monoid
 -/
#check @measure_theory.fin_meas_additive.smul /- _inst_8: add_comm_monoid ↝ add_monoid has_smul
 -/
#check @measure_theory.fin_meas_additive.of_eq_top_imp_eq_top /- _inst_8: add_comm_monoid ↝ add_monoid
 -/
#check @measure_theory.fin_meas_additive.map_empty_eq_zero /- _inst_9: add_cancel_monoid ↝ add_left_cancel_monoid
 -/
#check @measure_theory.dominated_fin_meas_additive /- _inst_8: seminormed_add_comm_group ↝ add_monoid has_norm
 -/
#check @measure_theory.simple_func.set_to_simple_func /- _inst_3: normed_add_comm_group ↝ seminormed_add_comm_group
_inst_5: normed_add_comm_group ↝ seminormed_add_comm_group
 -/
#check @measure_theory.simple_func.set_to_simple_func_smul /- _inst_10: normed_space ↝ distrib_mul_action has_smul
_inst_12: normed_space ↝ distrib_mul_action has_smul
 -/
#check @measure_theory.simple_func.set_to_simple_func_mono_left /- _inst_8: normed_lattice_add_comm_group ↝ normed_linear_ordered_group
 -/
#check @measure_theory.simple_func.set_to_simple_func_mono_left' /- _inst_8: normed_lattice_add_comm_group ↝ normed_linear_ordered_group
 -/
#check @measure_theory.simple_func.set_to_simple_func_nonneg /- _inst_8: normed_lattice_add_comm_group ↝ normed_linear_ordered_group
_inst_10: normed_lattice_add_comm_group ↝ normed_add_comm_group preorder
 -/
#check @measure_theory.simple_func.set_to_simple_func_nonneg' /- _inst_8: normed_lattice_add_comm_group ↝ normed_linear_ordered_group
_inst_10: normed_lattice_add_comm_group ↝ has_le normed_add_comm_group
 -/
#check @measure_theory.L1.set_to_L1_mono_left' /- _inst_12: normed_lattice_add_comm_group ↝ covariant_class covariant_class normed_add_comm_group order_closed_topology preorder
 -/
#check @measure_theory.continuous_at_set_to_fun_of_dominated /- _inst_10: topological_space.first_countable_topology ↝ filter.is_countably_generated no_meet_fake_name
 -/

-- measure_theory/integral/vitali_caratheodory.lean
#check @measure_theory.simple_func.exists_le_lower_semicontinuous_lintegral_ge /- _inst_3: borel_space ↝ opens_measurable_space
_inst_4: measure_theory.measure.weakly_regular ↝ measure_theory.measure.outer_regular
 -/
#check @measure_theory.simple_func.exists_upper_semicontinuous_le_lintegral_le /- _inst_3: borel_space ↝ opens_measurable_space
 -/

-- measure_theory/measurable_space.lean
#check @measurable_of_empty /- _inst_4: is_empty ↝ subsingleton
 -/
#check @measurable_of_fintype /- _inst_4: fintype ↝ finite
 -/
#check @measurable_set.univ_pi /- _inst_4: encodable ↝ countable
 -/
#check @measurable_set.coe_insert /- _inst_2: measurable_singleton_class ↝ has_insert
 -/

-- measure_theory/measure/ae_disjoint.lean
#check @measure_theory.exists_null_pairwise_disjoint_diff /- _inst_1: encodable ↝ countable
 -/

-- measure_theory/measure/content.lean
#check @measure_theory.content.is_add_left_invariant_inner_content /- _inst_3: topological_add_group ↝ has_continuous_add
 -/
#check @measure_theory.content.is_mul_left_invariant_inner_content /- _inst_3: topological_group ↝ has_continuous_mul
 -/
#check @measure_theory.content.is_add_left_invariant_outer_measure /- _inst_4: topological_add_group ↝ has_continuous_add
 -/
#check @measure_theory.content.is_mul_left_invariant_outer_measure /- _inst_4: topological_group ↝ has_continuous_mul
 -/

-- measure_theory/measure/finite_measure_weak_convergence.lean
#check @measure_theory.finite_measure.coe_smul /- _inst_4: is_scalar_tower ↝ has_smul
_inst_5: is_scalar_tower ↝ has_smul has_smul
 -/

-- measure_theory/measure/haar.lean
#check @measure_theory.measure.haar.add_index /- _inst_1: add_group ↝ has_add
 -/
#check @measure_theory.measure.haar.index /- _inst_1: group ↝ has_mul
 -/
#check @measure_theory.measure.sigma_finite_add_haar_measure /- _inst_7: topological_space.second_countable_topology ↝ sigma_compact_space
 -/
#check @measure_theory.measure.sigma_finite_haar_measure /- _inst_7: topological_space.second_countable_topology ↝ sigma_compact_space
 -/
#check @measure_theory.measure.haar_measure_unique /- _inst_7: topological_space.second_countable_topology ↝ has_measurable_mul₂ measure_theory.sigma_finite
 -/
#check @measure_theory.measure.add_haar_measure_unique /- _inst_7: topological_space.second_countable_topology ↝ has_measurable_add₂ measure_theory.sigma_finite
 -/
#check @measure_theory.measure.is_haar_measure_eq_smul_is_haar_measure /- _inst_9: measure_theory.measure.is_haar_measure ↝ measure_theory.is_finite_measure_on_compacts measure_theory.measure.is_mul_left_invariant measure_theory.measure.is_open_pos_measure measure_theory.sigma_finite
_inst_10: measure_theory.measure.is_haar_measure ↝ measure_theory.is_finite_measure_on_compacts measure_theory.measure.is_mul_left_invariant measure_theory.measure.is_open_pos_measure measure_theory.sigma_finite
 -/
#check @measure_theory.measure.is_add_haar_measure_eq_smul_is_add_haar_measure /- _inst_9: measure_theory.measure.is_add_haar_measure ↝ measure_theory.is_finite_measure_on_compacts measure_theory.measure.is_add_left_invariant measure_theory.measure.is_open_pos_measure measure_theory.sigma_finite
_inst_10: measure_theory.measure.is_add_haar_measure ↝ measure_theory.is_finite_measure_on_compacts measure_theory.measure.is_add_left_invariant measure_theory.measure.is_open_pos_measure measure_theory.sigma_finite
 -/
#check @measure_theory.measure.sub_mem_nhds_zero_of_add_haar_pos /- _inst_6: borel_space ↝ has_measurable_add measure_theory.measure.regular opens_measurable_space
_inst_7: topological_space.second_countable_topology ↝ measure_theory.measure.regular
_inst_8: measure_theory.measure.is_add_haar_measure ↝ measure_theory.measure.is_add_left_invariant measure_theory.measure.regular
_inst_9: locally_compact_space ↝ measure_theory.measure.regular
 -/
#check @measure_theory.measure.div_mem_nhds_one_of_haar_pos /- _inst_6: borel_space ↝ has_measurable_mul measure_theory.measure.regular opens_measurable_space
_inst_7: topological_space.second_countable_topology ↝ measure_theory.measure.regular
_inst_8: measure_theory.measure.is_haar_measure ↝ measure_theory.measure.is_mul_left_invariant measure_theory.measure.regular
_inst_9: locally_compact_space ↝ measure_theory.measure.regular
 -/

-- measure_theory/measure/haar_lebesgue.lean
#check @measure_theory.measure.add_haar_eq_zero_of_disjoint_translates_aux /- _inst_1: normed_add_comm_group ↝ has_measurable_add measure_theory.is_finite_measure_on_compacts measure_theory.measure.is_add_left_invariant no_meet_fake_name proper_space seminormed_add_comm_group
_inst_4: borel_space ↝ has_measurable_add
_inst_5: finite_dimensional ↝ no_meet_fake_name proper_space
_inst_6: measure_theory.measure.is_add_haar_measure ↝ measure_theory.is_finite_measure_on_compacts measure_theory.measure.is_add_left_invariant
 -/
#check @measure_theory.measure.map_linear_map_add_haar_eq_smul_add_haar /- _inst_1: normed_add_comm_group ↝ opens_measurable_space seminormed_add_comm_group t2_space
 -/
#check @measure_theory.measure.add_haar_ball_center /- _inst_7: normed_add_comm_group ↝ has_measurable_add measure_theory.measure.is_add_left_invariant seminormed_add_comm_group
_inst_9: borel_space ↝ has_measurable_add
_inst_10: measure_theory.measure.is_add_haar_measure ↝ measure_theory.measure.is_add_left_invariant
 -/
#check @measure_theory.measure.add_haar_closed_ball_center /- _inst_7: normed_add_comm_group ↝ has_measurable_add measure_theory.measure.is_add_left_invariant seminormed_add_comm_group
_inst_9: borel_space ↝ has_measurable_add
_inst_10: measure_theory.measure.is_add_haar_measure ↝ measure_theory.measure.is_add_left_invariant
 -/
#check @measure_theory.measure.add_haar_sphere /- _inst_7: nontrivial ↝ filter.ne_bot no_meet_fake_name
 -/

-- measure_theory/measure/haar_quotient.lean
#check @subgroup.smul_invariant_measure /- _inst_4: topological_group ↝ has_measurable_mul
_inst_5: borel_space ↝ has_measurable_mul
 -/
#check @add_subgroup.vadd_invariant_measure /- _inst_4: topological_add_group ↝ has_measurable_add
_inst_5: borel_space ↝ has_measurable_add
 -/
#check @quotient_group.has_measurable_smul /- _inst_5: borel_space ↝ opens_measurable_space
 -/
#check @quotient_add_group.has_measurable_vadd /- _inst_5: borel_space ↝ opens_measurable_space
 -/
#check @measure_theory.is_fundamental_domain.map_restrict_quotient /- _inst_12: measure_theory.measure.is_haar_measure ↝ measure_theory.measure.is_mul_left_invariant
 -/
#check @measure_theory.is_add_fundamental_domain.map_restrict_quotient /- _inst_12: measure_theory.measure.is_add_haar_measure ↝ measure_theory.measure.is_add_left_invariant
 -/

-- measure_theory/measure/hausdorff.lean
#check @measure_theory.outer_measure.mk_metric'.pre /- _inst_1: emetric_space ↝ pseudo_emetric_space
 -/
#check @measure_theory.outer_measure.trim_mk_metric /- _inst_4: borel_space ↝ opens_measurable_space
 -/

-- measure_theory/measure/measure_space.lean
#check @measure_theory.measure.smul_to_outer_measure /- _inst_4: is_scalar_tower ↝ has_smul has_smul
 -/
#check @measure_theory.measure.coe_smul /- _inst_4: is_scalar_tower ↝ has_smul
 -/
#check @measure_theory.measure.smul_apply /- _inst_4: is_scalar_tower ↝ has_smul
 -/
#check @measure_theory.measure.smul_comm_class /- _inst_4: is_scalar_tower ↝ has_smul
_inst_6: is_scalar_tower ↝ has_smul
 -/
#check @measure_theory.measure.is_scalar_tower /- _inst_4: is_scalar_tower ↝ has_smul
_inst_6: is_scalar_tower ↝ has_smul
 -/
#check @measure_theory.measure.map_eq_sum /- _inst_3: encodable ↝ countable
 -/
#check @measure_theory.is_finite_measure_smul_of_nnreal_tower /- _inst_7: measure_theory.is_finite_measure ↝ measure_theory.is_finite_measure no_meet_fake_name
 -/
#check @measure_theory.ae_of_forall_measure_lt_top_ae_restrict' /- _inst_3: measure_theory.sigma_finite ↝ measure_theory.sigma_finite no_meet_fake_name
_inst_4: measure_theory.sigma_finite ↝ measure_theory.sigma_finite no_meet_fake_name
 -/
#check @measure_theory.measure.smul_finite /- _inst_3: measure_theory.is_finite_measure ↝ measure_theory.is_finite_measure no_meet_fake_name
 -/
#check @measure_theory.measure.exists_eq_disjoint_finite_spanning_sets_in /- _inst_3: measure_theory.sigma_finite ↝ measure_theory.sigma_finite no_meet_fake_name
_inst_4: measure_theory.sigma_finite ↝ measure_theory.sigma_finite no_meet_fake_name
 -/
#check @measure_Icc_lt_top /- _inst_4: measure_theory.is_locally_finite_measure ↝ measure_theory.is_finite_measure_on_compacts
 -/

-- measure_theory/measure/open_pos.lean
#check @measure_theory.measure.measure_Ioi_pos /- _inst_3: order_topology ↝ order_closed_topology
 -/
#check @measure_theory.measure.measure_Iio_pos /- _inst_3: order_topology ↝ order_closed_topology
 -/
#check @measure_theory.measure.measure_Ioo_pos /- _inst_3: order_topology ↝ order_closed_topology
 -/
#check @measure_theory.measure.measure_Ioo_eq_zero /- _inst_3: order_topology ↝ order_closed_topology
 -/
#check @measure_theory.measure.eq_on_Ioo_of_ae_eq /- _inst_3: order_topology ↝ order_closed_topology
 -/

-- measure_theory/measure/outer_measure.lean
#check @measure_theory.outer_measure.coe_smul /- _inst_2: is_scalar_tower ↝ has_smul
 -/
#check @measure_theory.outer_measure.smul_apply /- _inst_2: is_scalar_tower ↝ has_smul
 -/
#check @measure_theory.outer_measure.smul_comm_class /- _inst_2: is_scalar_tower ↝ has_smul
_inst_4: is_scalar_tower ↝ has_smul
 -/
#check @measure_theory.outer_measure.is_scalar_tower /- _inst_2: is_scalar_tower ↝ has_smul
_inst_4: is_scalar_tower ↝ has_smul
 -/

-- measure_theory/measure/regular.lean
#check @measure_theory.measure.regular.sigma_finite /- _inst_4: measure_theory.measure.regular ↝ measure_theory.is_finite_measure_on_compacts
 -/
#check @measure_theory.measure.weakly_regular.of_pseudo_emetric_sigma_compact_space_of_locally_finite /- _inst_6: borel_space ↝ measure_theory.measure.weakly_regular no_meet_fake_name opens_measurable_space
 -/
#check @measure_theory.measure.regular.of_sigma_compact_space_of_is_locally_finite_measure /- _inst_3: emetric_space ↝ measure_theory.is_finite_measure_on_compacts measure_theory.measure.outer_regular pseudo_emetric_space
_inst_6: borel_space ↝ measure_theory.measure.outer_regular
_inst_7: measure_theory.is_locally_finite_measure ↝ measure_theory.is_finite_measure_on_compacts measure_theory.measure.outer_regular
 -/

-- measure_theory/measure/vector_measure.lean
#check @measure_theory.vector_measure.coe_smul /- _inst_3: semiring ↝ has_smul monoid
_inst_4: distrib_mul_action ↝ has_smul has_smul
_inst_5: has_continuous_const_smul ↝ has_smul
 -/
#check @measure_theory.vector_measure.smul_apply /- _inst_3: semiring ↝ has_smul monoid
_inst_4: distrib_mul_action ↝ has_smul has_smul
_inst_5: has_continuous_const_smul ↝ has_smul
 -/
#check @measure_theory.vector_measure.nonneg_of_zero_le_restrict /- _inst_2: ordered_add_comm_monoid ↝ add_comm_monoid partial_order
 -/
#check @measure_theory.vector_measure.nonpos_of_restrict_le_zero /- _inst_2: ordered_add_comm_monoid ↝ add_comm_monoid partial_order
 -/
#check @measure_theory.vector_measure.zero_le_restrict_not_measurable /- _inst_2: ordered_add_comm_monoid ↝ add_comm_monoid partial_order
 -/
#check @measure_theory.vector_measure.restrict_le_zero_of_not_measurable /- _inst_2: ordered_add_comm_monoid ↝ add_comm_monoid partial_order
 -/
#check @measure_theory.vector_measure.zero_le_restrict_subset /- _inst_2: ordered_add_comm_monoid ↝ add_comm_monoid partial_order
 -/
#check @measure_theory.vector_measure.restrict_le_zero_subset /- _inst_2: ordered_add_comm_monoid ↝ add_comm_monoid partial_order
 -/
#check @measure_theory.vector_measure.absolutely_continuous.map /- _inst_7: measure_theory.measure_space ↝ measurable_space
 -/

-- model_theory/direct_limit.lean
#check @first_order.language.direct_limit.Structure /- _inst_5: nonempty ↝ first_order.language.prestructure no_meet_fake_name
 -/
#check @first_order.language.direct_limit.cg /- _inst_7: encodable ↝ countable
 -/

-- model_theory/elementary_maps.lean
#check @first_order.language.elementary_substructure.nonempty /- h: nonempty ↝ first_order.language.Theory.model no_meet_fake_name
 -/

-- number_theory/arithmetic_function.lean
#check @nat.arithmetic_function.has_mul /- _inst_1: semiring ↝ add_comm_monoid has_smul
 -/
#check @nat.arithmetic_function.one_smul' /- _inst_3: module ↝ has_smul mul_action no_meet_fake_name smul_with_zero
 -/
#check @nat.arithmetic_function.coe_zeta_smul_apply /- _inst_1: comm_ring ↝ mul_action semiring
_inst_2: add_comm_group ↝ add_comm_monoid has_smul mul_action
_inst_3: module ↝ has_smul mul_action
 -/
#check @nat.arithmetic_function.pmul_comm /- _inst_1: comm_monoid_with_zero ↝ non_unital_comm_semiring
 -/
#check @nat.arithmetic_function.is_multiplicative /- _inst_1: monoid_with_zero ↝ has_mul mul_zero_one_class
 -/

-- number_theory/bernoulli.lean
#check @bernoulli'_power_series /- _inst_1: comm_ring ↝ semiring
 -/
#check @bernoulli_power_series /- _inst_1: comm_ring ↝ semiring
 -/

-- number_theory/class_number/finite.lean
#check @class_group.norm_bound_pos /- _inst_2: comm_ring ↝ euclidean_domain module
 -/
#check @class_group.norm_lt /- _inst_2: comm_ring ↝ euclidean_domain module
 -/
#check @class_group.exists_min /- _inst_1: euclidean_domain ↝ comm_ring
_inst_2: comm_ring ↝ euclidean_domain
_inst_3: is_domain ↝ nontrivial
 -/
#check @class_group.exists_mem_finset_approx /- _inst_2: comm_ring ↝ distrib_mul_action euclidean_domain module mul_action
 -/
#check @class_group.exists_mem_finset_approx' /- _inst_2: comm_ring ↝ distrib_mul_action euclidean_domain module no_meet_fake_name smul_comm_class
 -/
#check @class_group.prod_finset_approx_ne_zero /- _inst_2: comm_ring ↝ euclidean_domain module
 -/
#check @class_group.exists_mk0_eq_mk0 /- _inst_2: comm_ring ↝ euclidean_domain module no_zero_divisors
 -/

-- number_theory/cyclotomic/basic.lean
#check @is_cyclotomic_extension.adjoin_roots_cyclotomic_eq_adjoin_nth_roots /- _inst_2: comm_ring ↝ euclidean_domain
 -/
#check @is_cyclotomic_extension.adjoin_roots_cyclotomic_eq_adjoin_root_cyclotomic /- _inst_2: comm_ring ↝ euclidean_domain
 -/
#check @cyclotomic_field.algebra_base /- _inst_7: is_domain ↝
_inst_9: is_fraction_ring ↝
 -/
#check @cyclotomic_ring.cyclotomic_field.is_fraction_ring /- _inst_1: comm_ring ↝ euclidean_domain is_scalar_tower no_meet_fake_name
_inst_7: is_domain ↝ is_scalar_tower no_meet_fake_name
 -/

-- number_theory/cyclotomic/gal.lean
#check @is_primitive_root.aut_to_pow_injective /- _inst_2: field ↝ comm_ring is_domain
 -/

-- number_theory/cyclotomic/primitive_roots.lean
#check @is_primitive_root.norm_eq_neg_one_pow /- _inst_5: field ↝ comm_ring module no_zero_divisors
 -/
#check @is_primitive_root.norm_eq_one /- _inst_5: field ↝ comm_ring is_domain module
 -/
#check @is_primitive_root.norm_eq_one_of_linearly_ordered /- _inst_5: field ↝ comm_ring module
 -/
#check @is_primitive_root.pow_sub_one_norm_two /- _inst_5: field ↝ comm_ring is_domain module no_zero_divisors
 -/

-- number_theory/function_field.lean
#check @function_field /- _inst_1: field ↝ comm_ring is_domain
_inst_2: field ↝ ring
 -/
#check @algebra_map_injective /- _inst_1: field ↝ algebra comm_ring has_smul is_domain no_meet_fake_name
_inst_2: field ↝ division_semiring
 -/
#check @function_field.ring_of_integers /- _inst_1: field ↝ comm_ring
_inst_2: field ↝ comm_ring
 -/

-- number_theory/legendre_symbol/add_character.lean
#check @add_char /- _inst_1: add_monoid ↝ add_zero_class
_inst_2: comm_monoid ↝ mul_one_class
 -/
#check @add_char.has_inv /- _inst_1: add_comm_group ↝ subtraction_comm_monoid
 -/
#check @add_char.is_nontrivial /- _inst_1: comm_ring ↝ add_monoid
_inst_2: comm_ring ↝ comm_monoid
 -/
#check @add_char.mul_shift /- _inst_1: comm_ring ↝ non_unital_non_assoc_semiring
_inst_2: comm_ring ↝ comm_monoid
 -/
#check @add_char.sum_eq_zero_of_is_nontrivial' /- _inst_2: comm_ring ↝ field
_inst_5: is_domain ↝ cancel_monoid_with_zero
 -/

-- number_theory/legendre_symbol/gauss_sum.lean
#check @gauss_sum /- _inst_1: comm_ring ↝ comm_semiring
_inst_3: comm_ring ↝ comm_semiring
 -/
#check @char.card_pow_char_pow /- _inst_3: comm_ring ↝ field no_zero_divisors
_inst_4: is_domain ↝ group_with_zero no_zero_divisors
 -/

-- number_theory/legendre_symbol/mul_character.lean
#check @mul_char.inv_apply_eq_inv' /- _inst_3: field ↝ comm_group_with_zero
 -/
#check @mul_char.inv_apply' /- _inst_3: field ↝ comm_group_with_zero
 -/
#check @mul_char.is_nontrivial /- _inst_1: comm_ring ↝ comm_monoid
_inst_2: comm_ring ↝ comm_monoid_with_zero
 -/
#check @mul_char.is_quadratic /- _inst_1: comm_ring ↝ comm_monoid
_inst_2: comm_ring ↝ comm_monoid_with_zero has_neg
 -/
#check @mul_char.is_nontrivial.sum_eq_zero /- _inst_2: comm_ring ↝ field
_inst_5: is_domain ↝ cancel_monoid_with_zero
 -/
#check @mul_char.sum_one_eq_card_units /- _inst_1: comm_ring ↝ comm_monoid
_inst_2: comm_ring ↝ comm_semiring
 -/

-- number_theory/legendre_symbol/quadratic_char.lean
#check @char.quadratic_char_fun /- _inst_1: monoid_with_zero ↝ has_mul has_zero
 -/
#check @char.quadratic_char_eq_zero_iff' /- _inst_1: field ↝ decidable_pred monoid_with_zero
_inst_2: fintype ↝ decidable_pred
 -/
#check @char.quadratic_char_zero /- _inst_1: field ↝ decidable_pred monoid_with_zero
_inst_2: fintype ↝ decidable_pred
 -/
#check @char.quadratic_char_one /- _inst_1: field ↝ decidable_pred group_with_zero
_inst_2: fintype ↝ decidable_pred
 -/

-- number_theory/number_field.lean
#check @number_field.ring_of_integers /- _inst_1: field ↝ comm_ring
 -/
#check @number_field.ring_of_integers.char_zero /- _inst_3: number_field ↝ char_zero
 -/

-- number_theory/ramification_inertia.lean
#check @ideal.ramification_idx /- _inst_1: comm_ring ↝ semiring
_inst_2: comm_ring ↝ comm_semiring
 -/
#check @ideal.finrank_quotient_map.linear_independent_of_nontrivial /- _inst_2: comm_ring ↝ mul_action semiring
_inst_9: add_comm_group ↝ add_comm_monoid distrib_mul_action has_smul is_scalar_tower mul_action
_inst_13: add_comm_group ↝ add_comm_monoid has_smul mul_action
_inst_17: add_comm_group ↝ add_comm_monoid has_smul
 -/
#check @ideal.finrank_quotient_map.span_eq_top /- _inst_1: comm_ring ↝ distrib_mul_action euclidean_domain has_quotient has_smul is_scalar_tower module module module.finite mul_action no_meet_fake_name smul_comm_class
_inst_19: is_domain ↝ no_meet_fake_name
 -/

-- number_theory/zsqrtd/basic.lean
#check @zsqrtd.hom_ext /- _inst_1: ring ↝ non_assoc_ring
 -/

-- number_theory/zsqrtd/gaussian_int.lean
#check @gaussian_int.nat_cast_nat_abs_norm /- _inst_1: ring ↝ add_group_with_one
 -/

-- order/atoms.lean
#check @is_atom /- _inst_1: preorder ↝ has_bot has_le has_lt
_inst_2: order_bot ↝ has_bot
 -/
#check @is_coatom /- _inst_1: preorder ↝ has_le has_lt has_top
_inst_2: order_top ↝ has_top
 -/
#check @is_atomistic.is_atomic /- _inst_1: complete_lattice ↝ no_meet_fake_name
 -/
#check @Sup_atoms_le_eq /- _inst_1: complete_lattice ↝ no_meet_fake_name
 -/
#check @Sup_atoms_eq_top /- _inst_1: complete_lattice ↝ no_meet_fake_name
 -/
#check @le_iff_atom_le_imp /- _inst_1: complete_lattice ↝ no_meet_fake_name
 -/
#check @is_coatomistic.is_coatomic /- _inst_1: complete_lattice ↝ no_meet_fake_name
 -/
#check @is_simple_order_iff_is_simple_order_order_dual /- _inst_2: bounded_order ↝ no_meet_fake_name
 -/
#check @is_simple_order.bot_ne_top /- _inst_2: bounded_order ↝ no_meet_fake_name
 -/
#check @is_simple_order.is_atomic /- _inst_1: lattice ↝ bounded_order partial_order
 -/
#check @is_simple_order.is_atomistic /- _inst_1: complete_lattice ↝ no_meet_fake_name
 -/
#check @fintype.is_simple_order.univ /- _inst_1: partial_order ↝ boolean_algebra fintype has_le
 -/
#check @fintype.is_simple_order.card /- _inst_1: partial_order ↝ fintype has_le
 -/
#check @fintype.to_is_coatomic /- _inst_3: fintype ↝ finite
 -/

-- order/basic.lean
#check @subtype.decidable_le /- _inst_1: preorder ↝ has_le
 -/
#check @subtype.decidable_lt /- _inst_1: preorder ↝ has_lt
 -/
#check @prod.mk_le_mk_iff_left /- _inst_1: preorder ↝ has_le
 -/
#check @prod.mk_le_mk_iff_right /- _inst_2: preorder ↝ has_le
 -/

-- order/boolean_algebra.lean
#check @generalized_boolean_algebra.to_boolean_algebra /- _inst_1: generalized_boolean_algebra ↝ boolean_algebra
 -/
#check @inf_compl_eq_bot /- _inst_1: boolean_algebra ↝ no_meet_fake_name
 -/
#check @sup_compl_eq_top /- _inst_1: boolean_algebra ↝ no_meet_fake_name
 -/
#check @disjoint_compl_right /- _inst_1: boolean_algebra ↝ no_meet_fake_name
 -/
#check @disjoint_compl_left /- _inst_1: boolean_algebra ↝ no_meet_fake_name
 -/
#check @le_compl_iff_disjoint_right /- _inst_1: boolean_algebra ↝ no_meet_fake_name
 -/
#check @le_compl_iff_disjoint_left /- _inst_1: boolean_algebra ↝ no_meet_fake_name
 -/
#check @disjoint_compl_left_iff /- _inst_1: boolean_algebra ↝ no_meet_fake_name
 -/
#check @disjoint_compl_right_iff /- _inst_1: boolean_algebra ↝ no_meet_fake_name
 -/
#check @disjoint.le_compl_right /- _inst_1: boolean_algebra ↝ no_meet_fake_name
 -/
#check @disjoint.le_compl_left /- _inst_1: boolean_algebra ↝ no_meet_fake_name
 -/
#check @has_le.le.disjoint_compl_left /- _inst_1: boolean_algebra ↝ no_meet_fake_name
 -/
#check @has_le.le.disjoint_compl_right /- _inst_1: boolean_algebra ↝ no_meet_fake_name
 -/
#check @top_sdiff /- _inst_1: boolean_algebra ↝ no_meet_fake_name
 -/

-- order/bounded_order.lean
#check @is_max_top /- _inst_1: preorder ↝ has_le has_top
 -/
#check @is_min_bot /- _inst_1: preorder ↝ has_bot has_le
 -/
#check @strict_mono.minimal_preimage_bot /- _inst_2: partial_order ↝ has_bot preorder
 -/
#check @eq_bot_of_bot_eq_top /- _inst_2: bounded_order ↝ bounded_order
 -/
#check @eq_top_of_bot_eq_top /- _inst_2: bounded_order ↝ bounded_order
 -/
#check @subsingleton_of_top_le_bot /- _inst_2: bounded_order ↝ bounded_order
 -/
#check @disjoint /- _inst_1: semilattice_inf ↝ has_bot has_inf has_le
_inst_2: order_bot ↝ has_bot
 -/
#check @disjoint_top /- _inst_1: lattice ↝ bounded_order semilattice_inf
_inst_2: bounded_order ↝ bounded_order
 -/
#check @top_disjoint /- _inst_1: lattice ↝ bounded_order semilattice_inf
_inst_2: bounded_order ↝ bounded_order
 -/
#check @codisjoint /- _inst_1: semilattice_sup ↝ has_le has_sup has_top
_inst_2: order_top ↝ has_top
 -/
#check @codisjoint_bot /- _inst_1: lattice ↝ bounded_order semilattice_sup
_inst_2: bounded_order ↝ bounded_order
 -/
#check @bot_codisjoint /- _inst_1: lattice ↝ bounded_order semilattice_sup
_inst_2: bounded_order ↝ bounded_order
 -/

-- order/bounds.lean
#check @upper_bounds /- _inst_1: preorder ↝ has_le
 -/
#check @lower_bounds /- _inst_1: preorder ↝ has_le
 -/
#check @is_glb.exists_between_self_add /- _inst_1: linear_ordered_add_comm_group ↝ add_zero_class covariant_class linear_order
 -/
#check @is_glb.exists_between_self_add' /- _inst_1: linear_ordered_add_comm_group ↝ add_zero_class covariant_class linear_order
 -/
#check @is_lub.exists_between_sub_self /- _inst_1: linear_ordered_add_comm_group ↝ add_group covariant_class covariant_class linear_order
 -/
#check @is_lub.exists_between_sub_self' /- _inst_1: linear_ordered_add_comm_group ↝ add_group covariant_class covariant_class linear_order
 -/

-- order/category/Frame.lean
#check @Frame.hom /- _inst_1: order.frame ↝ complete_lattice
_inst_2: order.frame ↝ complete_lattice
 -/

-- order/chain.lean
#check @flag.le_or_le /- _inst_1: preorder ↝ has_le is_refl
 -/

-- order/circular.lean
#check @set.cIcc /- _inst_1: circular_preorder ↝ has_btw
 -/
#check @set.cIoo /- _inst_1: circular_preorder ↝ has_sbtw
 -/

-- order/closure.lean
#check @closure_operator.ext /- _inst_1: partial_order ↝ preorder
 -/
#check @closure_operator.monotone /- _inst_1: partial_order ↝ preorder
 -/
#check @closure_operator.le_closure /- _inst_1: partial_order ↝ preorder
 -/
#check @closure_operator.idempotent /- _inst_1: partial_order ↝ preorder
 -/
#check @closure_operator.closed /- _inst_1: partial_order ↝ preorder
 -/
#check @lower_adjoint.mem_closed_iff_closure_le /- _inst_2: partial_order ↝ preorder
 -/
#check @lower_adjoint.closure_is_closed /- _inst_2: partial_order ↝ preorder
 -/
#check @lower_adjoint.closed_eq_range_close /- _inst_2: partial_order ↝ preorder
 -/
#check @lower_adjoint.closure_le_closed_iff_le /- _inst_2: partial_order ↝ preorder
 -/
#check @lower_adjoint.subset_closure /- _inst_1: set_like ↝ has_coe_t preorder
 -/
#check @lower_adjoint.le_iff_subset /- _inst_1: set_like ↝ has_coe_t preorder
 -/
#check @lower_adjoint.closure_union_closure_subset /- _inst_1: set_like ↝ has_coe_t preorder
 -/
#check @lower_adjoint.closure_union_closure_left /- _inst_1: set_like ↝ has_coe_t preorder
 -/

-- order/compactly_generated.lean
#check @complete_lattice.is_sup_closed_compact /- _inst_1: complete_lattice ↝ has_Sup has_sup
 -/
#check @complete_lattice.is_Sup_finite_compact /- _inst_1: complete_lattice ↝ no_meet_fake_name semilattice_sup
 -/
#check @complete_lattice.is_compact_element /- _inst_2: complete_lattice ↝ no_meet_fake_name semilattice_sup
 -/
#check @complete_lattice.is_compact_element_iff /- _inst_2: complete_lattice ↝ no_meet_fake_name
 -/
#check @complete_lattice.is_compact_element_iff_le_of_directed_Sup_le /- _inst_1: complete_lattice ↝ no_meet_fake_name
 -/
#check @complete_lattice.finset_sup_compact_of_compact /- _inst_2: complete_lattice ↝ no_meet_fake_name
 -/
#check @complete_lattice.well_founded.is_Sup_finite_compact /- _inst_1: complete_lattice ↝ no_meet_fake_name
 -/
#check @complete_lattice.is_Sup_finite_compact.is_sup_closed_compact /- _inst_1: complete_lattice ↝ no_meet_fake_name
 -/
#check @complete_lattice.is_Sup_finite_compact_iff_all_elements_compact /- _inst_1: complete_lattice ↝ no_meet_fake_name
 -/
#check @complete_lattice.well_founded.finite_of_set_independent /- _inst_1: complete_lattice ↝ no_meet_fake_name
 -/
#check @Sup_compact_eq_top /- _inst_1: complete_lattice ↝ no_meet_fake_name
 -/
#check @inf_Sup_eq_of_directed_on /- _inst_1: complete_lattice ↝ no_meet_fake_name
 -/
#check @inf_Sup_eq_supr_inf_sup_finset /- _inst_1: complete_lattice ↝ no_meet_fake_name
 -/
#check @complete_lattice.set_independent_iff_finite /- _inst_1: complete_lattice ↝ no_meet_fake_name
 -/
#check @complete_lattice.set_independent_Union_of_directed /- _inst_1: complete_lattice ↝ no_meet_fake_name
 -/
#check @complete_lattice.coatomic_of_top_compact /- _inst_1: complete_lattice ↝ no_meet_fake_name
 -/
#check @is_atomic_of_is_complemented /- _inst_1: complete_lattice ↝ no_meet_fake_name
 -/
#check @is_atomistic_of_is_complemented /- _inst_1: complete_lattice ↝ is_atomic no_meet_fake_name
_inst_3: is_compactly_generated ↝ is_atomic
 -/
#check @is_complemented_of_Sup_atoms_eq_top /- _inst_1: complete_lattice ↝ no_meet_fake_name
 -/

-- order/complete_boolean_algebra.lean
#check @supr_disjoint_iff /- _inst_1: order.frame ↝ no_meet_fake_name
 -/
#check @disjoint_supr_iff /- _inst_1: order.frame ↝ no_meet_fake_name
 -/
#check @supr₂_disjoint_iff /- _inst_1: order.frame ↝ no_meet_fake_name
 -/
#check @disjoint_supr₂_iff /- _inst_1: order.frame ↝ no_meet_fake_name
 -/
#check @Sup_disjoint_iff /- _inst_1: order.frame ↝ no_meet_fake_name
 -/
#check @disjoint_Sup_iff /- _inst_1: order.frame ↝ no_meet_fake_name
 -/

-- order/complete_lattice.lean
#check @Sup_empty /- _inst_1: complete_lattice ↝ no_meet_fake_name
 -/
#check @Inf_empty /- _inst_1: complete_lattice ↝ no_meet_fake_name
 -/
#check @Sup_univ /- _inst_1: complete_lattice ↝ no_meet_fake_name
 -/
#check @Inf_univ /- _inst_1: complete_lattice ↝ no_meet_fake_name
 -/
#check @Sup_le_Sup_of_subset_insert_bot /- _inst_1: complete_lattice ↝ no_meet_fake_name
 -/
#check @Inf_le_Inf_of_subset_insert_top /- _inst_1: complete_lattice ↝ no_meet_fake_name
 -/
#check @Sup_eq_bot /- _inst_1: complete_lattice ↝ no_meet_fake_name
 -/
#check @Sup_eq_of_forall_le_of_forall_lt_exists_gt /- _inst_1: complete_lattice ↝ complete_semilattice_Sup
 -/
#check @Sup_eq_top /- _inst_1: complete_linear_order ↝ no_meet_fake_name
 -/
#check @le_supr /- _inst_1: complete_lattice ↝ complete_semilattice_Sup
 -/
#check @infi_le /- _inst_1: complete_lattice ↝ complete_semilattice_Inf
 -/
#check @le_supr' /- _inst_1: complete_lattice ↝ complete_semilattice_Sup
 -/
#check @infi_le' /- _inst_1: complete_lattice ↝ complete_semilattice_Inf
 -/
#check @is_lub_supr /- _inst_1: complete_lattice ↝ complete_semilattice_Sup
 -/
#check @is_glb_infi /- _inst_1: complete_lattice ↝ complete_semilattice_Inf
 -/
#check @is_lub.supr_eq /- _inst_1: complete_lattice ↝ complete_semilattice_Sup
 -/
#check @is_glb.infi_eq /- _inst_1: complete_lattice ↝ complete_semilattice_Inf
 -/
#check @supr_le /- _inst_1: complete_lattice ↝ complete_semilattice_Sup
 -/
#check @le_infi /- _inst_1: complete_lattice ↝ complete_semilattice_Inf
 -/
#check @supr_const /- _inst_1: complete_lattice ↝ complete_semilattice_Sup
 -/
#check @supr_bot /- _inst_1: complete_lattice ↝ no_meet_fake_name
 -/
#check @infi_top /- _inst_1: complete_lattice ↝ no_meet_fake_name
 -/
#check @supr_neg /- _inst_1: complete_lattice ↝ no_meet_fake_name
 -/
#check @infi_neg /- _inst_1: complete_lattice ↝ no_meet_fake_name
 -/
#check @supr_false /- _inst_1: complete_lattice ↝ no_meet_fake_name
 -/
#check @infi_false /- _inst_1: complete_lattice ↝ no_meet_fake_name
 -/
#check @supr_dite /- _inst_1: complete_lattice ↝ no_meet_fake_name
 -/
#check @supr_extend_bot /- _inst_1: complete_lattice ↝ no_meet_fake_name
 -/
#check @supr_ne_bot_subtype /- _inst_1: complete_lattice ↝ no_meet_fake_name
 -/
#check @disjoint_Sup_left /- _inst_1: complete_lattice ↝ no_meet_fake_name
 -/
#check @disjoint_Sup_right /- _inst_1: complete_lattice ↝ no_meet_fake_name
 -/

-- order/complete_lattice_intervals.lean
#check @Sup_within_of_ord_connected /- _inst_1: conditionally_complete_linear_order ↝ conditionally_complete_lattice
 -/
#check @Inf_within_of_ord_connected /- _inst_1: conditionally_complete_linear_order ↝ conditionally_complete_lattice
 -/

-- order/conditionally_complete_lattice.lean
#check @csupr_set /- _inst_1: conditionally_complete_lattice ↝ has_Sup
 -/
#check @cInf_le_cInf' /- _inst_1: conditionally_complete_linear_order_bot ↝ conditionally_complete_lattice order_bot
 -/
#check @with_top.is_glb_Inf /- _inst_1: conditionally_complete_linear_order_bot ↝ conditionally_complete_lattice order_bot
 -/

-- order/cover.lean
#check @wcovby /- _inst_1: preorder ↝ has_le has_lt
 -/
#check @apply_wcovby_apply_iff /- _inst_3: order_iso_class ↝ has_coe_t order_hom_class
 -/
#check @apply_covby_apply_iff /- _inst_3: order_iso_class ↝ has_coe_t order_hom_class
 -/
#check @prod.swap_wcovby_swap /- _inst_1: partial_order ↝ preorder
_inst_2: partial_order ↝ preorder
 -/
#check @prod.swap_covby_swap /- _inst_1: partial_order ↝ preorder
_inst_2: partial_order ↝ preorder
 -/
#check @wcovby.fst /- _inst_1: partial_order ↝ preorder
_inst_2: partial_order ↝ preorder
 -/
#check @wcovby.snd /- _inst_1: partial_order ↝ preorder
_inst_2: partial_order ↝ preorder
 -/

-- order/filter/archimedean.lean
#check @filter.tendsto.at_top_nsmul_const /- _inst_1: linear_ordered_cancel_add_comm_monoid ↝ ordered_add_comm_monoid
 -/
#check @filter.tendsto.at_top_zsmul_const /- _inst_1: linear_ordered_add_comm_group ↝ ordered_add_comm_group
 -/

-- order/filter/at_top_bot.lean
#check @filter.at_top_countable_basis /- _inst_3: encodable ↝ countable
 -/
#check @filter.at_bot_countable_basis /- _inst_3: encodable ↝ countable
 -/
#check @filter.tendsto_at_top_add_nonneg_left' /- _inst_1: ordered_add_comm_monoid ↝ add_zero_class covariant_class preorder
 -/
#check @filter.tendsto_at_top_add_nonneg_right' /- _inst_1: ordered_add_comm_monoid ↝ add_zero_class covariant_class preorder
 -/
#check @filter.tendsto.nsmul_at_top /- _inst_1: ordered_add_comm_monoid ↝ add_monoid covariant_class preorder
 -/
#check @filter.tendsto_at_top_of_add_const_left /- _inst_1: ordered_cancel_add_comm_monoid ↝ contravariant_class has_add preorder
 -/
#check @filter.tendsto_at_top_of_add_const_right /- _inst_1: ordered_cancel_add_comm_monoid ↝ contravariant_class has_add preorder
 -/
#check @filter.map_neg_at_bot /- _inst_1: ordered_add_comm_group ↝ add_group covariant_class covariant_class preorder
 -/
#check @filter.map_neg_at_top /- _inst_1: ordered_add_comm_group ↝ add_group covariant_class covariant_class preorder
 -/
#check @filter.comap_neg_at_bot /- _inst_1: ordered_add_comm_group ↝ add_group covariant_class covariant_class preorder
 -/
#check @filter.comap_neg_at_top /- _inst_1: ordered_add_comm_group ↝ add_group covariant_class covariant_class preorder
 -/
#check @filter.tendsto_neg_at_top_at_bot /- _inst_1: ordered_add_comm_group ↝ add_group covariant_class covariant_class preorder
 -/
#check @filter.tendsto_neg_at_top_iff /- _inst_1: ordered_add_comm_group ↝ add_group covariant_class covariant_class preorder
 -/
#check @filter.tendsto_neg_at_bot_iff /- _inst_1: ordered_add_comm_group ↝ add_group covariant_class covariant_class preorder
 -/
#check @filter.tendsto_abs_at_top_at_top /- _inst_1: linear_ordered_add_comm_group ↝ has_neg linear_order
 -/
#check @filter.tendsto.const_mul_at_top /- _inst_1: linear_ordered_field ↝ linear_ordered_semifield
 -/
#check @filter.prod_at_top_at_top_eq /- _inst_1: semilattice_sup ↝ preorder
_inst_2: semilattice_sup ↝ preorder
 -/
#check @filter.tendsto_at_top_of_monotone_of_subseq /- _inst_3: filter.ne_bot ↝ filter.ne_bot
 -/
#check @filter.tendsto_at_bot_of_monotone_of_subseq /- _inst_3: filter.ne_bot ↝ filter.ne_bot
 -/
#check @filter.has_antitone_basis.comp_mono /- _inst_1: semilattice_sup ↝ filter.ne_bot preorder
_inst_2: nonempty ↝ filter.ne_bot
 -/
#check @exists_lt_mul_self /- _inst_1: linear_ordered_semiring ↝ filter.ne_bot no_max_order ordered_semiring
 -/

-- order/filter/bases.lean
#check @filter.is_countably_generated_seq /- _inst_1: encodable ↝ countable
 -/

-- order/filter/basic.lean
#check @filter.Inter_mem /- _inst_1: fintype ↝ finite
 -/
#check @filter.eventually.ne_top_of_lt /- _inst_1: partial_order ↝ has_top preorder
 -/
#check @filter.eventually_sub_nonneg /- _inst_1: ordered_ring ↝ add_group covariant_class has_le
 -/

-- order/filter/countable_Inter.lean
#check @countable_Inter_mem /- _inst_2: encodable ↝ countable
 -/

-- order/filter/extr.lean
#check @is_min_filter /- _inst_1: preorder ↝ has_le
 -/
#check @is_max_filter /- _inst_1: preorder ↝ has_le
 -/
#check @is_min_filter.add /- _inst_1: ordered_add_comm_monoid ↝ covariant_class covariant_class has_add preorder
 -/
#check @is_max_filter.add /- _inst_1: ordered_add_comm_monoid ↝ covariant_class covariant_class has_add preorder
 -/
#check @is_max_on.supr_eq /- _inst_1: conditionally_complete_linear_order ↝ conditionally_complete_lattice
 -/

-- order/filter/filter_product.lean
#check @filter.germ.const_div /- _inst_1: division_ring ↝ has_div
 -/
#check @filter.germ.abs_def /- _inst_1: linear_ordered_add_comm_group ↝ has_neg has_sup
 -/

-- order/filter/germ.lean
#check @filter.germ.has_nat_pow /- _inst_1: monoid ↝ has_pow
 -/
#check @filter.germ.has_int_pow /- _inst_1: div_inv_monoid ↝ has_pow
 -/
#check @filter.germ.coe_smul /- _inst_1: has_smul ↝ has_smul has_smul
 -/

-- order/filter/indicator_function.lean
#check @indicator_union_eventually_eq /- _inst_1: add_monoid ↝ add_zero_class
 -/

-- order/filter/interval.lean
#check @filter.tendsto_Icc_pure_pure /- _inst_1: partial_order ↝ no_meet_fake_name preorder set.ord_connected
 -/
#check @filter.tendsto_Ico_pure_bot /- _inst_1: partial_order ↝ preorder
 -/
#check @filter.tendsto_Ioc_pure_bot /- _inst_1: partial_order ↝ preorder
 -/
#check @filter.tendsto_Ioo_pure_bot /- _inst_1: partial_order ↝ preorder
 -/
#check @filter.tendsto.interval /- _inst_2: filter.tendsto_Ixx_class ↝ filter.tendsto_Ixx_class
 -/

-- order/filter/pointwise.lean
#check @filter.comap_mul_comap_le /- _inst_1: mul_one_class ↝ fun_like has_mul
_inst_2: mul_one_class ↝ fun_like has_mul
 -/
#check @filter.comap_add_comap_le /- _inst_1: add_zero_class ↝ fun_like has_add
_inst_2: add_zero_class ↝ fun_like has_add
 -/
#check @filter.tendsto.mul_mul /- _inst_1: mul_one_class ↝ fun_like has_mul
_inst_2: mul_one_class ↝ fun_like has_mul
 -/
#check @filter.tendsto.add_add /- _inst_1: add_zero_class ↝ fun_like has_add
_inst_2: add_zero_class ↝ fun_like has_add
 -/
#check @filter.mul_add_subset /- _inst_1: distrib ↝ has_add has_mul left_distrib_class
 -/
#check @filter.add_mul_subset /- _inst_1: distrib ↝ has_add has_mul right_distrib_class
 -/

-- order/filter/ultrafilter.lean
#check @ultrafilter.eq_pure_of_fintype /- _inst_1: fintype ↝ finite
 -/
#check @filter.hyperfilter /- _inst_1: infinite ↝ filter.ne_bot
 -/

-- order/fixed_points.lean
#check @order_hom.le_map_sup_fixed_points /- _inst_1: complete_lattice ↝ semilattice_sup
 -/
#check @order_hom.le_map_Sup_subset_fixed_points /- _inst_1: complete_lattice ↝ complete_semilattice_Sup
 -/
#check @order_hom.map_Inf_subset_fixed_points_le /- _inst_1: complete_lattice ↝ complete_semilattice_Inf
 -/

-- order/galois_connection.lean
#check @galois_connection /- _inst_1: preorder ↝ has_le
_inst_2: preorder ↝ has_le
 -/
#check @galois_connection.l_supr /- _inst_1: complete_lattice ↝ complete_semilattice_Sup
 -/

-- order/hom/basic.lean
#check @order_embedding.le_iff_le /- _inst_1: preorder ↝ has_le
_inst_2: preorder ↝ has_le
 -/
#check @order_embedding.eq_iff_eq /- _inst_1: preorder ↝ has_le
_inst_2: preorder ↝ has_le
 -/
#check @order_embedding.of_map_le_iff /- _inst_3: partial_order ↝ has_le is_antisymm
_inst_4: preorder ↝ has_le is_refl
 -/

-- order/hom/bounded.lean
#check @map_eq_top_iff /- _inst_2: order_top ↝ fun_like has_top top_hom_class
_inst_3: partial_order ↝ equiv_like has_le has_top top_hom_class
_inst_4: order_top ↝ fun_like has_top top_hom_class
_inst_5: order_iso_class ↝ equiv_like top_hom_class
 -/
#check @map_eq_bot_iff /- _inst_2: order_bot ↝ bot_hom_class fun_like has_bot
_inst_3: partial_order ↝ bot_hom_class equiv_like has_bot has_le
_inst_4: order_bot ↝ bot_hom_class fun_like has_bot
_inst_5: order_iso_class ↝ bot_hom_class equiv_like
 -/

-- order/hom/lattice.lean
#check @map_finset_sup /- _inst_5: sup_bot_hom_class ↝ sup_bot_hom_class
 -/
#check @map_finset_inf /- _inst_5: inf_top_hom_class ↝ inf_top_hom_class
 -/
#check @disjoint.map /- _inst_5: bounded_lattice_hom_class ↝ bot_hom_class inf_hom_class
 -/
#check @codisjoint.map /- _inst_5: bounded_lattice_hom_class ↝ sup_hom_class top_hom_class
 -/

-- order/hom/order.lean
#check @order_hom.has_bot /- _inst_3: order_bot ↝ has_bot
 -/
#check @order_hom.has_top /- _inst_3: order_top ↝ has_top
 -/
#check @order_hom.complete_lattice /- _inst_2: complete_lattice ↝ no_meet_fake_name
 -/

-- order/ideal.lean
#check @order.ideal.is_proper.not_mem_of_compl_mem /- _inst_1: boolean_algebra ↝ no_meet_fake_name
 -/

-- order/imp.lean
#check @lattice.imp_bot /- _inst_1: boolean_algebra ↝ has_bot has_compl order_bot semilattice_sup
 -/
#check @lattice.imp_top /- _inst_1: boolean_algebra ↝ no_meet_fake_name
 -/
#check @lattice.biimp_mp /- _inst_1: boolean_algebra ↝ has_compl has_sup semilattice_inf
 -/
#check @lattice.biimp_mpr /- _inst_1: boolean_algebra ↝ has_compl has_sup semilattice_inf
 -/
#check @lattice.biimp_comm /- _inst_1: boolean_algebra ↝ has_compl has_sup semilattice_inf
 -/
#check @lattice.biimp_eq_top_iff /- _inst_1: boolean_algebra ↝ no_meet_fake_name
 -/

-- order/lattice.lean
#check @sup_ind /- _inst_1: linear_order ↝ is_total semilattice_sup
 -/
#check @le_sup_iff /- _inst_1: linear_order ↝ is_total semilattice_sup
 -/
#check @lt_sup_iff /- _inst_1: linear_order ↝ is_total semilattice_sup
 -/
#check @monotone.map_sup /- _inst_1: linear_order ↝ is_total semilattice_sup
 -/

-- order/liminf_limsup.lean
#check @filter.is_bounded.is_cobounded_ge /- _inst_1: preorder ↝ has_le is_trans
 -/
#check @filter.is_bounded.is_cobounded_le /- _inst_1: preorder ↝ has_le is_trans
 -/
#check @filter.is_cobounded_le_of_bot /- _inst_1: preorder ↝ has_bot has_le
 -/
#check @filter.is_cobounded_ge_of_top /- _inst_1: preorder ↝ has_le has_top
 -/
#check @filter.is_bounded_le_of_top /- _inst_1: preorder ↝ has_le has_top
 -/
#check @filter.is_bounded_ge_of_bot /- _inst_1: preorder ↝ has_bot has_le
 -/
#check @order_iso.is_bounded_under_le_comp /- _inst_1: preorder ↝ has_le
_inst_2: preorder ↝ has_le
 -/
#check @filter.is_bounded_under_le_inv /- _inst_1: ordered_comm_group ↝ covariant_class covariant_class group preorder
 -/
#check @filter.is_bounded_under_le_neg /- _inst_1: ordered_add_comm_group ↝ add_group covariant_class covariant_class preorder
 -/
#check @filter.is_bounded_under_ge_neg /- _inst_1: ordered_add_comm_group ↝ add_group covariant_class covariant_class preorder
 -/
#check @filter.is_bounded_under_ge_inv /- _inst_1: ordered_comm_group ↝ covariant_class covariant_class group preorder
 -/
#check @filter.Limsup /- _inst_1: conditionally_complete_lattice ↝ has_Inf has_le
 -/
#check @filter.Liminf /- _inst_1: conditionally_complete_lattice ↝ has_Sup has_le
 -/
#check @filter.liminf_le_limsup /- _inst_2: filter.ne_bot ↝ filter.ne_bot
 -/
#check @filter.Limsup_bot /- _inst_1: complete_lattice ↝ no_meet_fake_name
 -/
#check @filter.Liminf_bot /- _inst_1: complete_lattice ↝ no_meet_fake_name
 -/
#check @filter.Limsup_top /- _inst_1: complete_lattice ↝ no_meet_fake_name
 -/
#check @filter.Liminf_top /- _inst_1: complete_lattice ↝ no_meet_fake_name
 -/
#check @filter.limsup_const_bot /- _inst_1: complete_lattice ↝ no_meet_fake_name
 -/

-- order/locally_finite.lean
#check @finset.Ici_eq_Icc /- _inst_3: order_top ↝ has_top locally_finite_order_top
 -/
#check @finset.Ioi_eq_Ioc /- _inst_3: order_top ↝ has_top locally_finite_order_top
 -/
#check @finset.Iic_eq_Icc /- _inst_2: order_bot ↝ has_bot locally_finite_order_bot
 -/
#check @finset.Iio_eq_Ico /- _inst_2: order_bot ↝ has_bot locally_finite_order_bot
 -/

-- order/max.lean
#check @is_bot.prod_mk /- _inst_1: preorder ↝ has_le
_inst_2: preorder ↝ has_le
 -/
#check @is_top.prod_mk /- _inst_1: preorder ↝ has_le
_inst_2: preorder ↝ has_le
 -/
#check @is_min.prod_mk /- _inst_1: preorder ↝ has_le
_inst_2: preorder ↝ has_le
 -/
#check @is_max.prod_mk /- _inst_1: preorder ↝ has_le
_inst_2: preorder ↝ has_le
 -/
#check @is_bot.fst /- _inst_1: preorder ↝ has_le
_inst_2: preorder ↝ has_le
 -/
#check @is_bot.snd /- _inst_1: preorder ↝ has_le
_inst_2: preorder ↝ has_le
 -/
#check @is_top.fst /- _inst_1: preorder ↝ has_le
_inst_2: preorder ↝ has_le
 -/
#check @is_top.snd /- _inst_1: preorder ↝ has_le
_inst_2: preorder ↝ has_le
 -/
#check @is_min.fst /- _inst_1: preorder ↝ has_le
 -/
#check @is_min.snd /- _inst_2: preorder ↝ has_le
 -/
#check @is_max.fst /- _inst_1: preorder ↝ has_le
 -/
#check @is_max.snd /- _inst_2: preorder ↝ has_le
 -/

-- order/monotone.lean
#check @monotone /- _inst_1: preorder ↝ has_le
_inst_2: preorder ↝ has_le
 -/
#check @antitone /- _inst_1: preorder ↝ has_le
_inst_2: preorder ↝ has_le
 -/
#check @monotone_on /- _inst_1: preorder ↝ has_le
_inst_2: preorder ↝ has_le
 -/
#check @antitone_on /- _inst_1: preorder ↝ has_le
_inst_2: preorder ↝ has_le
 -/
#check @strict_mono /- _inst_1: preorder ↝ has_lt
_inst_2: preorder ↝ has_lt
 -/
#check @strict_anti /- _inst_1: preorder ↝ has_lt
_inst_2: preorder ↝ has_lt
 -/
#check @strict_mono_on /- _inst_1: preorder ↝ has_lt
_inst_2: preorder ↝ has_lt
 -/
#check @strict_anti_on /- _inst_1: preorder ↝ has_lt
_inst_2: preorder ↝ has_lt
 -/

-- order/monovary.lean
#check @monovary /- _inst_1: preorder ↝ has_le
_inst_2: preorder ↝ has_lt
 -/
#check @antivary /- _inst_1: preorder ↝ has_le
_inst_2: preorder ↝ has_lt
 -/
#check @monovary_on /- _inst_1: preorder ↝ has_le
_inst_2: preorder ↝ has_lt
 -/
#check @antivary_on /- _inst_1: preorder ↝ has_le
_inst_2: preorder ↝ has_lt
 -/

-- order/omega_complete_partial_order.lean
#check @complete_lattice.top_continuous /- _inst_2: complete_lattice ↝ omega_complete_partial_order order_top
 -/
#check @complete_lattice.bot_continuous /- _inst_2: complete_lattice ↝ no_meet_fake_name
 -/
#check @omega_complete_partial_order.continuous_hom.ωSup_bind /- _inst_1: omega_complete_partial_order ↝ preorder
 -/

-- order/ord_continuous.lean
#check @left_ord_continuous.map_Sup' /- _inst_1: complete_lattice ↝ complete_semilattice_Sup
_inst_2: complete_lattice ↝ complete_semilattice_Sup
 -/

-- order/partial_sups.lean
#check @partial_sups_eq_bsupr /- _inst_1: complete_lattice ↝ no_meet_fake_name
 -/

-- order/pfilter.lean
#check @order.is_pfilter /- _inst_1: preorder ↝ has_le
 -/

-- order/rel_classes.lean
#check @is_preorder.swap /- _inst_1: is_preorder ↝ is_refl is_trans
 -/
#check @is_strict_order.swap /- _inst_1: is_strict_order ↝ is_irrefl is_trans
 -/
#check @is_partial_order.swap /- _inst_1: is_partial_order ↝ is_antisymm is_preorder
 -/
#check @is_total_preorder.swap /- _inst_1: is_total_preorder ↝ is_preorder is_total
 -/
#check @is_linear_order.swap /- _inst_1: is_linear_order ↝ is_partial_order is_total
 -/
#check @is_strict_total_order'.swap /- _inst_1: is_strict_total_order' ↝ is_strict_order is_trichotomous
 -/
#check @is_order_connected_of_is_strict_total_order' /- _inst_1: is_strict_total_order' ↝ is_trans is_trichotomous
 -/
#check @is_strict_total_order_of_is_strict_total_order' /- _inst_1: is_strict_total_order' ↝ is_asymm is_order_connected is_trichotomous
 -/
#check @is_well_founded.is_irrefl /- _inst_1: is_well_founded ↝ is_asymm
 -/
#check @is_well_order.is_strict_total_order /- _inst_1: is_well_order ↝ is_strict_total_order
 -/
#check @is_well_order.is_trichotomous /- _inst_1: is_well_order ↝ is_trichotomous
 -/
#check @is_well_order.is_trans /- _inst_1: is_well_order ↝ is_trans
 -/
#check @is_well_order.is_irrefl /- _inst_1: is_well_order ↝ is_irrefl
 -/
#check @is_well_order.is_asymm /- _inst_1: is_well_order ↝ is_asymm
 -/
#check @is_well_order.linear_order /- _inst_1: is_well_order ↝ is_strict_total_order'
 -/
#check @ge.is_refl /- _inst_1: preorder ↝ has_le is_refl
 -/
#check @ge.is_trans /- _inst_1: preorder ↝ has_le is_trans
 -/
#check @has_le.le.is_preorder /- _inst_1: preorder ↝ has_le is_refl is_trans
 -/
#check @ge.is_preorder /- _inst_1: preorder ↝ has_le is_refl is_trans
 -/
#check @gt.is_irrefl /- _inst_1: preorder ↝ has_lt is_irrefl
 -/
#check @gt.is_trans /- _inst_1: preorder ↝ has_lt is_trans
 -/
#check @gt.is_asymm /- _inst_1: preorder ↝ has_lt is_asymm
 -/
#check @has_lt.lt.is_antisymm /- _inst_1: preorder ↝ has_lt is_asymm
 -/
#check @gt.is_antisymm /- _inst_1: preorder ↝ has_lt is_asymm
 -/
#check @has_lt.lt.is_strict_order /- _inst_1: preorder ↝ has_lt is_irrefl is_trans
 -/
#check @gt.is_strict_order /- _inst_1: preorder ↝ has_lt is_irrefl is_trans
 -/
#check @ge.is_antisymm /- _inst_1: partial_order ↝ has_le is_antisymm
 -/
#check @has_le.le.is_partial_order /- _inst_1: partial_order ↝ has_le is_antisymm is_refl is_trans
 -/
#check @ge.is_partial_order /- _inst_1: partial_order ↝ has_le is_antisymm is_refl is_trans
 -/
#check @ge.is_total /- _inst_1: linear_order ↝ has_le is_total
 -/
#check @linear_order.is_total_preorder /- _inst_1: linear_order ↝ has_le is_total_preorder
 -/
#check @ge.is_total_preorder /- _inst_1: linear_order ↝ has_le is_total is_trans
 -/
#check @has_le.le.is_linear_order /- _inst_1: linear_order ↝ has_le is_antisymm is_refl is_total is_trans
 -/
#check @ge.is_linear_order /- _inst_1: linear_order ↝ has_le is_antisymm is_refl is_total is_trans
 -/
#check @gt.is_trichotomous /- _inst_1: linear_order ↝ has_lt is_trichotomous
 -/
#check @has_le.le.is_trichotomous /- _inst_1: linear_order ↝ has_le is_total
 -/
#check @ge.is_trichotomous /- _inst_1: linear_order ↝ has_le is_total
 -/
#check @has_lt.lt.is_strict_total_order /- _inst_1: linear_order ↝ has_lt is_strict_total_order
 -/
#check @has_lt.lt.is_strict_total_order' /- _inst_1: linear_order ↝ has_lt is_irrefl is_trans is_trichotomous
 -/
#check @has_lt.lt.is_order_connected /- _inst_1: linear_order ↝ has_lt is_strict_total_order'
 -/
#check @has_lt.lt.is_incomp_trans /- _inst_1: linear_order ↝ has_lt is_strict_weak_order
 -/
#check @has_lt.lt.is_strict_weak_order /- _inst_1: linear_order ↝ has_lt is_strict_weak_order
 -/
#check @transitive_le /- _inst_1: preorder ↝ has_le is_trans
 -/
#check @transitive_lt /- _inst_1: preorder ↝ has_lt is_trans
 -/
#check @transitive_ge /- _inst_1: preorder ↝ has_le is_trans
 -/
#check @transitive_gt /- _inst_1: preorder ↝ has_lt is_trans
 -/
#check @gt.is_well_order /- _inst_1: linear_order ↝ has_lt
 -/
#check @has_lt.lt.is_well_order /- _inst_1: linear_order ↝ has_lt
 -/

-- order/rel_iso.lean
#check @rel_embedding.is_preorder /- _inst_1: is_preorder ↝ is_refl is_trans
 -/
#check @rel_embedding.is_partial_order /- _inst_1: is_partial_order ↝ is_antisymm is_preorder
 -/
#check @rel_embedding.is_linear_order /- _inst_1: is_linear_order ↝ is_partial_order is_total
 -/
#check @rel_embedding.is_strict_order /- _inst_1: is_strict_order ↝ is_irrefl is_trans
 -/
#check @rel_embedding.is_strict_total_order' /- _inst_1: is_strict_total_order' ↝ is_strict_order is_trichotomous
 -/

-- order/semiconj_Sup.lean
#check @is_order_right_adjoint /- _inst_2: preorder ↝ has_le
 -/
#check @is_order_right_adjoint_Sup /- _inst_1: complete_lattice ↝ complete_semilattice_Sup
 -/

-- order/succ_pred/basic.lean
#check @order.succ_eq_infi /- _inst_1: complete_lattice ↝ no_meet_fake_name
 -/
#check @order.pred_eq_supr /- _inst_1: complete_lattice ↝ no_meet_fake_name
 -/

-- order/sup_indep.lean
#check @complete_lattice.set_independent /- _inst_1: complete_lattice ↝ no_meet_fake_name semilattice_inf
 -/
#check @complete_lattice.set_independent_empty /- _inst_1: complete_lattice ↝ no_meet_fake_name
 -/
#check @complete_lattice.set_independent.mono /- _inst_1: complete_lattice ↝ no_meet_fake_name
 -/
#check @complete_lattice.set_independent.pairwise_disjoint /- _inst_1: complete_lattice ↝ no_meet_fake_name
 -/
#check @complete_lattice.set_independent_pair /- _inst_1: complete_lattice ↝ no_meet_fake_name
 -/
#check @complete_lattice.set_independent.disjoint_Sup /- _inst_1: complete_lattice ↝ no_meet_fake_name
 -/
#check @complete_lattice.independent /- _inst_2: complete_lattice ↝ no_meet_fake_name semilattice_inf
 -/
#check @complete_lattice.set_independent_iff /- _inst_2: complete_lattice ↝ no_meet_fake_name
 -/
#check @complete_lattice.independent_def /- _inst_1: complete_lattice ↝ no_meet_fake_name
 -/
#check @complete_lattice.independent_def' /- _inst_1: complete_lattice ↝ no_meet_fake_name
 -/
#check @complete_lattice.independent_def'' /- _inst_1: complete_lattice ↝ no_meet_fake_name
 -/
#check @complete_lattice.independent_empty /- _inst_1: complete_lattice ↝ no_meet_fake_name
 -/
#check @complete_lattice.independent_pempty /- _inst_1: complete_lattice ↝ no_meet_fake_name
 -/
#check @complete_lattice.independent.pairwise_disjoint /- _inst_1: complete_lattice ↝ no_meet_fake_name
 -/
#check @complete_lattice.independent.mono /- _inst_1: complete_lattice ↝ no_meet_fake_name
 -/
#check @complete_lattice.independent.comp /- _inst_1: complete_lattice ↝ no_meet_fake_name
 -/
#check @complete_lattice.independent.comp' /- _inst_1: complete_lattice ↝ no_meet_fake_name
 -/
#check @complete_lattice.independent.injective /- _inst_1: complete_lattice ↝ no_meet_fake_name
 -/
#check @complete_lattice.independent_pair /- _inst_1: complete_lattice ↝ no_meet_fake_name
 -/
#check @complete_lattice.independent.map_order_iso /- _inst_2: complete_lattice ↝ no_meet_fake_name
_inst_3: complete_lattice ↝ no_meet_fake_name
 -/
#check @complete_lattice.independent.disjoint_bsupr /- _inst_2: complete_lattice ↝ no_meet_fake_name
 -/
#check @complete_lattice.independent_iff_sup_indep /- _inst_1: complete_lattice ↝ no_meet_fake_name
 -/
#check @finset.sup_indep.independent /- _inst_1: complete_lattice ↝ no_meet_fake_name
 -/
#check @complete_lattice.independent.sup_indep /- _inst_1: complete_lattice ↝ no_meet_fake_name
 -/
#check @complete_lattice.independent_iff_sup_indep_univ /- _inst_1: complete_lattice ↝ no_meet_fake_name
 -/
#check @complete_lattice.independent.sup_indep_univ /- _inst_1: complete_lattice ↝ no_meet_fake_name
 -/
#check @finset.sup_indep.independent_of_univ /- _inst_1: complete_lattice ↝ no_meet_fake_name
 -/
#check @complete_lattice.set_independent_iff_pairwise_disjoint /- _inst_1: order.frame ↝ no_meet_fake_name
 -/
#check @set.pairwise_disjoint.set_independent /- _inst_1: order.frame ↝ no_meet_fake_name
 -/
#check @complete_lattice.independent_iff_pairwise_disjoint /- _inst_1: order.frame ↝ no_meet_fake_name
 -/

-- order/symm_diff.lean
#check @symm_diff_comm /- _inst_1: generalized_boolean_algebra ↝ has_sdiff semilattice_sup
 -/
#check @symm_diff_top /- _inst_1: boolean_algebra ↝ no_meet_fake_name
 -/
#check @compl_symm_diff /- _inst_1: boolean_algebra ↝ no_meet_fake_name
 -/
#check @symm_diff_eq_top_iff /- _inst_1: boolean_algebra ↝ no_meet_fake_name
 -/

-- order/upper_lower.lean
#check @is_lower_set.top_mem /- _inst_1: preorder ↝ has_le has_top
 -/
#check @is_upper_set.top_mem /- _inst_1: preorder ↝ has_le has_top
 -/
#check @is_upper_set.bot_mem /- _inst_1: preorder ↝ has_bot has_le
 -/
#check @is_lower_set.bot_mem /- _inst_1: preorder ↝ has_bot has_le
 -/
#check @upper_set.Ici_Sup /- _inst_1: complete_lattice ↝ complete_semilattice_Sup
 -/
#check @lower_set.Iic_Inf /- _inst_1: complete_lattice ↝ complete_semilattice_Inf
 -/

-- order/well_founded_set.lean
#check @set.is_strict_order.subset /- _inst_1: is_strict_order ↝ is_irrefl is_trans
 -/
#check @set.well_founded_on_iff_no_descending_seq /- _inst_1: is_strict_order ↝ is_strict_order
 -/
#check @set.is_wf_iff_no_descending_seq /- _inst_1: partial_order ↝ preorder
 -/
#check @set.is_pwo /- _inst_1: preorder ↝ has_le
 -/
#check @set.partially_well_ordered_on.well_founded_on /- _inst_1: is_partial_order ↝ is_antisymm is_trans
 -/
#check @set.is_pwo.exists_monotone_subseq /- _inst_1: partial_order ↝ preorder
 -/
#check @set.is_pwo_iff_exists_monotone_subseq /- _inst_1: partial_order ↝ preorder
 -/
#check @set.is_pwo.image_of_monotone /- _inst_1: partial_order ↝ preorder
_inst_2: partial_order ↝ preorder
 -/
#check @finset.is_pwo /- _inst_1: partial_order ↝ preorder
 -/
#check @set.fintype.is_pwo /- _inst_2: fintype ↝ finite
 -/
#check @set.is_wf.min /- _inst_1: partial_order ↝ has_lt
 -/
#check @set.is_pwo.add /- _inst_1: ordered_cancel_add_comm_monoid ↝ covariant_class covariant_class has_add partial_order
 -/
#check @set.is_pwo.mul /- _inst_1: ordered_cancel_comm_monoid ↝ covariant_class covariant_class has_mul partial_order
 -/
#check @set.is_wf.add /- _inst_1: linear_ordered_cancel_add_comm_monoid ↝ linear_ordered_semiring
 -/
#check @set.is_pwo.submonoid_closure /- _inst_1: ordered_cancel_comm_monoid ↝ covariant_class covariant_class monoid preorder
 -/
#check @set.is_pwo.add_submonoid_closure /- _inst_1: ordered_cancel_add_comm_monoid ↝ add_monoid covariant_class covariant_class preorder
 -/
#check @set.add_antidiagonal /- _inst_1: add_monoid ↝ has_add
 -/
#check @set.mul_antidiagonal /- _inst_1: monoid ↝ has_mul
 -/
#check @set.add_antidiagonal.fst_eq_fst_iff_snd_eq_snd /- _inst_1: add_cancel_comm_monoid ↝ add_cancel_monoid
 -/
#check @set.mul_antidiagonal.fst_eq_fst_iff_snd_eq_snd /- _inst_1: cancel_comm_monoid ↝ cancel_monoid
 -/
#check @set.add_antidiagonal.eq_of_fst_le_fst_of_snd_le_snd /- _inst_1: ordered_cancel_add_comm_monoid ↝ add_cancel_comm_monoid covariant_class covariant_class partial_order
 -/
#check @set.mul_antidiagonal.eq_of_fst_le_fst_of_snd_le_snd /- _inst_1: ordered_cancel_comm_monoid ↝ cancel_comm_monoid covariant_class covariant_class partial_order
 -/
#check @set.add_antidiagonal.finite_of_is_wf /- _inst_1: linear_ordered_cancel_add_comm_monoid ↝ linear_ordered_semiring
 -/
#check @finset.add_antidiagonal_min_add_min /- _inst_2: linear_ordered_cancel_add_comm_monoid ↝ covariant_class linear_ordered_semiring
 -/

-- probability/density.lean
#check @measure_theory.pdf.quasi_measure_preserving_has_pdf' /- _inst_3: measure_theory.is_finite_measure ↝ measure_theory.is_finite_measure no_meet_fake_name
 -/

-- probability/hitting_time.lean
#check @measure_theory.hitting_of_lt /- _inst_1: conditionally_complete_linear_order ↝ has_Inf preorder
 -/
#check @measure_theory.le_hitting /- _inst_1: conditionally_complete_linear_order ↝ conditionally_complete_lattice
 -/
#check @measure_theory.hitting_le_of_mem /- _inst_1: conditionally_complete_linear_order ↝ conditionally_complete_lattice
 -/
#check @measure_theory.hitting_eq_Inf /- _inst_1: complete_lattice ↝ no_meet_fake_name
 -/

-- probability/ident_distrib.lean
#check @probability_theory.ident_distrib.ae_strongly_measurable_fst /- _inst_6: topological_space.metrizable_space ↝ topological_space.pseudo_metrizable_space
 -/
#check @probability_theory.ident_distrib.ae_strongly_measurable_snd /- _inst_6: topological_space.metrizable_space ↝ topological_space.pseudo_metrizable_space
 -/
#check @probability_theory.ident_distrib.norm /- _inst_6: borel_space ↝ opens_measurable_space
 -/
#check @probability_theory.ident_distrib.nnnorm /- _inst_6: borel_space ↝ opens_measurable_space
 -/
#check @probability_theory.mem_ℒp.uniform_integrable_of_ident_distrib_aux /- _inst_7: borel_space ↝ opens_measurable_space
 -/

-- probability/martingale.lean
#check @measure_theory.martingale.set_integral_eq /- _inst_5: measure_theory.sigma_finite_filtration ↝ measure_theory.sigma_finite no_meet_fake_name
 -/
#check @measure_theory.martingale_condexp /- _inst_5: measure_theory.sigma_finite_filtration ↝ measure_theory.sigma_finite no_meet_fake_name
 -/
#check @measure_theory.supermartingale.set_integral_le /- _inst_5: measure_theory.sigma_finite_filtration ↝ measure_theory.sigma_finite no_meet_fake_name
 -/
#check @measure_theory.submartingale_of_set_integral_le /- _inst_5: measure_theory.is_finite_measure ↝ measure_theory.sigma_finite no_meet_fake_name
 -/
#check @measure_theory.submartingale_of_condexp_sub_nonneg /- _inst_5: measure_theory.is_finite_measure ↝ measure_theory.sigma_finite no_meet_fake_name
 -/
#check @measure_theory.supermartingale.smul_nonneg /- _inst_5: normed_lattice_add_comm_group ↝ normed_linear_ordered_group
 -/

-- probability/stopping.lean
#check @measure_theory.prog_measurable.comp /- _inst_6: topological_space.metrizable_space ↝ topological_space.pseudo_metrizable_space
 -/
#check @measure_theory.prog_measurable.sub /- _inst_5: topological_add_group ↝ has_continuous_sub
 -/
#check @measure_theory.prog_measurable.div /- _inst_5: topological_group ↝ has_continuous_div
 -/
#check @measure_theory.prog_measurable_of_tendsto' /- _inst_4: topological_space.metrizable_space ↝ topological_space.pseudo_metrizable_space
 -/
#check @measure_theory.adapted.prog_measurable_of_continuous /- _inst_8: topological_space.metrizable_space ↝ topological_space.pseudo_metrizable_space
 -/
#check @measure_theory.is_stopping_time.measurable_set_eq_of_encodable /- _inst_2: encodable ↝ countable
 -/
#check @measure_theory.is_stopping_time.measurable_set_lt_of_encodable /- _inst_2: encodable ↝ countable
 -/
#check @measure_theory.is_stopping_time.measurable_set_ge_of_encodable /- _inst_3: encodable ↝ countable
 -/
#check @measure_theory.is_stopping_time.measurable_set_lt_of_is_lub /- _inst_4: topological_space.first_countable_topology ↝ filter.is_countably_generated no_meet_fake_name
 -/
#check @measure_theory.is_stopping_time_of_measurable_set_eq /- _inst_2: encodable ↝ countable
 -/
#check @measure_theory.is_stopping_time.measurable_space_le /- _inst_2: semilattice_sup ↝ filter.ne_bot preorder
 -/
#check @measure_theory.is_stopping_time.sigma_finite_stopping_time /- _inst_4: measure_theory.sigma_finite_filtration ↝ measure_theory.sigma_finite no_meet_fake_name
 -/
#check @measure_theory.is_stopping_time.measurable_set_eq_of_countable' /- _inst_1: linear_order ↝ partial_order
 -/
#check @measure_theory.is_stopping_time.measurable_set_eq_of_encodable' /- _inst_2: encodable ↝ countable
 -/
#check @measure_theory.is_stopping_time.measurable_set_ge_of_encodable' /- _inst_2: encodable ↝ countable
 -/
#check @measure_theory.is_stopping_time.measurable_set_lt_of_encodable' /- _inst_2: encodable ↝ countable
 -/
#check @measure_theory.is_stopping_time.measurable_space_le_of_countable /- _inst_1: linear_order ↝ preorder
 -/
#check @measure_theory.prog_measurable_min_stopping_time /- _inst_8: topological_space.metrizable_space ↝ topological_space.pseudo_metrizable_space
 -/
#check @measure_theory.measurable_stopped_value /- _inst_8: topological_space.metrizable_space ↝ topological_space.pseudo_metrizable_space
 -/

-- probability/upcrossing.lean
#check @measure_theory.lower_crossing_time_le /- _inst_1: conditionally_complete_linear_order_bot ↝ conditionally_complete_linear_order order_bot
 -/

-- representation_theory/Action.lean
#check @Action.zero_hom /- _inst_2: category_theory.preadditive ↝ category_theory.limits.has_zero_morphisms
 -/
#check @Action.res_linear /- _inst_4: category_theory.linear ↝ category_theory.linear
 -/

-- representation_theory/Rep.lean
#check @Rep.category_theory.linear /- _inst_1: comm_ring ↝ category_theory.linear ring
 -/
#check @Rep.has_coe_to_sort /- _inst_1: comm_ring ↝ ring
 -/
#check @Rep.of /- _inst_1: comm_ring ↝ ring
 -/
#check @Rep.to_Module_monoid_algebra_map_aux /- _inst_3: comm_ring ↝ algebra comm_semiring distrib_mul_action has_smul module no_meet_fake_name ring_hom_comp_triple smul_comm_class
 -/

-- representation_theory/basic.lean
#check @representation /- _inst_1: comm_semiring ↝ semiring
_inst_2: monoid ↝ mul_one_class
 -/
#check @representation.as_module.add_comm_group /- _inst_1: comm_ring ↝ comm_semiring
 -/

-- representation_theory/group_cohomology_resolution.lean
#check @group_cohomology.resolution.to_tensor_aux /- _inst_1: comm_ring ↝ comm_semiring module module no_meet_fake_name
_inst_2: group ↝ has_inv has_mul
 -/
#check @group_cohomology.resolution.of_tensor_aux /- _inst_2: group ↝ monoid
 -/

-- representation_theory/invariants.lean
#check @group_algebra.average /- _inst_1: comm_semiring ↝ has_smul semiring
_inst_2: group ↝ mul_one_class
 -/

-- representation_theory/maschke.lean
#check @linear_map.conjugate /- _inst_2: group ↝ has_inv monoid
_inst_3: add_comm_group ↝ add_comm_monoid has_smul
_inst_7: add_comm_group ↝ add_comm_monoid has_smul
 -/

-- ring_theory/adjoin/basic.lean
#check @algebra.adjoin_int /- _inst_1: comm_ring ↝ ring
 -/

-- ring_theory/adjoin/fg.lean
#check @alg_hom.is_noetherian_ring_range /- _inst_2: comm_ring ↝ ring
_inst_3: comm_ring ↝ ring
 -/

-- ring_theory/adjoin/power_basis.lean
#check @power_basis.repr_gen_pow_is_integral /- _inst_2: comm_ring ↝ distrib_mul_action euclidean_domain is_scalar_tower module
 -/
#check @power_basis.to_matrix_is_integral /- _inst_1: field ↝ comm_ring distrib_mul_action is_domain is_scalar_tower module
 -/

-- ring_theory/adjoin_root.lean
#check @adjoin_root.nontrivial /- _inst_1: comm_ring ↝ euclidean_domain
_inst_2: is_domain ↝ no_meet_fake_name
 -/
#check @adjoin_root.algebra /- _inst_3: algebra ↝ algebra
 -/
#check @adjoin_root.is_scalar_tower /- _inst_5: algebra ↝ algebra algebra has_smul has_smul is_scalar_tower no_meet_fake_name
_inst_6: algebra ↝ algebra algebra has_smul has_smul is_scalar_tower no_meet_fake_name
_inst_7: is_scalar_tower ↝ is_scalar_tower
 -/
#check @adjoin_root.smul_comm_class /- _inst_4: algebra ↝ algebra algebra has_smul has_smul no_meet_fake_name smul_comm_class
_inst_5: algebra ↝ algebra algebra has_smul has_smul no_meet_fake_name smul_comm_class
_inst_6: smul_comm_class ↝ smul_comm_class
 -/
#check @adjoin_root.aeval_alg_hom_eq_zero /- _inst_2: comm_ring ↝ semiring
 -/
#check @adjoin_root.minpoly.to_adjoin.injective /- _inst_1: comm_ring ↝ algebra algebra algebra field has_coe_t no_meet_fake_name
_inst_2: comm_ring ↝ algebra euclidean_domain no_meet_fake_name no_zero_divisors
_inst_4: is_domain ↝ no_meet_fake_name
 -/
#check @adjoin_root.minpoly.equiv_adjoin_symm_apply /- _inst_1: comm_ring ↝ algebra algebra field no_meet_fake_name
 -/
#check @adjoin_root.minpoly.equiv_adjoin /- _inst_1: comm_ring ↝ algebra algebra field no_meet_fake_name
 -/
#check @adjoin_root.minpoly.equiv_adjoin_apply /- _inst_1: comm_ring ↝ algebra algebra field no_meet_fake_name
 -/
#check @algebra.adjoin.power_basis' /- _inst_1: comm_ring ↝ algebra algebra field no_meet_fake_name
 -/
#check @algebra.adjoin.power_basis'_gen /- _inst_1: comm_ring ↝ algebra field no_meet_fake_name
 -/
#check @algebra.adjoin.power_basis'_dim /- _inst_1: comm_ring ↝ algebra field no_meet_fake_name
 -/
#check @power_basis.of_gen_mem_adjoin'_dim /- _inst_1: comm_ring ↝ field
 -/
#check @power_basis.of_gen_mem_adjoin' /- _inst_1: comm_ring ↝ algebra field no_meet_fake_name
 -/
#check @power_basis.of_gen_mem_adjoin'_gen /- _inst_1: comm_ring ↝ algebra field no_meet_fake_name
 -/

-- ring_theory/algebra_tower.lean
#check @linear_independent_smul /- _inst_4: algebra ↝ has_smul module
 -/
#check @exists_subalgebra_of_fg /- _inst_7: is_scalar_tower ↝ is_scalar_tower no_meet_fake_name
 -/
#check @fg_of_fg_of_fg /- _inst_3: comm_ring ↝ module ring
 -/
#check @alg_hom.restrict_domain /- _inst_2: comm_semiring ↝ semiring
_inst_3: comm_semiring ↝ semiring
 -/

-- ring_theory/algebraic.lean
#check @is_algebraic /- _inst_1: comm_ring ↝ algebra comm_semiring
_inst_2: ring ↝ semiring
 -/
#check @is_algebraic_of_larger_base_of_injective /- _inst_5: comm_ring ↝ ring
 -/
#check @is_algebraic_of_larger_base /- _inst_2: field ↝ euclidean_domain
 -/
#check @algebra.is_algebraic_of_larger_base /- _inst_2: field ↝ euclidean_domain
 -/
#check @algebra.is_integral_of_finite /- _inst_2: field ↝ finite_dimensional module module no_meet_fake_name ring
_inst_14: finite_dimensional ↝ finite_dimensional no_meet_fake_name
 -/
#check @inv_eq_of_aeval_div_X_ne_zero /- _inst_4: field ↝ algebra comm_semiring
 -/

-- ring_theory/algebraic_independent.lean
#check @algebraic_independent /- _inst_1: comm_ring ↝ algebra comm_semiring
_inst_2: comm_ring ↝ comm_semiring
 -/

-- ring_theory/artinian.lean
#check @is_artinian_of_injective /- _inst_1: ring ↝ semiring
_inst_2: add_comm_group ↝ add_comm_monoid
_inst_3: add_comm_group ↝ add_comm_monoid
 -/
#check @is_artinian_of_surjective /- _inst_1: ring ↝ semiring
_inst_2: add_comm_group ↝ add_comm_monoid
_inst_3: add_comm_group ↝ add_comm_monoid
 -/
#check @is_artinian_of_range_eq_ker /- _inst_2: add_comm_group ↝ add_comm_monoid
 -/
#check @is_artinian_of_fintype /- _inst_1: ring ↝ semiring
_inst_2: add_comm_group ↝ add_comm_monoid
 -/
#check @is_artinian_pi' /- _inst_11: fintype ↝ is_artinian no_meet_fake_name
 -/
#check @is_artinian_iff_well_founded /- _inst_1: ring ↝ semiring
_inst_2: add_comm_group ↝ add_comm_monoid
 -/
#check @is_artinian.induction /- _inst_1: ring ↝ semiring
_inst_2: add_comm_group ↝ add_comm_monoid
 -/
#check @is_artinian_of_submodule_of_artinian /- _inst_1: ring ↝ is_artinian module no_meet_fake_name semiring
_inst_2: add_comm_group ↝ add_comm_monoid is_artinian module no_meet_fake_name
 -/
#check @is_artinian_of_tower /- _inst_4: algebra ↝ has_smul
 -/
#check @is_artinian_of_fg_of_artinian /- _inst_4: is_artinian_ring ↝ is_artinian
 -/
#check @is_artinian_ring.is_nilpotent_jacobson_bot /- _inst_2: is_artinian_ring ↝ is_artinian
 -/

-- ring_theory/bezout.lean
#check @is_bezout.gcd /- _inst_2: is_bezout ↝ no_meet_fake_name submodule.is_principal
 -/
#check @is_bezout.to_gcd_domain /- _inst_1: comm_ring ↝ field
_inst_3: is_domain ↝ cancel_comm_monoid_with_zero
 -/
#check @is_bezout.of_is_principal_ideal_ring /- _inst_2: is_principal_ideal_ring ↝ no_meet_fake_name submodule.is_principal
 -/
#check @is_bezout.tfae /- _inst_1: comm_ring ↝ field is_noetherian unique_factorization_monoid wf_dvd_monoid
 -/

-- ring_theory/chain_of_divisors.lean
#check @divisor_chain.card_subset_divisors_le_length_of_chain /- _inst_1: cancel_comm_monoid_with_zero ↝ comm_monoid
 -/

-- ring_theory/class_group.lean
#check @class_group.mk0_eq_mk0_iff /- _inst_1: comm_ring ↝ euclidean_domain no_zero_divisors
 -/
#check @class_group.mk0_surjective /- _inst_1: comm_ring ↝ euclidean_domain module no_zero_divisors
 -/
#check @card_class_group_eq_one_iff /- _inst_1: comm_ring ↝ euclidean_domain no_zero_divisors submodule.is_principal
 -/

-- ring_theory/coprime/basic.lean
#check @is_coprime /- _inst_1: comm_semiring ↝ has_add has_mul has_one
 -/
#check @is_coprime.neg_left /- _inst_1: comm_ring ↝ comm_semiring has_distrib_neg has_neg
 -/

-- ring_theory/dedekind_domain/adic_valuation.lean
#check @is_dedekind_domain.height_one_spectrum.int_valuation_ne_zero' /- _inst_1: comm_ring ↝ euclidean_domain
 -/
#check @is_dedekind_domain.height_one_spectrum.int_valuation_zero_le /- _inst_1: comm_ring ↝ euclidean_domain
 -/
#check @is_dedekind_domain.height_one_spectrum.int_valuation_le_pow_iff_dvd /- _inst_1: comm_ring ↝ euclidean_domain
 -/
#check @is_dedekind_domain.height_one_spectrum.int_valuation.map_one' /- _inst_1: comm_ring ↝ euclidean_domain
 -/
#check @is_dedekind_domain.height_one_spectrum.int_valuation.map_add_le_max' /- _inst_1: comm_ring ↝ euclidean_domain
 -/
#check @is_dedekind_domain.height_one_spectrum.int_valuation_exists_uniformizer /- _inst_1: comm_ring ↝ euclidean_domain
 -/
#check @is_dedekind_domain.height_one_spectrum.valuation /- _inst_4: field ↝ comm_ring
 -/

-- ring_theory/dedekind_domain/basic.lean
#check @ring.dimension_le_one /- _inst_1: comm_ring ↝ semiring
 -/

-- ring_theory/dedekind_domain/ideal.lean
#check @is_dedekind_domain_inv_iff /- _inst_2: comm_ring ↝ algebra euclidean_domain is_localization
 -/
#check @is_dedekind_domain_inv.integrally_closed /- _inst_2: comm_ring ↝ algebra euclidean_domain is_localization
 -/
#check @fractional_ideal.exists_not_mem_one_of_ne_bot /- _inst_2: comm_ring ↝ euclidean_domain module
 -/
#check @sup_eq_prod_inf_factors /- _inst_5: comm_ring ↝ euclidean_domain
 -/
#check @irreducible_pow_sup_of_le /- _inst_5: comm_ring ↝ euclidean_domain
 -/
#check @irreducible_pow_sup_of_ge /- _inst_5: comm_ring ↝ euclidean_domain
 -/
#check @ideal.coprime_of_no_prime_ge /- _inst_1: comm_ring ↝ comm_semiring
 -/
#check @ideal.count_normalized_factors_eq /- _inst_1: comm_ring ↝ euclidean_domain
 -/
#check @ideal.prod_le_prime /- _inst_1: comm_ring ↝ euclidean_domain no_zero_divisors
 -/

-- ring_theory/dedekind_domain/integral_closure.lean
#check @exists_integral_multiples /- _inst_2: comm_ring ↝ euclidean_domain mul_action no_zero_divisors
 -/
#check @is_integral_closure.is_dedekind_domain /- _inst_2: comm_ring ↝ euclidean_domain is_integrally_closed is_noetherian_ring
 -/

-- ring_theory/derivation.lean
#check @derivation.coe_smul /- _inst_8: distrib_mul_action ↝ has_smul has_smul
_inst_9: smul_comm_class ↝ has_smul
_inst_10: smul_comm_class ↝ has_smul
 -/
#check @derivation.coe_smul_linear_map /- _inst_10: smul_comm_class ↝ has_smul
 -/
#check @derivation.smul_apply /- _inst_8: distrib_mul_action ↝ has_smul has_smul
_inst_9: smul_comm_class ↝ has_smul
_inst_10: smul_comm_class ↝ has_smul
 -/
#check @derivation.is_central_scalar /- _inst_8: distrib_mul_action ↝ has_smul has_smul smul_comm_class
 -/
#check @derivation.map_neg /- _inst_1: comm_ring ↝ comm_semiring
_inst_4: add_comm_group ↝ subtraction_comm_monoid
 -/
#check @derivation.map_sub /- _inst_1: comm_ring ↝ comm_semiring
_inst_4: add_comm_group ↝ subtraction_comm_monoid
 -/
#check @derivation.map_coe_int /- _inst_1: comm_ring ↝ comm_semiring linear_map.compatible_smul
 -/
#check @derivation.leibniz_of_mul_eq_one /- _inst_1: comm_ring ↝ comm_semiring
 -/

-- ring_theory/discrete_valuation_ring.lean
#check @discrete_valuation_ring.irreducible_iff_uniformizer /- _inst_1: comm_ring ↝ field is_principal_ideal_ring local_ring
 -/
#check @discrete_valuation_ring.iff_pid_with_one_nonzero_prime /- _inst_4: comm_ring ↝ field ideal.is_maximal ideal.is_prime local_ring no_meet_fake_name submodule.is_principal
 -/
#check @discrete_valuation_ring.has_unit_mul_pow_irreducible_factorization /- _inst_1: comm_ring ↝ monoid_with_zero
 -/
#check @discrete_valuation_ring.has_unit_mul_pow_irreducible_factorization.to_unique_factorization_monoid /- _inst_1: comm_ring ↝ field
_inst_2: is_domain ↝ cancel_comm_monoid_with_zero
 -/
#check @discrete_valuation_ring.has_unit_mul_pow_irreducible_factorization.of_ufd_of_unique_irreducible /- _inst_1: comm_ring ↝ field wf_dvd_monoid
_inst_2: is_domain ↝ cancel_comm_monoid_with_zero wf_dvd_monoid
_inst_3: unique_factorization_monoid ↝ wf_dvd_monoid
 -/
#check @discrete_valuation_ring.aux_pid_of_ufd_of_unique_irreducible /- _inst_1: comm_ring ↝ field
 -/
#check @discrete_valuation_ring.of_ufd_of_unique_irreducible /- _inst_1: comm_ring ↝ field no_meet_fake_name submodule.is_principal
 -/
#check @discrete_valuation_ring.of_has_unit_mul_pow_irreducible_factorization /- _inst_1: comm_ring ↝ field
 -/
#check @discrete_valuation_ring.unit_mul_pow_congr_pow /- _inst_1: comm_ring ↝ field unique_factorization_monoid
_inst_3: discrete_valuation_ring ↝ unique_factorization_monoid
 -/
#check @discrete_valuation_ring.add_val_def /- _inst_1: comm_ring ↝ field is_principal_ideal_ring
 -/
#check @discrete_valuation_ring.add_val_eq_top_iff /- _inst_1: comm_ring ↝ field
 -/
#check @discrete_valuation_ring.add_val_le_iff_dvd /- _inst_1: comm_ring ↝ field
 -/

-- ring_theory/discriminant.lean
#check @algebra.discr_zero_of_not_linear_independent /- _inst_1: comm_ring ↝ field module
 -/
#check @algebra.discr_eq_discr_of_to_matrix_coeff_is_integral /- _inst_19: number_field ↝ char_zero
 -/

-- ring_theory/etale.lean
#check @algebra.formally_etale.of_equiv /- _inst_6: algebra.formally_etale ↝ algebra.formally_smooth algebra.formally_unramified
 -/
#check @algebra.formally_etale.comp /- _inst_8: algebra.formally_etale ↝ algebra.formally_smooth algebra.formally_unramified
_inst_9: algebra.formally_etale ↝ algebra.formally_smooth algebra.formally_unramified
 -/
#check @algebra.formally_etale.base_change /- _inst_6: algebra.formally_etale ↝ algebra.formally_smooth algebra.formally_unramified no_meet_fake_name
 -/

-- ring_theory/euclidean_domain.lean
#check @gcd_ne_zero_of_left /- _inst_1: euclidean_domain ↝ cancel_comm_monoid_with_zero
 -/
#check @gcd_ne_zero_of_right /- _inst_1: euclidean_domain ↝ cancel_comm_monoid_with_zero
 -/
#check @left_div_gcd_ne_zero /- _inst_1: euclidean_domain ↝ field no_zero_divisors
 -/
#check @right_div_gcd_ne_zero /- _inst_1: euclidean_domain ↝ field no_zero_divisors
 -/
#check @euclidean_domain.gcd_monoid /- _inst_1: euclidean_domain ↝ field
 -/
#check @euclidean_domain.span_gcd /- _inst_3: euclidean_domain ↝ field
 -/
#check @euclidean_domain.gcd_is_unit_iff /- _inst_3: euclidean_domain ↝ field
 -/
#check @euclidean_domain.is_coprime_of_dvd /- _inst_3: euclidean_domain ↝ field
 -/
#check @euclidean_domain.dvd_or_coprime /- _inst_3: euclidean_domain ↝ field
 -/

-- ring_theory/finiteness.lean
#check @module.finite.of_restrict_scalars_finite /- _inst_11: algebra ↝ has_smul
 -/
#check @module.finite.trans /- _inst_8: algebra ↝ has_smul module smul_comm_class
_inst_10: algebra ↝ has_smul module smul_comm_class
_inst_11: algebra ↝ has_smul module smul_comm_class
 -/
#check @module.finite.base_change /- _inst_3: algebra ↝ has_smul has_smul is_scalar_tower module module module smul_comm_class
 -/
#check @algebra.finite_type.self /- _inst_1: comm_ring ↝ comm_semiring
 -/
#check @algebra.finite_type.of_restrict_scalars_finite_type /- _inst_1: comm_ring ↝ comm_semiring
_inst_2: comm_ring ↝ comm_semiring
_inst_4: comm_ring ↝ semiring
 -/
#check @algebra.finite_type.of_surjective /- _inst_1: comm_ring ↝ comm_semiring
_inst_2: comm_ring ↝ semiring
_inst_4: comm_ring ↝ semiring
 -/
#check @algebra.finite_type.trans /- _inst_1: comm_ring ↝ comm_semiring
_inst_2: comm_ring ↝ comm_semiring
_inst_4: comm_ring ↝ comm_semiring
 -/
#check @algebra.finite_presentation.equiv /- _inst_1: comm_ring ↝ comm_semiring
_inst_2: comm_ring ↝ ring
_inst_4: comm_ring ↝ semiring
 -/
#check @ring_hom.finite /- _inst_1: comm_ring ↝ comm_semiring module
_inst_2: comm_ring ↝ comm_semiring module
 -/
#check @ring_hom.finite_type /- _inst_1: comm_ring ↝ comm_semiring
_inst_2: comm_ring ↝ comm_semiring
 -/
#check @ring_hom.finite_presentation /- _inst_1: comm_ring ↝ comm_semiring
_inst_2: comm_ring ↝ comm_semiring
 -/
#check @alg_hom.finite /- _inst_1: comm_ring ↝ comm_semiring
 -/
#check @alg_hom.finite_type /- _inst_1: comm_ring ↝ comm_semiring
 -/
#check @alg_hom.finite_presentation /- _inst_1: comm_ring ↝ comm_semiring
 -/
#check @add_monoid_algebra.exists_finset_adjoin_eq_top /- _inst_1: comm_ring ↝ comm_semiring
_inst_2: add_comm_monoid ↝ add_monoid
 -/
#check @add_monoid_algebra.of'_mem_span /- _inst_1: comm_ring ↝ module module no_meet_fake_name semiring
_inst_2: add_comm_monoid ↝ add_zero_class
 -/
#check @monoid_algebra.exists_finset_adjoin_eq_top /- _inst_1: comm_ring ↝ comm_semiring
_inst_2: comm_monoid ↝ monoid
 -/
#check @monoid_algebra.of_mem_span_of_iff /- _inst_1: comm_ring ↝ module module no_meet_fake_name semiring
_inst_2: comm_monoid ↝ mul_one_class
 -/
#check @module_polynomial_of_endo /- _inst_1: comm_ring ↝ algebra algebra comm_semiring no_meet_fake_name
_inst_2: add_comm_group ↝ add_comm_monoid algebra no_meet_fake_name
 -/

-- ring_theory/fractional_ideal.lean
#check @fractional_ideal.exists_ne_zero_mem_is_integer /- _inst_4: field ↝ comm_ring module no_zero_divisors
 -/
#check @fractional_ideal.map_ne_zero /- _inst_5: field ↝ comm_ring
 -/
#check @fractional_ideal.coe_ideal_injective /- _inst_4: field ↝ comm_ring
 -/
#check @fractional_ideal.nontrivial /- _inst_5: field ↝ euclidean_domain
 -/
#check @is_fractional.div_of_nonzero /- _inst_4: comm_ring ↝ euclidean_domain module mul_action no_zero_divisors
_inst_5: field ↝ comm_ring module mul_action no_zero_divisors
_inst_7: is_domain ↝ no_zero_divisors nontrivial
 -/
#check @fractional_ideal.map_div /- _inst_4: comm_ring ↝ euclidean_domain module
 -/
#check @fractional_ideal.exists_eq_span_singleton_mul /- _inst_4: comm_ring ↝ euclidean_domain module no_zero_divisors
_inst_8: is_domain ↝ no_zero_divisors nontrivial
 -/
#check @fractional_ideal.is_principal /- _inst_11: is_principal_ideal_ring ↝ no_meet_fake_name submodule.is_principal
 -/
#check @fractional_ideal.is_noetherian_zero /- _inst_5: field ↝ comm_ring module module no_meet_fake_name
 -/
#check @fractional_ideal.is_noetherian_iff /- _inst_5: field ↝ comm_ring module module no_meet_fake_name
 -/
#check @fractional_ideal.is_noetherian_coe_to_fractional_ideal /- _inst_7: is_noetherian_ring ↝ is_noetherian
 -/

-- ring_theory/graded_algebra/basic.lean
#check @graded_algebra /- _inst_5: algebra ↝ module
 -/

-- ring_theory/graded_algebra/homogeneous_ideal.lean
#check @ideal.is_homogeneous /- _inst_6: graded_ring ↝ direct_sum.decomposition
 -/

-- ring_theory/graded_algebra/homogeneous_localization.lean
#check @homogeneous_localization.num_denom_same_deg.deg_smul /- _inst_10: is_scalar_tower ↝ has_smul no_meet_fake_name
 -/
#check @homogeneous_localization.num_denom_same_deg.num_smul /- _inst_10: is_scalar_tower ↝ has_smul no_meet_fake_name
 -/
#check @homogeneous_localization.num_denom_same_deg.denom_smul /- _inst_10: is_scalar_tower ↝ has_smul no_meet_fake_name
 -/

-- ring_theory/graded_algebra/radical.lean
#check @ideal.is_homogeneous.is_prime_of_homogeneous_mem_or_mem /- _inst_2: linear_ordered_cancel_add_comm_monoid ↝ add_left_cancel_monoid contravariant_class covariant_class linear_order no_meet_fake_name set_like.has_graded_mul
 -/

-- ring_theory/hahn_series.lean
#check @hahn_series.order_le_of_coeff_ne_zero /- _inst_4: linear_ordered_cancel_add_comm_monoid ↝ has_zero linear_order
 -/
#check @hahn_series.min_order_le_order_add /- _inst_3: linear_ordered_cancel_add_comm_monoid ↝ has_zero linear_order
 -/
#check @hahn_series.smul_coeff /- _inst_4: distrib_mul_action ↝ has_smul has_smul
 -/
#check @hahn_series.has_one /- _inst_1: ordered_cancel_add_comm_monoid ↝ has_zero partial_order
 -/
#check @hahn_series.single_zero_mul_eq_smul /- _inst_2: semiring ↝ has_smul non_unital_non_assoc_semiring
 -/
#check @hahn_series.is_domain /- _inst_3: ring ↝ euclidean_domain no_zero_divisors
_inst_4: is_domain ↝ no_zero_divisors nontrivial
 -/
#check @hahn_series.emb_domain_one /- _inst_3: non_assoc_semiring ↝ mul_zero_one_class
 -/
#check @hahn_series.algebra_map_apply' /- _inst_1: comm_semiring ↝ algebra no_meet_fake_name semiring
 -/
#check @hahn_series.is_pwo_Union_support_powers /- _inst_2: ring ↝ euclidean_domain
 -/
#check @hahn_series.unit_aux /- _inst_2: comm_ring ↝ distrib_mul_action euclidean_domain has_smul
 -/
#check @hahn_series.is_unit_iff /- _inst_2: comm_ring ↝ euclidean_domain no_zero_divisors
 -/

-- ring_theory/ideal/basic.lean
#check @ideal.bot_prime /- _inst_2: ring ↝ euclidean_domain no_zero_divisors
_inst_3: is_domain ↝ no_zero_divisors nontrivial
 -/
#check @ideal.span_singleton_eq_span_singleton /- _inst_2: comm_ring ↝ field
_inst_3: is_domain ↝ cancel_monoid_with_zero
 -/
#check @ideal.span_singleton_lt_span_singleton /- _inst_2: comm_ring ↝ field
_inst_3: is_domain ↝ cancel_comm_monoid_with_zero
 -/
#check @ideal.factors_decreasing /- _inst_2: comm_ring ↝ field
_inst_3: is_domain ↝ cancel_monoid_with_zero
 -/
#check @ideal.eq_bot_or_top /- _inst_1: division_ring ↝ division_semiring
 -/
#check @ring.not_is_field_of_subsingleton /- _inst_2: ring ↝ semiring
 -/
#check @ring.exists_not_is_unit_of_not_is_field /- _inst_1: comm_ring ↝ comm_semiring
 -/
#check @zero_mem_nonunits /- _inst_1: semiring ↝ monoid_with_zero
 -/

-- ring_theory/ideal/local_ring.lean
#check @local_ring.of_is_unit_or_is_unit_of_is_unit_add /- _inst_1: comm_semiring ↝ semiring
 -/
#check @local_ring.of_nonunits_add /- _inst_1: comm_semiring ↝ semiring
 -/
#check @local_ring.of_is_unit_or_is_unit_one_sub_self /- _inst_1: comm_ring ↝ ring
 -/
#check @ring_hom.domain_local_ring /- _inst_5: comm_semiring ↝ semifield
 -/
#check @local_ring.residue_field /- _inst_1: comm_ring ↝ comm_semiring has_quotient
 -/

-- ring_theory/ideal/operations.lean
#check @ideal.prod_eq_bot /- _inst_2: comm_ring ↝ euclidean_domain no_zero_divisors
_inst_3: is_domain ↝ no_zero_divisors nontrivial
 -/
#check @ideal.map /- rc: ring_hom_class ↝ fun_like
 -/
#check @ideal.comap_le_comap_iff_of_surjective /- _inst_1: ring ↝ fun_like semiring
_inst_2: ring ↝ fun_like semiring
 -/
#check @ideal.map_of_equiv /- _inst_1: ring ↝ semiring
_inst_2: ring ↝ semiring
 -/
#check @ideal.comap_of_equiv /- _inst_1: ring ↝ semiring
_inst_2: ring ↝ semiring
 -/
#check @ideal.map_mul /- _inst_1: comm_ring ↝ comm_semiring fun_like mul_hom_class no_meet_fake_name
_inst_2: comm_ring ↝ comm_semiring fun_like mul_hom_class no_meet_fake_name
 -/
#check @ideal.comap_radical /- _inst_1: comm_ring ↝ comm_semiring fun_like monoid_hom_class no_meet_fake_name
_inst_2: comm_ring ↝ comm_semiring fun_like monoid_hom_class no_meet_fake_name
 -/
#check @ideal.map_radical_le /- _inst_1: comm_ring ↝ comm_semiring fun_like monoid_hom_class no_meet_fake_name
_inst_2: comm_ring ↝ comm_semiring fun_like monoid_hom_class no_meet_fake_name
 -/
#check @ideal.finsupp_total /- _inst_1: add_comm_group ↝ add_comm_monoid
 -/
#check @ring_hom.ker_equiv /- _inst_3: ring_equiv_class ↝ equiv_like ring_hom_class
 -/
#check @ring_hom.ker_is_prime /- _inst_1: ring ↝ fun_like mul_hom_class no_meet_fake_name semiring
_inst_2: ring ↝ euclidean_domain fun_like mul_hom_class no_meet_fake_name no_zero_divisors
_inst_3: is_domain ↝ no_zero_divisors nontrivial
 -/
#check @ring_hom.ker_is_maximal_of_surjective /- _inst_2: field ↝ add_monoid_hom_class division_ring fun_like mul_hom_class no_meet_fake_name one_hom_class
 -/
#check @ideal.map_eq_iff_sup_ker_eq_of_surjective /- _inst_1: comm_ring ↝ ring
_inst_2: comm_ring ↝ ring
 -/
#check @ideal.quotient.is_scalar_tower /- _inst_5: comm_ring ↝ has_quotient has_smul is_scalar_tower no_meet_fake_name semiring
_inst_7: algebra ↝ has_smul has_smul is_scalar_tower no_meet_fake_name
_inst_8: algebra ↝ has_smul has_smul is_scalar_tower no_meet_fake_name
_inst_11: is_scalar_tower ↝ is_scalar_tower no_meet_fake_name
 -/

-- ring_theory/ideal/over.lean
#check @ideal.coeff_zero_mem_comap_of_root_mem_of_eval_mem /- _inst_1: comm_ring ↝ semiring
 -/
#check @ideal.exists_coeff_ne_zero_mem_comap_of_root_mem /- _inst_3: is_domain ↝ no_zero_divisors
 -/
#check @ideal.mem_of_one_mem /- _inst_2: comm_ring ↝ semiring
 -/

-- ring_theory/ideal/quotient.lean
#check @ideal.has_quotient /- _inst_1: comm_ring ↝ has_quotient semiring
 -/
#check @ideal.quotient.has_one /- _inst_1: comm_ring ↝ has_quotient ring
 -/
#check @ideal.map_pi /- _inst_1: comm_ring ↝ comm_semiring module no_meet_fake_name
 -/

-- ring_theory/integral_closure.lean
#check @ring_hom.is_integral_elem /- _inst_1: comm_ring ↝ semiring
_inst_2: ring ↝ semiring
 -/
#check @is_integral_alg_hom /- _inst_2: comm_ring ↝ ring
_inst_3: comm_ring ↝ ring
 -/
#check @is_integral_of_is_scalar_tower /- _inst_3: comm_ring ↝ ring
 -/
#check @is_integral.algebra_map /- _inst_3: comm_ring ↝ ring
 -/
#check @ring_hom.is_integral_zero /- _inst_4: comm_ring ↝ ring
 -/
#check @ring_hom.is_integral_one /- _inst_4: comm_ring ↝ ring
 -/
#check @is_integral_smul /- _inst_1: comm_ring ↝ comm_semiring
 -/
#check @normalize_scale_roots /- _inst_1: comm_ring ↝ module ring
 -/
#check @normalize_scale_roots_eval₂_leading_coeff_mul /- _inst_4: comm_ring ↝ comm_semiring
 -/
#check @is_integral_trans_aux /- _inst_2: comm_ring ↝ algebra comm_semiring
 -/
#check @ring_hom.is_integral_of_surjective /- _inst_4: comm_ring ↝ ring
 -/
#check @is_integral_tower_bot_of_is_integral /- _inst_3: comm_ring ↝ ring
 -/
#check @ring_hom.is_integral_elem_of_is_integral_elem_comp /- _inst_5: comm_ring ↝ ring
 -/
#check @is_integral_tower_top_of_is_integral /- _inst_3: comm_ring ↝ ring
 -/
#check @is_field_of_is_integral_of_is_field /- _inst_12: comm_ring ↝ euclidean_domain no_zero_divisors
_inst_13: is_domain ↝ no_zero_divisors nontrivial
 -/
#check @is_field_of_is_integral_of_is_field' /- _inst_11: comm_ring ↝ algebra euclidean_domain module module no_meet_fake_name no_zero_divisors
_inst_12: is_domain ↝ no_zero_divisors nontrivial
 -/

-- ring_theory/integral_domain.lean
#check @fintype.division_ring_of_is_domain /- _inst_4: ring ↝ division_ring
 -/
#check @fintype.field_of_domain /- _inst_4: comm_ring ↝ field
 -/
#check @card_nth_roots_subgroup_units /- _inst_3: group ↝ monoid
 -/
#check @subgroup_units_cyclic /- _inst_1: comm_ring ↝ field
 -/
#check @sum_hom_units_eq_zero /- _inst_1: comm_ring ↝ field
 -/

-- ring_theory/integrally_closed.lean
#check @is_integrally_closed_iff /- _inst_3: field ↝ comm_ring
 -/
#check @is_integrally_closed.is_integral_iff /- iic: is_integrally_closed ↝ is_integral_closure
_inst_2: field ↝ comm_ring is_integral_closure
ifr: is_fraction_ring ↝ is_integral_closure
 -/

-- ring_theory/jacobson.lean
#check @ideal.disjoint_powers_iff_not_mem /- _inst_1: comm_ring ↝ comm_semiring
 -/
#check @ideal.is_maximal_iff_is_maximal_disjoint /- _inst_2: comm_ring ↝ comm_semiring
 -/
#check @ideal.polynomial.jacobson_bot_of_integral_localization /- _inst_7: is_domain ↝ no_zero_divisors
 -/

-- ring_theory/jacobson_ideal.lean
#check @ideal.jacobson /- _inst_1: ring ↝ semiring
 -/
#check @ideal.comap_jacobson /- _inst_1: ring ↝ semiring
 -/

-- ring_theory/laurent_series.lean
#check @laurent_series.power_series_part /- _inst_1: semiring ↝ has_zero
 -/

-- ring_theory/local_properties.lean
#check @is_localization.smul_mem_finset_integer_multiple_span /- _inst_1: comm_ring ↝ comm_semiring distrib_mul_action is_scalar_tower module mul_action no_meet_fake_name smul_comm_class
 -/
#check @multiple_mem_span_of_mem_localization_span /- _inst_1: comm_ring ↝ comm_semiring distrib_mul_action module mul_action
_inst_2: comm_ring ↝ comm_semiring distrib_mul_action module mul_action
_inst_3: comm_ring ↝ comm_semiring module
 -/
#check @is_localization.exists_smul_mem_of_mem_adjoin /- _inst_1: comm_ring ↝ comm_semiring
 -/

-- ring_theory/localization/away.lean
#check @is_localization.away_of_is_unit_of_bijective /- _inst_6: comm_ring ↝ comm_semiring
_inst_7: comm_ring ↝ comm_semiring
 -/

-- ring_theory/localization/basic.lean
#check @is_localization.mul_add_inv_left /- _inst_1: comm_semiring ↝ semiring
 -/
#check @is_localization.monoid_hom_ext /- _inst_4: comm_semiring ↝ comm_monoid
 -/
#check @is_localization.to_map_eq_zero_iff /- _inst_1: comm_ring ↝ comm_semiring
_inst_2: comm_ring ↝ comm_semiring
 -/
#check @is_localization.sec_snd_ne_zero /- _inst_1: comm_ring ↝ comm_semiring
_inst_2: comm_ring ↝ comm_semiring
 -/
#check @is_localization.map_injective_of_injective /- _inst_1: comm_ring ↝ comm_semiring
_inst_4: comm_ring ↝ comm_semiring
_inst_6: comm_ring ↝ comm_semiring
 -/
#check @is_localization.is_domain_of_le_non_zero_divisors /- _inst_8: comm_ring ↝ euclidean_domain no_zero_divisors
_inst_9: is_domain ↝ no_zero_divisors nontrivial
 -/
#check @localization_algebra /- _inst_5: comm_ring ↝ comm_semiring
_inst_6: comm_ring ↝ comm_semiring
 -/

-- ring_theory/localization/cardinality.lean
#check @is_localization.algebra_map_surjective_of_fintype /- _inst_1: comm_ring ↝ comm_semiring
_inst_2: comm_ring ↝ comm_semiring
 -/

-- ring_theory/localization/fraction_ring.lean
#check @is_fraction_ring /- _inst_1: comm_ring ↝ comm_semiring
_inst_7: comm_ring ↝ comm_semiring
 -/
#check @is_fraction_ring.mul_inv_cancel /- _inst_5: comm_ring ↝ euclidean_domain no_zero_divisors
 -/
#check @is_fraction_ring.mk'_mk_eq_div /- _inst_5: comm_ring ↝ euclidean_domain
_inst_6: is_domain ↝ nontrivial
 -/
#check @is_fraction_ring.is_unit_map_of_injective /- _inst_5: comm_ring ↝ euclidean_domain
_inst_6: is_domain ↝ nontrivial
_inst_10: field ↝ division_semiring
 -/
#check @is_fraction_ring.mk'_eq_zero_iff_eq_zero /- _inst_9: field ↝ comm_ring
 -/
#check @is_fraction_ring.mk'_eq_one_iff_eq /- _inst_5: comm_ring ↝ euclidean_domain
 -/
#check @is_fraction_ring.lift /- _inst_9: field ↝ comm_ring
 -/
#check @is_fraction_ring.field_equiv_of_ring_equiv /- _inst_9: field ↝ comm_ring
_inst_10: field ↝ comm_ring
 -/
#check @fraction_ring /- _inst_1: comm_ring ↝ comm_monoid_with_zero
 -/
#check @fraction_ring.alg_equiv /- _inst_7: field ↝ comm_ring
 -/
#check @fraction_ring.no_zero_smul_divisors /- _inst_5: comm_ring ↝ algebra euclidean_domain has_smul is_localization is_scalar_tower is_scalar_tower no_zero_smul_divisors
 -/

-- ring_theory/localization/integer.lean
#check @is_localization.is_integer /- _inst_2: comm_ring ↝ ring
 -/

-- ring_theory/localization/integral.lean
#check @is_localization.integer_normalization_eval₂_eq_zero /- _inst_6: comm_ring ↝ semiring
 -/
#check @is_fraction_ring.integer_normalization_eq_zero_iff /- _inst_5: comm_ring ↝ distrib_mul_action euclidean_domain no_zero_divisors
_inst_6: is_domain ↝ no_zero_divisors nontrivial
_inst_7: field ↝ comm_ring distrib_mul_action no_zero_divisors
 -/
#check @ring_hom.is_integral_elem_localization_at_leading_coeff /- _inst_11: comm_ring ↝ comm_semiring
_inst_12: comm_ring ↝ comm_semiring
 -/
#check @is_integral_closure.is_fraction_ring_of_algebraic /- _inst_12: comm_ring ↝ field no_zero_divisors
_inst_13: is_domain ↝ group_with_zero no_zero_divisors
 -/
#check @is_fraction_ring.is_algebraic_iff' /- _inst_1: comm_ring ↝ algebra algebra euclidean_domain is_localization is_scalar_tower no_meet_fake_name no_zero_smul_divisors
_inst_2: comm_ring ↝ euclidean_domain no_zero_smul_divisors
 -/
#check @is_fraction_ring.ideal_span_singleton_map_subset /- _inst_1: comm_ring ↝ euclidean_domain is_scalar_tower linear_map.compatible_smul module no_zero_divisors
_inst_2: comm_ring ↝ euclidean_domain is_scalar_tower linear_map.compatible_smul module no_zero_divisors
_inst_9: field ↝ module semifield
 -/

-- ring_theory/localization/inv_submonoid.lean
#check @is_localization.inv_submonoid /- _inst_1: comm_ring ↝ comm_semiring
_inst_2: comm_ring ↝ semiring
 -/
#check @is_localization.submonoid_map_le_is_unit /- _inst_1: comm_ring ↝ comm_semiring
_inst_2: comm_ring ↝ comm_semiring
 -/

-- ring_theory/localization/localization_localization.lean
#check @is_localization.localization_localization_submodule /- _inst_1: comm_ring ↝ comm_semiring
_inst_2: comm_ring ↝ semiring
 -/
#check @is_localization.localization_localization_map_units /- _inst_5: comm_ring ↝ comm_semiring
 -/
#check @is_localization.localization_localization_surj /- _inst_5: comm_ring ↝ comm_semiring
 -/
#check @is_localization.localization_localization_eq_iff_exists /- _inst_5: comm_ring ↝ comm_semiring
 -/
#check @is_localization.localization_algebra_of_submonoid_le /- _inst_2: comm_ring ↝ comm_semiring
 -/
#check @is_localization.is_localization_of_submonoid_le /- _inst_1: comm_ring ↝ comm_semiring
_inst_2: comm_ring ↝ comm_semiring
_inst_5: comm_ring ↝ comm_semiring
 -/
#check @is_localization.is_localization_of_is_exists_mul_mem /- _inst_1: comm_ring ↝ comm_semiring
_inst_2: comm_ring ↝ comm_semiring
 -/
#check @is_fraction_ring.is_fraction_ring_of_is_domain_of_is_localization /- _inst_1: comm_ring ↝ euclidean_domain no_zero_divisors
_inst_5: is_domain ↝ no_zero_divisors nontrivial
 -/

-- ring_theory/localization/module.lean
#check @linear_independent.iff_fraction_ring /- _inst_2: field ↝ euclidean_domain module no_meet_fake_name no_zero_smul_divisors smul_with_zero
_inst_5: add_comm_group ↝ add_comm_monoid has_smul
 -/

-- ring_theory/localization/num_denom.lean
#check @is_fraction_ring.exists_reduced_fraction /- _inst_5: comm_ring ↝ field no_zero_divisors
_inst_6: is_domain ↝ comm_group_with_zero no_zero_divisors
 -/
#check @is_fraction_ring.num /- _inst_5: comm_ring ↝ field
 -/
#check @is_fraction_ring.denom /- _inst_5: comm_ring ↝ field
 -/
#check @is_fraction_ring.num_denom_reduced /- _inst_5: comm_ring ↝ field
 -/
#check @is_fraction_ring.mk'_num_denom /- _inst_5: comm_ring ↝ field
 -/
#check @is_fraction_ring.num_mul_denom_eq_num_iff_eq /- _inst_5: comm_ring ↝ field
 -/
#check @is_fraction_ring.num_mul_denom_eq_num_iff_eq' /- _inst_5: comm_ring ↝ field
 -/
#check @is_fraction_ring.num_mul_denom_eq_num_mul_denom_iff_eq /- _inst_5: comm_ring ↝ field
 -/
#check @is_fraction_ring.eq_zero_of_num_eq_zero /- _inst_5: comm_ring ↝ field
 -/
#check @is_fraction_ring.is_integer_of_is_unit_denom /- _inst_5: comm_ring ↝ field
 -/
#check @is_fraction_ring.is_unit_denom_of_num_eq_zero /- _inst_5: comm_ring ↝ field
 -/

-- ring_theory/localization/submodule.lean
#check @is_localization.coe_submodule /- _inst_2: comm_ring ↝ module semiring
 -/
#check @is_localization.is_noetherian_ring /- _inst_1: comm_ring ↝ comm_semiring
_inst_2: comm_ring ↝ comm_semiring
 -/
#check @is_localization.mem_span_iff /- _inst_1: comm_ring ↝ comm_semiring
_inst_2: comm_ring ↝ comm_semiring distrib_mul_action mul_action
_inst_9: add_comm_group ↝ add_comm_monoid distrib_mul_action has_smul mul_action
 -/

-- ring_theory/matrix_algebra.lean
#check @matrix_equiv_tensor.inv_fun /- _inst_3: algebra ↝ module
 -/

-- ring_theory/multiplicity.lean
#check @multiplicity /- _inst_1: comm_monoid ↝ has_dvd has_pow
 -/
#check @multiplicity.finite /- _inst_1: comm_monoid ↝ has_dvd has_pow
 -/
#check @multiplicity.min_le_multiplicity_add /- _inst_1: comm_semiring ↝ comm_monoid has_add left_distrib_class
 -/
#check @multiplicity.neg /- _inst_1: comm_ring ↝ comm_monoid has_distrib_neg has_neg
 -/

-- ring_theory/mv_polynomial/basic.lean
#check @mv_polynomial.map_range_eq_map /- _inst_2: comm_ring ↝ comm_semiring module
_inst_3: comm_ring ↝ comm_semiring module
 -/

-- ring_theory/nilpotent.lean
#check @is_nilpotent.neg /- _inst_1: ring ↝ has_distrib_neg has_neg monoid_with_zero
 -/
#check @is_nilpotent.map /- _inst_3: monoid_with_zero_hom_class ↝ fun_like monoid_hom_class no_meet_fake_name zero_hom_class
 -/
#check @commute.is_nilpotent_mul_left /- _inst_1: semiring ↝ monoid_with_zero
 -/

-- ring_theory/noetherian.lean
#check @submodule.fg_ker_comp /- _inst_11: add_comm_group ↝ add_comm_monoid
 -/
#check @submodule.fg_restrict_scalars /- _inst_9: add_comm_group ↝ add_comm_monoid has_smul
 -/
#check @ideal.is_idempotent_elem_iff_eq_bot_or_top /- _inst_4: comm_ring ↝ field
_inst_5: is_domain ↝ cancel_monoid_with_zero
 -/
#check @is_noetherian_of_injective /- _inst_6: is_noetherian ↝ is_noetherian no_meet_fake_name
 -/
#check @is_noetherian_of_ker_bot /- _inst_6: is_noetherian ↝ is_noetherian no_meet_fake_name
 -/
#check @is_noetherian_of_range_eq_ker /- _inst_2: add_comm_group ↝ add_comm_monoid
 -/
#check @is_noetherian.exists_endomorphism_iterate_ker_inf_range_eq_bot /- _inst_1: ring ↝ semiring
_inst_2: add_comm_group ↝ add_comm_monoid
 -/
#check @is_noetherian.disjoint_partial_sups_eventually_bot /- _inst_1: ring ↝ semiring
_inst_2: add_comm_group ↝ add_comm_monoid
 -/
#check @ring.is_noetherian_of_subsingleton /- _inst_2: subsingleton ↝ is_noetherian no_meet_fake_name
 -/
#check @ideal.quotient.is_noetherian_ring /- h: is_noetherian_ring ↝ is_noetherian no_meet_fake_name
 -/
#check @is_noetherian_of_fg_of_noetherian /- _inst_2: add_comm_group ↝ add_comm_monoid distrib_mul_action has_smul module mul_action no_meet_fake_name smul_with_zero
_inst_4: is_noetherian_ring ↝ is_noetherian
 -/

-- ring_theory/non_zero_divisors.lean
#check @eq_zero_of_ne_zero_of_mul_right_eq_zero /- _inst_1: monoid_with_zero ↝ has_mul has_zero
 -/
#check @eq_zero_of_ne_zero_of_mul_left_eq_zero /- _inst_1: monoid_with_zero ↝ has_mul has_zero
 -/
#check @map_ne_zero_of_mem_non_zero_divisors /- _inst_2: monoid_with_zero ↝ fun_like has_zero
 -/
#check @map_le_non_zero_divisors_of_injective /- _inst_7: monoid_with_zero_hom_class ↝ fun_like monoid_hom_class no_meet_fake_name zero_hom_class
 -/

-- ring_theory/norm.lean
#check @algebra.norm /- _inst_2: comm_ring ↝ algebra module no_meet_fake_name ring
 -/
#check @algebra.norm_eq_zero_iff_of_basis /- _inst_2: comm_ring ↝ euclidean_domain module no_zero_divisors
_inst_11: is_domain ↝ no_zero_divisors nontrivial
 -/
#check @algebra.norm_eq_prod_automorphisms /- _inst_13: is_galois ↝ is_separable normal
 -/

-- ring_theory/nullstellensatz.lean
#check @mv_polynomial.zero_locus /- _inst_1: field ↝ comm_ring
 -/

-- ring_theory/perfection.lean
#check @ring.perfection /- _inst_1: comm_semiring ↝ has_pow
 -/
#check @mod_p /- _inst_1: field ↝ comm_ring
 -/

-- ring_theory/polynomial/basic.lean
#check @ideal.eq_zero_of_constant_mem_of_maximal /- _inst_1: ring ↝ semiring
 -/
#check @ideal.is_fg_degree_le /- _inst_1: comm_ring ↝ module ring
 -/
#check @polynomial.disjoint_ker_aeval_of_coprime /- _inst_1: comm_ring ↝ algebra algebra comm_semiring no_meet_fake_name
_inst_3: add_comm_group ↝ add_comm_monoid algebra no_meet_fake_name
 -/
#check @polynomial.sup_aeval_range_eq_top_of_coprime /- _inst_3: add_comm_group ↝ add_comm_monoid algebra no_meet_fake_name
 -/
#check @polynomial.sup_ker_aeval_le_ker_aeval_mul /- _inst_3: add_comm_group ↝ add_comm_monoid algebra no_meet_fake_name
 -/
#check @mv_polynomial.is_domain /- _inst_5: comm_ring ↝ euclidean_domain
_inst_6: is_domain ↝ no_meet_fake_name
 -/
#check @mv_polynomial.map_mv_polynomial_eq_eval₂ /- _inst_5: comm_ring ↝ comm_semiring
 -/
#check @mv_polynomial.ker_map /- _inst_2: comm_ring ↝ comm_semiring
 -/
#check @polynomial.unique_factorization_monoid /- _inst_5: comm_ring ↝ field wf_dvd_monoid
_inst_6: is_domain ↝ no_meet_fake_name wf_dvd_monoid
 -/
#check @mv_polynomial.unique_factorization_monoid /- _inst_5: comm_ring ↝ algebra field
 -/

-- ring_theory/polynomial/bernstein.lean
#check @bernstein_polynomial /- _inst_1: comm_ring ↝ ring
 -/

-- ring_theory/polynomial/content.lean
#check @polynomial.content /- _inst_1: comm_ring ↝ field
_inst_2: is_domain ↝ cancel_comm_monoid_with_zero
 -/
#check @polynomial.content_dvd_coeff /- _inst_1: comm_ring ↝ field
 -/
#check @polynomial.content_C /- _inst_1: comm_ring ↝ field normalization_monoid
 -/
#check @polynomial.content_zero /- _inst_1: comm_ring ↝ field normalization_monoid
 -/
#check @polynomial.content_one /- _inst_1: comm_ring ↝ field normalization_monoid
 -/
#check @polynomial.content_X_mul /- _inst_1: comm_ring ↝ field
 -/
#check @polynomial.content_X_pow /- _inst_1: comm_ring ↝ field
 -/
#check @polynomial.content_X /- _inst_1: comm_ring ↝ field
 -/
#check @polynomial.content_C_mul /- _inst_1: comm_ring ↝ field no_zero_divisors normalization_monoid
 -/
#check @polynomial.content_monomial /- _inst_1: comm_ring ↝ field module normalization_monoid
 -/
#check @polynomial.content_eq_zero_iff /- _inst_1: comm_ring ↝ field
 -/
#check @polynomial.normalize_content /- _inst_1: comm_ring ↝ field normalization_monoid
 -/
#check @polynomial.content_eq_gcd_range_of_lt /- _inst_1: comm_ring ↝ field normalization_monoid
 -/
#check @polynomial.content_eq_gcd_range_succ /- _inst_1: comm_ring ↝ field
 -/
#check @polynomial.content_eq_gcd_leading_coeff_content_erase_lead /- _inst_1: comm_ring ↝ field gcd_monoid normalization_monoid
 -/
#check @polynomial.dvd_content_iff_C_dvd /- _inst_1: comm_ring ↝ field
 -/
#check @polynomial.C_content_dvd /- _inst_1: comm_ring ↝ field
 -/
#check @polynomial.is_primitive_iff_content_eq_one /- _inst_1: comm_ring ↝ field normalization_monoid
 -/
#check @polynomial.is_primitive.content_eq_one /- _inst_1: comm_ring ↝ field
 -/
#check @polynomial.prim_part /- _inst_1: comm_ring ↝ field
 -/
#check @polynomial.eq_C_content_mul_prim_part /- _inst_1: comm_ring ↝ field
 -/
#check @polynomial.prim_part_zero /- _inst_1: comm_ring ↝ field
 -/
#check @polynomial.is_primitive_prim_part /- _inst_1: comm_ring ↝ field normalization_monoid
 -/
#check @polynomial.content_prim_part /- _inst_1: comm_ring ↝ field
 -/
#check @polynomial.prim_part_ne_zero /- _inst_1: comm_ring ↝ field
 -/
#check @polynomial.nat_degree_prim_part /- _inst_1: comm_ring ↝ field no_zero_divisors
 -/
#check @polynomial.is_primitive.prim_part_eq /- _inst_1: comm_ring ↝ field
 -/
#check @polynomial.is_unit_prim_part_C /- _inst_1: comm_ring ↝ field normalization_monoid
 -/
#check @polynomial.prim_part_dvd /- _inst_1: comm_ring ↝ field
 -/
#check @polynomial.aeval_prim_part_eq_zero /- _inst_1: comm_ring ↝ algebra distrib_mul_action field
_inst_4: ring ↝ distrib_mul_action euclidean_domain no_zero_divisors
_inst_5: is_domain ↝ no_zero_divisors nontrivial
 -/
#check @polynomial.eval₂_prim_part_eq_zero /- _inst_1: comm_ring ↝ field
_inst_5: is_domain ↝ no_zero_divisors
 -/
#check @polynomial.gcd_content_eq_of_dvd_sub /- _inst_1: comm_ring ↝ field gcd_monoid
 -/
#check @polynomial.content_mul_aux /- _inst_1: comm_ring ↝ field gcd_monoid no_zero_divisors
 -/
#check @polynomial.content_mul /- _inst_1: comm_ring ↝ field gcd_monoid no_zero_divisors normalization_monoid
 -/
#check @polynomial.is_primitive.mul /- _inst_1: comm_ring ↝ field
 -/
#check @polynomial.prim_part_mul /- _inst_1: comm_ring ↝ field
 -/
#check @polynomial.is_primitive.is_primitive_of_dvd /- _inst_1: comm_ring ↝ field normalization_monoid
 -/
#check @polynomial.is_primitive.dvd_prim_part_iff_dvd /- _inst_1: comm_ring ↝ field
 -/
#check @polynomial.exists_primitive_lcm_of_is_primitive /- _inst_1: comm_ring ↝ field no_zero_divisors normalization_monoid
 -/
#check @polynomial.dvd_iff_content_dvd_content_and_prim_part_dvd_prim_part /- _inst_1: comm_ring ↝ field
 -/
#check @polynomial.normalized_gcd_monoid /- _inst_1: comm_ring ↝ field normalization_monoid
 -/
#check @polynomial.degree_gcd_le_left /- _inst_1: comm_ring ↝ field no_zero_divisors
 -/
#check @polynomial.degree_gcd_le_right /- _inst_1: comm_ring ↝ field
 -/

-- ring_theory/polynomial/cyclotomic/basic.lean
#check @polynomial.cyclotomic'_two /- _inst_3: comm_ring ↝ euclidean_domain no_zero_divisors
 -/
#check @polynomial.cyclotomic'_ne_zero /- _inst_3: comm_ring ↝ euclidean_domain
 -/
#check @polynomial.nat_degree_cyclotomic' /- _inst_1: comm_ring ↝ euclidean_domain no_zero_divisors
 -/
#check @polynomial.X_pow_sub_one_eq_prod /- _inst_1: comm_ring ↝ euclidean_domain
 -/
#check @polynomial.cyclotomic'_eq_X_pow_sub_one_div /- _inst_2: comm_ring ↝ euclidean_domain
 -/
#check @polynomial.int_coeff_of_cyclotomic' /- _inst_2: comm_ring ↝ euclidean_domain
 -/
#check @polynomial.prod_cyclotomic_eq_geom_sum /- _inst_1: comm_ring ↝ euclidean_domain
 -/
#check @is_root_of_unity_iff /- _inst_1: comm_ring ↝ euclidean_domain
 -/
#check @polynomial.cyclotomic_eq_prod_X_pow_sub_one_pow_moebius /- _inst_1: comm_ring ↝ algebra euclidean_domain no_meet_fake_name
 -/
#check @is_primitive_root.is_root_cyclotomic /- _inst_1: comm_ring ↝ euclidean_domain
 -/
#check @polynomial.roots_cyclotomic_nodup /- _inst_1: comm_ring ↝ euclidean_domain
 -/
#check @polynomial.cyclotomic.roots_to_finset_eq_primitive_roots /- _inst_1: comm_ring ↝ euclidean_domain
 -/
#check @polynomial.is_root_cyclotomic_iff_char_zero /- _inst_3: char_zero ↝ ne_zero
 -/
#check @polynomial.cyclotomic_injective /- _inst_1: comm_ring ↝ euclidean_domain
 -/
#check @is_primitive_root.minpoly_dvd_cyclotomic /- _inst_1: field ↝ comm_ring is_domain no_zero_divisors
 -/
#check @is_primitive_root.minpoly_eq_cyclotomic_of_irreducible /- _inst_2: comm_ring ↝ euclidean_domain no_zero_smul_divisors
 -/

-- ring_theory/polynomial/eisenstein.lean
#check @polynomial.is_weakly_eisenstein_at.map /- _inst_2: comm_ring ↝ comm_semiring
 -/
#check @polynomial.is_weakly_eisenstein_at.pow_nat_degree_le_of_aeval_zero_of_monic_mem_map /- _inst_1: comm_ring ↝ algebra comm_semiring
 -/
#check @polynomial.monic.leading_coeff_not_mem /- _inst_1: comm_semiring ↝ semiring
 -/
#check @dvd_coeff_zero_of_aeval_eq_prime_smul_of_minpoly_is_eiseinstein_at /- _inst_1: comm_ring ↝ algebra distrib_mul_action field is_scalar_tower mul_action
 -/
#check @mem_adjoin_of_smul_prime_smul_of_minpoly_is_eiseinstein_at /- _inst_1: comm_ring ↝ algebra distrib_mul_action field is_scalar_tower module no_zero_smul_divisors smul_comm_class
_inst_9: is_domain ↝ no_meet_fake_name
 -/
#check @mem_adjoin_of_smul_prime_pow_smul_of_minpoly_is_eiseinstein_at /- _inst_1: comm_ring ↝ field mul_action
 -/

-- ring_theory/polynomial/gauss_lemma.lean
#check @polynomial.is_primitive.is_unit_iff_is_unit_map_of_injective /- _inst_1: comm_ring ↝ field normalization_monoid
_inst_4: comm_ring ↝ euclidean_domain
 -/
#check @polynomial.is_primitive.irreducible_of_irreducible_map_of_injective /- _inst_1: comm_ring ↝ field
 -/
#check @polynomial.is_primitive.is_unit_iff_is_unit_map /- _inst_1: comm_ring ↝ field
_inst_4: field ↝ comm_ring is_domain
 -/
#check @polynomial.is_unit_or_eq_zero_of_is_unit_integer_normalization_prim_part /- _inst_1: comm_ring ↝ algebra field has_smul no_zero_divisors
 -/
#check @polynomial.is_primitive.irreducible_iff_irreducible_map_fraction_map /- _inst_1: comm_ring ↝ algebra field has_smul no_zero_divisors normalization_monoid
 -/
#check @polynomial.is_primitive.dvd_of_fraction_map_dvd_fraction_map /- _inst_1: comm_ring ↝ algebra field has_smul no_zero_divisors
_inst_4: field ↝ algebra comm_ring has_smul is_domain
 -/
#check @polynomial.is_primitive.dvd_iff_fraction_map_dvd_fraction_map /- _inst_1: comm_ring ↝ field
 -/

-- ring_theory/polynomial/rational_root.lean
#check @num_is_root_scale_roots_of_aeval_eq_zero /- _inst_1: comm_ring ↝ algebra field
 -/
#check @num_dvd_of_is_root /- _inst_1: comm_ring ↝ algebra field
 -/
#check @denom_dvd_of_is_root /- _inst_1: comm_ring ↝ algebra field no_zero_divisors
 -/
#check @is_integer_of_is_root_of_monic /- _inst_1: comm_ring ↝ algebra field
 -/
#check @unique_factorization_monoid.integer_of_integral /- _inst_1: comm_ring ↝ field
 -/
#check @unique_factorization_monoid.is_integrally_closed /- _inst_1: comm_ring ↝ algebra field is_localization
 -/

-- ring_theory/polynomial/scale_roots.lean
#check @polynomial.scale_roots /- _inst_4: comm_ring ↝ module ring
 -/
#check @polynomial.scale_roots_eval₂_eq_zero /- _inst_4: comm_ring ↝ comm_semiring
 -/
#check @polynomial.scale_roots_eval₂_eq_zero_of_eval₂_div_eq_zero /- _inst_1: comm_ring ↝ euclidean_domain
_inst_2: is_domain ↝ nontrivial
 -/

-- ring_theory/polynomial/tower.lean
#check @is_scalar_tower.aeval_eq_zero_of_aeval_algebra_map_eq_zero_field /- _inst_10: comm_semiring ↝ semiring
 -/

-- ring_theory/power_basis.lean
#check @power_basis.coe_basis /- _inst_2: comm_ring ↝ module ring
 -/
#check @power_basis.finite_dimensional /- _inst_2: comm_ring ↝ module ring
 -/
#check @power_basis.finrank /- _inst_2: comm_ring ↝ module ring
 -/
#check @power_basis.mem_span_pow' /- _inst_1: comm_ring ↝ algebra comm_semiring module
_inst_2: comm_ring ↝ module semiring
 -/
#check @power_basis.dim_ne_zero /- _inst_2: comm_ring ↝ module ring
 -/
#check @power_basis.minpoly_gen /- _inst_2: comm_ring ↝ module ring
 -/
#check @power_basis.degree_minpoly_gen /- _inst_8: comm_ring ↝ euclidean_domain module
_inst_16: is_domain ↝ nontrivial
 -/
#check @power_basis.minpoly_gen_monic /- _inst_8: comm_ring ↝ euclidean_domain module
_inst_16: is_domain ↝ nontrivial
 -/
#check @power_basis.nat_degree_minpoly /- _inst_8: comm_ring ↝ euclidean_domain
 -/
#check @power_basis.nat_degree_lt_nat_degree /- _inst_1: comm_ring ↝ semiring
 -/
#check @power_basis.constr_pow_aeval /- _inst_8: comm_ring ↝ algebra euclidean_domain module module no_meet_fake_name smul_comm_class
 -/
#check @is_integral.linear_independent_pow /- _inst_2: comm_ring ↝ module ring
 -/
#check @power_basis.adjoin_gen_eq_top /- _inst_2: comm_ring ↝ module ring
 -/

-- ring_theory/power_series/basic.lean
#check @mv_power_series.local_ring /- _inst_1: comm_ring ↝ euclidean_domain
 -/
#check @mv_power_series.map.is_local_ring_hom /- _inst_2: comm_ring ↝ semiring
 -/
#check @mv_power_series.inv /- _inst_1: field ↝ has_inv ring
 -/
#check @power_series.coeff_smul /- _inst_3: module ↝ has_smul module
 -/
#check @power_series.trunc /- _inst_1: comm_semiring ↝ module module semiring
 -/
#check @power_series.eq_zero_or_eq_zero_of_mul_eq_zero /- _inst_2: is_domain ↝ no_zero_divisors
 -/
#check @power_series.is_domain /- _inst_1: ring ↝ euclidean_domain
 -/
#check @power_series.X_prime /- _inst_1: comm_ring ↝ euclidean_domain module
 -/
#check @power_series.rescale_injective /- _inst_1: comm_ring ↝ field module no_zero_divisors
_inst_2: is_domain ↝ cancel_monoid_with_zero no_zero_divisors
 -/
#check @power_series.coeff_mul_one_sub_of_lt_order /- _inst_2: comm_ring ↝ module ring
 -/
#check @polynomial.coe_to_power_series /- _inst_1: comm_semiring ↝ semiring
 -/

-- ring_theory/power_series/well_known.lean
#check @power_series.inv_units_sub /- _inst_1: ring ↝ monoid
 -/
#check @power_series.exp /- _inst_1: ring ↝ semiring
 -/
#check @power_series.sin /- _inst_1: ring ↝ semiring
 -/
#check @power_series.cos /- _inst_1: ring ↝ semiring
 -/

-- ring_theory/principal_ideal_domain.lean
#check @submodule.is_principal.generator_map_dvd_of_mem /- _inst_1: add_comm_group ↝ add_comm_monoid
 -/
#check @submodule.is_principal.generator_submodule_image_dvd_of_mem /- _inst_1: add_comm_group ↝ add_comm_monoid module no_meet_fake_name
 -/
#check @is_prime.to_maximal_ideal /- _inst_1: comm_ring ↝ field no_meet_fake_name submodule.is_principal
_inst_2: is_domain ↝ cancel_monoid_with_zero
_inst_3: is_principal_ideal_ring ↝ no_meet_fake_name submodule.is_principal
 -/
#check @is_field.is_principal_ideal_ring /- _inst_1: comm_ring ↝ ring
 -/
#check @principal_ideal_ring.is_noetherian_ring /- _inst_2: is_principal_ideal_ring ↝ no_meet_fake_name submodule.is_principal
 -/
#check @principal_ideal_ring.is_maximal_of_irreducible /- _inst_2: is_principal_ideal_ring ↝ no_meet_fake_name submodule.is_principal
 -/
#check @principal_ideal_ring.irreducible_iff_prime /- _inst_1: comm_ring ↝ field
_inst_2: is_domain ↝ cancel_comm_monoid_with_zero
 -/
#check @principal_ideal_ring.ring_hom_mem_submonoid_of_factors_subset_of_units_subset /- _inst_7: semiring ↝ non_assoc_semiring
 -/
#check @principal_ideal_ring.to_unique_factorization_monoid /- _inst_1: comm_ring ↝ field wf_dvd_monoid
 -/
#check @is_principal_ideal_ring.of_surjective /- _inst_7: is_principal_ideal_ring ↝ no_meet_fake_name submodule.is_principal
 -/
#check @span_gcd /- _inst_1: comm_ring ↝ field no_meet_fake_name submodule.is_principal
_inst_2: is_domain ↝ cancel_comm_monoid_with_zero
_inst_3: is_principal_ideal_ring ↝ no_meet_fake_name submodule.is_principal
 -/
#check @gcd_dvd_iff_exists /- _inst_1: comm_ring ↝ field
 -/
#check @exists_gcd_eq_mul_add_mul /- _inst_1: comm_ring ↝ field
 -/
#check @gcd_is_unit_iff /- _inst_1: comm_ring ↝ field
 -/
#check @is_coprime_of_dvd /- _inst_1: comm_ring ↝ field
 -/
#check @dvd_or_coprime /- _inst_1: comm_ring ↝ field
 -/
#check @is_coprime_of_irreducible_dvd /- _inst_1: comm_ring ↝ field wf_dvd_monoid
 -/
#check @is_coprime_of_prime_dvd /- _inst_1: comm_ring ↝ field
 -/
#check @irreducible.coprime_iff_not_dvd /- _inst_1: comm_ring ↝ field
 -/
#check @prime.coprime_iff_not_dvd /- _inst_1: comm_ring ↝ field
 -/
#check @irreducible.dvd_iff_not_coprime /- _inst_1: comm_ring ↝ field
 -/
#check @irreducible.coprime_pow_of_not_dvd /- _inst_1: comm_ring ↝ field
 -/
#check @irreducible.coprime_or_dvd /- _inst_1: comm_ring ↝ field
 -/
#check @exists_associated_pow_of_mul_eq_pow' /- _inst_1: comm_ring ↝ field
 -/

-- ring_theory/rees_algebra.lean
#check @monomial_mem_adjoin_monomial /- _inst_1: comm_ring ↝ algebra comm_semiring module module
 -/
#check @rees_algebra.algebra.finite_type /- _inst_4: is_noetherian_ring ↝ is_noetherian
 -/

-- ring_theory/roots_of_unity.lean
#check @is_primitive_root.zpow_eq_one /- _inst_3: comm_group ↝ division_comm_monoid
 -/
#check @is_primitive_root.zpow_eq_one_iff_dvd /- _inst_3: comm_group ↝ division_comm_monoid
 -/
#check @is_primitive_root.inv /- _inst_3: comm_group ↝ division_comm_monoid
 -/
#check @is_primitive_root.zpow_eq_one₀ /- _inst_4: comm_group_with_zero ↝ division_comm_monoid
 -/
#check @is_primitive_root.zpow_eq_one_iff_dvd₀ /- _inst_4: comm_group_with_zero ↝ division_comm_monoid
 -/
#check @is_primitive_root.inv' /- _inst_4: comm_group_with_zero ↝ division_comm_monoid
 -/
#check @is_primitive_root.map_of_injective /- _inst_5: comm_semiring ↝ comm_monoid fun_like no_meet_fake_name one_hom_class
_inst_6: comm_semiring ↝ comm_monoid fun_like no_meet_fake_name one_hom_class
 -/
#check @is_primitive_root.of_map_of_injective /- _inst_5: comm_semiring ↝ comm_monoid fun_like no_meet_fake_name one_hom_class
_inst_6: comm_semiring ↝ comm_monoid fun_like no_meet_fake_name one_hom_class
 -/
#check @is_primitive_root.ne_zero' /- _inst_5: comm_ring ↝ euclidean_domain is_reduced no_zero_divisors
_inst_6: is_domain ↝ is_reduced no_zero_divisors nontrivial
 -/
#check @is_primitive_root.minpoly_dvd_X_pow_sub_one /- _inst_5: field ↝ comm_ring is_domain no_zero_divisors
 -/
#check @is_primitive_root.minpoly_dvd_expand /- _inst_5: field ↝ comm_ring is_domain no_zero_divisors
 -/

-- ring_theory/simple_module.lean
#check @is_simple_module /- _inst_1: ring ↝ semiring
_inst_2: add_comm_group ↝ add_comm_monoid
 -/
#check @is_semisimple_module /- _inst_1: ring ↝ semiring
_inst_2: add_comm_group ↝ add_comm_monoid
 -/
#check @linear_map.surjective_or_eq_zero /- _inst_2: add_comm_group ↝ add_comm_monoid
 -/

-- ring_theory/subring/basic.lean
#check @coe_int_mem /- hSR: subring_class ↝ add_subgroup_class no_meet_fake_name one_mem_class
 -/
#check @subring_class.is_domain /- _inst_3: ring ↝ add_submonoid_class euclidean_domain mul_mem_class no_zero_divisors subsemiring_class
_inst_4: is_domain ↝ no_zero_divisors nontrivial
 -/
#check @subring.is_domain /- _inst_4: ring ↝ euclidean_domain no_zero_divisors
_inst_5: is_domain ↝ no_zero_divisors nontrivial
 -/
#check @ring_hom.eq_of_eq_on_set_top /- _inst_2: ring ↝ non_assoc_semiring
 -/
#check @subring.range_fst /- _inst_1: ring ↝ non_assoc_semiring
_inst_2: ring ↝ non_assoc_semiring
 -/
#check @subring.range_snd /- _inst_1: ring ↝ non_assoc_semiring
_inst_2: ring ↝ non_assoc_semiring
 -/
#check @subring.smul_comm_class_right /- _inst_6: smul_comm_class ↝ no_meet_fake_name smul_comm_class
 -/

-- ring_theory/subsemiring/basic.lean
#check @nat_cast_mem /- _inst_3: add_submonoid_with_one_class ↝ add_mem_class no_meet_fake_name one_mem_class zero_mem_class
 -/
#check @coe_nat_mem /- hSR: subsemiring_class ↝ add_submonoid_class one_mem_class
 -/
#check @subsemiring_class.nontrivial /- hSR: subsemiring_class ↝ add_submonoid_class submonoid_class
 -/
#check @subsemiring_class.no_zero_divisors /- hSR: subsemiring_class ↝ add_submonoid_class mul_mem_class
 -/
#check @subsemiring.smul_comm_class_right /- _inst_7: smul_comm_class ↝ no_meet_fake_name smul_comm_class
 -/

-- ring_theory/tensor_product.lean
#check @linear_map.base_change_sub /- _inst_1: comm_ring ↝ comm_semiring is_scalar_tower is_scalar_tower module module module smul_comm_class
 -/
#check @linear_map.base_change_neg /- _inst_1: comm_ring ↝ comm_semiring is_scalar_tower is_scalar_tower module module module smul_comm_class
 -/
#check @algebra.tensor_product.mul_assoc' /- _inst_3: algebra ↝ module module
_inst_5: algebra ↝ module module
 -/
#check @algebra.tensor_product.tensor_product.has_one /- _inst_3: algebra ↝ module
_inst_5: algebra ↝ module
 -/
#check @algebra.tensor_product.algebra_map_apply /- _inst_7: algebra ↝ algebra has_smul
_inst_9: is_scalar_tower ↝ algebra
 -/
#check @algebra.tensor_product.tensor_product.is_scalar_tower /- _inst_3: algebra ↝ has_smul has_smul is_scalar_tower module
_inst_5: algebra ↝ has_smul is_scalar_tower module
_inst_7: algebra ↝ has_smul has_smul is_scalar_tower
_inst_8: algebra ↝ has_smul has_smul is_scalar_tower
_inst_9: is_scalar_tower ↝ has_smul is_scalar_tower
 -/

-- ring_theory/trace.lean
#check @algebra.trace_algebra_map /- _inst_7: field ↝ comm_ring module
 -/
#check @trace_eq_sum_embeddings_gen /- _inst_7: field ↝ euclidean_domain module
 -/
#check @trace_eq_sum_automorphisms /- _inst_21: is_galois ↝ is_separable normal
 -/

-- ring_theory/unique_factorization_domain.lean
#check @is_noetherian_ring.wf_dvd_monoid /- _inst_3: is_noetherian_ring ↝ is_noetherian
 -/
#check @unique_factorization_monoid.le_multiplicity_iff_repeat_le_normalized_factors /- _inst_3: nontrivial ↝ nonempty
 -/
#check @associates.factor_set /- _inst_2: cancel_comm_monoid_with_zero ↝ comm_monoid_with_zero
 -/
#check @associates.quot_out /- _inst_1: comm_monoid ↝ monoid
 -/

-- ring_theory/valuation/valuation_ring.lean
#check @valuation_ring.value_group /- _inst_1: comm_ring ↝ comm_semiring mul_action
_inst_2: field ↝ mul_action semiring
_inst_3: algebra ↝ mul_action
 -/
#check @valuation_ring.le_total /- _inst_1: comm_ring ↝ euclidean_domain mul_action
_inst_4: is_domain ↝ no_meet_fake_name
 -/
#check @valuation_ring.local_ring /- _inst_1: comm_ring ↝ euclidean_domain
_inst_2: is_domain ↝ no_meet_fake_name
 -/
#check @valuation_ring.iff_dvd_total /- _inst_1: comm_ring ↝ field
 -/
#check @valuation_ring.unique_irreducible /- _inst_1: comm_ring ↝ field
 -/
#check @valuation_ring.iff_is_integer_or_is_integer /- _inst_1: comm_ring ↝ euclidean_domain
 -/
#check @valuation_ring.iff_local_bezout_domain /- _inst_1: comm_ring ↝ field is_bezout local_ring no_meet_fake_name submodule.is_principal
 -/

-- ring_theory/witt_vector/domain.lean
#check @witt_vector.is_domain /- _inst_1: comm_ring ↝ euclidean_domain no_zero_divisors
_inst_3: is_domain ↝ no_zero_divisors nontrivial
 -/

-- ring_theory/witt_vector/frobenius_fraction_field.lean
#check @witt_vector.recursion_main.succ_nth_defining_poly_degree /- _inst_1: comm_ring ↝ euclidean_domain no_zero_divisors
_inst_3: is_domain ↝ no_zero_divisors nontrivial
 -/

-- ring_theory/witt_vector/init_tail.lean
#check @witt_vector.select /- _inst_1: comm_ring ↝ has_zero
 -/

-- ring_theory/witt_vector/teichmuller.lean
#check @witt_vector.teichmuller_fun /- _inst_1: comm_ring ↝ has_zero
 -/

-- ring_theory/witt_vector/truncated.lean
#check @truncated_witt_vector.out /- _inst_1: comm_ring ↝ has_zero
 -/
#check @witt_vector.lift_fun /- _inst_2: semiring ↝ non_assoc_semiring
 -/

-- ring_theory/witt_vector/verschiebung.lean
#check @witt_vector.verschiebung_fun /- _inst_1: comm_ring ↝ has_zero
 -/

-- ring_theory/witt_vector/witt_polynomial.lean
#check @aeval_witt_polynomial /- _inst_3: comm_ring ↝ comm_semiring
 -/

-- set_theory/cardinal/cofinality.lean
#check @strict_order.cof_nonempty /- _inst_1: is_irrefl ↝ is_refl no_meet_fake_name
 -/

-- set_theory/cardinal/finite.lean
#check @nat.card_unique /- _inst_1: unique ↝ inhabited subsingleton
 -/

-- set_theory/zfc/basic.lean
#check @Set.map_definable_aux /- H: pSet.definable ↝
 -/

-- tactic/abel.lean
#check @tactic.abel.term /- _inst_1: add_comm_monoid ↝ add_monoid
 -/
#check @tactic.abel.termg /- _inst_1: add_comm_group ↝ sub_neg_monoid
 -/
#check @tactic.abel.smul /- _inst_1: add_comm_monoid ↝ add_monoid
 -/
#check @tactic.abel.smulg /- _inst_1: add_comm_group ↝ sub_neg_monoid
 -/
#check @tactic.abel.unfold_sub /- _inst_1: subtraction_monoid ↝ sub_neg_monoid
 -/

-- tactic/cancel_denoms.lean
#check @cancel_factors.mul_subst /- _inst_1: comm_ring ↝ comm_semigroup
 -/
#check @cancel_factors.div_subst /- _inst_1: field ↝ division_comm_monoid
 -/
#check @cancel_factors.cancel_factors_eq_div /- _inst_1: field ↝ comm_group_with_zero
 -/
#check @cancel_factors.add_subst /- _inst_1: ring ↝ add_right_cancel_semigroup has_mul left_distrib_class
 -/
#check @cancel_factors.sub_subst /- _inst_1: ring ↝ add_group has_distrib_neg has_mul left_distrib_class
 -/
#check @cancel_factors.neg_subst /- _inst_1: ring ↝ has_distrib_neg has_involutive_neg has_mul
 -/
#check @cancel_factors.cancel_factors_lt /- _inst_1: linear_ordered_field ↝ linear_ordered_semifield
 -/
#check @cancel_factors.cancel_factors_le /- _inst_1: linear_ordered_field ↝ linear_ordered_semifield
 -/
#check @cancel_factors.cancel_factors_eq /- _inst_1: linear_ordered_field ↝ linear_ordered_semifield no_zero_divisors
 -/

-- tactic/linarith/lemmas.lean
#check @linarith.eq_of_eq_of_eq /- _inst_1: ordered_semiring ↝ add_zero_class
 -/
#check @linarith.le_of_eq_of_le /- _inst_1: ordered_semiring ↝ add_zero_class has_le
 -/
#check @linarith.lt_of_eq_of_lt /- _inst_1: ordered_semiring ↝ add_zero_class has_lt
 -/
#check @linarith.le_of_le_of_eq /- _inst_1: ordered_semiring ↝ add_zero_class has_le
 -/
#check @linarith.lt_of_lt_of_eq /- _inst_1: ordered_semiring ↝ add_zero_class has_lt
 -/
#check @linarith.mul_eq /- _inst_1: ordered_semiring ↝ has_lt mul_zero_class
 -/
#check @linarith.mul_zero_eq /- _inst_1: semiring ↝ mul_zero_class
 -/
#check @linarith.zero_mul_eq /- _inst_1: semiring ↝ mul_zero_class
 -/

-- tactic/linear_combination.lean
#check @linear_combo.eq_zero_of_sub_eq_zero /- _inst_1: add_group ↝ subtraction_monoid
 -/

-- tactic/norm_num.lean
#check @norm_num.zero_succ /- _inst_1: semiring ↝ add_monoid_with_one
 -/
#check @norm_num.one_succ /- _inst_1: semiring ↝ has_add has_one
 -/
#check @norm_num.bit0_succ /- _inst_1: semiring ↝ has_add has_one
 -/
#check @norm_num.bit1_succ /- _inst_1: semiring ↝ add_comm_semigroup has_one
 -/
#check @norm_num.zero_adc /- _inst_1: semiring ↝ add_monoid_with_one
 -/
#check @norm_num.adc_zero /- _inst_1: semiring ↝ add_monoid_with_one
 -/
#check @norm_num.one_add /- _inst_1: semiring ↝ add_comm_semigroup has_one
 -/
#check @norm_num.add_bit0_bit0 /- _inst_1: semiring ↝ add_comm_semigroup
 -/
#check @norm_num.add_bit0_bit1 /- _inst_1: semiring ↝ add_comm_semigroup has_one
 -/
#check @norm_num.add_bit1_bit0 /- _inst_1: semiring ↝ add_comm_semigroup has_one
 -/
#check @norm_num.add_bit1_bit1 /- _inst_1: semiring ↝ add_comm_semigroup has_one
 -/
#check @norm_num.adc_one_one /- _inst_1: semiring ↝ has_add has_one
 -/
#check @norm_num.adc_bit0_one /- _inst_1: semiring ↝ add_comm_semigroup has_one
 -/
#check @norm_num.adc_one_bit0 /- _inst_1: semiring ↝ add_comm_semigroup has_one
 -/
#check @norm_num.adc_bit1_one /- _inst_1: semiring ↝ add_comm_semigroup has_one
 -/
#check @norm_num.adc_one_bit1 /- _inst_1: semiring ↝ add_comm_semigroup has_one
 -/
#check @norm_num.adc_bit0_bit0 /- _inst_1: semiring ↝ add_comm_semigroup has_one
 -/
#check @norm_num.adc_bit1_bit0 /- _inst_1: semiring ↝ add_comm_semigroup has_one
 -/
#check @norm_num.adc_bit0_bit1 /- _inst_1: semiring ↝ add_comm_semigroup has_one
 -/
#check @norm_num.adc_bit1_bit1 /- _inst_1: semiring ↝ add_comm_semigroup has_one
 -/
#check @norm_num.bit0_mul /- _inst_1: semiring ↝ has_add has_mul right_distrib_class
 -/
#check @norm_num.mul_bit0' /- _inst_1: semiring ↝ has_add has_mul left_distrib_class
 -/
#check @norm_num.mul_bit1_bit1 /- _inst_1: semiring ↝ add_comm_semigroup left_distrib_class mul_one_class right_distrib_class
 -/
#check @norm_num.ne_zero_of_pos /- _inst_1: ordered_add_comm_group ↝ has_zero preorder
 -/
#check @norm_num.ne_zero_neg /- _inst_1: add_group ↝ subtraction_monoid
 -/
#check @norm_num.clear_denom_div /- _inst_1: division_ring ↝ group_with_zero
 -/
#check @norm_num.nonneg_pos /- _inst_1: ordered_cancel_add_comm_monoid ↝ has_zero preorder
 -/
#check @norm_num.nat_cast_zero /- _inst_1: semiring ↝ add_monoid_with_one
 -/
#check @norm_num.nat_cast_one /- _inst_1: semiring ↝ add_monoid_with_one
 -/
#check @norm_num.nat_cast_bit0 /- _inst_1: semiring ↝ add_monoid_with_one
 -/
#check @norm_num.nat_cast_bit1 /- _inst_1: semiring ↝ add_monoid_with_one
 -/
#check @norm_num.int_cast_zero /- _inst_1: ring ↝ add_group_with_one
 -/
#check @norm_num.int_cast_one /- _inst_1: ring ↝ add_group_with_one
 -/
#check @norm_num.int_cast_bit0 /- _inst_1: ring ↝ add_group_with_one
 -/
#check @norm_num.int_cast_bit1 /- _inst_1: ring ↝ add_group_with_one
 -/
#check @norm_num.int_cast_neg /- _inst_1: ring ↝ add_group_with_one
 -/
#check @norm_num.nat_cast_ne /- _inst_1: semiring ↝ add_monoid_with_one
 -/
#check @norm_num.int_cast_ne /- _inst_1: ring ↝ add_group_with_one
 -/
#check @norm_num.clear_denom_add /- _inst_1: division_ring ↝ cancel_monoid_with_zero has_add right_distrib_class
 -/
#check @norm_num.clear_denom_simple_nat /- _inst_1: division_ring ↝ group_with_zero
 -/
#check @norm_num.clear_denom_simple_div /- _inst_1: division_ring ↝ group_with_zero
 -/
#check @norm_num.clear_denom_mul /- _inst_1: field ↝ cancel_comm_monoid_with_zero
 -/
#check @norm_num.mul_neg_pos /- _inst_1: ring ↝ has_distrib_neg has_involutive_neg has_mul
 -/
#check @norm_num.mul_pos_neg /- _inst_1: ring ↝ has_distrib_neg has_involutive_neg has_mul
 -/
#check @norm_num.mul_neg_neg /- _inst_1: ring ↝ has_distrib_neg has_involutive_neg has_mul
 -/
#check @norm_num.inv_one /- _inst_1: division_ring ↝ division_monoid
 -/
#check @norm_num.inv_one_div /- _inst_1: division_ring ↝ division_monoid
 -/
#check @norm_num.inv_div_one /- _inst_1: division_ring ↝ div_inv_monoid
 -/
#check @norm_num.inv_div /- _inst_1: division_ring ↝ division_monoid
 -/
#check @norm_num.div_eq /- _inst_1: division_ring ↝ div_inv_monoid
 -/
#check @norm_num.sub_pos /- _inst_1: add_group ↝ sub_neg_monoid
 -/
#check @norm_num.sub_neg /- _inst_1: add_group ↝ subtraction_monoid
 -/

-- tactic/ring.lean
#check @tactic.ring.horner /- _inst_1: comm_semiring ↝ has_add has_mul has_pow
 -/
#check @tactic.ring.pow_succ /- _inst_1: comm_semiring ↝ monoid
 -/
#check @tactic.ring.subst_into_pow /- _inst_1: monoid ↝ has_pow
 -/
#check @tactic.ring.unfold_sub /- _inst_1: add_group ↝ sub_neg_monoid
 -/
#check @tactic.ring.unfold_div /- _inst_1: division_ring ↝ div_inv_monoid
 -/
#check @tactic.ring.add_neg_eq_sub /- _inst_1: add_group ↝ sub_neg_monoid
 -/

-- tactic/ring_exp.lean
#check @tactic.ring_exp.sum_congr /- _inst_1: comm_semiring ↝ has_add is_commutative
 -/
#check @tactic.ring_exp.prod_congr /- _inst_1: comm_semiring ↝ has_mul is_commutative
 -/
#check @tactic.ring_exp.exp_congr /- _inst_1: comm_semiring ↝ has_pow
 -/
#check @tactic.ring_exp.base_to_exp_pf /- _inst_1: comm_semiring ↝ monoid
 -/
#check @tactic.ring_exp.exp_to_prod_pf /- _inst_1: comm_semiring ↝ mul_one_class
 -/
#check @tactic.ring_exp.prod_to_sum_pf /- _inst_1: comm_semiring ↝ add_zero_class
 -/
#check @tactic.ring_exp.atom_to_sum_pf /- _inst_1: comm_semiring ↝ semiring
 -/
#check @tactic.ring_exp.mul_coeff_pf_one_mul /- _inst_1: comm_semiring ↝ mul_one_class
 -/
#check @tactic.ring_exp.mul_coeff_pf_mul_one /- _inst_1: comm_semiring ↝ mul_one_class
 -/
#check @tactic.ring_exp.add_overlap_pf /- _inst_1: comm_semiring ↝ has_add has_mul left_distrib_class
 -/
#check @tactic.ring_exp.add_overlap_pf_zero /- _inst_1: comm_semiring ↝ has_add left_distrib_class mul_zero_class
 -/
#check @tactic.ring_exp.add_pf_z_sum /- _inst_1: comm_semiring ↝ add_zero_class
 -/
#check @tactic.ring_exp.add_pf_sum_z /- _inst_1: comm_semiring ↝ add_zero_class
 -/
#check @tactic.ring_exp.add_pf_sum_overlap /- _inst_1: comm_semiring ↝ has_add is_associative is_commutative
 -/
#check @tactic.ring_exp.add_pf_sum_overlap_zero /- _inst_1: comm_semiring ↝ add_zero_class is_associative is_commutative
 -/
#check @tactic.ring_exp.add_pf_sum_lt /- _inst_1: comm_semiring ↝ has_add is_associative is_commutative
 -/
#check @tactic.ring_exp.add_pf_sum_gt /- _inst_1: comm_semiring ↝ has_add is_associative is_commutative
 -/
#check @tactic.ring_exp.mul_pf_c_c /- _inst_1: comm_semiring ↝ has_mul is_commutative
 -/
#check @tactic.ring_exp.mul_pf_c_prod /- _inst_1: comm_semiring ↝ has_mul is_associative is_commutative
 -/
#check @tactic.ring_exp.mul_pf_prod_c /- _inst_1: comm_semiring ↝ has_mul is_associative is_commutative
 -/
#check @tactic.ring_exp.mul_pp_pf_overlap /- _inst_1: comm_semiring ↝ is_commutative monoid
 -/
#check @tactic.ring_exp.mul_pp_pf_prod_lt /- _inst_1: comm_semiring ↝ has_mul is_associative is_commutative
 -/
#check @tactic.ring_exp.mul_pp_pf_prod_gt /- _inst_1: comm_semiring ↝ has_mul is_associative is_commutative
 -/
#check @tactic.ring_exp.mul_p_pf_zero /- _inst_1: comm_semiring ↝ mul_zero_class
 -/
#check @tactic.ring_exp.mul_p_pf_sum /- _inst_1: comm_semiring ↝ has_add has_mul right_distrib_class
 -/
#check @tactic.ring_exp.mul_pf_zero /- _inst_1: comm_semiring ↝ mul_zero_class
 -/
#check @tactic.ring_exp.mul_pf_sum /- _inst_1: comm_semiring ↝ has_add has_mul left_distrib_class
 -/
#check @tactic.ring_exp.pow_e_pf_exp /- _inst_1: comm_semiring ↝ monoid
 -/
#check @tactic.ring_exp.pow_pp_pf_one /- _inst_1: comm_semiring ↝ monoid
 -/
#check @tactic.ring_exp.pow_pf_c_c /- _inst_1: comm_semiring ↝ has_pow
 -/
#check @tactic.ring_exp.pow_pp_pf_c /- _inst_1: comm_semiring ↝ has_pow mul_one_class
 -/
#check @tactic.ring_exp.pow_pp_pf_prod /- _inst_1: comm_semiring ↝ comm_monoid
 -/
#check @tactic.ring_exp.pow_p_pf_one /- _inst_1: comm_semiring ↝ monoid
 -/
#check @tactic.ring_exp.pow_p_pf_zero /- _inst_1: comm_semiring ↝ monoid_with_zero
 -/
#check @tactic.ring_exp.pow_p_pf_succ /- _inst_1: comm_semiring ↝ monoid
 -/
#check @tactic.ring_exp.pow_p_pf_singleton /- _inst_1: comm_semiring ↝ add_zero_class has_pow
 -/
#check @tactic.ring_exp.pow_p_pf_cons /- _inst_1: comm_semiring ↝ has_pow
 -/
#check @tactic.ring_exp.pow_pf_zero /- _inst_1: comm_semiring ↝ monoid
 -/
#check @tactic.ring_exp.pow_pf_sum /- _inst_1: comm_semiring ↝ monoid
 -/
#check @tactic.ring_exp.simple_pf_sum_zero /- _inst_1: comm_semiring ↝ add_zero_class
 -/
#check @tactic.ring_exp.simple_pf_prod_one /- _inst_1: comm_semiring ↝ mul_one_class
 -/
#check @tactic.ring_exp.simple_pf_prod_neg_one /- _inst_2: ring ↝ has_distrib_neg has_involutive_neg mul_one_class
 -/
#check @tactic.ring_exp.simple_pf_var_one /- _inst_1: comm_semiring ↝ monoid
 -/
#check @tactic.ring_exp.simple_pf_exp_one /- _inst_1: comm_semiring ↝ monoid
 -/
#check @tactic.ring_exp.negate_pf /- _inst_2: ring ↝ has_distrib_neg has_neg mul_one_class
 -/
#check @tactic.ring_exp.inverse_pf /- _inst_2: division_ring ↝ has_inv
 -/
#check @tactic.ring_exp.sub_pf /- _inst_2: ring ↝ sub_neg_monoid
 -/
#check @tactic.ring_exp.div_pf /- _inst_2: division_ring ↝ div_inv_monoid
 -/

-- topology/G_delta.lean
#check @is_Gδ_Inter_of_open /- _inst_2: encodable ↝ countable
 -/
#check @is_Gδ_Inter /- _inst_2: encodable ↝ countable
 -/
#check @is_Gδ_singleton /- _inst_3: topological_space.first_countable_topology ↝ filter.is_countably_generated no_meet_fake_name
 -/

-- topology/alexandroff.lean
#check @alexandroff.nhds_within_compl_infty_ne_bot /- _inst_2: noncompact_space ↝ filter.ne_bot
 -/

-- topology/algebra/affine.lean
#check @affine_map.continuous_iff /- _inst_5: topological_add_group ↝ has_continuous_add has_continuous_sub
 -/
#check @affine_map.homothety_continuous /- _inst_5: topological_add_group ↝ has_continuous_add has_continuous_sub
 -/

-- topology/algebra/algebra.lean
#check @continuous_algebra_map_iff_smul /- _inst_6: topological_semiring ↝ has_continuous_mul
 -/
#check @subalgebra.has_continuous_smul /- _inst_6: has_continuous_smul ↝ has_continuous_smul no_meet_fake_name
 -/
#check @subalgebra.topological_closure_comap_homeomorph /- _inst_8: topological_ring ↝ topological_semiring
 -/
#check @algebra.elemental_algebra /- _inst_1: comm_ring ↝ comm_semiring
 -/

-- topology/algebra/const_mul_action.lean
#check @units.has_continuous_const_smul /- _inst_3: mul_action ↝ has_smul
 -/
#check @add_units.has_continuous_const_vadd /- _inst_3: add_action ↝ has_vadd
 -/
#check @vadd_closure_subset /- _inst_3: add_action ↝ has_vadd
 -/
#check @smul_closure_subset /- _inst_3: mul_action ↝ has_smul
 -/
#check @closure_smul₀ /- _inst_7: mul_action_with_zero ↝ has_smul mul_action no_meet_fake_name smul_with_zero
 -/
#check @is_closed_map_smul₀ /- _inst_6: division_ring ↝ division_semiring mul_action no_meet_fake_name smul_with_zero
_inst_10: module ↝ has_smul mul_action no_meet_fake_name smul_with_zero
 -/
#check @fintype.properly_discontinuous_smul /- _inst_1: group ↝ monoid
_inst_3: mul_action ↝ has_smul
_inst_4: fintype ↝ finite
 -/
#check @fintype.properly_discontinuous_vadd /- _inst_1: add_group ↝ add_monoid
_inst_3: add_action ↝ has_vadd
_inst_4: fintype ↝ finite
 -/

-- topology/algebra/continuous_affine_map.lean
#check @continuous_affine_map.coe_smul /- _inst_16: distrib_mul_action ↝ has_smul has_smul
_inst_17: smul_comm_class ↝ has_smul
_inst_18: has_continuous_const_smul ↝ has_smul
 -/
#check @continuous_affine_map.smul_apply /- _inst_16: distrib_mul_action ↝ has_smul has_smul
_inst_17: smul_comm_class ↝ has_smul
_inst_18: has_continuous_const_smul ↝ has_smul
 -/
#check @continuous_affine_map.is_central_scalar /- _inst_16: distrib_mul_action ↝ has_smul has_smul smul_comm_class
 -/

-- topology/algebra/field.lean
#check @topological_ring.topological_space_units /- _inst_1: semiring ↝ monoid
 -/
#check @topological_ring.top_monoid_units /- _inst_4: topological_semiring ↝ has_continuous_mul
 -/
#check @topological_division_ring.induced_units /- _inst_1: division_ring ↝ semiring
 -/
#check @topological_division_ring.units_top_group /- _inst_3: topological_division_ring ↝ has_continuous_inv₀ topological_semiring
 -/

-- topology/algebra/filter_basis.lean
#check @has_continuous_smul.of_basis_zero /- _inst_1: comm_ring ↝ ring
 -/

-- topology/algebra/group.lean
#check @is_open.neg /- _inst_2: has_involutive_neg ↝ has_neg
 -/
#check @is_open.inv /- _inst_2: has_involutive_inv ↝ has_inv
 -/
#check @is_closed.inv /- _inst_2: has_involutive_inv ↝ has_inv
 -/
#check @is_closed.neg /- _inst_2: has_involutive_neg ↝ has_neg
 -/
#check @continuous_zsmul /- _inst_3: topological_add_group ↝ has_continuous_add has_continuous_neg
 -/
#check @continuous_zpow /- _inst_3: topological_group ↝ has_continuous_inv has_continuous_mul
 -/
#check @tendsto_neg_nhds_within_Ioi /- _inst_6: ordered_add_comm_group ↝ add_group covariant_class covariant_class has_continuous_neg preorder
_inst_7: topological_add_group ↝ has_continuous_neg
 -/
#check @tendsto_inv_nhds_within_Ioi /- _inst_6: ordered_comm_group ↝ covariant_class covariant_class group has_continuous_inv preorder
_inst_7: topological_group ↝ has_continuous_inv
 -/
#check @tendsto_neg_nhds_within_Iio /- _inst_6: ordered_add_comm_group ↝ add_group covariant_class covariant_class has_continuous_neg preorder
_inst_7: topological_add_group ↝ has_continuous_neg
 -/
#check @tendsto_inv_nhds_within_Iio /- _inst_6: ordered_comm_group ↝ covariant_class covariant_class group has_continuous_inv preorder
_inst_7: topological_group ↝ has_continuous_inv
 -/
#check @tendsto_neg_nhds_within_Ici /- _inst_6: ordered_add_comm_group ↝ add_group covariant_class covariant_class has_continuous_neg preorder
_inst_7: topological_add_group ↝ has_continuous_neg
 -/
#check @tendsto_inv_nhds_within_Ici /- _inst_6: ordered_comm_group ↝ covariant_class covariant_class group has_continuous_inv preorder
_inst_7: topological_group ↝ has_continuous_inv
 -/
#check @tendsto_neg_nhds_within_Iic /- _inst_6: ordered_add_comm_group ↝ add_group covariant_class covariant_class has_continuous_neg preorder
_inst_7: topological_add_group ↝ has_continuous_neg
 -/
#check @tendsto_inv_nhds_within_Iic /- _inst_6: ordered_comm_group ↝ covariant_class covariant_class group has_continuous_inv preorder
_inst_7: topological_group ↝ has_continuous_inv
 -/
#check @prod.topological_group /- _inst_3: topological_group ↝ has_continuous_inv has_continuous_mul
_inst_7: topological_group ↝ has_continuous_inv has_continuous_mul
 -/
#check @prod.topological_add_group /- _inst_3: topological_add_group ↝ has_continuous_add has_continuous_neg
_inst_7: topological_add_group ↝ has_continuous_add has_continuous_neg
 -/
#check @mul_opposite.has_continuous_inv /- _inst_5: group ↝ has_inv
 -/
#check @add_opposite.has_continuous_neg /- _inst_5: add_group ↝ has_neg
 -/
#check @mul_opposite.topological_group /- _inst_6: topological_group ↝ has_continuous_inv has_continuous_mul
 -/
#check @add_opposite.topological_add_group /- _inst_6: topological_add_group ↝ has_continuous_add has_continuous_neg
 -/
#check @nhds_zero_symm /- _inst_3: topological_add_group ↝ has_continuous_neg
 -/
#check @nhds_one_symm /- _inst_3: topological_group ↝ has_continuous_inv
 -/
#check @inducing.topological_add_group /- _inst_3: topological_add_group ↝ has_continuous_add has_continuous_neg
 -/
#check @inducing.topological_group /- _inst_3: topological_group ↝ has_continuous_inv has_continuous_mul
 -/
#check @neg_mem_connected_component_zero /- _inst_7: topological_add_group ↝ has_continuous_neg
 -/
#check @inv_mem_connected_component_one /- _inst_7: topological_group ↝ has_continuous_inv
 -/
#check @exists_nhds_split_inv /- _inst_3: topological_group ↝ has_continuous_inv has_continuous_mul
 -/
#check @exists_nhds_half_neg /- _inst_3: topological_add_group ↝ has_continuous_add has_continuous_neg
 -/
#check @nhds_translation_mul_inv /- _inst_3: topological_group ↝ has_continuous_mul
 -/
#check @nhds_translation_add_neg /- _inst_3: topological_add_group ↝ has_continuous_add
 -/
#check @map_mul_left_nhds /- _inst_3: topological_group ↝ has_continuous_mul
 -/
#check @map_add_left_nhds /- _inst_3: topological_add_group ↝ has_continuous_add
 -/
#check @quotient_add_group.is_open_map_coe /- _inst_3: topological_add_group ↝ has_continuous_add
 -/
#check @quotient_group.is_open_map_coe /- _inst_3: topological_group ↝ has_continuous_mul
 -/
#check @topological_group.to_has_continuous_div /- _inst_3: topological_group ↝ has_continuous_inv has_continuous_mul
 -/
#check @topological_add_group.to_has_continuous_sub /- _inst_3: topological_add_group ↝ has_continuous_add has_continuous_neg
 -/
#check @tendsto_sub_nhds_zero_iff /- _inst_3: topological_add_group ↝ has_continuous_add has_continuous_sub
 -/
#check @tendsto_div_nhds_one_iff /- _inst_3: topological_group ↝ has_continuous_div has_continuous_mul
 -/
#check @is_open.add_closure /- _inst_3: topological_add_group ↝ has_continuous_add has_continuous_neg
 -/
#check @is_open.mul_closure /- _inst_3: topological_group ↝ has_continuous_inv has_continuous_mul
 -/
#check @topological_group.t1_space /- _inst_3: topological_group ↝ has_continuous_mul
 -/
#check @topological_add_group.t1_space /- _inst_3: topological_add_group ↝ has_continuous_add
 -/
#check @topological_group.t3_space /- _inst_3: topological_group ↝ has_continuous_inv has_continuous_mul
_inst_4: t1_space ↝ t0_space
 -/
#check @topological_add_group.t3_space /- _inst_3: topological_add_group ↝ has_continuous_add has_continuous_neg
_inst_4: t1_space ↝ t0_space
 -/
#check @compact_open_separated_mul_right /- _inst_3: topological_group ↝ has_continuous_mul
 -/
#check @compact_open_separated_add_right /- _inst_3: topological_add_group ↝ has_continuous_add
 -/
#check @compact_covered_by_mul_left_translates /- _inst_3: topological_group ↝ has_continuous_mul
 -/
#check @compact_covered_by_add_left_translates /- _inst_3: topological_add_group ↝ has_continuous_add
 -/
#check @separable_locally_compact_group.sigma_compact_space /- _inst_3: topological_group ↝ has_continuous_mul
 -/
#check @separable_locally_compact_add_group.sigma_compact_space /- _inst_3: topological_add_group ↝ has_continuous_add
 -/
#check @topological_space.positive_compacts.locally_compact_space_of_group /- _inst_3: topological_group ↝ has_continuous_mul
 -/
#check @topological_space.positive_compacts.locally_compact_space_of_add_group /- _inst_3: topological_add_group ↝ has_continuous_add
 -/
#check @additive.topological_add_group /- _inst_3: topological_group ↝ has_continuous_inv has_continuous_mul
 -/
#check @multiplicative.topological_group /- _inst_3: topological_add_group ↝ has_continuous_add has_continuous_neg
 -/
#check @quotient_add_group.has_continuous_const_vadd /- _inst_3: topological_add_group ↝ has_continuous_add
 -/
#check @quotient_group.has_continuous_const_smul /- _inst_3: topological_group ↝ has_continuous_mul
 -/
#check @quotient_group.continuous_smul₁ /- _inst_3: topological_group ↝ has_continuous_mul
 -/
#check @quotient_add_group.continuous_smul₁ /- _inst_3: topological_add_group ↝ has_continuous_add
 -/
#check @quotient_group.has_continuous_smul /- _inst_3: topological_group ↝ has_continuous_mul
 -/
#check @quotient_add_group.has_continuous_vadd /- _inst_3: topological_add_group ↝ has_continuous_add
 -/

-- topology/algebra/group_with_zero.lean
#check @filter.tendsto.div_const /- _inst_1: group_with_zero ↝ div_inv_monoid
 -/
#check @continuous_at.div_const /- _inst_1: group_with_zero ↝ div_inv_monoid
 -/
#check @continuous_on.div_const /- _inst_1: group_with_zero ↝ div_inv_monoid
 -/
#check @continuous.div_const /- _inst_1: group_with_zero ↝ div_inv_monoid
 -/

-- topology/algebra/infinite_sum.lean
#check @has_sum.neg /- _inst_3: topological_add_group ↝ has_continuous_neg
 -/
#check @summable.trans_sub /- _inst_3: topological_add_group ↝ has_continuous_add
 -/
#check @has_sum.update /- _inst_3: topological_add_group ↝ has_continuous_add
 -/
#check @has_sum.int_rec /- _inst_3: topological_add_group ↝ has_continuous_add
 -/
#check @has_sum.mul_left /- _inst_3: topological_semiring ↝ has_continuous_mul
 -/
#check @has_sum.mul_right /- _inst_3: topological_semiring ↝ has_continuous_mul
 -/
#check @has_sum.div_const /- _inst_3: topological_ring ↝ topological_semiring
 -/
#check @has_sum_mul_left_iff /- _inst_3: topological_ring ↝ topological_semiring
 -/
#check @has_sum_mul_right_iff /- _inst_3: topological_ring ↝ topological_semiring
 -/
#check @summable_mul_left_iff /- _inst_3: topological_ring ↝ topological_semiring
 -/
#check @summable_mul_right_iff /- _inst_3: topological_ring ↝ topological_semiring
 -/
#check @has_sum_le_of_sum_le /- _inst_1: ordered_add_comm_monoid ↝ add_comm_monoid preorder
 -/
#check @le_has_sum_of_le_sum /- _inst_1: ordered_add_comm_monoid ↝ add_comm_monoid preorder
 -/
#check @summable_iff_cauchy_seq_finset /- _inst_1: add_comm_group ↝ add_comm_monoid
 -/
#check @has_sum_of_is_lub_of_nonneg /- _inst_1: linear_ordered_add_comm_monoid ↝ Sup_convergence_class ordered_add_comm_monoid
_inst_3: order_topology ↝ Sup_convergence_class
 -/
#check @has_sum_of_is_lub /- _inst_1: canonically_linear_ordered_add_monoid ↝ Sup_convergence_class canonically_ordered_add_monoid
_inst_3: order_topology ↝ Sup_convergence_class
 -/
#check @summable_abs_iff /- _inst_1: linear_ordered_add_comm_group ↝ add_comm_group covariant_class linear_order topological_add_group
 -/
#check @finite_of_summable_const /- _inst_1: linear_ordered_add_comm_group ↝ covariant_class covariant_class linear_ordered_add_comm_monoid
 -/
#check @summable_mul_prod_iff_summable_mul_sigma_antidiagonal /- _inst_2: non_unital_non_assoc_semiring ↝ add_comm_monoid has_mul
 -/
#check @summable_sum_mul_antidiagonal_of_summable_mul /- _inst_4: topological_semiring ↝ has_continuous_add
 -/

-- topology/algebra/module/basic.lean
#check @has_continuous_smul.of_nhds_zero /- _inst_6: topological_ring ↝ has_continuous_sub
_inst_7: topological_add_group ↝ has_continuous_add has_continuous_sub
 -/
#check @module.punctured_nhds_ne_bot /- _inst_1: ring ↝ no_meet_fake_name semiring smul_with_zero
_inst_4: add_comm_group ↝ add_cancel_comm_monoid has_smul no_meet_fake_name smul_with_zero
 -/
#check @is_closed_set_of_map_smul /- _inst_7: module ↝ has_smul
_inst_8: module ↝ has_smul
 -/
#check @continuous_linear_map.smul_apply /- _inst_20: distrib_mul_action ↝ has_smul mul_action
_inst_21: smul_comm_class ↝ mul_action
_inst_22: has_continuous_const_smul ↝ mul_action
 -/
#check @continuous_linear_map.coe_smul /- _inst_20: distrib_mul_action ↝ has_smul has_smul mul_action
_inst_21: smul_comm_class ↝ has_smul mul_action
_inst_22: has_continuous_const_smul ↝ mul_action
 -/
#check @continuous_linear_map.coe_smul' /- _inst_20: distrib_mul_action ↝ has_smul mul_action
_inst_21: smul_comm_class ↝ mul_action
_inst_22: has_continuous_const_smul ↝ mul_action
 -/
#check @continuous_linear_map.is_scalar_tower /- _inst_20: distrib_mul_action ↝ has_smul mul_action
_inst_21: smul_comm_class ↝ mul_action
_inst_22: has_continuous_const_smul ↝ mul_action
_inst_23: distrib_mul_action ↝ has_smul mul_action
_inst_24: smul_comm_class ↝ mul_action
_inst_25: has_continuous_const_smul ↝ mul_action
 -/
#check @continuous_linear_map.smul_comm_class /- _inst_20: distrib_mul_action ↝ has_smul mul_action
_inst_21: smul_comm_class ↝ mul_action
_inst_22: has_continuous_const_smul ↝ mul_action
_inst_23: distrib_mul_action ↝ has_smul mul_action
_inst_24: smul_comm_class ↝ mul_action
_inst_25: has_continuous_const_smul ↝ mul_action
 -/
#check @continuous_linear_map.smul_right_comp /- _inst_22: has_continuous_mul ↝ has_continuous_smul
 -/
#check @continuous_linear_map.map_neg /- _inst_1: ring ↝ semiring
_inst_2: ring ↝ semiring
_inst_7: add_comm_group ↝ subtraction_comm_monoid
 -/
#check @continuous_linear_map.map_sub /- _inst_1: ring ↝ semiring
_inst_2: ring ↝ semiring
_inst_7: add_comm_group ↝ subtraction_comm_monoid
 -/
#check @continuous_linear_map.sub_apply' /- _inst_1: ring ↝ semiring
_inst_2: ring ↝ semiring
_inst_5: add_comm_group ↝ add_comm_monoid
 -/
#check @continuous_linear_map.smul_right_one_pow /- _inst_16: topological_ring ↝ has_continuous_mul has_continuous_smul topological_add_group
 -/
#check @continuous_linear_map.is_open_map_of_ne_zero /- _inst_4: add_comm_group ↝ add_comm_monoid has_smul no_meet_fake_name smul_with_zero
 -/
#check @continuous_linear_map.smul_comp /- _inst_21: distrib_mul_action ↝ has_smul mul_action
_inst_22: smul_comm_class ↝ mul_action
_inst_23: has_continuous_const_smul ↝ mul_action
 -/
#check @continuous_linear_map.is_central_scalar /- _inst_21: module ↝ has_smul module smul_comm_class
 -/
#check @continuous_linear_map.restrict_scalars /- _inst_8: ring ↝ semiring
 -/
#check @continuous_linear_map.restrict_scalars_add /- _inst_12: topological_add_group ↝ has_continuous_add
 -/
#check @continuous_linear_map.restrict_scalars_smul /- _inst_12: ring ↝ distrib_mul_action semiring
_inst_13: module ↝ distrib_mul_action has_smul
 -/
#check @continuous_linear_map.to_ring_inverse /- _inst_7: add_comm_group ↝ add_comm_monoid
 -/
#check @submodule.closed_complemented /- _inst_1: ring ↝ module no_meet_fake_name semiring
_inst_3: add_comm_group ↝ add_comm_monoid module no_meet_fake_name
 -/

-- topology/algebra/module/character_space.lean
#check @weak_dual.character_space /- _inst_5: non_unital_non_assoc_semiring ↝ add_comm_monoid has_mul
 -/
#check @weak_dual.character_space.map_one /- _inst_8: algebra ↝ module
 -/

-- topology/algebra/module/finite_dimension.lean
#check @continuous_linear_map.finite_dimensional /- _inst_2: field ↝ division_ring finite_dimensional has_continuous_const_smul module module no_meet_fake_name smul_comm_class
_inst_11: has_continuous_smul ↝ has_continuous_const_smul module
_inst_12: finite_dimensional ↝ finite_dimensional
_inst_13: finite_dimensional ↝ finite_dimensional
 -/
#check @linear_map.continuous_of_finite_dimensional /- _inst_14: topological_add_group ↝ has_continuous_add
 -/

-- topology/algebra/module/multilinear.lean
#check @continuous_multilinear_map.smul_apply /- _inst_26: distrib_mul_action ↝ has_smul has_smul
_inst_27: has_continuous_const_smul ↝ has_smul
_inst_28: smul_comm_class ↝ has_smul
 -/
#check @continuous_multilinear_map.to_multilinear_map_smul /- _inst_26: distrib_mul_action ↝ has_smul has_smul has_smul
_inst_27: has_continuous_const_smul ↝ has_smul
_inst_28: smul_comm_class ↝ has_smul has_smul
 -/
#check @continuous_multilinear_map.smul_comm_class /- _inst_26: distrib_mul_action ↝ has_smul has_smul
_inst_27: has_continuous_const_smul ↝ has_smul
_inst_28: smul_comm_class ↝ has_smul
_inst_29: distrib_mul_action ↝ has_smul has_smul
_inst_30: has_continuous_const_smul ↝ has_smul
_inst_31: smul_comm_class ↝ has_smul
 -/
#check @continuous_multilinear_map.is_scalar_tower /- _inst_26: distrib_mul_action ↝ has_smul has_smul
_inst_27: has_continuous_const_smul ↝ has_smul
_inst_28: smul_comm_class ↝ has_smul
_inst_29: distrib_mul_action ↝ has_smul has_smul
_inst_30: has_continuous_const_smul ↝ has_smul
_inst_31: smul_comm_class ↝ has_smul
 -/
#check @continuous_multilinear_map.is_central_scalar /- _inst_26: distrib_mul_action ↝ has_smul has_smul smul_comm_class
 -/
#check @continuous_multilinear_map.map_sub /- _inst_2: ring ↝ semiring
 -/

-- topology/algebra/module/weak_dual.lean
#check @weak_bilin.module' /- _inst_2: comm_semiring ↝ semiring
_inst_3: add_comm_group ↝ add_comm_monoid
_inst_5: add_comm_group ↝ add_comm_monoid module
 -/
#check @weak_bilin.is_scalar_tower /- _inst_2: comm_semiring ↝ module no_meet_fake_name semiring
_inst_3: add_comm_group ↝ add_comm_monoid has_smul module module no_meet_fake_name
_inst_5: add_comm_group ↝ add_comm_monoid module module module no_meet_fake_name
_inst_8: module ↝ has_smul module no_meet_fake_name
 -/
#check @weak_dual.module' /- _inst_9: module ↝ has_smul module
_inst_10: smul_comm_class ↝ module
_inst_11: has_continuous_const_smul ↝ module
 -/
#check @weak_dual.has_continuous_const_smul /- _inst_9: distrib_mul_action ↝ has_smul mul_action no_meet_fake_name
_inst_10: smul_comm_class ↝ mul_action no_meet_fake_name
 -/
#check @weak_dual.has_continuous_smul /- _inst_9: distrib_mul_action ↝ has_smul mul_action no_meet_fake_name
_inst_10: smul_comm_class ↝ mul_action no_meet_fake_name
 -/

-- topology/algebra/monoid.lean
#check @has_continuous_mul.of_nhds_one /- _inst_5: monoid ↝ has_one semigroup
 -/
#check @has_continuous_add.of_nhds_zero /- _inst_5: add_monoid ↝ add_semigroup has_zero
 -/
#check @add_subsemigroup.has_continuous_add /- _inst_3: add_semigroup ↝ has_add
 -/
#check @subsemigroup.has_continuous_mul /- _inst_3: semigroup ↝ has_mul
 -/
#check @exists_open_nhds_zero_half /- _inst_3: add_monoid ↝ add_zero_class
 -/
#check @exists_open_nhds_one_split /- _inst_3: monoid ↝ mul_one_class
 -/
#check @is_compact.mul /- _inst_3: monoid ↝ has_mul
 -/
#check @is_compact.add /- _inst_3: add_monoid ↝ has_add
 -/
#check @is_scalar_tower.has_continuous_const_smul /- _inst_5: monoid ↝ mul_one_class
 -/
#check @smul_comm_class.has_continuous_const_smul /- _inst_5: monoid ↝ mul_one_class
 -/
#check @submonoid.mem_nhds_one /- _inst_3: comm_monoid ↝ mul_one_class
 -/
#check @add_submonoid.mem_nhds_zero /- _inst_3: add_comm_monoid ↝ add_zero_class
 -/
#check @locally_finite.exists_finset_support /- _inst_5: add_comm_monoid ↝ has_zero
 -/
#check @locally_finite.exists_finset_mul_support /- _inst_5: comm_monoid ↝ has_one
 -/

-- topology/algebra/mul_action.lean
#check @add_units.has_continuous_vadd /- _inst_5: add_action ↝ has_vadd
 -/
#check @units.has_continuous_smul /- _inst_5: mul_action ↝ has_smul
 -/

-- topology/algebra/nonarchimedean/adic_topology.lean
#check @is_adic_iff /- _inst_2: topological_ring ↝ topological_add_group
 -/
#check @with_ideal.uniform_add_group /- _inst_2: with_ideal ↝ topological_add_group uniform_space
 -/

-- topology/algebra/nonarchimedean/basic.lean
#check @nonarchimedean_group.nonarchimedean_of_emb /- _inst_6: topological_group ↝ has_continuous_inv has_continuous_mul
 -/
#check @nonarchimedean_add_group.nonarchimedean_of_emb /- _inst_6: topological_add_group ↝ has_continuous_add has_continuous_neg
 -/
#check @nonarchimedean_ring.prod.nonarchimedean_ring /- _inst_3: nonarchimedean_ring ↝ has_continuous_add has_continuous_mul has_continuous_neg nonarchimedean_add_group
_inst_6: nonarchimedean_ring ↝ has_continuous_add has_continuous_mul has_continuous_neg nonarchimedean_add_group
 -/
#check @nonarchimedean_ring.left_mul_subset /- _inst_3: nonarchimedean_ring ↝ has_continuous_mul
 -/
#check @nonarchimedean_ring.mul_subset /- _inst_3: nonarchimedean_ring ↝ has_continuous_mul nonarchimedean_add_group
 -/

-- topology/algebra/open_subgroup.lean
#check @submodule.is_open_mono /- _inst_1: comm_ring ↝ ring
_inst_4: topological_add_group ↝ has_continuous_add
 -/
#check @ideal.is_open_of_open_subideal /- _inst_3: topological_ring ↝ topological_add_group
 -/

-- topology/algebra/order/basic.lean
#check @preorder.topology /- _inst_1: preorder ↝ has_lt
 -/
#check @order_dual.order_topology /- _inst_2: partial_order ↝ preorder
 -/
#check @is_open_iff_generate_intervals /- _inst_2: partial_order ↝ preorder
 -/
#check @nhds_eq_order /- _inst_2: partial_order ↝ preorder
 -/
#check @tendsto_Ico_class_nhds /- _inst_2: partial_order ↝ filter.tendsto_Ixx_class no_meet_fake_name preorder
t: order_topology ↝ filter.tendsto_Ixx_class no_meet_fake_name
 -/
#check @tendsto_Ioc_class_nhds /- _inst_2: partial_order ↝ filter.tendsto_Ixx_class no_meet_fake_name preorder
t: order_topology ↝ filter.tendsto_Ixx_class no_meet_fake_name
 -/
#check @tendsto_Ioo_class_nhds /- _inst_2: partial_order ↝ filter.tendsto_Ixx_class no_meet_fake_name preorder
t: order_topology ↝ filter.tendsto_Ixx_class no_meet_fake_name
 -/
#check @induced_order_topology' /- _inst_1: partial_order ↝ preorder
 -/
#check @order_topology.t2_space /- _inst_2: linear_order ↝ preorder t2_space
_inst_3: order_topology ↝ t2_space
 -/
#check @disjoint_nhds_at_top /- _inst_3: order_topology ↝ order_closed_topology
 -/
#check @continuous_abs /- _inst_2: linear_ordered_add_comm_group ↝ has_continuous_neg has_neg linear_order order_closed_topology
_inst_3: order_topology ↝ has_continuous_neg order_closed_topology
 -/
#check @nhds_basis_Ioo_pos /- _inst_2: linear_ordered_add_comm_group ↝ add_comm_group contravariant_class covariant_class covariant_class linear_order
 -/
#check @filter.tendsto.add_at_top /- _inst_2: linear_ordered_add_comm_group ↝ no_min_order ordered_add_comm_group
 -/
#check @tendsto_inv_zero_at_top /- _inst_1: linear_ordered_field ↝ linear_ordered_semifield order_closed_topology
_inst_3: order_topology ↝ order_closed_topology
 -/
#check @tendsto_inv_at_top_zero' /- _inst_1: linear_ordered_field ↝ linear_ordered_semifield
 -/
#check @preimage_neg /- _inst_1: add_group ↝ has_involutive_neg
 -/
#check @filter.map_neg_eq_comap_neg /- _inst_1: add_group ↝ has_involutive_neg
 -/
#check @exists_seq_strict_mono_tendsto' /- _inst_11: topological_space.first_countable_topology ↝ filter.is_countably_generated no_meet_fake_name
 -/
#check @exists_seq_tendsto_Sup /- _inst_10: topological_space.first_countable_topology ↝ filter.is_countably_generated no_meet_fake_name
 -/
#check @filter.eventually.exists_gt /- _inst_2: linear_order ↝ filter.ne_bot no_meet_fake_name preorder
_inst_3: order_topology ↝ filter.ne_bot no_meet_fake_name
_inst_4: densely_ordered ↝ filter.ne_bot no_meet_fake_name
_inst_5: no_max_order ↝ filter.ne_bot no_meet_fake_name
 -/
#check @dense.exists_countable_dense_subset_no_bot_top /- _inst_2: linear_order ↝ filter.ne_bot no_meet_fake_name partial_order t1_space
_inst_3: order_topology ↝ filter.ne_bot no_meet_fake_name t1_space
_inst_4: densely_ordered ↝ filter.ne_bot no_meet_fake_name
_inst_5: nontrivial ↝ filter.ne_bot no_meet_fake_name
 -/
#check @monotone.map_Sup_of_continuous_at' /- _inst_4: complete_linear_order ↝ complete_semilattice_Sup
 -/
#check @monotone.map_cSup_of_continuous_at /- _inst_4: conditionally_complete_linear_order ↝ conditionally_complete_lattice
 -/

-- topology/algebra/order/compact.lean
#check @compact_space_of_complete_linear_order /- _inst_1: complete_linear_order ↝ boolean_algebra bounded_order compact_Icc_space partial_order
_inst_3: order_topology ↝ compact_Icc_space
 -/
#check @is_compact.is_glb_Inf /- _inst_3: order_topology ↝ order_closed_topology
 -/

-- topology/algebra/order/floor.lean
#check @continuous_on_fract /- _inst_4: topological_add_group ↝ has_continuous_sub
 -/
#check @tendsto_fract_left' /- _inst_5: topological_add_group ↝ has_continuous_sub
 -/
#check @tendsto_fract_right' /- _inst_5: topological_add_group ↝ has_continuous_sub
 -/
#check @continuous_on.comp_fract' /- _inst_4: order_topology ↝ order_closed_topology
 -/

-- topology/algebra/order/intermediate_value.lean
#check @is_connected.Ioo_cInf_cSup_subset /- _inst_3: order_topology ↝ order_closed_topology
 -/
#check @is_preconnected.Ioi_cInf_subset /- _inst_3: order_topology ↝ order_closed_topology
 -/
#check @continuous.surjective /- _inst_1: conditionally_complete_linear_order ↝ filter.ne_bot filter.ne_bot preconnected_space preorder
_inst_3: order_topology ↝ preconnected_space
_inst_8: densely_ordered ↝ preconnected_space
 -/

-- topology/algebra/order/liminf_limsup.lean
#check @is_bounded_le_nhds /- _inst_1: semilattice_sup ↝ is_directed partial_order
 -/
#check @filter.tendsto.is_cobounded_under_ge /- _inst_4: filter.ne_bot ↝ filter.ne_bot
 -/
#check @filter.tendsto.is_cobounded_under_le /- _inst_4: filter.ne_bot ↝ filter.ne_bot
 -/
#check @filter.tendsto.limsup_eq /- _inst_4: filter.ne_bot ↝ filter.ne_bot
 -/
#check @filter.tendsto.liminf_eq /- _inst_4: filter.ne_bot ↝ filter.ne_bot
 -/
#check @antitone.map_Limsup_of_continuous_at /- _inst_2: complete_linear_order ↝ no_meet_fake_name
 -/
#check @antitone.map_limsup_of_continuous_at /- _inst_1: filter.ne_bot ↝ filter.ne_bot
 -/
#check @antitone.map_liminf_of_continuous_at /- _inst_1: filter.ne_bot ↝ filter.ne_bot
 -/
#check @monotone.map_limsup_of_continuous_at /- _inst_1: filter.ne_bot ↝ filter.ne_bot
 -/
#check @monotone.map_liminf_of_continuous_at /- _inst_1: filter.ne_bot ↝ filter.ne_bot
 -/

-- topology/algebra/order/monotone_continuity.lean
#check @strict_mono_on.continuous_at_right_of_exists_between /- _inst_3: order_topology ↝ order_closed_topology
_inst_4: linear_order ↝ partial_order
 -/
#check @continuous_at_right_of_monotone_on_of_exists_between /- _inst_3: order_topology ↝ order_closed_topology
_inst_4: linear_order ↝ partial_order
 -/
#check @order_iso.continuous /- _inst_2: partial_order ↝ preorder
 -/

-- topology/algebra/order/monotone_convergence.lean
#check @tendsto_at_top_supr /- _inst_3: complete_lattice ↝ no_meet_fake_name
 -/
#check @tendsto_at_bot_supr /- _inst_3: complete_lattice ↝ no_meet_fake_name
 -/
#check @tendsto_at_bot_infi /- _inst_3: complete_lattice ↝ no_meet_fake_name
 -/
#check @tendsto_at_top_infi /- _inst_3: complete_lattice ↝ no_meet_fake_name
 -/
#check @tendsto_of_monotone /- _inst_4: order_topology ↝ Sup_convergence_class
 -/
#check @tendsto_iff_tendsto_subseq_of_monotone /- _inst_1: semilattice_sup ↝ filter.ne_bot preorder
_inst_3: nonempty ↝ filter.ne_bot
 -/
#check @is_lub_of_tendsto_at_top /- _inst_4: nonempty ↝ filter.ne_bot
 -/
#check @supr_eq_of_tendsto /- _inst_2: complete_linear_order ↝ Sup_convergence_class complete_lattice t2_space
_inst_3: order_topology ↝ Sup_convergence_class t2_space
_inst_4: nonempty ↝ filter.ne_bot
_inst_5: semilattice_sup ↝ filter.ne_bot preorder
 -/
#check @infi_eq_of_tendsto /- _inst_2: complete_linear_order ↝ Inf_convergence_class complete_lattice t2_space
_inst_3: order_topology ↝ Inf_convergence_class t2_space
_inst_4: nonempty ↝ filter.ne_bot
_inst_5: semilattice_sup ↝ filter.ne_bot preorder
 -/

-- topology/algebra/order/proj_Icc.lean
#check @continuous_proj_Icc /- _inst_4: order_topology ↝ order_closed_topology
 -/

-- topology/algebra/polynomial.lean
#check @polynomial.continuous_eval₂ /- _inst_3: topological_semiring ↝ has_continuous_add has_continuous_mul
 -/
#check @polynomial.tendsto_norm_at_top /- _inst_1: normed_ring ↝ has_norm ring
 -/

-- topology/algebra/ring.lean
#check @topological_semiring.has_continuous_neg_of_mul /- _inst_2: non_assoc_ring ↝ has_distrib_neg has_neg mul_one_class
 -/
#check @topological_ring.to_topological_add_group /- _inst_3: topological_ring ↝ has_continuous_add has_continuous_neg
 -/
#check @discrete_topology.topological_semiring /- _inst_3: discrete_topology ↝ has_continuous_add has_continuous_mul
 -/
#check @discrete_topology.topological_ring /- _inst_3: discrete_topology ↝ has_continuous_neg topological_semiring
 -/
#check @subsemiring.topological_semiring /- _inst_3: topological_semiring ↝ has_continuous_add has_continuous_mul
 -/
#check @prod.topological_semiring /- _inst_5: topological_semiring ↝ has_continuous_add has_continuous_mul
_inst_6: topological_semiring ↝ has_continuous_add has_continuous_mul
 -/
#check @prod.topological_ring /- _inst_5: topological_ring ↝ has_continuous_add has_continuous_mul has_continuous_neg
_inst_6: topological_ring ↝ has_continuous_add has_continuous_mul has_continuous_neg
 -/
#check @mul_opposite.has_continuous_add /- _inst_1: non_unital_non_assoc_semiring ↝ has_add
 -/
#check @mul_opposite.topological_semiring /- _inst_3: topological_semiring ↝ has_continuous_add has_continuous_mul
 -/
#check @mul_opposite.has_continuous_neg /- _inst_1: non_unital_non_assoc_ring ↝ has_neg
 -/
#check @mul_opposite.topological_ring /- _inst_3: topological_ring ↝ has_continuous_add has_continuous_mul has_continuous_neg
 -/
#check @add_opposite.has_continuous_mul /- _inst_1: non_unital_non_assoc_semiring ↝ has_mul
 -/
#check @add_opposite.topological_semiring /- _inst_3: topological_semiring ↝ has_continuous_add has_continuous_mul
 -/
#check @add_opposite.topological_ring /- _inst_3: topological_ring ↝ has_continuous_add has_continuous_mul has_continuous_neg
 -/
#check @mul_left_continuous /- _inst_3: topological_ring ↝ has_continuous_mul
 -/
#check @mul_right_continuous /- _inst_3: topological_ring ↝ has_continuous_mul
 -/
#check @subring.topological_ring /- _inst_3: topological_ring ↝ topological_semiring
 -/
#check @topological_ring_quotient_topology /- _inst_2: comm_ring ↝ has_quotient ring
 -/
#check @quotient_ring.is_open_map_coe /- _inst_3: topological_ring ↝ has_continuous_add
 -/

-- topology/algebra/uniform_field.lean
#check @uniform_space.completion.nontrivial /- _inst_1: field ↝ euclidean_domain
 -/
#check @uniform_space.completion.hat_inv /- _inst_1: field ↝ has_inv
 -/
#check @uniform_space.completion.hat_inv_extends /- _inst_3: topological_division_ring ↝ has_continuous_inv₀
 -/
#check @uniform_space.completion.coe_inv /- _inst_4: completable_top_field ↝ separated_space
 -/

-- topology/algebra/uniform_group.lean
#check @tendsto_sub_comap_self /- _inst_2: add_comm_group ↝ add_group fun_like has_continuous_sub no_meet_fake_name zero_hom_class
_inst_3: topological_add_group ↝ has_continuous_sub
_inst_5: add_comm_group ↝ add_group fun_like no_meet_fake_name zero_hom_class
 -/
#check @tendsto_div_comap_self /- _inst_2: comm_group ↝ fun_like group has_continuous_div no_meet_fake_name one_hom_class
_inst_3: topological_group ↝ has_continuous_div
_inst_5: comm_group ↝ fun_like group no_meet_fake_name one_hom_class
 -/

-- topology/algebra/uniform_ring.lean
#check @uniform_space.completion.has_one /- _inst_1: ring ↝ has_one
 -/
#check @uniform_space.completion.has_mul /- _inst_1: ring ↝ has_mul
 -/
#check @uniform_space.completion.coe_mul /- _inst_3: topological_ring ↝ has_continuous_mul
 -/
#check @uniform_space.completion.continuous_mul /- _inst_3: topological_ring ↝ has_continuous_mul topological_add_group
 -/

-- topology/algebra/with_zero_topology.lean
#check @linear_ordered_comm_group_with_zero.nhds_fun /- _inst_1: linear_ordered_comm_group_with_zero ↝ linear_order monoid_with_zero
 -/
#check @linear_ordered_comm_group_with_zero.directed_lt /- _inst_1: linear_ordered_comm_group_with_zero ↝ linear_order monoid
 -/

-- topology/bases.lean
#check @topological_space.encodable.to_separable_space /- _inst_1: encodable ↝ countable
 -/
#check @topological_space.separable_space_of_dense_range /- _inst_1: encodable ↝ countable
 -/
#check @topological_space.is_separable_Union /- _inst_1: encodable ↝ countable
 -/
#check @topological_space.first_countable_topology.tendsto_subseq /- _inst_1: topological_space.first_countable_topology ↝ filter.is_countably_generated no_meet_fake_name
 -/
#check @topological_space.second_countable_topology_of_countable_cover /- _inst_1: encodable ↝ countable
 -/
#check @topological_space.sigma.second_countable_topology /- _inst_2: encodable ↝ countable
 -/

-- topology/basic.lean
#check @is_open_Inter /- _inst_2: fintype ↝ finite
 -/
#check @is_closed_Union /- _inst_2: fintype ↝ finite
 -/

-- topology/bornology/basic.lean
#check @bornology.is_bounded_Union /- _inst_2: fintype ↝ finite
 -/

-- topology/category/Top/limits.lean
#check @nonempty_sections_of_fintype_inverse_system /- _inst_1: preorder ↝ category_theory.is_filtered category_theory.small_category has_le
_inst_2: is_directed ↝ category_theory.is_filtered
 -/

-- topology/connected.lean
#check @is_connected_univ /- _inst_2: connected_space ↝ nonempty preconnected_space
 -/
#check @is_connected_range /- _inst_3: connected_space ↝ nonempty preconnected_space
 -/
#check @prod.connected_space /- _inst_3: connected_space ↝ nonempty preconnected_space
_inst_4: connected_space ↝ nonempty preconnected_space
 -/
#check @irreducible_space.connected_space /- _inst_3: irreducible_space ↝ nonempty preconnected_space
 -/

-- topology/continuous_function/algebra.lean
#check @continuous_map.coe_vadd /- _inst_6: has_continuous_const_vadd ↝ has_vadd
 -/
#check @continuous_map.coe_smul /- _inst_6: has_continuous_const_smul ↝ has_smul
 -/
#check @continuous_map.smul_apply /- _inst_6: has_continuous_const_smul ↝ has_smul
 -/
#check @continuous_map.vadd_apply /- _inst_6: has_continuous_const_vadd ↝ has_vadd
 -/
#check @continuous_map.vadd_comp /- _inst_6: has_continuous_const_vadd ↝ has_vadd
 -/
#check @continuous_map.smul_comp /- _inst_6: has_continuous_const_smul ↝ has_smul
 -/
#check @continuous_map.smul_comm_class /- _inst_6: has_continuous_const_smul ↝ has_smul
_inst_8: has_continuous_const_smul ↝ has_smul
 -/
#check @continuous_map.vadd_comm_class /- _inst_6: has_continuous_const_vadd ↝ has_vadd
_inst_8: has_continuous_const_vadd ↝ has_vadd
 -/
#check @continuous_map.is_scalar_tower /- _inst_6: has_continuous_const_smul ↝ has_smul
_inst_8: has_continuous_const_smul ↝ has_smul
 -/
#check @subalgebra.separates_points /- _inst_5: algebra ↝ algebra has_smul
_inst_11: has_continuous_const_smul ↝ algebra
 -/
#check @algebra_map_apply /- _inst_5: algebra ↝ algebra has_smul
_inst_11: has_continuous_const_smul ↝ algebra
 -/
#check @continuous_map.inf_eq /- _inst_5: topological_ring ↝ has_continuous_add
 -/
#check @continuous_map.sup_eq /- _inst_5: topological_ring ↝ distrib_mul_action has_continuous_add
 -/
#check @continuous_map.star_module /- _inst_8: has_continuous_const_smul ↝ has_smul
 -/

-- topology/continuous_function/bounded.lean
#check @bounded_continuous_function.has_norm /- _inst_2: seminormed_add_comm_group ↝ has_zero pseudo_metric_space
 -/
#check @bounded_continuous_function.coe_smul /- _inst_7: has_bounded_smul ↝ has_smul
 -/
#check @bounded_continuous_function.smul_apply /- _inst_7: has_bounded_smul ↝ has_smul
 -/
#check @bounded_continuous_function.has_nat_cast /- _inst_2: semi_normed_ring ↝ has_nat_cast pseudo_metric_space
 -/
#check @bounded_continuous_function.has_int_cast /- _inst_2: semi_normed_ring ↝ has_int_cast pseudo_metric_space
 -/
#check @bounded_continuous_function.algebra_map_apply /- _inst_5: normed_ring ↝ algebra semi_normed_ring
_inst_6: normed_algebra ↝ algebra has_smul
 -/
#check @bounded_continuous_function.star_module /- _inst_2: star_ring ↝ has_star
_inst_7: normed_space ↝ has_smul has_smul
 -/

-- topology/continuous_function/compact.lean
#check @continuous_map.has_norm /- _inst_4: normed_add_comm_group ↝ has_zero metric_space
 -/
#check @continuous_map.uniform_continuity /- _inst_1: metric_space ↝ pseudo_metric_space separated_space
_inst_3: metric_space ↝ pseudo_metric_space
 -/
#check @bounded_continuous_function.mk_of_compact_star /- _inst_2: normed_add_comm_group ↝ has_continuous_star has_star seminormed_add_comm_group
 -/

-- topology/continuous_function/units.lean
#check @continuous_map.is_unit_iff_forall_ne_zero /- _inst_2: normed_field ↝ normed_division_ring
 -/

-- topology/continuous_function/zero_at_infty.lean
#check @zero_at_infty_continuous_map.coe_smul /- _inst_5: smul_with_zero ↝ has_smul has_smul
_inst_6: has_continuous_const_smul ↝ has_smul
 -/
#check @zero_at_infty_continuous_map.smul_apply /- _inst_5: smul_with_zero ↝ has_smul has_smul
_inst_6: has_continuous_const_smul ↝ has_smul
 -/
#check @zero_at_infty_continuous_map.is_central_scalar /- _inst_5: smul_with_zero ↝ has_smul has_smul
 -/
#check @zero_at_infty_continuous_map.is_scalar_tower /- _inst_5: topological_semiring ↝ has_continuous_mul
_inst_6: module ↝ has_smul has_smul no_meet_fake_name smul_with_zero
 -/
#check @zero_at_infty_continuous_map.smul_comm_class /- _inst_5: topological_semiring ↝ has_continuous_mul
_inst_6: module ↝ has_smul has_smul no_meet_fake_name smul_with_zero
 -/
#check @zero_at_infty_continuous_map.bounded /- _inst_2: metric_space ↝ continuous_map_class pseudo_metric_space
 -/
#check @zero_at_infty_continuous_map.star_module /- _inst_8: smul_with_zero ↝ has_smul has_smul
_inst_9: has_continuous_const_smul ↝ has_smul
 -/

-- topology/continuous_on.lean
#check @nhds_within_pi_univ_eq /- _inst_2: fintype ↝ finite
 -/

-- topology/instances/discrete.lean
#check @discrete_topology.order_topology_of_pred_succ /- _inst_2: linear_order ↝ is_directed is_directed partial_order
 -/

-- topology/instances/ennreal.lean
#check @edist_ne_top_of_mem_ball /- _inst_1: emetric_space ↝ pseudo_emetric_space
 -/
#check @nhds_eq_nhds_emetric_ball /- _inst_1: emetric_space ↝ pseudo_emetric_space
 -/

-- topology/instances/matrix.lean
#check @matrix.topological_semiring /- _inst_5: topological_semiring ↝ has_continuous_add has_continuous_mul
 -/
#check @matrix.topological_ring /- _inst_5: topological_ring ↝ has_continuous_add has_continuous_mul has_continuous_neg
 -/
#check @continuous.matrix_det /- _inst_6: topological_ring ↝ has_continuous_add has_continuous_mul topological_add_group
 -/

-- topology/locally_constant/algebra.lean
#check @locally_constant.coe_smul /- _inst_2: has_smul ↝ has_smul has_smul
 -/
#check @locally_constant.coe_algebra_map /- _inst_4: algebra ↝ algebra algebra no_meet_fake_name
 -/

-- topology/metric_space/antilipschitz.lean
#check @antilipschitz_with /- _inst_1: pseudo_emetric_space ↝ has_edist
_inst_2: pseudo_emetric_space ↝ has_edist
 -/
#check @antilipschitz_with.is_closed_range /- _inst_5: emetric_space ↝ pseudo_emetric_space separated_space
 -/
#check @antilipschitz_with.proper_space /- _inst_3: metric_space ↝ pseudo_metric_space t2_space
 -/

-- topology/metric_space/baire.lean
#check @dense_Inter_of_open /- _inst_3: encodable ↝ countable
 -/
#check @dense_Inter_of_Gδ /- _inst_3: encodable ↝ countable
 -/

-- topology/metric_space/basic.lean
#check @dist_nndist /- _inst_1: pseudo_metric_space ↝ has_dist has_nndist
 -/
#check @dist_lt_coe /- _inst_1: pseudo_metric_space ↝ has_dist has_nndist
 -/
#check @dist_le_coe /- _inst_1: pseudo_metric_space ↝ has_dist has_nndist
 -/
#check @metric.ball /- _inst_1: pseudo_metric_space ↝ has_dist
 -/
#check @metric.closed_ball /- _inst_1: pseudo_metric_space ↝ has_dist
 -/
#check @metric.sphere /- _inst_1: pseudo_metric_space ↝ has_dist
 -/
#check @metric.complete_of_cauchy_seq_tendsto /- _inst_1: pseudo_metric_space ↝ pseudo_emetric_space
 -/
#check @totally_bounded_Icc /- _inst_1: pseudo_metric_space ↝ uniform_space
 -/
#check @metric.bounded /- _inst_1: pseudo_metric_space ↝ has_dist
 -/
#check @metric.diam /- _inst_1: pseudo_metric_space ↝ pseudo_emetric_space
 -/
#check @metric.uniform_embedding_iff' /- _inst_3: metric_space ↝ pseudo_metric_space
 -/
#check @metric.is_closed_of_pairwise_le_dist /- _inst_2: metric_space ↝ pseudo_metric_space separated_space
 -/
#check @metric.closed_embedding_of_pairwise_le_dist /- _inst_2: metric_space ↝ pseudo_metric_space separated_space
 -/
#check @metric.second_countable_of_countable_discretization /- _inst_3: metric_space ↝ proper_space pseudo_metric_space
 -/

-- topology/metric_space/cau_seq_filter.lean
#check @cau_seq.tendsto_limit /- _inst_1: normed_ring ↝ semi_normed_ring
 -/
#check @normed_field.is_absolute_value /- _inst_1: normed_field ↝ normed_division_ring
 -/
#check @cauchy_seq.is_cau_seq /- _inst_1: normed_field ↝ semi_normed_ring
 -/

-- topology/metric_space/closeds.lean
#check @emetric.nonempty_compacts.second_countable_topology /- _inst_2: topological_space.second_countable_topology ↝ topological_space.separable_space
 -/

-- topology/metric_space/completion.lean
#check @uniform_space.completion.has_dist /- _inst_1: pseudo_metric_space ↝ has_dist uniform_space
 -/

-- topology/metric_space/contracting.lean
#check @contracting_with /- _inst_1: emetric_space ↝ pseudo_emetric_space
 -/
#check @contracting_with.one_sub_K_pos /- _inst_1: metric_space ↝ emetric_space
 -/

-- topology/metric_space/emetric_paracompact.lean
#check @emetric.normal_of_emetric /- _inst_1: emetric_space ↝ paracompact_space t2_space topological_space
 -/

-- topology/metric_space/emetric_space.lean
#check @uniformity_dist_of_mem_uniformity /- _inst_1: linear_order ↝ has_lt
 -/
#check @emetric.ball /- _inst_1: pseudo_emetric_space ↝ has_edist
 -/
#check @emetric.closed_ball /- _inst_1: pseudo_emetric_space ↝ has_edist
 -/
#check @emetric.diam /- _inst_1: pseudo_emetric_space ↝ has_edist
 -/
#check @uniform_embedding_iff' /- _inst_3: emetric_space ↝ pseudo_emetric_space
 -/
#check @uniformity_edist /- _inst_2: emetric_space ↝ pseudo_emetric_space
 -/
#check @emetric.countable_closure_of_compact /- _inst_2: emetric_space ↝ pseudo_emetric_space t2_space
 -/

-- topology/metric_space/hausdorff_dimension.lean
#check @cont_diff_on.dimH_image_le /- _inst_5: finite_dimensional ↝ topological_space.second_countable_topology
 -/

-- topology/metric_space/hausdorff_distance.lean
#check @emetric.inf_edist /- _inst_1: pseudo_emetric_space ↝ has_edist
 -/
#check @metric.inf_dist /- _inst_1: pseudo_metric_space ↝ pseudo_emetric_space
 -/
#check @metric.inf_nndist /- _inst_1: pseudo_metric_space ↝ pseudo_emetric_space
 -/
#check @metric.Hausdorff_dist /- _inst_1: pseudo_metric_space ↝ pseudo_emetric_space
 -/

-- topology/metric_space/holder.lean
#check @holder_with /- _inst_1: pseudo_emetric_space ↝ has_edist
_inst_2: pseudo_emetric_space ↝ has_edist
 -/
#check @holder_on_with /- _inst_1: pseudo_emetric_space ↝ has_edist
_inst_2: pseudo_emetric_space ↝ has_edist
 -/

-- topology/metric_space/isometry.lean
#check @isometry /- _inst_1: pseudo_emetric_space ↝ has_edist
_inst_2: pseudo_emetric_space ↝ has_edist
 -/

-- topology/metric_space/lipschitz.lean
#check @lipschitz_with /- _inst_1: pseudo_emetric_space ↝ has_edist
_inst_2: pseudo_emetric_space ↝ has_edist
 -/
#check @lipschitz_on_with /- _inst_1: pseudo_emetric_space ↝ has_edist
_inst_2: pseudo_emetric_space ↝ has_edist
 -/

-- topology/metric_space/metric_separated.lean
#check @is_metric_separated /- _inst_1: emetric_space ↝ has_edist
 -/

-- topology/metric_space/partition_of_unity.lean
#check @emetric.eventually_nhds_zero_forall_closed_ball_subset /- _inst_1: emetric_space ↝ pseudo_emetric_space
 -/
#check @emetric.exists_forall_closed_ball_subset_aux₂ /- _inst_1: emetric_space ↝ pseudo_emetric_space
 -/

-- topology/metric_space/pi_nat.lean
#check @exists_nat_nat_continuous_surjective_of_complete_space /- _inst_3: topological_space.second_countable_topology ↝ topological_space.separable_space
 -/

-- topology/metric_space/polish.lean
#check @polish_space.has_dist_complete_copy /- _inst_1: metric_space ↝ pseudo_metric_space
 -/

-- topology/metric_space/shrinking_lemma.lean
#check @exists_subset_Union_ball_radius_lt /- _inst_1: metric_space ↝ normal_space pseudo_metric_space
 -/
#check @exists_subset_Union_ball_radius_pos_lt /- _inst_1: metric_space ↝ normal_space pseudo_metric_space
 -/

-- topology/partition_of_unity.lean
#check @partition_of_unity.continuous_smul /- _inst_2: add_comm_monoid ↝ has_zero
 -/

-- topology/semicontinuous.lean
#check @lower_semicontinuous_within_at /- _inst_2: preorder ↝ has_lt
 -/
#check @lower_semicontinuous_at /- _inst_2: preorder ↝ has_lt
 -/
#check @upper_semicontinuous_within_at /- _inst_2: preorder ↝ has_lt
 -/
#check @upper_semicontinuous_at /- _inst_2: preorder ↝ has_lt
 -/
#check @continuous_within_at.lower_semicontinuous_within_at /- _inst_5: order_topology ↝ order_closed_topology
 -/
#check @continuous_at.lower_semicontinuous_at /- _inst_5: order_topology ↝ order_closed_topology
 -/
#check @continuous_at.comp_lower_semicontinuous_within_at /- _inst_8: order_topology ↝ order_closed_topology
 -/
#check @lower_semicontinuous_within_at.add' /- _inst_3: linear_ordered_add_comm_monoid ↝ covariant_class covariant_class has_add linear_order order_closed_topology
 -/
#check @continuous_within_at.upper_semicontinuous_within_at /- _inst_5: order_topology ↝ order_closed_topology
 -/
#check @continuous_at.upper_semicontinuous_at /- _inst_5: order_topology ↝ order_closed_topology
 -/

-- topology/separation.lean
#check @exists_open_singleton_of_fintype /- _inst_3: fintype ↝ finite
 -/
#check @discrete_of_t1_of_finite /- _inst_4: fintype ↝ finite
 -/
#check @tendsto_nhds_unique /- _inst_3: filter.ne_bot ↝ filter.ne_bot
 -/
#check @filter.tendsto.lim_eq /- _inst_3: filter.ne_bot ↝ filter.ne_bot
 -/

-- topology/sequences.lean
#check @topological_space.first_countable_topology.sequential_space /- _inst_2: topological_space.first_countable_topology ↝ filter.is_countably_generated no_meet_fake_name
 -/
#check @compact_space.tendsto_subseq /- _inst_2: topological_space.first_countable_topology ↝ seq_compact_space
_inst_3: compact_space ↝ seq_compact_space
 -/

-- topology/subset_properties.lean
#check @compact_Union /- _inst_3: fintype ↝ finite
 -/
#check @filter.coclosed_compact.filter.ne_bot /- _inst_3: noncompact_space ↝ filter.ne_bot
 -/
#check @closed_embedding.noncompact_space /- _inst_3: noncompact_space ↝ filter.ne_bot
 -/
#check @fintype.compact_space /- _inst_3: fintype ↝ finite
 -/
#check @irreducible_space.is_irreducible_univ /- _inst_4: irreducible_space ↝ nonempty preirreducible_space
 -/

-- topology/support.lean
#check @has_compact_mul_support.mul /- _inst_2: monoid ↝ mul_one_class
 -/
#check @has_compact_support.add /- _inst_2: add_monoid ↝ add_zero_class
 -/
#check @has_compact_support.smul_left /- _inst_2: monoid_with_zero ↝ monoid
 -/

-- topology/uniform_space/abstract_completion.lean
#check @abstract_completion.extend_unique /- _inst_4: separated_space ↝ t2_space
 -/
#check @abstract_completion.extend_comp_coe /- _inst_4: separated_space ↝ t2_space
 -/
#check @abstract_completion.extend_map /- _inst_5: separated_space ↝ t2_space
 -/
#check @abstract_completion.extension₂_coe_coe /- _inst_4: separated_space ↝ t2_space
 -/

-- topology/uniform_space/basic.lean
#check @uniform_space.is_open_ball /- _inst_1: uniform_space ↝ topological_space
 -/

-- topology/uniform_space/cauchy.lean
#check @filter.tendsto.cauchy_map /- _inst_2: filter.ne_bot ↝ filter.ne_bot
 -/
#check @cauchy_seq /- _inst_2: semilattice_sup ↝ preorder
 -/
#check @filter.tendsto.cauchy_seq /- _inst_3: nonempty ↝ filter.ne_bot
 -/
#check @cauchy_seq_iff_tendsto /- _inst_2: nonempty ↝ filter.ne_bot
 -/
#check @cauchy_map_iff_exists_tendsto /- _inst_3: filter.ne_bot ↝ filter.ne_bot
 -/

-- topology/uniform_space/compact_convergence.lean
#check @continuous_map.compact_conv_nhd /- _inst_2: uniform_space ↝ topological_space
 -/

-- topology/uniform_space/complete_separated.lean
#check @is_complete.is_closed /- _inst_2: separated_space ↝ t2_space
 -/
#check @dense_inducing.continuous_extend_of_cauchy /- _inst_5: separated_space ↝ t3_space
 -/

-- topology/uniform_space/completion.lean
#check @Cauchy.Cauchy_eq /- _inst_1: inhabited ↝ nonempty
 -/
#check @uniform_space.completion.extension_coe /- _inst_4: separated_space ↝ t2_space
 -/

-- topology/uniform_space/uniform_embedding.lean
#check @uniformly_extend_of_ind /- _inst_4: separated_space ↝ t2_space
 -/
#check @uniformly_extend_unique /- _inst_4: separated_space ↝ t2_space
 -/

-- topology/vector_bundle/basic.lean
#check @continuous_transitions /- _inst_4: normed_add_comm_group ↝ module seminormed_add_comm_group
 -/
#check @topological_vector_bundle.bundle.trivial.module /- _inst_1: nontrivially_normed_field ↝ semiring
 -/

-- topology/vector_bundle/hom.lean
#check @bundle.continuous_linear_map /- _inst_1: normed_field ↝ semiring
_inst_2: normed_field ↝ semiring
 -/

-- topology/vector_bundle/prod.lean
#check @topological_vector_bundle.trivialization.prod.to_fun' /- _inst_1: nontrivially_normed_field ↝ module normed_field
_inst_3: normed_add_comm_group ↝ module seminormed_add_comm_group
_inst_4: normed_space ↝ module
_inst_8: normed_add_comm_group ↝ module seminormed_add_comm_group
_inst_9: normed_space ↝ module
 -/
#check @topological_vector_bundle.trivialization.prod.inv_fun' /- _inst_1: nontrivially_normed_field ↝ module normed_field
_inst_3: normed_add_comm_group ↝ module seminormed_add_comm_group
_inst_4: normed_space ↝ module
_inst_8: normed_add_comm_group ↝ module seminormed_add_comm_group
_inst_9: normed_space ↝ module
 -/
#check @topological_vector_bundle.trivialization.prod /- _inst_16: topological_vector_bundle ↝
 -/



definition Power (X : Type*) := X → Type*
notation `𝒫` X := Power X
definition const {X : Type*} {Y : Type*} := λ b:Y, (λ x:X, b)
notation `↓`:max y:max := const y
section difference_domain
variables (Y : Type*)
class DifferenceDomain extends has_zero Y, has_sub Y := (vanishing_diagonal : Π y, y - y = zero)
class OrderedDifferenceDomain extends has_le Y, DifferenceDomain Y
end difference_domain
section reduction
variables {Y : Type*} {X : Type*} (𝓕 : 𝒫 (X → Y))
definition Reduction := Π f, 𝓕 f → Y
definition left_closed_at (f : X → Y) (g : Y → Y) := 𝓕 f → 𝓕 (g ∘ f)
definition left_closed (g : Y → Y) := Π f, left_closed_at 𝓕 f g
class PointFamily := (has_constants : Π y, 𝓕 ↓y)
section subtraction
instance pointwise_subtraction [has_sub Y] : has_sub (X → Y) := ⟨λ f g, (λ x, f x - g x)⟩
class DifferenceFamily [has_sub Y] := (closure : Π f g (f𝓕 : 𝓕 f) (g𝓕 : 𝓕 g), 𝓕 (f - g))
variables (Int : Reduction 𝓕)
definition left_factors (β : Y → Y) (lc_β : left_closed 𝓕 β) := Π f (f𝓕 : 𝓕 f), Int (β ∘ f) (lc_β f f𝓕) = β (Int f f𝓕)
variables [PointFamily 𝓕]
class UnitalReduction := (constant_reduction : Π y, Int ↓y (PointFamily.has_constants 𝓕 y) = y)
variables [has_le Y]
instance pointwise_le : has_le (X → Y) := ⟨λ f g, (Π x, f x ≤ g x)⟩
class MonotonicReduction := (monotonicity : Π f g {f𝓕 g𝓕}, (f ≤ g) → (Int f f𝓕 ≤ Int g g𝓕))
variables [has_zero Y] [has_sub Y] [DifferenceFamily 𝓕]
definition constant_difference_property := Π f k {f𝓕}, Int (f - ↓k) (DifferenceFamily.closure f ↓k f𝓕 (PointFamily.has_constants 𝓕 k)) = Int f f𝓕 - Int ↓k (PointFamily.has_constants 𝓕 k)
definition translation_invariance_property := Π f g {f𝓕 g𝓕}, 0 ≤ Int (g - f) (DifferenceFamily.closure g f g𝓕 f𝓕) → Int f f𝓕 ≤ Int g g𝓕
class TranslativeReduction := (constant_difference : constant_difference_property 𝓕 Int) (translation_invariance : translation_invariance_property 𝓕 Int)
end subtraction
end reduction
section subdifferential
variables {Y : Type*} [has_zero Y] [has_sub Y] [has_le Y] (φ : Y → Y) (t : Y) (𝒩 : 𝒫 Y)
structure SubDifferential := (map : Y → Y) (root_at_zero : map 0 = 0) (lower_bound_property : Π s, 𝒩 s → map (s - t) ≤ (φ s) - (φ t))
variables {X : Type*} (𝓕 : 𝒫 (X → Y)) (Int : Reduction 𝓕)
structure LeftFactorSubDifferential extends SubDifferential φ t 𝒩 := (is_left_closed : left_closed 𝓕 map) (left_factors : left_factors 𝓕 Int map is_left_closed)
end subdifferential
section jensen_inequality
variables {Y : Type*} [OrderedDifferenceDomain Y] {X : Type*} (𝓕 : 𝒫 (X → Y)) [PointFamily 𝓕] [DifferenceFamily 𝓕] (Int : Reduction 𝓕)
class JensenReduction extends UnitalReduction 𝓕 Int, MonotonicReduction 𝓕 Int, TranslativeReduction 𝓕 Int
theorem jensen_inequality [JensenReduction 𝓕 Int] (f : X → Y) (f𝓕 : 𝓕 f) (𝒩 : 𝒫 Y) (image_contained_in_𝒩 : Π x, 𝒩 (f x)) (φ : Y → Y) (φf𝓕 : 𝓕 (φ ∘ f)) (subdifferential : LeftFactorSubDifferential φ (Int f f𝓕) 𝒩 𝓕 Int) : φ (Int f f𝓕) ≤ Int (φ ∘ f) φf𝓕 := begin
    let t := Int f f𝓕,
    let F := f - ↓t,
    let F𝓕 := DifferenceFamily.closure f ↓t _ _,
    let β := subdifferential.map,
    let inequality := λ x, subdifferential.lower_bound_property (f x) (image_contained_in_𝒩 x),
    let inequality := MonotonicReduction.monotonicity Int (β ∘ F) (φ ∘ f - ↓(φ t)) inequality,
    rewrite subdifferential.left_factors F F𝓕 at inequality,
    rewrite TranslativeReduction.constant_difference Int at inequality,
    rewrite UnitalReduction.constant_reduction Int at inequality,
    rewrite DifferenceDomain.vanishing_diagonal at inequality,
    rewrite subdifferential.root_at_zero at inequality,
    let inequality := TranslativeReduction.translation_invariance Int ↓(φ t) (φ ∘ f) inequality,
    rewrite UnitalReduction.constant_reduction Int at inequality,
    exact inequality,
end
end jensen_inequality


inductive Geometry
  | point
  | line
  | circle

open Geometry

inductive Draw : Geometry → Type
  | point₀ : Draw point
  | point₁ : Draw point
  | ruler : Draw point → Draw point → Draw line
  | compass : Draw point → Draw point → Draw circle
  | line_line : Draw line → Draw line → Draw point
  | line_circle : Draw line → Draw circle → Draw point
  | circle_circle : Draw circle → Draw circle → Draw point

open Draw

#check line
#check ruler

#check ruler point₀ point₁
#check compass point₀ point₁
#check compass point₁ point₀
#check ruler point₀ point₁
#check Inhabited

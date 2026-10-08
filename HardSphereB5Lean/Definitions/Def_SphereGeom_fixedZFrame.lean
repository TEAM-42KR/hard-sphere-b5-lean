import HardSphereB5Lean.Definitions.Def_SphereGeom_sphereMeasure
set_option autoImplicit false

namespace SphereGeom

noncomputable def fixedZRadius (p : E3) : ℝ := Real.sqrt (p 0 ^ 2 + p 1 ^ 2)

noncomputable def fixedZA (p : E3) : E3 :=
  WithLp.toLp 2 ![-p 1 / fixedZRadius p, p 0 / fixedZRadius p, 0]

noncomputable def fixedZB (p : E3) : E3 :=
  WithLp.toLp 2 ![-p 2 * p 0 / fixedZRadius p, -p 2 * p 1 / fixedZRadius p,
    fixedZRadius p]

noncomputable def fixedZFrame (p : E3) : Fin 3 → E3 := ![fixedZA p, fixedZB p, p]

end SphereGeom

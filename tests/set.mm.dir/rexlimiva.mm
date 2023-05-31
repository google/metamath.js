include "cv.mm"
include "wcel.mm"
include "ex.mm"
include "rexlimiv.mm"

theorem rexlimiva
  param wph: wff ph
  param wps: wff ps
  param vx: setvar x
  param cA: class A
  assume rexlimiva.1: |- ( ( x e. A /\ ph ) -> ps )

  disjoint ps x
  assert |- ( E. x e. A ph -> ps )

  proof
    wph
    wps
    vx
    cA
    vx
    cv
    cA
    wcel
    wph
    wps
    rexlimiva.1
    ex
    rexlimiv
end

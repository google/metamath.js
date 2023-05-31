include "cv.mm"
include "wcel.mm"
include "wi.mm"
include "ex.mm"
include "rexlimdv.mm"

theorem rexlimdva
  param wph: wff ph
  param wps: wff ps
  param wch: wff ch
  param vx: setvar x
  param cA: class A
  assume rexlimdva.1: |- ( ( ph /\ x e. A ) -> ( ps -> ch ) )

  disjoint ph x
  disjoint ch x
  assert |- ( ph -> ( E. x e. A ps -> ch ) )

  proof
    wph
    wps
    wch
    vx
    cA
    wph
    vx
    cv
    cA
    wcel
    wps
    wch
    wi
    rexlimdva.1
    ex
    rexlimdv
end

include "cv.mm"
include "wcel.mm"
include "wa.mm"
include "wi.mm"
include "ex.mm"
include "rexlimdvv.mm"

theorem rexlimdvva
  param wph: wff ph
  param wps: wff ps
  param wch: wff ch
  param vx: setvar x
  param vy: setvar y
  param cA: class A
  param cB: class B
  assume rexlimdvva.1: |- ( ( ph /\ ( x e. A /\ y e. B ) ) -> ( ps -> ch ) )

  disjoint x y
  disjoint ph x
  disjoint ph y
  disjoint ch x
  disjoint ch y
  disjoint A y
  assert |- ( ph -> ( E. x e. A E. y e. B ps -> ch ) )

  proof
    wph
    wps
    wch
    vx
    vy
    cA
    cB
    wph
    vx
    cv
    cA
    wcel
    vy
    cv
    cB
    wcel
    wa
    wps
    wch
    wi
    rexlimdvva.1
    ex
    rexlimdvv
end

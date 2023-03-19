include "cv.mm"
include "wcel.mm"
include "wa.mm"
include "wi.mm"
include "ex.mm"
include "rexlimdvv.mm"

theorem rexlimdvva
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
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

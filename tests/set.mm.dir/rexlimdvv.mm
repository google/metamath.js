include "wrex.mm"
include "cv.mm"
include "wcel.mm"
include "wa.mm"
include "wi.mm"
include "expdimp.mm"
include "rexlimdv.mm"
include "rexlimdva.mm"

theorem rexlimdvv
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  assume rexlimdvv.1: |- ( ph -> ( ( x e. A /\ y e. B ) -> ( ps -> ch ) ) )

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
    vy
    cB
    wrex
    wch
    vx
    cA
    wph
    vx
    cv
    cA
    wcel
    #
    wa
    wps
    wch
    vy
    cB
    wph
    @0
    vy
    cv
    cB
    wcel
    wps
    wch
    wi
    rexlimdvv.1
    expdimp
    rexlimdv
    rexlimdva
end

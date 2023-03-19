include "wrex.mm"
include "nfv.mm"
include "cv.mm"
include "wcel.mm"
include "wi.mm"
include "wa.mm"
include "nfan.mm"
include "expdimp.mm"
include "rexlimd.mm"
include "ex.mm"

theorem rexlim2d
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  assume rexlim2d.x: |- F/ x ph
  assume rexlim2d.y: |- F/ y ph
  assume rexlim2d.3: |- ( ph -> ( ( x e. A /\ y e. B ) -> ( ps -> ch ) ) )

  disjoint A y
  disjoint ch x
  disjoint ch y
  disjoint x y
  assert |- ( ph -> ( E. x e. A E. y e. B ps -> ch ) )

  proof
    wph
    wps
    vy
    cB
    wrex
    #
    wch
    vx
    cA
    rexlim2d.x
    wch
    vx
    nfv
    wph
    vx
    cv
    cA
    wcel
    #
    @0
    wch
    wi
    wph
    @1
    wa
    wps
    wch
    vy
    cB
    wph
    @1
    vy
    rexlim2d.y
    @1
    vy
    nfv
    nfan
    wch
    vy
    nfv
    wph
    @1
    vy
    cv
    cB
    wcel
    wps
    wch
    wi
    rexlim2d.3
    expdimp
    rexlimd
    ex
    rexlimd
end

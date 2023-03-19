include "wrex.mm"
include "wi.mm"
include "cv.mm"
include "wcel.mm"
include "com3l.mm"
include "rexlimiv.mm"
include "com12.mm"

theorem rexlimdv
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let vx: setvar x
  let cA: class A
  assume rexlimdv.1: |- ( ph -> ( x e. A -> ( ps -> ch ) ) )

  disjoint ph x
  disjoint ch x
  assert |- ( ph -> ( E. x e. A ps -> ch ) )

  proof
    wps
    vx
    cA
    wrex
    wph
    wch
    wps
    wph
    wch
    wi
    vx
    cA
    wph
    vx
    cv
    cA
    wcel
    wps
    wch
    rexlimdv.1
    com3l
    rexlimiv
    com12
end

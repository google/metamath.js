include "wi.mm"
include "cv.mm"
include "wcel.mm"
include "a1d.mm"
include "rexlimdv.mm"

theorem rexlimdvw
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let vx: setvar x
  let cA: class A
  assume rexlimdvw.1: |- ( ph -> ( ps -> ch ) )

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
    wps
    wch
    wi
    vx
    cv
    cA
    wcel
    rexlimdvw.1
    a1d
    rexlimdv
end

include "cv.mm"
include "wcel.mm"
include "exp31.mm"
include "rexlimdv.mm"

theorem rexlimdva2
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let vx: setvar x
  let cA: class A
  assume rexlimdva2.1: |- ( ( ( ph /\ x e. A ) /\ ps ) -> ch )

  disjoint ch x
  disjoint ph x
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
    rexlimdva2.1
    exp31
    rexlimdv
end

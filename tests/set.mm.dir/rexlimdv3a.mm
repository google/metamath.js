include "cv.mm"
include "wcel.mm"
include "3exp.mm"
include "rexlimdv.mm"

theorem rexlimdv3a
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let vx: setvar x
  let cA: class A
  assume rexlimdv3a.1: |- ( ( ph /\ x e. A /\ ps ) -> ch )

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
    rexlimdv3a.1
    3exp
    rexlimdv
end

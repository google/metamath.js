include "cv.mm"
include "wcel.mm"
include "expr.mm"
include "rexlimdva.mm"

theorem rexlimdvaa
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let vx: setvar x
  let cA: class A
  assume rexlimdvaa.1: |- ( ( ph /\ ( x e. A /\ ps ) ) -> ch )

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
    rexlimdvaa.1
    expr
    rexlimdva
end

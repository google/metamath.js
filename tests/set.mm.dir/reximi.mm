include "wi.mm"
include "cv.mm"
include "wcel.mm"
include "a1i.mm"
include "reximia.mm"

theorem reximi
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let cA: class A
  assume reximi.1: |- ( ph -> ps )


  assert |- ( E. x e. A ph -> E. x e. A ps )

  proof
    wph
    wps
    vx
    cA
    wph
    wps
    wi
    vx
    cv
    cA
    wcel
    reximi.1
    a1i
    reximia
end

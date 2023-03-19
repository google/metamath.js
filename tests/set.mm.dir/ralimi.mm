include "wi.mm"
include "cv.mm"
include "wcel.mm"
include "a1i.mm"
include "ralimia.mm"

theorem ralimi
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let cA: class A
  assume ralimi.1: |- ( ph -> ps )


  assert |- ( A. x e. A ph -> A. x e. A ps )

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
    ralimi.1
    a1i
    ralimia
end

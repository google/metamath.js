include "cv.mm"
include "wcel.mm"
include "a2i.mm"
include "ralimi2.mm"

theorem ralimia
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let cA: class A
  assume ralimia.1: |- ( x e. A -> ( ph -> ps ) )


  assert |- ( A. x e. A ph -> A. x e. A ps )

  proof
    wph
    wps
    vx
    cA
    cA
    vx
    cv
    cA
    wcel
    wph
    wps
    ralimia.1
    a2i
    ralimi2
end

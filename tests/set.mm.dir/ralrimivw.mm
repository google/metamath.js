include "cv.mm"
include "wcel.mm"
include "a1d.mm"
include "ralrimiv.mm"

theorem ralrimivw
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let cA: class A
  assume ralrimivw.1: |- ( ph -> ps )

  disjoint ph x
  assert |- ( ph -> A. x e. A ps )

  proof
    wph
    wps
    vx
    cA
    wph
    wps
    vx
    cv
    cA
    wcel
    ralrimivw.1
    a1d
    ralrimiv
end

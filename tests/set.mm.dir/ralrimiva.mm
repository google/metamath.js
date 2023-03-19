include "cv.mm"
include "wcel.mm"
include "ex.mm"
include "ralrimiv.mm"

theorem ralrimiva
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let cA: class A
  assume ralrimiva.1: |- ( ( ph /\ x e. A ) -> ps )

  disjoint ph x
  assert |- ( ph -> A. x e. A ps )

  proof
    wph
    wps
    vx
    cA
    wph
    vx
    cv
    cA
    wcel
    wps
    ralrimiva.1
    ex
    ralrimiv
end

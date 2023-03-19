include "cv.mm"
include "wcel.mm"
include "ex.mm"
include "ralrimi.mm"

theorem ralrimia
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let cA: class A
  assume ralrimia.1: |- F/ x ph
  assume ralrimia.2: |- ( ( ph /\ x e. A ) -> ps )


  assert |- ( ph -> A. x e. A ps )

  proof
    wph
    wps
    vx
    cA
    ralrimia.1
    wph
    vx
    cv
    cA
    wcel
    wps
    ralrimia.2
    ex
    ralrimi
end

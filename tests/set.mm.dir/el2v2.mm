include "cv.mm"
include "cvv.mm"
include "wcel.mm"
include "vex.mm"
include "mpan2.mm"

theorem el2v2
  let wph: wff ph
  let wps: wff ps
  let vy: setvar y
  assume el2v2.1: |- ( ( ph /\ y e. _V ) -> ps )


  assert |- ( ph -> ps )

  proof
    wph
    vy
    cv
    cvv
    wcel
    wps
    vy
    vex
    el2v2.1
    mpan2
end

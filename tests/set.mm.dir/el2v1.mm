include "cv.mm"
include "cvv.mm"
include "wcel.mm"
include "vex.mm"
include "mpan.mm"

theorem el2v1
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  assume el2v1.1: |- ( ( x e. _V /\ ph ) -> ps )


  assert |- ( ph -> ps )

  proof
    vx
    cv
    cvv
    wcel
    wph
    wps
    vx
    vex
    el2v1.1
    mpan
end

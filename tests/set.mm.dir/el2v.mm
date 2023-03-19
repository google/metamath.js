include "cv.mm"
include "cvv.mm"
include "wcel.mm"
include "vex.mm"
include "mp2an.mm"

theorem el2v
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  assume el2v.1: |- ( ( x e. _V /\ y e. _V ) -> ph )


  assert |- ph

  proof
    vx
    cv
    cvv
    wcel
    vy
    cv
    cvv
    wcel
    wph
    vx
    vex
    vy
    vex
    el2v.1
    mp2an
end

include "cv.mm"
include "cvv.mm"
include "wcel.mm"
include "vex.mm"
include "mp3an.mm"

theorem el3v
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  assume el3v.1: |- ( ( x e. _V /\ y e. _V /\ z e. _V ) -> ph )


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
    vz
    cv
    cvv
    wcel
    wph
    vx
    vex
    vy
    vex
    vz
    vex
    el3v.1
    mp3an
end

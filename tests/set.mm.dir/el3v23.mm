include "cv.mm"
include "cvv.mm"
include "wcel.mm"
include "el3v3.mm"
include "el2v2.mm"

theorem el3v23
  let wph: wff ph
  let wth: wff th
  let vy: setvar y
  let vz: setvar z
  assume el3v23.1: |- ( ( ph /\ y e. _V /\ z e. _V ) -> th )


  assert |- ( ph -> th )

  proof
    wph
    wth
    vy
    wph
    vy
    cv
    cvv
    wcel
    wth
    vz
    el3v23.1
    el3v3
    el2v2
end

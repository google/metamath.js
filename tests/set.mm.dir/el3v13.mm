include "cv.mm"
include "cvv.mm"
include "wcel.mm"
include "el3v3.mm"
include "el2v1.mm"

theorem el3v13
  let wps: wff ps
  let wth: wff th
  let vx: setvar x
  let vz: setvar z
  assume el3v13.1: |- ( ( x e. _V /\ ps /\ z e. _V ) -> th )


  assert |- ( ps -> th )

  proof
    wps
    wth
    vx
    vx
    cv
    cvv
    wcel
    wps
    wth
    vz
    el3v13.1
    el3v3
    el2v1
end

include "cv.mm"
include "cvv.mm"
include "wcel.mm"
include "vex.mm"
include "mp3an1.mm"

theorem el3v1
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let vx: setvar x
  assume el3v1.1: |- ( ( x e. _V /\ ps /\ ch ) -> th )


  assert |- ( ( ps /\ ch ) -> th )

  proof
    vx
    cv
    cvv
    wcel
    wps
    wch
    wth
    vx
    vex
    el3v1.1
    mp3an1
end

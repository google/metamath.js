include "cv.mm"
include "cvv.mm"
include "wcel.mm"
include "vex.mm"
include "mp3an3.mm"

theorem el3v3
  let wph: wff ph
  let wps: wff ps
  let wth: wff th
  let vz: setvar z
  assume el3v3.1: |- ( ( ph /\ ps /\ z e. _V ) -> th )


  assert |- ( ( ph /\ ps ) -> th )

  proof
    wph
    wps
    vz
    cv
    cvv
    wcel
    wth
    vz
    vex
    el3v3.1
    mp3an3
end

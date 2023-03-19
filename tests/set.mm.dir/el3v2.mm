include "cv.mm"
include "cvv.mm"
include "wcel.mm"
include "vex.mm"
include "mp3an2.mm"

theorem el3v2
  let wph: wff ph
  let wch: wff ch
  let wth: wff th
  let vy: setvar y
  assume el3v2.1: |- ( ( ph /\ y e. _V /\ ch ) -> th )


  assert |- ( ( ph /\ ch ) -> th )

  proof
    wph
    vy
    cv
    cvv
    wcel
    wch
    wth
    vy
    vex
    el3v2.1
    mp3an2
end

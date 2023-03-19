include "cv.mm"
include "cvv.mm"
include "wcel.mm"
include "vex.mm"
include "ax-mp.mm"

theorem elv
  let wph: wff ph
  let vx: setvar x
  assume elv.1: |- ( x e. _V -> ph )


  assert |- ph

  proof
    vx
    cv
    cvv
    wcel
    wph
    vx
    vex
    elv.1
    ax-mp
end

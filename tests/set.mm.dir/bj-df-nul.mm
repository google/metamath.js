include "wfal.mm"
include "c0.mm"
include "cv.mm"
include "wcel.mm"
include "noel.mm"
include "bifal.mm"
include "bj-abbi2i.mm"

theorem bj-df-nul
  let vx: setvar x


  assert |- (/) = { x | F. }

  proof
    wfal
    vx
    c0
    vx
    cv
    #
    c0
    wcel
    @0
    noel
    bifal
    bj-abbi2i
end

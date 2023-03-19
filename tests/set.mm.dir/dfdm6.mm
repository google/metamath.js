include "cv.mm"
include "cec.mm"
include "c0.mm"
include "wne.mm"
include "cdm.mm"
include "ecdmn0.mm"
include "abbi2i.mm"

theorem dfdm6
  let vx: setvar x
  let cR: class R

  disjoint R x
  assert |- dom R = { x | [ x ] R =/= (/) }

  proof
    vx
    cv
    #
    cR
    cec
    c0
    wne
    vx
    cR
    cdm
    @0
    cR
    ecdmn0
    abbi2i
end

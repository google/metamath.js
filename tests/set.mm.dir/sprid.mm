include "cv.mm"
include "cpr.mm"
include "wceq.mm"
include "cvv.mm"
include "wrex.mm"
include "wex.mm"
include "rexv.mm"
include "exbii.mm"
include "bitri.mm"
include "abbii.mm"

theorem sprid
  let vp: setvar p
  let va: setvar a
  let vb: setvar b
  let vk: setvar k
  let vx: setvar x


  assert |- { p | E. a e. _V E. b e. _V p = { a , b } } = { p | E. a E. b p = { a , b } }

  proof
    vp
    cv
    va
    cv
    vb
    cv
    cpr
    wceq
    #
    vb
    cvv
    wrex
    #
    va
    cvv
    wrex
    #
    @0
    vb
    wex
    #
    va
    wex
    #
    vp
    @2
    @1
    va
    wex
    @4
    @1
    va
    rexv
    @1
    @3
    va
    @0
    vb
    rexv
    exbii
    bitri
    abbii
end

include "cvv.mm"
include "cv.mm"
include "cts.mm"
include "cfv.mm"
include "cbs.mm"
include "crest.mm"
include "co.mm"
include "ctopn.mm"
include "ovex.mm"
include "df-topn.mm"
include "fnmpti.mm"

theorem topnfn
  let vj: setvar j
  let vx: setvar x
  let vy: setvar y
  let vw: setvar w


  assert |- TopOpen Fn _V

  proof
    vw
    cvv
    vw
    cv
    #
    cts
    cfv
    #
    @0
    cbs
    cfv
    #
    crest
    co
    ctopn
    @1
    @2
    crest
    ovex
    vw
    df-topn
    fnmpti
end

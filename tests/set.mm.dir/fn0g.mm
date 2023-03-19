include "cvv.mm"
include "cv.mm"
include "cbs.mm"
include "cfv.mm"
include "wcel.mm"
include "cplusg.mm"
include "co.mm"
include "wceq.mm"
include "wa.mm"
include "wral.mm"
include "cio.mm"
include "c0g.mm"
include "iotaex.mm"
include "df-0g.mm"
include "fnmpti.mm"

theorem fn0g
  let ve: setvar e
  let vg: setvar g
  let vx: setvar x


  assert |- 0g Fn _V

  proof
    vg
    cvv
    ve
    cv
    #
    vg
    cv
    #
    cbs
    cfv
    #
    wcel
    @0
    vx
    cv
    #
    @1
    cplusg
    cfv
    #
    co
    @3
    wceq
    @3
    @0
    @4
    co
    @3
    wceq
    wa
    vx
    @2
    wral
    wa
    #
    ve
    cio
    c0g
    @5
    ve
    iotaex
    vx
    ve
    vg
    df-0g
    fnmpti
end

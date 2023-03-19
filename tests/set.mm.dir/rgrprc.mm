include "cv.mm"
include "cc0.mm"
include "crusgr.mm"
include "wbr.mm"
include "cab.mm"
include "crgr.mm"
include "wss.mm"
include "cvv.mm"
include "wnel.mm"
include "rusgrrgr.mm"
include "ss2abi.mm"
include "rusgrprc.mm"
include "prcssprc.mm"
include "mp2an.mm"

theorem rgrprc
  let vg: setvar g
  let ve: setvar e
  let vp: setvar p
  let vv: setvar v


  assert |- { g | g RegGraph 0 } e/ _V

  proof
    vg
    cv
    #
    cc0
    crusgr
    wbr
    #
    vg
    cab
    #
    @0
    cc0
    crgr
    wbr
    #
    vg
    cab
    #
    wss
    @2
    cvv
    wnel
    @4
    cvv
    wnel
    @1
    @3
    vg
    @0
    cc0
    rusgrrgr
    ss2abi
    vg
    rusgrprc
    @2
    @4
    prcssprc
    mp2an
end

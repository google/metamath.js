include "cxr.mm"
include "cle.mm"
include "crn.mm"
include "cv.mm"
include "wcel.mm"
include "wbr.mm"
include "xrleid.mm"
include "lerel.mm"
include "relelrni.mm"
include "syl.mm"
include "ssriv.mm"
include "cxp.mm"
include "wss.mm"
include "lerelxr.mm"
include "rnss.mm"
include "ax-mp.mm"
include "rnxpss.mm"
include "sstri.mm"
include "eqssi.mm"

theorem lern
  let vx: setvar x


  assert |- RR* = ran <_

  proof
    cxr
    cle
    crn
    #
    vx
    cxr
    @0
    vx
    cv
    #
    cxr
    wcel
    @1
    @1
    cle
    wbr
    @1
    @0
    wcel
    @1
    xrleid
    @1
    @1
    cle
    lerel
    relelrni
    syl
    ssriv
    @0
    cxr
    cxr
    cxp
    #
    crn
    #
    cxr
    cle
    @2
    wss
    @0
    @3
    wss
    lerelxr
    cle
    @2
    rnss
    ax-mp
    cxr
    cxr
    rnxpss
    sstri
    eqssi
end

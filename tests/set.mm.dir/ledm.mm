include "cxr.mm"
include "cle.mm"
include "cdm.mm"
include "cv.mm"
include "wcel.mm"
include "wbr.mm"
include "xrleid.mm"
include "lerel.mm"
include "releldmi.mm"
include "syl.mm"
include "ssriv.mm"
include "cxp.mm"
include "wss.mm"
include "lerelxr.mm"
include "dmss.mm"
include "ax-mp.mm"
include "dmxpss.mm"
include "sstri.mm"
include "eqssi.mm"

theorem ledm
  let vx: setvar x


  assert |- RR* = dom <_

  proof
    cxr
    cle
    cdm
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
    releldmi
    syl
    ssriv
    @0
    cxr
    cxr
    cxp
    #
    cdm
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
    dmss
    ax-mp
    cxr
    cxr
    dmxpss
    sstri
    eqssi
end

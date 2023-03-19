include "chlt.mm"
include "wcel.mm"
include "coml.mm"
include "ccla.mm"
include "clc.mm"
include "w3a.mm"
include "cv.mm"
include "wne.mm"
include "cjn.mm"
include "cfv.mm"
include "co.mm"
include "cple.mm"
include "wbr.mm"
include "catm.mm"
include "wrex.mm"
include "wi.mm"
include "wral.mm"
include "cp0.mm"
include "cplt.mm"
include "wa.mm"
include "cp1.mm"
include "cbs.mm"
include "eqid.mm"
include "ishlat1.mm"
include "simplbi.mm"

theorem hlomcmcv
  let cK: class K
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z


  assert |- ( K e. HL -> ( K e. OML /\ K e. CLat /\ K e. CvLat ) )

  proof
    cK
    chlt
    wcel
    cK
    coml
    wcel
    cK
    ccla
    wcel
    cK
    clc
    wcel
    w3a
    vx
    cv
    #
    vy
    cv
    #
    wne
    vz
    cv
    #
    @0
    wne
    @2
    @1
    wne
    @2
    @0
    @1
    cK
    cjn
    cfv
    #
    co
    cK
    cple
    cfv
    #
    wbr
    w3a
    vz
    cK
    catm
    cfv
    #
    wrex
    wi
    vy
    @5
    wral
    vx
    @5
    wral
    cK
    cp0
    cfv
    #
    @0
    cK
    cplt
    cfv
    #
    wbr
    @0
    @1
    @7
    wbr
    wa
    @1
    @2
    @7
    wbr
    @2
    cK
    cp1
    cfv
    #
    @7
    wbr
    wa
    wa
    vz
    cK
    cbs
    cfv
    #
    wrex
    vy
    @9
    wrex
    vx
    @9
    wrex
    wa
    vx
    vy
    vz
    @5
    @9
    @7
    @8
    @3
    cK
    @4
    @6
    @9
    eqid
    @4
    eqid
    @7
    eqid
    @3
    eqid
    @6
    eqid
    @8
    eqid
    @5
    eqid
    ishlat1
    simplbi
end

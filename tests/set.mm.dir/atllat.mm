include "cal.mm"
include "wcel.mm"
include "clat.mm"
include "cbs.mm"
include "cfv.mm"
include "cglb.mm"
include "cdm.mm"
include "cv.mm"
include "cp0.mm"
include "wne.mm"
include "cple.mm"
include "wbr.mm"
include "catm.mm"
include "wrex.mm"
include "wi.mm"
include "wral.mm"
include "eqid.mm"
include "isatl.mm"
include "simp1bi.mm"

theorem atllat
  let cK: class K
  let vp: setvar p
  let vx: setvar x


  assert |- ( K e. AtLat -> K e. Lat )

  proof
    cK
    cal
    wcel
    cK
    clat
    wcel
    cK
    cbs
    cfv
    #
    cK
    cglb
    cfv
    #
    cdm
    wcel
    vx
    cv
    #
    cK
    cp0
    cfv
    #
    wne
    vp
    cv
    @2
    cK
    cple
    cfv
    #
    wbr
    vp
    cK
    catm
    cfv
    #
    wrex
    wi
    vx
    @0
    wral
    vx
    vp
    @5
    @0
    @1
    cK
    @4
    @3
    @0
    eqid
    @1
    eqid
    @4
    eqid
    @3
    eqid
    @5
    eqid
    isatl
    simp1bi
end

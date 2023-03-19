include "clc.mm"
include "wcel.mm"
include "cal.mm"
include "cv.mm"
include "cple.mm"
include "cfv.mm"
include "wbr.mm"
include "wn.mm"
include "cjn.mm"
include "co.mm"
include "wa.mm"
include "wi.mm"
include "cbs.mm"
include "wral.mm"
include "catm.mm"
include "eqid.mm"
include "iscvlat.mm"
include "simplbi.mm"

theorem cvlatl
  let cK: class K
  let vp: setvar p
  let vq: setvar q
  let vx: setvar x


  assert |- ( K e. CvLat -> K e. AtLat )

  proof
    cK
    clc
    wcel
    cK
    cal
    wcel
    vp
    cv
    #
    vx
    cv
    #
    cK
    cple
    cfv
    #
    wbr
    wn
    @0
    @1
    vq
    cv
    #
    cK
    cjn
    cfv
    #
    co
    @2
    wbr
    wa
    @3
    @1
    @0
    @4
    co
    @2
    wbr
    wi
    vx
    cK
    cbs
    cfv
    #
    wral
    vq
    cK
    catm
    cfv
    #
    wral
    vp
    @6
    wral
    vx
    @6
    @5
    @4
    cK
    @2
    vq
    vp
    @5
    eqid
    @2
    eqid
    @4
    eqid
    @6
    eqid
    iscvlat
    simplbi
end

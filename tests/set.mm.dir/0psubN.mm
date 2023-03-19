include "wcel.mm"
include "c0.mm"
include "catm.mm"
include "cfv.mm"
include "wss.mm"
include "cv.mm"
include "cjn.mm"
include "co.mm"
include "cple.mm"
include "wbr.mm"
include "wi.mm"
include "wral.mm"
include "wa.mm"
include "0ss.mm"
include "ral0.mm"
include "pm3.2i.mm"
include "eqid.mm"
include "ispsubsp.mm"
include "mpbiri.mm"

theorem 0psubN
  let cS: class S
  let cK: class K
  let cV: class V
  let vp: setvar p
  let vq: setvar q
  let vr: setvar r
  assume 0psub.s: |- S = ( PSubSp ` K )


  assert |- ( K e. V -> (/) e. S )

  proof
    cK
    cV
    wcel
    c0
    cS
    wcel
    c0
    cK
    catm
    cfv
    #
    wss
    #
    vr
    cv
    #
    vp
    cv
    vq
    cv
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
    @2
    c0
    wcel
    wi
    vr
    @0
    wral
    vq
    c0
    wral
    #
    vp
    c0
    wral
    #
    wa
    @1
    @6
    @0
    0ss
    @5
    vp
    ral0
    pm3.2i
    @0
    cV
    cS
    @3
    cK
    @4
    c0
    vr
    vq
    vp
    @4
    eqid
    @3
    eqid
    @0
    eqid
    0psub.s
    ispsubsp
    mpbiri
end

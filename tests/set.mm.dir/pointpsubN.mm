include "cal.mm"
include "wcel.mm"
include "cv.mm"
include "csn.mm"
include "wceq.mm"
include "catm.mm"
include "cfv.mm"
include "wrex.mm"
include "eqid.mm"
include "ispointN.mm"
include "wi.mm"
include "snatpsubN.mm"
include "ex.mm"
include "eleq1a.mm"
include "syl6.mm"
include "rexlimdv.mm"
include "sylbid.mm"
include "imp.mm"

theorem pointpsubN
  let cP: class P
  let cS: class S
  let cK: class K
  let cX: class X
  let vq: setvar q
  assume pointpsub.p: |- P = ( Points ` K )
  assume pointpsub.s: |- S = ( PSubSp ` K )


  assert |- ( ( K e. AtLat /\ X e. P ) -> X e. S )

  proof
    cK
    cal
    wcel
    #
    cX
    cP
    wcel
    #
    cX
    cS
    wcel
    #
    @0
    @1
    cX
    vq
    cv
    #
    csn
    #
    wceq
    #
    vq
    cK
    catm
    cfv
    #
    wrex
    @2
    @6
    cal
    cP
    cK
    cX
    vq
    @6
    eqid
    #
    pointpsub.p
    ispointN
    @0
    @5
    @2
    vq
    @6
    @0
    @3
    @6
    wcel
    #
    @4
    cS
    wcel
    #
    @5
    @2
    wi
    @0
    @8
    @9
    @6
    @3
    cS
    cK
    @7
    pointpsub.s
    snatpsubN
    ex
    @4
    cS
    cX
    eleq1a
    syl6
    rexlimdv
    sylbid
    imp
end

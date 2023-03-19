include "crg.mm"
include "wcel.mm"
include "wa.mm"
include "wbr.mm"
include "cv.mm"
include "cmulr.mm"
include "cfv.mm"
include "co.mm"
include "wceq.mm"
include "wrex.mm"
include "ring0cl.mm"
include "adantr.mm"
include "eqid.mm"
include "ringlz.mm"
include "oveq1.mm"
include "eqeq1d.mm"
include "rspcev.mm"
include "syl2anc.mm"
include "wb.mm"
include "dvdsr2.mm"
include "adantl.mm"
include "mpbird.mm"

theorem dvdsr01
  let cB: class B
  let c.pa: class .||
  let cR: class R
  let cX: class X
  let c.0: class .0.
  let vx: setvar x
  assume dvdsr0.b: |- B = ( Base ` R )
  assume dvdsr0.d: |- .|| = ( ||r ` R )
  assume dvdsr0.z: |- .0. = ( 0g ` R )


  assert |- ( ( R e. Ring /\ X e. B ) -> X .|| .0. )

  proof
    cR
    crg
    wcel
    #
    cX
    cB
    wcel
    #
    wa
    #
    cX
    c.0
    c.pa
    wbr
    #
    vx
    cv
    #
    cX
    cR
    cmulr
    cfv
    #
    co
    #
    c.0
    wceq
    #
    vx
    cB
    wrex
    #
    @2
    c.0
    cB
    wcel
    #
    c.0
    cX
    @5
    co
    #
    c.0
    wceq
    #
    @8
    @0
    @9
    @1
    cB
    cR
    c.0
    dvdsr0.b
    dvdsr0.z
    ring0cl
    adantr
    cB
    cR
    @5
    cX
    c.0
    dvdsr0.b
    @5
    eqid
    #
    dvdsr0.z
    ringlz
    @7
    @11
    vx
    c.0
    cB
    @4
    c.0
    wceq
    @6
    @10
    c.0
    @4
    c.0
    cX
    @5
    oveq1
    eqeq1d
    rspcev
    syl2anc
    @1
    @3
    @8
    wb
    @0
    vx
    cB
    c.pa
    cR
    @5
    cX
    c.0
    dvdsr0.b
    dvdsr0.d
    @12
    dvdsr2
    adantl
    mpbird
end

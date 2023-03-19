include "wbr.mm"
include "crg.mm"
include "wcel.mm"
include "cv.mm"
include "cmulr.mm"
include "cfv.mm"
include "co.mm"
include "wceq.mm"
include "wrex.mm"
include "wa.mm"
include "eqid.mm"
include "dvdsr.mm"
include "ringcl.mm"
include "3expa.mm"
include "an32s.mm"
include "eleq1.mm"
include "syl5ibcom.mm"
include "rexlimdva.mm"
include "impr.mm"
include "sylan2b.mm"

theorem dvdsrcl2
  let cB: class B
  let c.pa: class .||
  let cR: class R
  let cX: class X
  let cY: class Y
  let vx: setvar x
  let vy: setvar y
  let vr: setvar r
  let vz: setvar z
  let cZ: class Z
  let c.x: class .x.
  assume dvdsr.1: |- B = ( Base ` R )
  assume dvdsr.2: |- .|| = ( ||r ` R )


  assert |- ( ( R e. Ring /\ X .|| Y ) -> Y e. B )

  proof
    cX
    cY
    c.pa
    wbr
    cR
    crg
    wcel
    #
    cX
    cB
    wcel
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
    cY
    wceq
    #
    vx
    cB
    wrex
    #
    wa
    cY
    cB
    wcel
    #
    vx
    cB
    c.pa
    cR
    @3
    cX
    cY
    dvdsr.1
    dvdsr.2
    @3
    eqid
    #
    dvdsr
    @0
    @1
    @6
    @7
    @0
    @1
    wa
    #
    @5
    @7
    vx
    cB
    @9
    @2
    cB
    wcel
    #
    wa
    @4
    cB
    wcel
    #
    @5
    @7
    @0
    @10
    @1
    @11
    @0
    @10
    @1
    @11
    cB
    cR
    @3
    @2
    cX
    dvdsr.1
    @8
    ringcl
    3expa
    an32s
    @4
    cY
    cB
    eleq1
    syl5ibcom
    rexlimdva
    impr
    sylan2b
end

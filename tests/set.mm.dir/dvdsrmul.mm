include "wcel.mm"
include "wa.mm"
include "cv.mm"
include "co.mm"
include "wceq.mm"
include "wrex.mm"
include "wbr.mm"
include "simpl.mm"
include "simpr.mm"
include "eqid.mm"
include "oveq1.mm"
include "eqeq1d.mm"
include "rspcev.mm"
include "sylancl.mm"
include "dvdsr.mm"
include "sylanbrc.mm"

theorem dvdsrmul
  let cB: class B
  let c.pa: class .||
  let cR: class R
  let c.x: class .x.
  let cX: class X
  let cY: class Y
  let vx: setvar x
  let vy: setvar y
  let vr: setvar r
  let vz: setvar z
  let cZ: class Z
  assume dvdsr.1: |- B = ( Base ` R )
  assume dvdsr.2: |- .|| = ( ||r ` R )
  assume dvdsr.3: |- .x. = ( .r ` R )


  assert |- ( ( X e. B /\ Y e. B ) -> X .|| ( Y .x. X ) )

  proof
    cX
    cB
    wcel
    #
    cY
    cB
    wcel
    #
    wa
    #
    @0
    vz
    cv
    #
    cX
    c.x
    co
    #
    cY
    cX
    c.x
    co
    #
    wceq
    #
    vz
    cB
    wrex
    #
    cX
    @5
    c.pa
    wbr
    @0
    @1
    simpl
    @2
    @1
    @5
    @5
    wceq
    #
    @7
    @0
    @1
    simpr
    @5
    eqid
    @6
    @8
    vz
    cY
    cB
    @3
    cY
    wceq
    @4
    @5
    @5
    @3
    cY
    cX
    c.x
    oveq1
    eqeq1d
    rspcev
    sylancl
    vz
    cB
    c.pa
    cR
    c.x
    cX
    @5
    dvdsr.1
    dvdsr.2
    dvdsr.3
    dvdsr
    sylanbrc
end

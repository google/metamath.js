include "cmulr.mm"
include "cfv.mm"
include "ctpos.mm"
include "cvv.mm"
include "wcel.mm"
include "wceq.mm"
include "cnx.mm"
include "cop.mm"
include "csts.mm"
include "co.mm"
include "fvex.mm"
include "eqeltri.mm"
include "tposex.mm"
include "mulrid.mm"
include "setsid.mm"
include "mpan2.mm"
include "opprval.mm"
include "fveq2i.mm"
include "syl6reqr.mm"
include "wn.mm"
include "c0.mm"
include "tpos0.mm"
include "str0.mm"
include "eqtr2i.mm"
include "coppr.mm"
include "fvprc.mm"
include "syl5eq.mm"
include "fveq2d.mm"
include "tposeqd.mm"
include "3eqtr4a.mm"
include "pm2.61i.mm"
include "eqtri.mm"

theorem opprmulfval
  let cB: class B
  let cR: class R
  let c.xb: class .xb
  let c.x: class .x.
  let cO: class O
  let vx: setvar x
  let cX: class X
  let cY: class Y
  assume opprval.1: |- B = ( Base ` R )
  assume opprval.2: |- .x. = ( .r ` R )
  assume opprval.3: |- O = ( oppR ` R )
  assume opprmulfval.4: |- .xb = ( .r ` O )


  assert |- .xb = tpos .x.

  proof
    c.xb
    cO
    cmulr
    cfv
    #
    c.x
    ctpos
    #
    opprmulfval.4
    cR
    cvv
    wcel
    #
    @0
    @1
    wceq
    @2
    @1
    cR
    cnx
    cmulr
    cfv
    #
    @1
    cop
    csts
    co
    #
    cmulr
    cfv
    #
    @0
    @2
    @1
    cvv
    wcel
    @1
    @5
    wceq
    c.x
    c.x
    cR
    cmulr
    cfv
    #
    cvv
    opprval.2
    cR
    cmulr
    fvex
    eqeltri
    tposex
    cvv
    @1
    cmulr
    cvv
    cR
    mulrid
    setsid
    mpan2
    cO
    @4
    cmulr
    cB
    cR
    c.x
    cO
    opprval.1
    opprval.2
    opprval.3
    opprval
    fveq2i
    syl6reqr
    @2
    wn
    #
    c0
    cmulr
    cfv
    #
    c0
    ctpos
    #
    @0
    @1
    @9
    c0
    @8
    tpos0
    cmulr
    @3
    mulrid
    str0
    eqtr2i
    @7
    cO
    c0
    cmulr
    @7
    cO
    cR
    coppr
    cfv
    c0
    opprval.3
    cR
    coppr
    fvprc
    syl5eq
    fveq2d
    @7
    c.x
    c0
    @7
    c.x
    @6
    c0
    opprval.2
    cR
    cmulr
    fvprc
    syl5eq
    tposeqd
    3eqtr4a
    pm2.61i
    eqtri
end

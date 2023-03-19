include "coppr.mm"
include "cfv.mm"
include "cnx.mm"
include "cmulr.mm"
include "ctpos.mm"
include "cop.mm"
include "csts.mm"
include "co.mm"
include "cvv.mm"
include "wcel.mm"
include "wceq.mm"
include "cv.mm"
include "id.mm"
include "fveq2.mm"
include "syl6eqr.mm"
include "tposeqd.mm"
include "opeq2d.mm"
include "oveq12d.mm"
include "df-oppr.mm"
include "ovex.mm"
include "fvmpt.mm"
include "wn.mm"
include "c0.mm"
include "fvprc.mm"
include "reldmsets.mm"
include "ovprc1.mm"
include "eqtr4d.mm"
include "pm2.61i.mm"
include "eqtri.mm"

theorem opprval
  let cB: class B
  let cR: class R
  let c.x: class .x.
  let cO: class O
  let vx: setvar x
  let cX: class X
  let cY: class Y
  assume opprval.1: |- B = ( Base ` R )
  assume opprval.2: |- .x. = ( .r ` R )
  assume opprval.3: |- O = ( oppR ` R )


  assert |- O = ( R sSet <. ( .r ` ndx ) , tpos .x. >. )

  proof
    cO
    cR
    coppr
    cfv
    #
    cR
    cnx
    cmulr
    cfv
    #
    c.x
    ctpos
    #
    cop
    #
    csts
    co
    #
    opprval.3
    cR
    cvv
    wcel
    #
    @0
    @4
    wceq
    vx
    cR
    vx
    cv
    #
    @1
    @6
    cmulr
    cfv
    #
    ctpos
    #
    cop
    #
    csts
    co
    @4
    cvv
    coppr
    @6
    cR
    wceq
    #
    @6
    cR
    @9
    @3
    csts
    @10
    id
    @10
    @8
    @2
    @1
    @10
    @7
    c.x
    @10
    @7
    cR
    cmulr
    cfv
    c.x
    @6
    cR
    cmulr
    fveq2
    opprval.2
    syl6eqr
    tposeqd
    opeq2d
    oveq12d
    vx
    df-oppr
    cR
    @3
    csts
    ovex
    fvmpt
    @5
    wn
    @0
    c0
    @4
    cR
    coppr
    fvprc
    cR
    @3
    csts
    reldmsets
    ovprc1
    eqtr4d
    pm2.61i
    eqtri
end

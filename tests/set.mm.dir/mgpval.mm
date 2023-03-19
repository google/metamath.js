include "cmgp.mm"
include "cfv.mm"
include "cnx.mm"
include "cplusg.mm"
include "cop.mm"
include "csts.mm"
include "co.mm"
include "cvv.mm"
include "wcel.mm"
include "wceq.mm"
include "cv.mm"
include "cmulr.mm"
include "id.mm"
include "fveq2.mm"
include "syl6eqr.mm"
include "opeq2d.mm"
include "oveq12d.mm"
include "df-mgp.mm"
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

theorem mgpval
  let cR: class R
  let c.x: class .x.
  let cM: class M
  let vr: setvar r
  assume mgpval.1: |- M = ( mulGrp ` R )
  assume mgpval.2: |- .x. = ( .r ` R )


  assert |- M = ( R sSet <. ( +g ` ndx ) , .x. >. )

  proof
    cM
    cR
    cmgp
    cfv
    #
    cR
    cnx
    cplusg
    cfv
    #
    c.x
    cop
    #
    csts
    co
    #
    mgpval.1
    cR
    cvv
    wcel
    #
    @0
    @3
    wceq
    vr
    cR
    vr
    cv
    #
    @1
    @5
    cmulr
    cfv
    #
    cop
    #
    csts
    co
    @3
    cvv
    cmgp
    @5
    cR
    wceq
    #
    @5
    cR
    @7
    @2
    csts
    @8
    id
    @8
    @6
    c.x
    @1
    @8
    @6
    cR
    cmulr
    cfv
    c.x
    @5
    cR
    cmulr
    fveq2
    mgpval.2
    syl6eqr
    opeq2d
    oveq12d
    vr
    df-mgp
    cR
    @2
    csts
    ovex
    fvmpt
    @4
    wn
    @0
    c0
    @3
    cR
    cmgp
    fvprc
    cR
    @2
    csts
    reldmsets
    ovprc1
    eqtr4d
    pm2.61i
    eqtri
end

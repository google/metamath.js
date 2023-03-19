include "cvv.mm"
include "wcel.mm"
include "cplusg.mm"
include "cfv.mm"
include "wceq.mm"
include "cnx.mm"
include "cop.mm"
include "csts.mm"
include "co.mm"
include "cmulr.mm"
include "fvex.mm"
include "eqeltri.mm"
include "plusgid.mm"
include "setsid.mm"
include "mpan2.mm"
include "mgpval.mm"
include "fveq2i.mm"
include "syl6eqr.mm"
include "wn.mm"
include "c0.mm"
include "str0.mm"
include "fvprc.mm"
include "syl5eq.mm"
include "cmgp.mm"
include "fveq2d.mm"
include "3eqtr4a.mm"
include "pm2.61i.mm"

theorem mgpplusg
  let cR: class R
  let c.x: class .x.
  let cM: class M
  let vr: setvar r
  assume mgpval.1: |- M = ( mulGrp ` R )
  assume mgpval.2: |- .x. = ( .r ` R )


  assert |- .x. = ( +g ` M )

  proof
    cR
    cvv
    wcel
    #
    c.x
    cM
    cplusg
    cfv
    #
    wceq
    @0
    c.x
    cR
    cnx
    cplusg
    cfv
    #
    c.x
    cop
    csts
    co
    #
    cplusg
    cfv
    #
    @1
    @0
    c.x
    cvv
    wcel
    c.x
    @4
    wceq
    c.x
    cR
    cmulr
    cfv
    #
    cvv
    mgpval.2
    cR
    cmulr
    fvex
    eqeltri
    cvv
    c.x
    cplusg
    cvv
    cR
    plusgid
    setsid
    mpan2
    cM
    @3
    cplusg
    cR
    c.x
    cM
    mgpval.1
    mgpval.2
    mgpval
    fveq2i
    syl6eqr
    @0
    wn
    #
    c0
    c0
    cplusg
    cfv
    c.x
    @1
    cplusg
    @2
    plusgid
    str0
    @6
    c.x
    @5
    c0
    mgpval.2
    cR
    cmulr
    fvprc
    syl5eq
    @6
    cM
    c0
    cplusg
    @6
    cM
    cR
    cmgp
    cfv
    c0
    mgpval.1
    cR
    cmgp
    fvprc
    syl5eq
    fveq2d
    3eqtr4a
    pm2.61i
end

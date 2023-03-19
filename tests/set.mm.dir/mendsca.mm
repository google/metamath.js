include "csca.mm"
include "cfv.mm"
include "cmend.mm"
include "cvv.mm"
include "wcel.mm"
include "wceq.mm"
include "cnx.mm"
include "cbs.mm"
include "clmhm.mm"
include "co.mm"
include "cop.mm"
include "cplusg.mm"
include "cv.mm"
include "cof.mm"
include "cmpt2.mm"
include "cmulr.mm"
include "ccom.mm"
include "ctp.mm"
include "cvsca.mm"
include "csn.mm"
include "cxp.mm"
include "cpr.mm"
include "cun.mm"
include "fvex.mm"
include "eqid.mm"
include "algsca.mm"
include "mp1i.mm"
include "mendval.mm"
include "fveq2d.mm"
include "eqtr4d.mm"
include "wn.mm"
include "c0.mm"
include "c5.mm"
include "df-sca.mm"
include "str0.mm"
include "fvprc.mm"
include "3eqtr4a.mm"
include "pm2.61i.mm"
include "fveq2i.mm"
include "3eqtr4i.mm"

theorem mendsca
  let cA: class A
  let cS: class S
  let cM: class M
  let vx: setvar x
  let vy: setvar y
  assume mendsca.a: |- A = ( MEndo ` M )
  assume mendsca.s: |- S = ( Scalar ` M )


  assert |- S = ( Scalar ` A )

  proof
    cM
    csca
    cfv
    #
    cM
    cmend
    cfv
    #
    csca
    cfv
    #
    cS
    cA
    csca
    cfv
    cM
    cvv
    wcel
    #
    @0
    @2
    wceq
    @3
    @0
    cnx
    cbs
    cfv
    cM
    cM
    clmhm
    co
    #
    cop
    cnx
    cplusg
    cfv
    vx
    vy
    @4
    @4
    vx
    cv
    #
    vy
    cv
    #
    cM
    cplusg
    cfv
    cof
    co
    cmpt2
    #
    cop
    cnx
    cmulr
    cfv
    vx
    vy
    @4
    @4
    @5
    @6
    ccom
    cmpt2
    #
    cop
    ctp
    cnx
    csca
    cfv
    @0
    cop
    cnx
    cvsca
    cfv
    vx
    vy
    @0
    cbs
    cfv
    @4
    cM
    cbs
    cfv
    @5
    csn
    cxp
    @6
    cM
    cvsca
    cfv
    cof
    co
    cmpt2
    #
    cop
    cpr
    cun
    #
    csca
    cfv
    #
    @2
    @0
    cvv
    wcel
    @0
    @11
    wceq
    @3
    cM
    csca
    fvex
    @10
    @4
    @7
    @0
    @9
    @8
    cvv
    @10
    eqid
    algsca
    mp1i
    @3
    @1
    @10
    csca
    vx
    vy
    @4
    @7
    @0
    @9
    @8
    cM
    cvv
    @4
    eqid
    @7
    eqid
    @8
    eqid
    @0
    eqid
    @9
    eqid
    mendval
    fveq2d
    eqtr4d
    @3
    wn
    #
    c0
    c0
    csca
    cfv
    @0
    @2
    csca
    c5
    df-sca
    str0
    cM
    csca
    fvprc
    @12
    @1
    c0
    csca
    cM
    cmend
    fvprc
    fveq2d
    3eqtr4a
    pm2.61i
    mendsca.s
    cA
    @1
    csca
    mendsca.a
    fveq2i
    3eqtr4i
end

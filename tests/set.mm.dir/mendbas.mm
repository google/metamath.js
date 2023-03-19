include "cvv.mm"
include "wcel.mm"
include "clmhm.mm"
include "co.mm"
include "cbs.mm"
include "cfv.mm"
include "wceq.mm"
include "cnx.mm"
include "cop.mm"
include "cplusg.mm"
include "cv.mm"
include "cof.mm"
include "cmpt2.mm"
include "cmulr.mm"
include "ccom.mm"
include "ctp.mm"
include "csca.mm"
include "cvsca.mm"
include "csn.mm"
include "cxp.mm"
include "cpr.mm"
include "cun.mm"
include "ovex.mm"
include "eqid.mm"
include "algbase.mm"
include "mp1i.mm"
include "cmend.mm"
include "mendval.mm"
include "syl5eq.mm"
include "fveq2d.mm"
include "eqtr4d.mm"
include "wn.mm"
include "c0.mm"
include "base0.mm"
include "reldmlmhm.mm"
include "ovprc1.mm"
include "fvprc.mm"
include "3eqtr4a.mm"
include "pm2.61i.mm"

theorem mendbas
  let cA: class A
  let cM: class M
  let vx: setvar x
  let vy: setvar y
  assume mendbas.a: |- A = ( MEndo ` M )


  assert |- ( M LMHom M ) = ( Base ` A )

  proof
    cM
    cvv
    wcel
    #
    cM
    cM
    clmhm
    co
    #
    cA
    cbs
    cfv
    #
    wceq
    @0
    @1
    cnx
    cbs
    cfv
    @1
    cop
    cnx
    cplusg
    cfv
    vx
    vy
    @1
    @1
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
    @1
    @1
    @3
    @4
    ccom
    cmpt2
    #
    cop
    ctp
    cnx
    csca
    cfv
    cM
    csca
    cfv
    #
    cop
    cnx
    cvsca
    cfv
    vx
    vy
    @7
    cbs
    cfv
    @1
    cM
    cbs
    cfv
    @3
    csn
    cxp
    @4
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
    cbs
    cfv
    #
    @2
    @1
    cvv
    wcel
    @1
    @10
    wceq
    @0
    cM
    cM
    clmhm
    ovex
    @9
    @1
    @5
    @7
    @8
    @6
    cvv
    @9
    eqid
    algbase
    mp1i
    @0
    cA
    @9
    cbs
    @0
    cA
    cM
    cmend
    cfv
    #
    @9
    mendbas.a
    vx
    vy
    @1
    @5
    @7
    @8
    @6
    cM
    cvv
    @1
    eqid
    @5
    eqid
    @6
    eqid
    @7
    eqid
    @8
    eqid
    mendval
    syl5eq
    fveq2d
    eqtr4d
    @0
    wn
    #
    c0
    c0
    cbs
    cfv
    @1
    @2
    base0
    cM
    cM
    clmhm
    reldmlmhm
    ovprc1
    @12
    cA
    c0
    cbs
    @12
    cA
    @11
    c0
    mendbas.a
    cM
    cmend
    fvprc
    syl5eq
    fveq2d
    3eqtr4a
    pm2.61i
end

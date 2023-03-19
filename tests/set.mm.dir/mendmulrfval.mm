include "cvv.mm"
include "wcel.mm"
include "cmulr.mm"
include "cfv.mm"
include "cv.mm"
include "ccom.mm"
include "cmpt2.mm"
include "wceq.mm"
include "cnx.mm"
include "cbs.mm"
include "cop.mm"
include "cplusg.mm"
include "cof.mm"
include "co.mm"
include "ctp.mm"
include "csca.mm"
include "cvsca.mm"
include "csn.mm"
include "cxp.mm"
include "cpr.mm"
include "cun.mm"
include "cmend.mm"
include "clmhm.mm"
include "mendbas.mm"
include "eqtr4i.mm"
include "eqid.mm"
include "mendval.mm"
include "syl5eq.mm"
include "fveq2d.mm"
include "fvex.mm"
include "eqeltri.mm"
include "mpt2ex.mm"
include "algmulr.mm"
include "mp1i.mm"
include "eqtr4d.mm"
include "wn.mm"
include "c0.mm"
include "fvprc.mm"
include "c3.mm"
include "df-mulr.mm"
include "str0.mm"
include "syl6eqr.mm"
include "base0.mm"
include "mpt2eq12.mm"
include "anidms.mm"
include "syl.mm"
include "mpt20.mm"
include "syl6eq.mm"
include "pm2.61i.mm"

theorem mendmulrfval
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let cM: class M
  let cX: class X
  let cY: class Y
  assume mendmulrfval.a: |- A = ( MEndo ` M )
  assume mendmulrfval.b: |- B = ( Base ` A )

  disjoint x y
  disjoint B x
  disjoint B y
  disjoint M x
  disjoint M y
  disjoint X x
  disjoint X y
  disjoint Y x
  disjoint Y y
  assert |- ( .r ` A ) = ( x e. B , y e. B |-> ( x o. y ) )

  proof
    cM
    cvv
    wcel
    #
    cA
    cmulr
    cfv
    #
    vx
    vy
    cB
    cB
    vx
    cv
    #
    vy
    cv
    #
    ccom
    #
    cmpt2
    #
    wceq
    @0
    @1
    cnx
    cbs
    cfv
    cB
    cop
    cnx
    cplusg
    cfv
    vx
    vy
    cB
    cB
    @2
    @3
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
    @5
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
    cB
    cM
    cbs
    cfv
    @2
    csn
    cxp
    @3
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
    cmulr
    cfv
    #
    @5
    @0
    cA
    @9
    cmulr
    @0
    cA
    cM
    cmend
    cfv
    #
    @9
    mendmulrfval.a
    vx
    vy
    cB
    @6
    @7
    @8
    @5
    cM
    cvv
    cB
    cA
    cbs
    cfv
    #
    cM
    cM
    clmhm
    co
    mendmulrfval.b
    cA
    cM
    mendmulrfval.a
    mendbas
    eqtr4i
    @6
    eqid
    @5
    eqid
    @7
    eqid
    @8
    eqid
    mendval
    syl5eq
    fveq2d
    @5
    cvv
    wcel
    @5
    @10
    wceq
    @0
    vx
    vy
    cB
    cB
    @4
    cB
    @12
    cvv
    mendmulrfval.b
    cA
    cbs
    fvex
    eqeltri
    #
    @13
    mpt2ex
    @9
    cB
    @6
    @7
    @8
    @5
    cvv
    @9
    eqid
    algmulr
    mp1i
    eqtr4d
    @0
    wn
    #
    @1
    c0
    @5
    @14
    @1
    c0
    cmulr
    cfv
    c0
    @14
    cA
    c0
    cmulr
    @14
    cA
    @11
    c0
    mendmulrfval.a
    cM
    cmend
    fvprc
    syl5eq
    #
    fveq2d
    cmulr
    c3
    df-mulr
    str0
    syl6eqr
    @14
    @5
    vx
    vy
    c0
    c0
    @4
    cmpt2
    #
    c0
    @14
    cB
    c0
    wceq
    #
    @5
    @16
    wceq
    #
    @14
    cB
    c0
    cbs
    cfv
    #
    c0
    @14
    cB
    @12
    @19
    mendmulrfval.b
    @14
    cA
    c0
    cbs
    @15
    fveq2d
    syl5eq
    base0
    syl6eqr
    @17
    @18
    vx
    vy
    cB
    cB
    c0
    c0
    @4
    mpt2eq12
    anidms
    syl
    vx
    vy
    c0
    @4
    mpt20
    syl6eq
    eqtr4d
    pm2.61i
end

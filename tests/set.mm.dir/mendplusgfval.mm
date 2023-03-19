include "cvv.mm"
include "wcel.mm"
include "cplusg.mm"
include "cfv.mm"
include "cv.mm"
include "cof.mm"
include "co.mm"
include "cmpt2.mm"
include "wceq.mm"
include "cnx.mm"
include "cbs.mm"
include "cop.mm"
include "cmulr.mm"
include "ccom.mm"
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
include "wa.mm"
include "ofeq.mm"
include "ax-mp.mm"
include "oveqi.mm"
include "a1i.mm"
include "mpt2eq3ia.mm"
include "eqid.mm"
include "mendval.mm"
include "syl5eq.mm"
include "fveq2d.mm"
include "fvex.mm"
include "eqeltri.mm"
include "mpt2ex.mm"
include "algaddg.mm"
include "mp1i.mm"
include "eqtr4d.mm"
include "wn.mm"
include "c0.mm"
include "fvprc.mm"
include "c2.mm"
include "df-plusg.mm"
include "str0.mm"
include "syl6eqr.mm"
include "base0.mm"
include "3eqtr4g.mm"
include "mpt2eq12.mm"
include "anidms.mm"
include "syl.mm"
include "mpt20.mm"
include "syl6eq.mm"
include "pm2.61i.mm"

theorem mendplusgfval
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let c.pl: class .+
  let cM: class M
  let cX: class X
  let cY: class Y
  assume mendplusgfval.a: |- A = ( MEndo ` M )
  assume mendplusgfval.b: |- B = ( Base ` A )
  assume mendplusgfval.p: |- .+ = ( +g ` M )

  disjoint x y
  disjoint B x
  disjoint B y
  disjoint M x
  disjoint M y
  disjoint .+ x
  disjoint .+ y
  disjoint X x
  disjoint X y
  disjoint Y x
  disjoint Y y
  assert |- ( +g ` A ) = ( x e. B , y e. B |-> ( x oF .+ y ) )

  proof
    cM
    cvv
    wcel
    #
    cA
    cplusg
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
    c.pl
    cof
    #
    co
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
    @6
    cop
    cnx
    cmulr
    cfv
    vx
    vy
    cB
    cB
    @2
    @3
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
    @8
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
    cplusg
    cfv
    #
    @6
    @0
    cA
    @10
    cplusg
    @0
    cA
    cM
    cmend
    cfv
    #
    @10
    mendplusgfval.a
    vx
    vy
    cB
    @6
    @8
    @9
    @7
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
    mendplusgfval.b
    cA
    cM
    mendplusgfval.a
    mendbas
    eqtr4i
    vx
    vy
    cB
    cB
    @5
    @2
    @3
    cM
    cplusg
    cfv
    #
    cof
    #
    co
    #
    @5
    @16
    wceq
    @2
    cB
    wcel
    @3
    cB
    wcel
    wa
    @4
    @15
    @2
    @3
    c.pl
    @14
    wceq
    @4
    @15
    wceq
    mendplusgfval.p
    c.pl
    @14
    ofeq
    ax-mp
    oveqi
    a1i
    mpt2eq3ia
    @7
    eqid
    @8
    eqid
    @9
    eqid
    mendval
    syl5eq
    fveq2d
    @6
    cvv
    wcel
    @6
    @11
    wceq
    @0
    vx
    vy
    cB
    cB
    @5
    cB
    @13
    cvv
    mendplusgfval.b
    cA
    cbs
    fvex
    eqeltri
    #
    @17
    mpt2ex
    @10
    cB
    @6
    @8
    @9
    @7
    cvv
    @10
    eqid
    algaddg
    mp1i
    eqtr4d
    @0
    wn
    #
    @1
    c0
    @6
    @18
    @1
    c0
    cplusg
    cfv
    c0
    @18
    cA
    c0
    cplusg
    @18
    cA
    @12
    c0
    mendplusgfval.a
    cM
    cmend
    fvprc
    syl5eq
    #
    fveq2d
    cplusg
    c2
    df-plusg
    str0
    syl6eqr
    @18
    @6
    vx
    vy
    c0
    c0
    @5
    cmpt2
    #
    c0
    @18
    cB
    c0
    wceq
    #
    @6
    @20
    wceq
    #
    @18
    @13
    c0
    cbs
    cfv
    cB
    c0
    @18
    cA
    c0
    cbs
    @19
    fveq2d
    mendplusgfval.b
    base0
    3eqtr4g
    @21
    @22
    vx
    vy
    cB
    cB
    c0
    c0
    @5
    mpt2eq12
    anidms
    syl
    vx
    vy
    c0
    @5
    mpt20
    syl6eq
    eqtr4d
    pm2.61i
end

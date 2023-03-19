include "cvsca.mm"
include "cfv.mm"
include "cmend.mm"
include "cv.mm"
include "csn.mm"
include "cxp.mm"
include "cof.mm"
include "co.mm"
include "cmpt2.mm"
include "fveq2i.mm"
include "cvv.mm"
include "wcel.mm"
include "wceq.mm"
include "cnx.mm"
include "cbs.mm"
include "cop.mm"
include "cplusg.mm"
include "cmulr.mm"
include "ccom.mm"
include "ctp.mm"
include "csca.mm"
include "cpr.mm"
include "cun.mm"
include "clmhm.mm"
include "mendbas.mm"
include "eqtr4i.mm"
include "eqid.mm"
include "xpeq1i.mm"
include "ofeq.mm"
include "ax-mp.mm"
include "oveq123i.mm"
include "mpt2eq123i.mm"
include "mendval.mm"
include "fveq2d.mm"
include "fvex.mm"
include "eqeltri.mm"
include "mpt2ex.mm"
include "algvsca.mm"
include "mp1i.mm"
include "eqtr4d.mm"
include "wn.mm"
include "c0.mm"
include "fvprc.mm"
include "c6.mm"
include "df-vsca.mm"
include "str0.mm"
include "syl6eqr.mm"
include "syl5eq.mm"
include "base0.mm"
include "3eqtr4g.mm"
include "mpt2eq12.mm"
include "sylancl.mm"
include "mpt20.mm"
include "syl6eq.mm"
include "pm2.61i.mm"
include "eqtri.mm"

theorem mendvscafval
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let cS: class S
  let c.x: class .x.
  let cE: class E
  let cK: class K
  let cM: class M
  assume mendvscafval.a: |- A = ( MEndo ` M )
  assume mendvscafval.v: |- .x. = ( .s ` M )
  assume mendvscafval.b: |- B = ( Base ` A )
  assume mendvscafval.s: |- S = ( Scalar ` M )
  assume mendvscafval.k: |- K = ( Base ` S )
  assume mendvscafval.e: |- E = ( Base ` M )

  disjoint x y
  disjoint B x
  disjoint B y
  disjoint K x
  disjoint K y
  disjoint M x
  disjoint M y
  assert |- ( .s ` A ) = ( x e. K , y e. B |-> ( ( E X. { x } ) oF .x. y ) )

  proof
    cA
    cvsca
    cfv
    cM
    cmend
    cfv
    #
    cvsca
    cfv
    #
    vx
    vy
    cK
    cB
    cE
    vx
    cv
    #
    csn
    #
    cxp
    #
    vy
    cv
    #
    c.x
    cof
    #
    co
    #
    cmpt2
    #
    cA
    @0
    cvsca
    mendvscafval.a
    fveq2i
    cM
    cvv
    wcel
    #
    @1
    @8
    wceq
    @9
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
    @5
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
    cB
    cB
    @2
    @5
    ccom
    cmpt2
    #
    cop
    ctp
    cnx
    csca
    cfv
    cS
    cop
    cnx
    cvsca
    cfv
    @8
    cop
    cpr
    cun
    #
    cvsca
    cfv
    #
    @8
    @9
    @0
    @12
    cvsca
    vx
    vy
    cB
    @10
    cS
    @8
    @11
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
    mendvscafval.b
    cA
    cM
    mendvscafval.a
    mendbas
    eqtr4i
    @10
    eqid
    @11
    eqid
    mendvscafval.s
    vx
    vy
    cK
    cB
    @7
    cS
    cbs
    cfv
    #
    cB
    cM
    cbs
    cfv
    #
    @3
    cxp
    #
    @5
    cM
    cvsca
    cfv
    #
    cof
    #
    co
    mendvscafval.k
    cB
    eqid
    #
    @4
    @5
    @17
    @5
    @6
    @19
    cE
    @16
    @3
    mendvscafval.e
    xpeq1i
    @5
    eqid
    c.x
    @18
    wceq
    @6
    @19
    wceq
    mendvscafval.v
    c.x
    @18
    ofeq
    ax-mp
    oveq123i
    mpt2eq123i
    mendval
    fveq2d
    @8
    cvv
    wcel
    @8
    @13
    wceq
    @9
    vx
    vy
    cK
    cB
    @7
    cK
    @15
    cvv
    mendvscafval.k
    cS
    cbs
    fvex
    eqeltri
    cB
    @14
    cvv
    mendvscafval.b
    cA
    cbs
    fvex
    eqeltri
    mpt2ex
    @12
    cB
    @10
    cS
    @8
    @11
    cvv
    @12
    eqid
    algvsca
    mp1i
    eqtr4d
    @9
    wn
    #
    @1
    c0
    @8
    @21
    @1
    c0
    cvsca
    cfv
    c0
    @21
    @0
    c0
    cvsca
    cM
    cmend
    fvprc
    fveq2d
    cvsca
    c6
    df-vsca
    str0
    syl6eqr
    @21
    @8
    vx
    vy
    c0
    cB
    @7
    cmpt2
    #
    c0
    @21
    cK
    c0
    wceq
    cB
    cB
    wceq
    @8
    @22
    wceq
    @21
    @15
    c0
    cbs
    cfv
    cK
    c0
    @21
    cS
    c0
    cbs
    @21
    cS
    cM
    csca
    cfv
    c0
    mendvscafval.s
    cM
    csca
    fvprc
    syl5eq
    fveq2d
    mendvscafval.k
    base0
    3eqtr4g
    @20
    vx
    vy
    cK
    cB
    c0
    cB
    @7
    mpt2eq12
    sylancl
    vx
    vy
    cB
    @7
    mpt20
    syl6eq
    eqtr4d
    pm2.61i
    eqtri
end

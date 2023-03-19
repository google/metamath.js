include "crg.mm"
include "wcel.mm"
include "cz.mm"
include "w3a.mm"
include "wa.mm"
include "coppr.mm"
include "cfv.mm"
include "cmg.mm"
include "co.mm"
include "cmulr.mm"
include "wceq.mm"
include "eqid.mm"
include "opprring.mm"
include "adantr.mm"
include "simpr1.mm"
include "simpr3.mm"
include "simpr2.mm"
include "opprbas.mm"
include "mulgass2.mm"
include "syl13anc.mm"
include "opprmul.mm"
include "oveq2i.mm"
include "3eqtr3g.mm"
include "cvv.mm"
include "cbs.mm"
include "a1i.mm"
include "wss.mm"
include "ssv.mm"
include "cv.mm"
include "cplusg.mm"
include "ovexd.mm"
include "oppradd.mm"
include "oveqi.mm"
include "mulgpropd.mm"
include "oveqd.mm"
include "oveq2d.mm"
include "3eqtr4d.mm"

theorem mulgass3
  let cB: class B
  let cR: class R
  let c.x: class .x.
  let c.xp: class .X.
  let cN: class N
  let cX: class X
  let cY: class Y
  let vx: setvar x
  let vy: setvar y
  assume mulgass3.b: |- B = ( Base ` R )
  assume mulgass3.m: |- .x. = ( .g ` R )
  assume mulgass3.t: |- .X. = ( .r ` R )


  assert |- ( ( R e. Ring /\ ( N e. ZZ /\ X e. B /\ Y e. B ) ) -> ( X .X. ( N .x. Y ) ) = ( N .x. ( X .X. Y ) ) )

  proof
    cR
    crg
    wcel
    #
    cN
    cz
    wcel
    #
    cX
    cB
    wcel
    #
    cY
    cB
    wcel
    #
    w3a
    #
    wa
    #
    cX
    cN
    cY
    cR
    coppr
    cfv
    #
    cmg
    cfv
    #
    co
    #
    c.xp
    co
    #
    cN
    cX
    cY
    c.xp
    co
    #
    @7
    co
    #
    cX
    cN
    cY
    c.x
    co
    #
    c.xp
    co
    cN
    @10
    c.x
    co
    @5
    @8
    cX
    @6
    cmulr
    cfv
    #
    co
    #
    cN
    cY
    cX
    @13
    co
    #
    @7
    co
    #
    @9
    @11
    @5
    @6
    crg
    wcel
    #
    @1
    @3
    @2
    @14
    @16
    wceq
    @0
    @17
    @4
    cR
    @6
    @6
    eqid
    #
    opprring
    adantr
    @0
    @1
    @2
    @3
    simpr1
    @0
    @1
    @2
    @3
    simpr3
    @0
    @1
    @2
    @3
    simpr2
    cB
    @6
    @7
    @13
    cN
    cY
    cX
    cB
    cR
    @6
    @18
    mulgass3.b
    opprbas
    #
    @7
    eqid
    #
    @13
    eqid
    #
    mulgass2
    syl13anc
    cB
    cR
    @13
    c.xp
    @6
    @8
    cX
    mulgass3.b
    mulgass3.t
    @18
    @21
    opprmul
    @15
    @10
    cN
    @7
    cB
    cR
    @13
    c.xp
    @6
    cY
    cX
    mulgass3.b
    mulgass3.t
    @18
    @21
    opprmul
    oveq2i
    3eqtr3g
    @5
    @12
    @8
    cX
    c.xp
    @5
    c.x
    @7
    cN
    cY
    @5
    vx
    vy
    cB
    c.x
    @7
    cR
    @6
    cvv
    mulgass3.m
    @20
    cB
    cR
    cbs
    cfv
    wceq
    @5
    mulgass3.b
    a1i
    cB
    @6
    cbs
    cfv
    wceq
    @5
    @19
    a1i
    cB
    cvv
    wss
    @5
    cB
    ssv
    a1i
    @5
    vx
    cv
    #
    cvv
    wcel
    vy
    cv
    #
    cvv
    wcel
    wa
    wa
    #
    @22
    @23
    cR
    cplusg
    cfv
    #
    ovexd
    @22
    @23
    @25
    co
    @22
    @23
    @6
    cplusg
    cfv
    #
    co
    wceq
    @24
    @25
    @26
    @22
    @23
    @25
    cR
    @6
    @18
    @25
    eqid
    oppradd
    oveqi
    a1i
    mulgpropd
    #
    oveqd
    oveq2d
    @5
    c.x
    @7
    cN
    @10
    @27
    oveqd
    3eqtr4d
end

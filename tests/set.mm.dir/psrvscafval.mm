include "cvv.mm"
include "wcel.mm"
include "wa.mm"
include "cv.mm"
include "csn.mm"
include "cxp.mm"
include "cof.mm"
include "co.mm"
include "cmpt2.mm"
include "wceq.mm"
include "cvsca.mm"
include "cfv.mm"
include "cnx.mm"
include "cbs.mm"
include "cop.mm"
include "cplusg.mm"
include "cmulr.mm"
include "ctp.mm"
include "csca.mm"
include "cts.mm"
include "ctopn.mm"
include "cpt.mm"
include "cun.mm"
include "eqid.mm"
include "simpl.mm"
include "psrbas.mm"
include "psrplusg.mm"
include "psrmulr.mm"
include "eqidd.mm"
include "simpr.mm"
include "psrval.mm"
include "fveq2d.mm"
include "fvex.mm"
include "eqeltri.mm"
include "mpt2ex.mm"
include "c1.mm"
include "c9.mm"
include "psrvalstr.mm"
include "vscaid.mm"
include "snsstp2.mm"
include "ssun2.mm"
include "sstri.mm"
include "strfv.mm"
include "ax-mp.mm"
include "3eqtr4g.mm"
include "wn.mm"
include "wfn.mm"
include "c0.mm"
include "fn0.mm"
include "mpbir.mm"
include "cmps.mm"
include "reldmpsr.mm"
include "ovprc.mm"
include "syl5eq.mm"
include "c6.mm"
include "df-vsca.mm"
include "str0.mm"
include "elbasov.mm"
include "con3i.mm"
include "eq0rdv.mm"
include "xpeq2d.mm"
include "xp0.mm"
include "syl6eq.mm"
include "fneq12d.mm"
include "mpbiri.mm"
include "fnov.mm"
include "sylib.mm"
include "wi.mm"
include "pm2.21d.mm"
include "a1d.mm"
include "3imp.mm"
include "mpt2eq3dva.mm"
include "eqtr4d.mm"
include "pm2.61i.mm"

theorem psrvscafval
  let vx: setvar x
  let cB: class B
  let cD: class D
  let cR: class R
  let cS: class S
  let c.xb: class .xb
  let c.x: class .x.
  let vf: setvar f
  let vh: setvar h
  let cI: class I
  let cK: class K
  let vg: setvar g
  let vk: setvar k
  let cF: class F
  let vy: setvar y
  let cX: class X
  assume psrvsca.s: |- S = ( I mPwSer R )
  assume psrvsca.n: |- .xb = ( .s ` S )
  assume psrvsca.k: |- K = ( Base ` R )
  assume psrvsca.b: |- B = ( Base ` S )
  assume psrvsca.m: |- .x. = ( .r ` R )
  assume psrvsca.d: |- D = { h e. ( NN0 ^m I ) | ( `' h " NN ) e. Fin }

  disjoint f x
  disjoint B f
  disjoint B x
  disjoint f h
  disjoint I f
  disjoint h x
  disjoint I h
  disjoint I x
  disjoint K f
  disjoint K x
  disjoint D f
  disjoint D x
  disjoint R f
  disjoint R x
  disjoint .x. f
  disjoint .x. x
  disjoint .xb f
  disjoint .xb x
  disjoint f g
  disjoint f k
  disjoint g k
  disjoint g x
  disjoint B g
  disjoint k x
  disjoint B k
  disjoint F f
  disjoint F x
  disjoint f y
  disjoint g h
  disjoint g y
  disjoint I g
  disjoint h k
  disjoint h y
  disjoint k y
  disjoint I k
  disjoint x y
  disjoint I y
  disjoint X f
  disjoint X x
  disjoint D g
  disjoint D k
  disjoint D y
  disjoint R g
  disjoint R k
  disjoint .x. g
  disjoint .x. k
  assert |- .xb = ( x e. K , f e. B |-> ( ( D X. { x } ) oF .x. f ) )

  proof
    cI
    cvv
    wcel
    #
    cR
    cvv
    wcel
    #
    wa
    #
    c.xb
    vx
    vf
    cK
    cB
    cD
    vx
    cv
    #
    csn
    cxp
    vf
    cv
    #
    c.x
    cof
    co
    #
    cmpt2
    #
    wceq
    @2
    cS
    cvsca
    cfv
    #
    cnx
    cbs
    cfv
    cB
    cop
    cnx
    cplusg
    cfv
    cS
    cplusg
    cfv
    #
    cop
    cnx
    cmulr
    cfv
    cS
    cmulr
    cfv
    #
    cop
    ctp
    #
    cnx
    csca
    cfv
    cR
    cop
    #
    cnx
    cvsca
    cfv
    @6
    cop
    #
    cnx
    cts
    cfv
    cD
    cR
    ctopn
    cfv
    #
    csn
    cxp
    cpt
    cfv
    #
    cop
    #
    ctp
    #
    cun
    #
    cvsca
    cfv
    #
    c.xb
    @6
    @2
    cS
    @17
    cvsca
    @2
    vx
    vy
    cB
    cD
    cR
    cplusg
    cfv
    #
    @8
    cR
    cS
    @6
    c.x
    @9
    vf
    vg
    vh
    vk
    cI
    @14
    cK
    @13
    cvv
    cvv
    psrvsca.s
    psrvsca.k
    @19
    eqid
    #
    psrvsca.m
    @13
    eqid
    psrvsca.d
    @2
    cB
    cD
    cR
    cS
    vh
    cI
    cK
    cvv
    psrvsca.s
    psrvsca.k
    psrvsca.d
    psrvsca.b
    @0
    @1
    simpl
    #
    psrbas
    cB
    @19
    @8
    cR
    cS
    cI
    psrvsca.s
    psrvsca.b
    @20
    @8
    eqid
    psrplusg
    vx
    vy
    cB
    cD
    cR
    cS
    @9
    c.x
    vf
    vg
    vh
    vk
    cI
    psrvsca.s
    psrvsca.b
    psrvsca.m
    @9
    eqid
    psrvsca.d
    psrmulr
    @6
    eqid
    @2
    @14
    eqidd
    @21
    @0
    @1
    simpr
    psrval
    fveq2d
    psrvsca.n
    @6
    cvv
    wcel
    @6
    @18
    wceq
    vx
    vf
    cK
    cB
    @5
    cK
    cR
    cbs
    cfv
    cvv
    psrvsca.k
    cR
    cbs
    fvex
    eqeltri
    cB
    cS
    cbs
    cfv
    cvv
    psrvsca.b
    cS
    cbs
    fvex
    eqeltri
    mpt2ex
    @6
    @17
    cvsca
    cvv
    c1
    c9
    cop
    cB
    @8
    cR
    @6
    @9
    @14
    psrvalstr
    vscaid
    @12
    csn
    @16
    @17
    @11
    @12
    @15
    snsstp2
    @16
    @10
    ssun2
    sstri
    strfv
    ax-mp
    3eqtr4g
    @2
    wn
    #
    c.xb
    vx
    vf
    cK
    cB
    @3
    @4
    c.xb
    co
    #
    cmpt2
    #
    @6
    @22
    c.xb
    cK
    cB
    cxp
    #
    wfn
    #
    c.xb
    @24
    wceq
    @22
    @26
    c0
    c0
    wfn
    #
    @27
    c0
    c0
    wceq
    c0
    eqid
    c0
    fn0
    mpbir
    @22
    @25
    c0
    c.xb
    c0
    @22
    @7
    c0
    cvsca
    cfv
    c.xb
    c0
    @22
    cS
    c0
    cvsca
    @22
    cS
    cI
    cR
    cmps
    co
    c0
    psrvsca.s
    cI
    cR
    cmps
    reldmpsr
    ovprc
    syl5eq
    fveq2d
    psrvsca.n
    cvsca
    c6
    df-vsca
    str0
    3eqtr4g
    @22
    @25
    cK
    c0
    cxp
    c0
    @22
    cB
    c0
    cK
    @22
    vf
    cB
    @4
    cB
    wcel
    #
    @2
    @4
    cB
    cS
    cmps
    cI
    cR
    reldmpsr
    psrvsca.s
    psrvsca.b
    elbasov
    con3i
    #
    eq0rdv
    xpeq2d
    cK
    xp0
    syl6eq
    fneq12d
    mpbiri
    vx
    vf
    cK
    cB
    c.xb
    fnov
    sylib
    @22
    vx
    vf
    cK
    cB
    @5
    @23
    @22
    @3
    cK
    wcel
    #
    @28
    @5
    @23
    wceq
    #
    @22
    @28
    @31
    wi
    @30
    @22
    @28
    @31
    @29
    pm2.21d
    a1d
    3imp
    mpt2eq3dva
    eqtr4d
    pm2.61i
end

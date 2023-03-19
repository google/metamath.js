include "ccatc.mm"
include "cfv.mm"
include "cnx.mm"
include "cbs.mm"
include "cop.mm"
include "chom.mm"
include "cco.mm"
include "ctp.mm"
include "cv.mm"
include "ccat.mm"
include "cin.mm"
include "cfunc.mm"
include "co.mm"
include "cmpt2.mm"
include "cxp.mm"
include "c2nd.mm"
include "ccofu.mm"
include "csb.mm"
include "cvv.mm"
include "cmpt.mm"
include "wceq.mm"
include "df-catc.mm"
include "a1i.mm"
include "wa.mm"
include "wcel.mm"
include "vex.mm"
include "inex1.mm"
include "simpr.mm"
include "ineq1d.mm"
include "adantr.mm"
include "eqtr4d.mm"
include "opeq2d.mm"
include "eqidd.mm"
include "mpt2eq123dv.mm"
include "ad2antrr.mm"
include "sqxpeqd.mm"
include "tpeq123d.mm"
include "csbied2.mm"
include "elex.mm"
include "syl.mm"
include "tpex.mm"
include "fvmptd.mm"
include "syl5eq.mm"

theorem catcval
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vv: setvar v
  let cB: class B
  let cC: class C
  let c.x: class .x.
  let cU: class U
  let vf: setvar f
  let vg: setvar g
  let cH: class H
  let cV: class V
  let vb: setvar b
  let vu: setvar u
  assume catcval.c: |- C = ( CatCat ` U )
  assume catcval.u: |- ( ph -> U e. V )
  assume catcval.b: |- ( ph -> B = ( U i^i Cat ) )
  assume catcval.h: |- ( ph -> H = ( x e. B , y e. B |-> ( x Func y ) ) )
  assume catcval.o: |- ( ph -> .x. = ( v e. ( B X. B ) , z e. B |-> ( g e. ( ( 2nd ` v ) Func z ) , f e. ( Func ` v ) |-> ( g o.func f ) ) ) )

  disjoint v x
  disjoint v y
  disjoint v z
  disjoint B v
  disjoint x y
  disjoint x z
  disjoint B x
  disjoint y z
  disjoint B y
  disjoint B z
  disjoint ph v
  disjoint ph x
  disjoint ph y
  disjoint ph z
  disjoint U v
  disjoint U x
  disjoint U y
  disjoint U z
  disjoint f g
  disjoint f v
  disjoint f x
  disjoint f y
  disjoint f z
  disjoint g v
  disjoint g x
  disjoint g y
  disjoint g z
  disjoint b u
  disjoint b v
  disjoint b x
  disjoint b y
  disjoint b z
  disjoint B b
  disjoint u v
  disjoint u x
  disjoint u y
  disjoint u z
  disjoint B u
  disjoint H b
  disjoint H u
  disjoint b ph
  disjoint ph u
  disjoint U b
  disjoint U u
  disjoint b f
  disjoint b g
  disjoint f u
  disjoint g u
  disjoint .x. b
  disjoint .x. u
  assert |- ( ph -> C = { <. ( Base ` ndx ) , B >. , <. ( Hom ` ndx ) , H >. , <. ( comp ` ndx ) , .x. >. } )

  proof
    wph
    cC
    cU
    ccatc
    cfv
    cnx
    cbs
    cfv
    #
    cB
    cop
    #
    cnx
    chom
    cfv
    #
    cH
    cop
    #
    cnx
    cco
    cfv
    #
    c.x
    cop
    #
    ctp
    #
    catcval.c
    wph
    vu
    cU
    vb
    vu
    cv
    #
    ccat
    cin
    #
    @0
    vb
    cv
    #
    cop
    #
    @2
    vx
    vy
    @9
    @9
    vx
    cv
    vy
    cv
    cfunc
    co
    #
    cmpt2
    #
    cop
    #
    @4
    vv
    vz
    @9
    @9
    cxp
    #
    @9
    vg
    vf
    vv
    cv
    #
    c2nd
    cfv
    vz
    cv
    cfunc
    co
    @15
    cfunc
    cfv
    vg
    cv
    vf
    cv
    ccofu
    co
    cmpt2
    #
    cmpt2
    #
    cop
    #
    ctp
    #
    csb
    #
    @6
    cvv
    ccatc
    cvv
    ccatc
    vu
    cvv
    @20
    cmpt
    wceq
    wph
    vx
    vy
    vz
    vv
    vu
    vf
    vg
    vb
    df-catc
    a1i
    wph
    @7
    cU
    wceq
    #
    wa
    #
    vb
    @8
    cB
    @19
    @6
    cvv
    @8
    cvv
    wcel
    @22
    @7
    ccat
    vu
    vex
    inex1
    a1i
    @22
    @8
    cU
    ccat
    cin
    #
    cB
    @22
    @7
    cU
    ccat
    wph
    @21
    simpr
    ineq1d
    wph
    cB
    @23
    wceq
    @21
    catcval.b
    adantr
    eqtr4d
    @22
    @9
    cB
    wceq
    #
    wa
    #
    @10
    @1
    @13
    @3
    @18
    @5
    @25
    @9
    cB
    @0
    @22
    @24
    simpr
    #
    opeq2d
    @25
    @12
    cH
    @2
    @25
    @12
    vx
    vy
    cB
    cB
    @11
    cmpt2
    #
    cH
    @25
    vx
    vy
    @9
    @9
    @11
    cB
    cB
    @11
    @26
    @26
    @25
    @11
    eqidd
    mpt2eq123dv
    wph
    cH
    @27
    wceq
    @21
    @24
    catcval.h
    ad2antrr
    eqtr4d
    opeq2d
    @25
    @17
    c.x
    @4
    @25
    @17
    vv
    vz
    cB
    cB
    cxp
    #
    cB
    @16
    cmpt2
    #
    c.x
    @25
    vv
    vz
    @14
    @9
    @16
    @28
    cB
    @16
    @25
    @9
    cB
    @26
    sqxpeqd
    @26
    @25
    @16
    eqidd
    mpt2eq123dv
    wph
    c.x
    @29
    wceq
    @21
    @24
    catcval.o
    ad2antrr
    eqtr4d
    opeq2d
    tpeq123d
    csbied2
    wph
    cU
    cV
    wcel
    cU
    cvv
    wcel
    catcval.u
    cU
    cV
    elex
    syl
    @6
    cvv
    wcel
    wph
    @1
    @3
    @5
    tpex
    a1i
    fvmptd
    syl5eq
end

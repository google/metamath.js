include "cringcALTV.mm"
include "cfv.mm"
include "cnx.mm"
include "cbs.mm"
include "cop.mm"
include "chom.mm"
include "cco.mm"
include "ctp.mm"
include "cv.mm"
include "crg.mm"
include "cin.mm"
include "crh.mm"
include "co.mm"
include "cmpt2.mm"
include "cxp.mm"
include "c2nd.mm"
include "c1st.mm"
include "ccom.mm"
include "csb.mm"
include "cvv.mm"
include "cmpt.mm"
include "wceq.mm"
include "df-ringcALTV.mm"
include "a1i.mm"
include "wa.mm"
include "wcel.mm"
include "vex.mm"
include "inex1.mm"
include "ineq1.mm"
include "adantl.mm"
include "adantr.mm"
include "eqtr4d.mm"
include "simpr.mm"
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

theorem ringcvalALTV
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
  let vk: setvar k
  assume ringcvalALTV.c: |- C = ( RingCatALTV ` U )
  assume ringcvalALTV.u: |- ( ph -> U e. V )
  assume ringcvalALTV.b: |- ( ph -> B = ( U i^i Ring ) )
  assume ringcvalALTV.h: |- ( ph -> H = ( x e. B , y e. B |-> ( x RingHom y ) ) )
  assume ringcvalALTV.o: |- ( ph -> .x. = ( v e. ( B X. B ) , z e. B |-> ( g e. ( ( 2nd ` v ) RingHom z ) , f e. ( ( 1st ` v ) RingHom ( 2nd ` v ) ) |-> ( g o. f ) ) ) )

  disjoint f g
  disjoint f v
  disjoint f x
  disjoint f y
  disjoint f z
  disjoint g v
  disjoint g x
  disjoint g y
  disjoint g z
  disjoint v x
  disjoint v y
  disjoint v z
  disjoint x y
  disjoint x z
  disjoint y z
  disjoint B v
  disjoint B x
  disjoint B y
  disjoint B z
  disjoint U v
  disjoint U x
  disjoint U y
  disjoint U z
  disjoint ph v
  disjoint ph x
  disjoint ph y
  disjoint ph z
  disjoint b f
  disjoint b g
  disjoint b u
  disjoint b v
  disjoint b x
  disjoint b y
  disjoint b z
  disjoint f u
  disjoint g u
  disjoint u v
  disjoint u x
  disjoint u y
  disjoint u z
  disjoint B b
  disjoint B u
  disjoint U b
  disjoint U u
  disjoint .x. b
  disjoint .x. u
  disjoint H b
  disjoint H u
  disjoint b ph
  disjoint ph u
  disjoint k x
  assert |- ( ph -> C = { <. ( Base ` ndx ) , B >. , <. ( Hom ` ndx ) , H >. , <. ( comp ` ndx ) , .x. >. } )

  proof
    wph
    cC
    cU
    cringcALTV
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
    ringcvalALTV.c
    wph
    vu
    cU
    vb
    vu
    cv
    #
    crg
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
    crh
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
    #
    vz
    cv
    crh
    co
    @15
    c1st
    cfv
    @16
    crh
    co
    vg
    cv
    vf
    cv
    ccom
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
    cringcALTV
    cvv
    cringcALTV
    vu
    cvv
    @21
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
    df-ringcALTV
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
    @20
    @6
    cvv
    @8
    cvv
    wcel
    @23
    @7
    crg
    vu
    vex
    inex1
    a1i
    @23
    @8
    cU
    crg
    cin
    #
    cB
    @22
    @8
    @24
    wceq
    wph
    @7
    cU
    crg
    ineq1
    adantl
    wph
    cB
    @24
    wceq
    @22
    ringcvalALTV.b
    adantr
    eqtr4d
    @23
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
    @19
    @5
    @26
    @9
    cB
    @0
    @23
    @25
    simpr
    #
    opeq2d
    @26
    @12
    cH
    @2
    @26
    @12
    vx
    vy
    cB
    cB
    @11
    cmpt2
    #
    cH
    @26
    vx
    vy
    @9
    @9
    @11
    cB
    cB
    @11
    @27
    @27
    @26
    @11
    eqidd
    mpt2eq123dv
    wph
    cH
    @28
    wceq
    @22
    @25
    ringcvalALTV.h
    ad2antrr
    eqtr4d
    opeq2d
    @26
    @18
    c.x
    @4
    @26
    @18
    vv
    vz
    cB
    cB
    cxp
    #
    cB
    @17
    cmpt2
    #
    c.x
    @26
    vv
    vz
    @14
    @9
    @17
    @29
    cB
    @17
    @26
    @9
    cB
    @27
    sqxpeqd
    @27
    @26
    @17
    eqidd
    mpt2eq123dv
    wph
    c.x
    @30
    wceq
    @22
    @25
    ringcvalALTV.o
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
    ringcvalALTV.u
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

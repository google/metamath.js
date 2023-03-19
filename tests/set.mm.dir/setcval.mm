include "csetc.mm"
include "cfv.mm"
include "cnx.mm"
include "cbs.mm"
include "cop.mm"
include "chom.mm"
include "cco.mm"
include "ctp.mm"
include "cv.mm"
include "cmap.mm"
include "co.mm"
include "cmpt2.mm"
include "cxp.mm"
include "c2nd.mm"
include "c1st.mm"
include "ccom.mm"
include "cvv.mm"
include "cmpt.mm"
include "wceq.mm"
include "df-setc.mm"
include "a1i.mm"
include "wa.mm"
include "simpr.mm"
include "opeq2d.mm"
include "eqidd.mm"
include "mpt2eq123dv.mm"
include "adantr.mm"
include "eqtr4d.mm"
include "sqxpeqd.mm"
include "tpeq123d.mm"
include "wcel.mm"
include "elex.mm"
include "syl.mm"
include "tpex.mm"
include "fvmptd.mm"
include "syl5eq.mm"

theorem setcval
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vv: setvar v
  let cC: class C
  let c.x: class .x.
  let cU: class U
  let vf: setvar f
  let vg: setvar g
  let cH: class H
  let cV: class V
  let vu: setvar u
  assume setcval.c: |- C = ( SetCat ` U )
  assume setcval.u: |- ( ph -> U e. V )
  assume setcval.h: |- ( ph -> H = ( x e. U , y e. U |-> ( y ^m x ) ) )
  assume setcval.o: |- ( ph -> .x. = ( v e. ( U X. U ) , z e. U |-> ( g e. ( z ^m ( 2nd ` v ) ) , f e. ( ( 2nd ` v ) ^m ( 1st ` v ) ) |-> ( g o. f ) ) ) )

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
  disjoint ph v
  disjoint ph x
  disjoint ph y
  disjoint ph z
  disjoint U v
  disjoint U x
  disjoint U y
  disjoint U z
  disjoint f u
  disjoint g u
  disjoint u v
  disjoint u x
  disjoint u y
  disjoint u z
  disjoint ph u
  disjoint U u
  disjoint .x. u
  disjoint H u
  assert |- ( ph -> C = { <. ( Base ` ndx ) , U >. , <. ( Hom ` ndx ) , H >. , <. ( comp ` ndx ) , .x. >. } )

  proof
    wph
    cC
    cU
    csetc
    cfv
    cnx
    cbs
    cfv
    #
    cU
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
    setcval.c
    wph
    vu
    cU
    @0
    vu
    cv
    #
    cop
    #
    @2
    vx
    vy
    @7
    @7
    vy
    cv
    vx
    cv
    cmap
    co
    #
    cmpt2
    #
    cop
    #
    @4
    vv
    vz
    @7
    @7
    cxp
    #
    @7
    vg
    vf
    vz
    cv
    vv
    cv
    #
    c2nd
    cfv
    #
    cmap
    co
    @14
    @13
    c1st
    cfv
    cmap
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
    @6
    cvv
    csetc
    cvv
    csetc
    vu
    cvv
    @18
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
    df-setc
    a1i
    wph
    @7
    cU
    wceq
    #
    wa
    #
    @8
    @1
    @11
    @3
    @17
    @5
    @20
    @7
    cU
    @0
    wph
    @19
    simpr
    #
    opeq2d
    @20
    @10
    cH
    @2
    @20
    @10
    vx
    vy
    cU
    cU
    @9
    cmpt2
    #
    cH
    @20
    vx
    vy
    @7
    @7
    @9
    cU
    cU
    @9
    @21
    @21
    @20
    @9
    eqidd
    mpt2eq123dv
    wph
    cH
    @22
    wceq
    @19
    setcval.h
    adantr
    eqtr4d
    opeq2d
    @20
    @16
    c.x
    @4
    @20
    @16
    vv
    vz
    cU
    cU
    cxp
    #
    cU
    @15
    cmpt2
    #
    c.x
    @20
    vv
    vz
    @12
    @7
    @15
    @23
    cU
    @15
    @20
    @7
    cU
    @21
    sqxpeqd
    @21
    @20
    @15
    eqidd
    mpt2eq123dv
    wph
    c.x
    @24
    wceq
    @19
    setcval.o
    adantr
    eqtr4d
    opeq2d
    tpeq123d
    wph
    cU
    cV
    wcel
    cU
    cvv
    wcel
    setcval.u
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

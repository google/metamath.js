include "chomf.mm"
include "cfv.mm"
include "wceq.mm"
include "ccomf.mm"
include "cv.mm"
include "chom.mm"
include "co.mm"
include "wral.mm"
include "wcel.mm"
include "wa.mm"
include "eqid.mm"
include "wss.mm"
include "adantr.mm"
include "simprl.mm"
include "sseldd.mm"
include "simprr.mm"
include "homfval.mm"
include "cxp.mm"
include "cres.mm"
include "ovresd.mm"
include "ccat.mm"
include "wfn.mm"
include "homffn.mm"
include "xpss12.mm"
include "syl2anc.mm"
include "fnssres.mm"
include "sylancr.mm"
include "reschom.mm"
include "oveqdr.mm"
include "eqtr3d.mm"
include "cvv.mm"
include "cbs.mm"
include "ressbas2.mm"
include "syl.mm"
include "fvex.mm"
include "syl6eqel.mm"
include "resshom.mm"
include "3eqtr3rd.mm"
include "ralrimivva.mm"
include "rescbas.mm"
include "homfeq.mm"
include "mpbird.mm"
include "cco.mm"
include "ressco.mm"
include "rescco.mm"
include "comfeqd.mm"
include "jca.mm"

theorem fullresc
  let wph: wff ph
  let cB: class B
  let cC: class C
  let cD: class D
  let cS: class S
  let cE: class E
  let cH: class H
  let vf: setvar f
  let vg: setvar g
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  assume fullsubc.b: |- B = ( Base ` C )
  assume fullsubc.h: |- H = ( Homf ` C )
  assume fullsubc.c: |- ( ph -> C e. Cat )
  assume fullsubc.s: |- ( ph -> S C_ B )
  assume fullsubc.d: |- D = ( C |`s S )
  assume fullsubc.e: |- E = ( C |`cat ( H |` ( S X. S ) ) )


  assert |- ( ph -> ( ( Homf ` D ) = ( Homf ` E ) /\ ( comf ` D ) = ( comf ` E ) ) )

  proof
    wph
    cD
    chomf
    cfv
    cE
    chomf
    cfv
    wceq
    #
    cD
    ccomf
    cfv
    cE
    ccomf
    cfv
    wceq
    wph
    @0
    vx
    cv
    #
    vy
    cv
    #
    cD
    chom
    cfv
    #
    co
    #
    @1
    @2
    cE
    chom
    cfv
    #
    co
    #
    wceq
    #
    vy
    cS
    wral
    vx
    cS
    wral
    wph
    @7
    vx
    vy
    cS
    cS
    wph
    @1
    cS
    wcel
    #
    @2
    cS
    wcel
    #
    wa
    #
    wa
    #
    @1
    @2
    cH
    co
    #
    @1
    @2
    cC
    chom
    cfv
    #
    co
    @6
    @4
    @11
    cB
    cC
    cH
    @13
    @1
    @2
    fullsubc.h
    fullsubc.b
    @13
    eqid
    #
    @11
    cS
    cB
    @1
    wph
    cS
    cB
    wss
    #
    @10
    fullsubc.s
    adantr
    #
    wph
    @8
    @9
    simprl
    #
    sseldd
    @11
    cS
    cB
    @2
    @16
    wph
    @8
    @9
    simprr
    #
    sseldd
    homfval
    @11
    @1
    @2
    cH
    cS
    cS
    cxp
    #
    cres
    #
    co
    @12
    @6
    @11
    @1
    @2
    cH
    cS
    @17
    @18
    ovresd
    wph
    @10
    vx
    vy
    @20
    @5
    wph
    cB
    cC
    cE
    cS
    @20
    ccat
    fullsubc.e
    fullsubc.b
    fullsubc.c
    wph
    cH
    cB
    cB
    cxp
    #
    wfn
    @19
    @21
    wss
    #
    @20
    @19
    wfn
    cB
    cC
    cH
    fullsubc.h
    fullsubc.b
    homffn
    wph
    @15
    @15
    @22
    fullsubc.s
    fullsubc.s
    cS
    cB
    cS
    cB
    xpss12
    syl2anc
    @21
    @19
    cH
    fnssres
    sylancr
    #
    fullsubc.s
    reschom
    oveqdr
    eqtr3d
    wph
    @10
    vx
    vy
    @13
    @3
    wph
    cS
    cvv
    wcel
    #
    @13
    @3
    wceq
    wph
    cS
    cD
    cbs
    cfv
    #
    cvv
    wph
    @15
    cS
    @25
    wceq
    fullsubc.s
    cS
    cB
    cD
    cC
    fullsubc.d
    fullsubc.b
    ressbas2
    syl
    #
    cD
    cbs
    fvex
    syl6eqel
    #
    cS
    cC
    cD
    @13
    cvv
    fullsubc.d
    @14
    resshom
    syl
    oveqdr
    3eqtr3rd
    ralrimivva
    wph
    vx
    vy
    cS
    cD
    cE
    @3
    @5
    @3
    eqid
    @5
    eqid
    @26
    wph
    cB
    cC
    cE
    cS
    @20
    ccat
    fullsubc.e
    fullsubc.b
    fullsubc.c
    @23
    fullsubc.s
    rescbas
    homfeq
    mpbird
    #
    wph
    cD
    cE
    wph
    cC
    cco
    cfv
    #
    cD
    cco
    cfv
    #
    cE
    cco
    cfv
    wph
    @24
    @29
    @30
    wceq
    @27
    cS
    cC
    cD
    @29
    cvv
    fullsubc.d
    @29
    eqid
    #
    ressco
    syl
    wph
    cB
    cC
    cE
    cS
    @29
    @20
    ccat
    fullsubc.e
    fullsubc.b
    fullsubc.c
    @23
    fullsubc.s
    @31
    rescco
    eqtr3d
    @28
    comfeqd
    jca
end

include "cful.mm"
include "co.mm"
include "relfull.mm"
include "cv.mm"
include "cfunc.mm"
include "wbr.mm"
include "crn.mm"
include "cfv.mm"
include "chom.mm"
include "wceq.mm"
include "cbs.mm"
include "wral.mm"
include "wa.mm"
include "homfeqbas.mm"
include "adantr.mm"
include "wcel.mm"
include "eqid.mm"
include "chomf.mm"
include "ad3antrrr.mm"
include "simpllr.mm"
include "funcf1.mm"
include "simplr.mm"
include "ffvelrnd.mm"
include "simpr.mm"
include "homfeqval.mm"
include "eqeq2d.mm"
include "raleqbidva.mm"
include "pm5.32da.mm"
include "funcpropd.mm"
include "breqd.mm"
include "anbi1d.mm"
include "bitrd.mm"
include "isfull.mm"
include "3bitr4g.mm"
include "eqbrrdiv.mm"

theorem fullpropd
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cV: class V
  let vf: setvar f
  let vg: setvar g
  let vx: setvar x
  let vy: setvar y
  assume fullpropd.1: |- ( ph -> ( Homf ` A ) = ( Homf ` B ) )
  assume fullpropd.2: |- ( ph -> ( comf ` A ) = ( comf ` B ) )
  assume fullpropd.3: |- ( ph -> ( Homf ` C ) = ( Homf ` D ) )
  assume fullpropd.4: |- ( ph -> ( comf ` C ) = ( comf ` D ) )
  assume fullpropd.a: |- ( ph -> A e. V )
  assume fullpropd.b: |- ( ph -> B e. V )
  assume fullpropd.c: |- ( ph -> C e. V )
  assume fullpropd.d: |- ( ph -> D e. V )


  assert |- ( ph -> ( A Full C ) = ( B Full D ) )

  proof
    wph
    vf
    vg
    cA
    cC
    cful
    co
    #
    cB
    cD
    cful
    co
    #
    cA
    cC
    relfull
    cB
    cD
    relfull
    wph
    vf
    cv
    #
    vg
    cv
    #
    cA
    cC
    cfunc
    co
    #
    wbr
    #
    vx
    cv
    #
    vy
    cv
    #
    @3
    co
    crn
    #
    @6
    @2
    cfv
    #
    @7
    @2
    cfv
    #
    cC
    chom
    cfv
    #
    co
    #
    wceq
    #
    vy
    cA
    cbs
    cfv
    #
    wral
    #
    vx
    @14
    wral
    #
    wa
    #
    @2
    @3
    cB
    cD
    cfunc
    co
    #
    wbr
    #
    @8
    @9
    @10
    cD
    chom
    cfv
    #
    co
    #
    wceq
    #
    vy
    cB
    cbs
    cfv
    #
    wral
    #
    vx
    @23
    wral
    #
    wa
    #
    @2
    @3
    @0
    wbr
    @2
    @3
    @1
    wbr
    wph
    @17
    @5
    @25
    wa
    @26
    wph
    @5
    @16
    @25
    wph
    @5
    wa
    #
    @15
    @24
    vx
    @14
    @23
    wph
    @14
    @23
    wceq
    #
    @5
    wph
    cA
    cB
    fullpropd.1
    homfeqbas
    adantr
    #
    @27
    @6
    @14
    wcel
    #
    wa
    #
    @13
    @22
    vy
    @14
    @23
    @27
    @28
    @30
    @29
    adantr
    @31
    @7
    @14
    wcel
    #
    wa
    #
    @12
    @21
    @8
    @33
    cC
    cbs
    cfv
    #
    cC
    cD
    @11
    @20
    @9
    @10
    @34
    eqid
    #
    @11
    eqid
    #
    @20
    eqid
    #
    wph
    cC
    chomf
    cfv
    cD
    chomf
    cfv
    wceq
    @5
    @30
    @32
    fullpropd.3
    ad3antrrr
    @33
    @14
    @34
    @6
    @2
    @33
    @14
    @34
    cA
    cC
    @2
    @3
    @14
    eqid
    #
    @35
    wph
    @5
    @30
    @32
    simpllr
    funcf1
    #
    @27
    @30
    @32
    simplr
    ffvelrnd
    @33
    @14
    @34
    @7
    @2
    @39
    @31
    @32
    simpr
    ffvelrnd
    homfeqval
    eqeq2d
    raleqbidva
    raleqbidva
    pm5.32da
    wph
    @5
    @19
    @25
    wph
    @4
    @18
    @2
    @3
    wph
    cA
    cB
    cC
    cD
    cV
    fullpropd.1
    fullpropd.2
    fullpropd.3
    fullpropd.4
    fullpropd.a
    fullpropd.b
    fullpropd.c
    fullpropd.d
    funcpropd
    breqd
    anbi1d
    bitrd
    vx
    vy
    @14
    cA
    cC
    @2
    @3
    @11
    @38
    @36
    isfull
    vx
    vy
    @23
    cB
    cD
    @2
    @3
    @20
    @23
    eqid
    @37
    isfull
    3bitr4g
    eqbrrdiv
end

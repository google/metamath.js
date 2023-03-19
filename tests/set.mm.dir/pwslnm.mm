include "clnm.mm"
include "wcel.mm"
include "cfn.mm"
include "wa.mm"
include "cpws.mm"
include "co.mm"
include "cv.mm"
include "wi.mm"
include "c0.mm"
include "csn.mm"
include "cun.mm"
include "wceq.mm"
include "oveq2.mm"
include "eleq1d.mm"
include "imbi2d.mm"
include "weq.mm"
include "clmod.mm"
include "lnmlmod.mm"
include "eqid.mm"
include "pwslnmlem0.mm"
include "syl.mm"
include "wel.mm"
include "wn.mm"
include "vex.mm"
include "snex.mm"
include "ad2antrl.mm"
include "cin.mm"
include "disjsn.mm"
include "biimpri.mm"
include "ad2antlr.mm"
include "simprr.mm"
include "pwslnmlem1.mm"
include "pwslnmlem2.mm"
include "exp32.mm"
include "a2d.mm"
include "findcard2s.mm"
include "impcom.mm"
include "syl5eqel.mm"

theorem pwslnm
  let cI: class I
  let cW: class W
  let cY: class Y
  let va: setvar a
  let vb: setvar b
  let vc: setvar c
  assume pwslnm.y: |- Y = ( W ^s I )


  assert |- ( ( W e. LNoeM /\ I e. Fin ) -> Y e. LNoeM )

  proof
    cW
    clnm
    wcel
    #
    cI
    cfn
    wcel
    #
    wa
    cY
    cW
    cI
    cpws
    co
    #
    clnm
    pwslnm.y
    @1
    @0
    @2
    clnm
    wcel
    #
    @0
    cW
    va
    cv
    #
    cpws
    co
    #
    clnm
    wcel
    #
    wi
    @0
    cW
    c0
    cpws
    co
    #
    clnm
    wcel
    #
    wi
    @0
    cW
    vb
    cv
    #
    cpws
    co
    #
    clnm
    wcel
    #
    wi
    @0
    cW
    @9
    vc
    cv
    #
    csn
    #
    cun
    #
    cpws
    co
    #
    clnm
    wcel
    #
    wi
    @0
    @3
    wi
    va
    vb
    vc
    cI
    @4
    c0
    wceq
    #
    @6
    @8
    @0
    @17
    @5
    @7
    clnm
    @4
    c0
    cW
    cpws
    oveq2
    eleq1d
    imbi2d
    va
    vb
    weq
    #
    @6
    @11
    @0
    @18
    @5
    @10
    clnm
    @4
    @9
    cW
    cpws
    oveq2
    eleq1d
    imbi2d
    @4
    @14
    wceq
    #
    @6
    @16
    @0
    @19
    @5
    @15
    clnm
    @4
    @14
    cW
    cpws
    oveq2
    eleq1d
    imbi2d
    @4
    cI
    wceq
    #
    @6
    @3
    @0
    @20
    @5
    @2
    clnm
    @4
    cI
    cW
    cpws
    oveq2
    eleq1d
    imbi2d
    @0
    cW
    clmod
    wcel
    #
    @8
    cW
    lnmlmod
    #
    cW
    @7
    @7
    eqid
    pwslnmlem0
    syl
    @9
    cfn
    wcel
    #
    vc
    vb
    wel
    wn
    #
    wa
    #
    @0
    @11
    @16
    @25
    @0
    @11
    @16
    @25
    @0
    @11
    wa
    #
    wa
    @9
    @13
    cW
    @10
    cW
    @13
    cpws
    co
    #
    @15
    vb
    vex
    @12
    snex
    @10
    eqid
    @27
    eqid
    #
    @15
    eqid
    @0
    @21
    @25
    @11
    @22
    ad2antrl
    @24
    @9
    @13
    cin
    c0
    wceq
    #
    @23
    @26
    @29
    @24
    @9
    @12
    disjsn
    biimpri
    ad2antlr
    @25
    @0
    @11
    simprr
    @0
    @27
    clnm
    wcel
    @25
    @11
    vc
    cW
    @27
    @28
    pwslnmlem1
    ad2antrl
    pwslnmlem2
    exp32
    a2d
    findcard2s
    impcom
    syl5eqel
end

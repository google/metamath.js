include "wcel.mm"
include "wss.mm"
include "wa.mm"
include "cfv.mm"
include "cv.mm"
include "crab.mm"
include "cint.mm"
include "pclvalN.mm"
include "cjn.mm"
include "co.mm"
include "cple.mm"
include "wbr.mm"
include "wi.mm"
include "wral.mm"
include "atpsubN.mm"
include "sseq2.mm"
include "intminss.mm"
include "sylan.mm"
include "r19.26.mm"
include "jcab.mm"
include "ralbii.mm"
include "vex.mm"
include "elintrab.mm"
include "anbi12i.mm"
include "3bitr4ri.mm"
include "w3a.mm"
include "simpll1.mm"
include "simplr.mm"
include "simpll3.mm"
include "simprl.mm"
include "simprr.mm"
include "simpll2.mm"
include "eqid.mm"
include "psubspi2N.mm"
include "syl33anc.mm"
include "ex.mm"
include "imim2d.mm"
include "ralimdva.mm"
include "syl6ibr.mm"
include "3exp.mm"
include "com24.mm"
include "syl5bi.mm"
include "ralrimdv.mm"
include "ralrimivv.mm"
include "adantr.mm"
include "wb.mm"
include "ispsubsp.mm"
include "mpbir2and.mm"
include "eqeltrd.mm"

theorem pclclN
  let cA: class A
  let cS: class S
  let cU: class U
  let cK: class K
  let cV: class V
  let cX: class X
  let vk: setvar k
  let vx: setvar x
  let vy: setvar y
  let vp: setvar p
  let vq: setvar q
  let vr: setvar r
  assume pclfval.a: |- A = ( Atoms ` K )
  assume pclfval.s: |- S = ( PSubSp ` K )
  assume pclfval.c: |- U = ( PCl ` K )


  assert |- ( ( K e. V /\ X C_ A ) -> ( U ` X ) e. S )

  proof
    cK
    cV
    wcel
    #
    cX
    cA
    wss
    #
    wa
    #
    cX
    cU
    cfv
    cX
    vy
    cv
    #
    wss
    #
    vy
    cS
    crab
    cint
    #
    cS
    vy
    cA
    cS
    cU
    cK
    cV
    cX
    pclfval.a
    pclfval.s
    pclfval.c
    pclvalN
    @2
    @5
    cS
    wcel
    #
    @5
    cA
    wss
    #
    vr
    cv
    #
    vp
    cv
    #
    vq
    cv
    #
    cK
    cjn
    cfv
    #
    co
    cK
    cple
    cfv
    #
    wbr
    #
    @8
    @5
    wcel
    #
    wi
    #
    vr
    cA
    wral
    #
    vq
    @5
    wral
    vp
    @5
    wral
    #
    @0
    cA
    cS
    wcel
    @1
    @7
    cA
    cS
    cK
    cV
    pclfval.a
    pclfval.s
    atpsubN
    @4
    @1
    vy
    cA
    cS
    @3
    cA
    cX
    sseq2
    intminss
    sylan
    @0
    @17
    @1
    @0
    @16
    vp
    vq
    @5
    @5
    @0
    @9
    @5
    wcel
    #
    @10
    @5
    wcel
    #
    wa
    #
    @15
    vr
    cA
    @20
    @4
    @9
    @3
    wcel
    #
    @10
    @3
    wcel
    #
    wa
    #
    wi
    #
    vy
    cS
    wral
    #
    @0
    @8
    cA
    wcel
    #
    @15
    wi
    @4
    @21
    wi
    #
    @4
    @22
    wi
    #
    wa
    #
    vy
    cS
    wral
    @27
    vy
    cS
    wral
    #
    @28
    vy
    cS
    wral
    #
    wa
    @25
    @20
    @27
    @28
    vy
    cS
    r19.26
    @24
    @29
    vy
    cS
    @4
    @21
    @22
    jcab
    ralbii
    @18
    @30
    @19
    @31
    @4
    vy
    @9
    cS
    vp
    vex
    elintrab
    @4
    vy
    @10
    cS
    vq
    vex
    elintrab
    anbi12i
    3bitr4ri
    @0
    @13
    @26
    @25
    @14
    @0
    @13
    @26
    @25
    @14
    wi
    @0
    @13
    @26
    w3a
    #
    @25
    @4
    @8
    @3
    wcel
    #
    wi
    #
    vy
    cS
    wral
    @14
    @32
    @24
    @34
    vy
    cS
    @32
    @3
    cS
    wcel
    #
    wa
    #
    @23
    @33
    @4
    @36
    @23
    @33
    @36
    @23
    wa
    @0
    @35
    @26
    @21
    @22
    @13
    @33
    @0
    @13
    @26
    @35
    @23
    simpll1
    @32
    @35
    @23
    simplr
    @0
    @13
    @26
    @35
    @23
    simpll3
    @36
    @21
    @22
    simprl
    @36
    @21
    @22
    simprr
    @0
    @13
    @26
    @35
    @23
    simpll2
    cA
    cV
    @8
    @9
    @10
    cS
    @11
    cK
    @12
    @3
    @12
    eqid
    #
    @11
    eqid
    #
    pclfval.a
    pclfval.s
    psubspi2N
    syl33anc
    ex
    imim2d
    ralimdva
    @4
    vy
    @8
    cS
    vr
    vex
    elintrab
    syl6ibr
    3exp
    com24
    syl5bi
    ralrimdv
    ralrimivv
    adantr
    @0
    @6
    @7
    @17
    wa
    wb
    @1
    cA
    cV
    cS
    @11
    cK
    @12
    @5
    vr
    vq
    vp
    @37
    @38
    pclfval.a
    pclfval.s
    ispsubsp
    adantr
    mpbir2and
    eqeltrd
end

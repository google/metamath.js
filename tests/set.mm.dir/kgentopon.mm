include "ctopon.mm"
include "cfv.mm"
include "wcel.mm"
include "ckgen.mm"
include "ctop.mm"
include "cuni.mm"
include "wceq.mm"
include "cv.mm"
include "wss.mm"
include "wi.mm"
include "wal.mm"
include "cin.mm"
include "wral.mm"
include "wa.mm"
include "crest.mm"
include "co.mm"
include "ccmp.mm"
include "cpw.mm"
include "uniss.mm"
include "crab.mm"
include "kgenval.mm"
include "ssrab2.mm"
include "syl6eqss.mm"
include "sspwuni.mm"
include "sylib.mm"
include "sylan9ssr.mm"
include "ciun.mm"
include "iunin2.mm"
include "uniiun.mm"
include "ineq2i.mm"
include "incom.mm"
include "3eqtr2i.mm"
include "cmptop.mm"
include "ad2antll.mm"
include "simplr.mm"
include "sselda.mm"
include "simplrr.mm"
include "kgeni.mm"
include "syl2anc.mm"
include "syl5eqelr.mm"
include "ralrimiva.mm"
include "iunopn.mm"
include "expr.mm"
include "wb.mm"
include "elkgen.mm"
include "adantr.mm"
include "mpbir2and.mm"
include "ex.mm"
include "alrimiv.mm"
include "inss1.mm"
include "elssuni.mm"
include "ad2antrl.mm"
include "ssid.mm"
include "a1i.mm"
include "elpwi.mm"
include "sseqin2.mm"
include "resttopon.mm"
include "sylan2.mm"
include "toponmax.mm"
include "syl.mm"
include "eqeltrd.mm"
include "eqssd.mm"
include "sseqtr4d.mm"
include "syl5ss.mm"
include "inindir.mm"
include "simplrl.mm"
include "simprr.mm"
include "inopn.mm"
include "syl3anc.mm"
include "syl5eqel.mm"
include "ralrimivva.mm"
include "cvv.mm"
include "fvex.mm"
include "istopg.mm"
include "ax-mp.mm"
include "sylanbrc.mm"
include "istopon.mm"

theorem kgentopon
  let cJ: class J
  let cX: class X
  let cA: class A
  let vy: setvar y
  let vk: setvar k
  let vx: setvar x
  let cK: class K
  let vj: setvar j


  assert |- ( J e. ( TopOn ` X ) -> ( kGen ` J ) e. ( TopOn ` X ) )

  proof
    cJ
    cX
    ctopon
    cfv
    #
    wcel
    #
    cJ
    ckgen
    cfv
    #
    ctop
    wcel
    #
    cX
    @2
    cuni
    #
    wceq
    #
    @2
    @0
    wcel
    @1
    vx
    cv
    #
    @2
    wss
    #
    @6
    cuni
    #
    @2
    wcel
    #
    wi
    #
    vx
    wal
    #
    @6
    vy
    cv
    #
    cin
    #
    @2
    wcel
    #
    vy
    @2
    wral
    vx
    @2
    wral
    #
    @3
    @1
    @10
    vx
    @1
    @7
    @9
    @1
    @7
    wa
    #
    @9
    @8
    cX
    wss
    #
    cJ
    vk
    cv
    #
    crest
    co
    #
    ccmp
    wcel
    #
    @8
    @18
    cin
    #
    @19
    wcel
    #
    wi
    #
    vk
    cX
    cpw
    #
    wral
    #
    @7
    @1
    @8
    @4
    cX
    @6
    @2
    uniss
    @1
    @2
    @24
    wss
    @4
    cX
    wss
    @1
    @2
    @20
    @6
    @18
    cin
    #
    @19
    wcel
    #
    wi
    vk
    @24
    wral
    #
    vx
    @24
    crab
    @24
    vx
    vk
    cJ
    cX
    kgenval
    @28
    vx
    @24
    ssrab2
    syl6eqss
    @2
    cX
    sspwuni
    sylib
    #
    sylan9ssr
    @16
    @23
    vk
    @24
    @16
    @18
    @24
    wcel
    #
    @20
    @22
    @16
    @30
    @20
    wa
    #
    wa
    #
    @21
    vy
    @6
    @18
    @12
    cin
    #
    ciun
    #
    @19
    @34
    @18
    vy
    @6
    @12
    ciun
    #
    cin
    @18
    @8
    cin
    @21
    vy
    @6
    @18
    @12
    iunin2
    @8
    @35
    @18
    vy
    @6
    uniiun
    ineq2i
    @18
    @8
    incom
    3eqtr2i
    @32
    @19
    ctop
    wcel
    #
    @33
    @19
    wcel
    #
    vy
    @6
    wral
    @34
    @19
    wcel
    @20
    @36
    @16
    @30
    @19
    cmptop
    #
    ad2antll
    @32
    @37
    vy
    @6
    @32
    @12
    @6
    wcel
    #
    wa
    #
    @33
    @12
    @18
    cin
    #
    @19
    @12
    @18
    incom
    @40
    @12
    @2
    wcel
    #
    @20
    @41
    @19
    wcel
    #
    @32
    @6
    @2
    @12
    @1
    @7
    @31
    simplr
    sselda
    @16
    @30
    @20
    @39
    simplrr
    @12
    cJ
    @18
    kgeni
    #
    syl2anc
    syl5eqelr
    ralrimiva
    vy
    @6
    @33
    @19
    iunopn
    syl2anc
    syl5eqelr
    expr
    ralrimiva
    @1
    @9
    @17
    @25
    wa
    wb
    @7
    @8
    vk
    cJ
    cX
    elkgen
    adantr
    mpbir2and
    ex
    alrimiv
    @1
    @14
    vx
    vy
    @2
    @2
    @1
    @6
    @2
    wcel
    #
    @42
    wa
    #
    wa
    #
    @14
    @13
    cX
    wss
    #
    @20
    @13
    @18
    cin
    #
    @19
    wcel
    #
    wi
    #
    vk
    @24
    wral
    #
    @47
    @13
    @6
    cX
    @6
    @12
    inss1
    @47
    @6
    @4
    cX
    @45
    @6
    @4
    wss
    @1
    @42
    @6
    @2
    elssuni
    ad2antrl
    @1
    @5
    @46
    @1
    cX
    @4
    @1
    cX
    @2
    wcel
    #
    cX
    @4
    wss
    @1
    @53
    cX
    cX
    wss
    #
    @20
    cX
    @18
    cin
    #
    @19
    wcel
    #
    wi
    #
    vk
    @24
    wral
    @54
    @1
    cX
    ssid
    a1i
    @1
    @57
    vk
    @24
    @1
    @30
    @20
    @56
    @1
    @31
    wa
    #
    @55
    @18
    @19
    @58
    @18
    cX
    wss
    #
    @55
    @18
    wceq
    @30
    @59
    @1
    @20
    @18
    cX
    elpwi
    #
    ad2antrl
    @18
    cX
    sseqin2
    sylib
    @58
    @19
    @18
    ctopon
    cfv
    wcel
    #
    @18
    @19
    wcel
    @31
    @1
    @59
    @61
    @30
    @59
    @20
    @60
    adantr
    @18
    cJ
    cX
    resttopon
    sylan2
    @18
    @19
    toponmax
    syl
    eqeltrd
    expr
    ralrimiva
    cX
    vk
    cJ
    cX
    elkgen
    mpbir2and
    cX
    @2
    elssuni
    syl
    @29
    eqssd
    #
    adantr
    sseqtr4d
    syl5ss
    @47
    @51
    vk
    @24
    @47
    @30
    @20
    @50
    @47
    @31
    wa
    #
    @49
    @26
    @41
    cin
    #
    @19
    @6
    @12
    @18
    inindir
    @63
    @36
    @27
    @43
    @64
    @19
    wcel
    @20
    @36
    @47
    @30
    @38
    ad2antll
    @63
    @45
    @20
    @27
    @1
    @45
    @42
    @31
    simplrl
    @47
    @30
    @20
    simprr
    #
    @6
    cJ
    @18
    kgeni
    syl2anc
    @63
    @42
    @20
    @43
    @1
    @45
    @42
    @31
    simplrr
    @65
    @44
    syl2anc
    @26
    @41
    @19
    inopn
    syl3anc
    syl5eqel
    expr
    ralrimiva
    @1
    @14
    @48
    @52
    wa
    wb
    @46
    @13
    vk
    cJ
    cX
    elkgen
    adantr
    mpbir2and
    ralrimivva
    @2
    cvv
    wcel
    @3
    @11
    @15
    wa
    wb
    cJ
    ckgen
    fvex
    vx
    vy
    cvv
    @2
    istopg
    ax-mp
    sylanbrc
    @62
    cX
    @2
    istopon
    sylanbrc
end

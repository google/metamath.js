include "ccn.mm"
include "co.mm"
include "wcel.mm"
include "wf.mm"
include "ccnv.mm"
include "cv.mm"
include "cima.mm"
include "cfi.mm"
include "cfv.mm"
include "wral.mm"
include "wa.mm"
include "tgcn.mm"
include "wss.mm"
include "wi.mm"
include "adantr.mm"
include "ssfii.mm"
include "ssralv.mm"
include "3syl.mm"
include "cint.mm"
include "wceq.mm"
include "cpw.mm"
include "cfn.mm"
include "cin.mm"
include "wrex.mm"
include "cvv.mm"
include "wb.mm"
include "vex.mm"
include "elfi.mm"
include "sylancr.mm"
include "w3a.mm"
include "ciin.mm"
include "simpr2.mm"
include "imaeq2d.mm"
include "wfun.mm"
include "c0.mm"
include "wne.mm"
include "ffun.mm"
include "ad2antlr.mm"
include "syl6eqelr.mm"
include "intex.mm"
include "sylibr.mm"
include "intpreima.mm"
include "syl2anc.mm"
include "eqtrd.mm"
include "ctop.mm"
include "ctopon.mm"
include "topontop.mm"
include "syl.mm"
include "ad2antrr.mm"
include "inss2.mm"
include "simpr1.mm"
include "sseldi.mm"
include "inss1.mm"
include "elpwid.mm"
include "simpr3.mm"
include "sylc.mm"
include "iinopn.mm"
include "syl13anc.mm"
include "eqeltrd.mm"
include "3exp2.mm"
include "rexlimdv.mm"
include "sylbid.mm"
include "com23.mm"
include "ralrimdv.mm"
include "imaeq2.mm"
include "eleq1d.mm"
include "cbvralv.mm"
include "syl6ibr.mm"
include "impbid.mm"
include "pm5.32da.mm"
include "bitrd.mm"

theorem subbascn
  let wph: wff ph
  let vy: setvar y
  let cB: class B
  let cF: class F
  let cJ: class J
  let cK: class K
  let cV: class V
  let cX: class X
  let cY: class Y
  let vx: setvar x
  let vz: setvar z
  assume subbascn.1: |- ( ph -> J e. ( TopOn ` X ) )
  assume subbascn.2: |- ( ph -> B e. V )
  assume subbascn.3: |- ( ph -> K = ( topGen ` ( fi ` B ) ) )
  assume subbascn.4: |- ( ph -> K e. ( TopOn ` Y ) )

  disjoint B y
  disjoint F y
  disjoint J y
  disjoint X y
  disjoint Y y
  disjoint K y
  disjoint x y
  disjoint x z
  disjoint B x
  disjoint y z
  disjoint B z
  disjoint F x
  disjoint F z
  disjoint J x
  disjoint J z
  disjoint X x
  disjoint X z
  disjoint Y x
  disjoint Y z
  disjoint ph x
  disjoint ph z
  disjoint V z
  assert |- ( ph -> ( F e. ( J Cn K ) <-> ( F : X --> Y /\ A. y e. B ( `' F " y ) e. J ) ) )

  proof
    wph
    cF
    cJ
    cK
    ccn
    co
    wcel
    cX
    cY
    cF
    wf
    #
    cF
    ccnv
    #
    vy
    cv
    #
    cima
    #
    cJ
    wcel
    #
    vy
    cB
    cfi
    cfv
    #
    wral
    #
    wa
    @0
    @4
    vy
    cB
    wral
    #
    wa
    wph
    vy
    @5
    cF
    cJ
    cK
    cX
    cY
    subbascn.1
    subbascn.3
    subbascn.4
    tgcn
    wph
    @0
    @6
    @7
    wph
    @0
    wa
    #
    @6
    @7
    @8
    cB
    cV
    wcel
    #
    cB
    @5
    wss
    @6
    @7
    wi
    wph
    @9
    @0
    subbascn.2
    adantr
    #
    cB
    cV
    ssfii
    @4
    vy
    cB
    @5
    ssralv
    3syl
    @8
    @7
    @1
    vx
    cv
    #
    cima
    #
    cJ
    wcel
    #
    vx
    @5
    wral
    @6
    @8
    @7
    @13
    vx
    @5
    @8
    @11
    @5
    wcel
    #
    @7
    @13
    @8
    @14
    @11
    vz
    cv
    #
    cint
    #
    wceq
    #
    vz
    cB
    cpw
    #
    cfn
    cin
    #
    wrex
    #
    @7
    @13
    wi
    #
    @8
    @11
    cvv
    wcel
    @9
    @14
    @20
    wb
    vx
    vex
    #
    @10
    vz
    @11
    cB
    cvv
    cV
    elfi
    sylancr
    @8
    @17
    @21
    vz
    @19
    @8
    @15
    @19
    wcel
    #
    @17
    @7
    @13
    @8
    @23
    @17
    @7
    w3a
    #
    wa
    #
    @12
    vy
    @15
    @3
    ciin
    #
    cJ
    @25
    @12
    @1
    @16
    cima
    #
    @26
    @25
    @11
    @16
    @1
    @8
    @23
    @17
    @7
    simpr2
    #
    imaeq2d
    @25
    cF
    wfun
    #
    @15
    c0
    wne
    #
    @27
    @26
    wceq
    @0
    @29
    wph
    @24
    cX
    cY
    cF
    ffun
    ad2antlr
    @25
    @16
    cvv
    wcel
    @30
    @25
    @16
    @11
    cvv
    @28
    @22
    syl6eqelr
    @15
    intex
    sylibr
    #
    vy
    @15
    cF
    intpreima
    syl2anc
    eqtrd
    @25
    cJ
    ctop
    wcel
    #
    @15
    cfn
    wcel
    @30
    @4
    vy
    @15
    wral
    #
    @26
    cJ
    wcel
    wph
    @32
    @0
    @24
    wph
    cJ
    cX
    ctopon
    cfv
    wcel
    @32
    subbascn.1
    cX
    cJ
    topontop
    syl
    ad2antrr
    @25
    @19
    cfn
    @15
    @18
    cfn
    inss2
    @8
    @23
    @17
    @7
    simpr1
    #
    sseldi
    @31
    @25
    @15
    cB
    wss
    @7
    @33
    @25
    @15
    cB
    @25
    @19
    @18
    @15
    @18
    cfn
    inss1
    @34
    sseldi
    elpwid
    @8
    @23
    @17
    @7
    simpr3
    @4
    vy
    @15
    cB
    ssralv
    sylc
    vy
    @15
    @3
    cJ
    iinopn
    syl13anc
    eqeltrd
    3exp2
    rexlimdv
    sylbid
    com23
    ralrimdv
    @4
    @13
    vy
    vx
    @5
    @2
    @11
    wceq
    @3
    @12
    cJ
    @2
    @11
    @1
    imaeq2
    eleq1d
    cbvralv
    syl6ibr
    impbid
    pm5.32da
    bitrd
end

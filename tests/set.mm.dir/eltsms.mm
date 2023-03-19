include "ctsu.mm"
include "co.mm"
include "wcel.mm"
include "cv.mm"
include "cres.mm"
include "cgsu.mm"
include "cmpt.mm"
include "wss.mm"
include "crab.mm"
include "crn.mm"
include "cfg.mm"
include "cflf.mm"
include "cfv.mm"
include "cima.mm"
include "wrex.mm"
include "wi.mm"
include "wral.mm"
include "wa.mm"
include "ccmn.mm"
include "eqid.mm"
include "tsmsval.mm"
include "eleq2d.mm"
include "ctopon.mm"
include "cfbas.mm"
include "wf.mm"
include "wb.mm"
include "ctps.mm"
include "istps.mm"
include "sylib.mm"
include "tsmsfbas.mm"
include "tsmslem1.mm"
include "fmptd.mm"
include "flffbas.mm"
include "syl3anc.mm"
include "cvv.mm"
include "cpw.mm"
include "cfn.mm"
include "cin.mm"
include "pwexg.mm"
include "inex1g.mm"
include "3syl.mm"
include "syl5eqel.mm"
include "adantr.mm"
include "rabexg.mm"
include "syl.mm"
include "ralrimivw.mm"
include "wceq.mm"
include "imaeq2.mm"
include "sseq1d.mm"
include "rexrnmpt.mm"
include "ccnv.mm"
include "wfun.mm"
include "cdm.mm"
include "funmpt.mm"
include "ssrab2.mm"
include "ovex.mm"
include "dmmpti.mm"
include "sseqtr4i.mm"
include "funimass3.mm"
include "mp2an.mm"
include "mptpreima.mm"
include "sseq2i.mm"
include "ss2rab.mm"
include "3bitri.mm"
include "rexbii.mm"
include "syl6bb.mm"
include "imbi2d.mm"
include "ralbidva.mm"
include "anbi2d.mm"
include "3bitrd.mm"

theorem eltsms
  let wph: wff ph
  let vy: setvar y
  let vz: setvar z
  let vu: setvar u
  let cA: class A
  let cB: class B
  let cC: class C
  let cS: class S
  let cF: class F
  let cG: class G
  let cJ: class J
  let cV: class V
  let vw: setvar w
  let cU: class U
  assume eltsms.b: |- B = ( Base ` G )
  assume eltsms.j: |- J = ( TopOpen ` G )
  assume eltsms.s: |- S = ( ~P A i^i Fin )
  assume eltsms.1: |- ( ph -> G e. CMnd )
  assume eltsms.2: |- ( ph -> G e. TopSp )
  assume eltsms.a: |- ( ph -> A e. V )
  assume eltsms.f: |- ( ph -> F : A --> B )

  disjoint u y
  disjoint B u
  disjoint B y
  disjoint C u
  disjoint u z
  disjoint F u
  disjoint y z
  disjoint F y
  disjoint F z
  disjoint G u
  disjoint G y
  disjoint G z
  disjoint J u
  disjoint J z
  disjoint A z
  disjoint ph u
  disjoint ph y
  disjoint ph z
  disjoint S u
  disjoint S y
  disjoint S z
  disjoint u w
  disjoint w y
  disjoint B w
  disjoint C w
  disjoint w z
  disjoint F w
  disjoint G w
  disjoint J w
  disjoint S w
  disjoint U u
  disjoint U y
  disjoint U z
  assert |- ( ph -> ( C e. ( G tsums F ) <-> ( C e. B /\ A. u e. J ( C e. u -> E. z e. S A. y e. S ( z C_ y -> ( G gsum ( F |` y ) ) e. u ) ) ) ) )

  proof
    wph
    cC
    cG
    cF
    ctsu
    co
    #
    wcel
    cC
    vy
    cS
    cG
    cF
    vy
    cv
    #
    cres
    #
    cgsu
    co
    #
    cmpt
    #
    cJ
    cS
    vz
    cS
    vz
    cv
    @1
    wss
    #
    vy
    cS
    crab
    #
    cmpt
    #
    crn
    #
    cfg
    co
    #
    cflf
    co
    cfv
    #
    wcel
    #
    cC
    cB
    wcel
    #
    cC
    vu
    cv
    #
    wcel
    #
    @4
    vw
    cv
    #
    cima
    #
    @13
    wss
    #
    vw
    @8
    wrex
    #
    wi
    #
    vu
    cJ
    wral
    #
    wa
    #
    @12
    @14
    @5
    @3
    @13
    wcel
    #
    wi
    vy
    cS
    wral
    #
    vz
    cS
    wrex
    #
    wi
    #
    vu
    cJ
    wral
    #
    wa
    wph
    @0
    @10
    cC
    wph
    vy
    vz
    cA
    cB
    cS
    cF
    cG
    cJ
    @8
    ccmn
    cV
    eltsms.b
    eltsms.j
    eltsms.s
    @8
    eqid
    #
    eltsms.1
    eltsms.a
    eltsms.f
    tsmsval
    eleq2d
    wph
    cJ
    cB
    ctopon
    cfv
    wcel
    #
    @8
    cS
    cfbas
    cfv
    wcel
    cS
    cB
    @4
    wf
    @11
    @21
    wb
    wph
    cG
    ctps
    wcel
    @28
    eltsms.2
    cB
    cJ
    cG
    eltsms.b
    eltsms.j
    istps
    sylib
    wph
    vy
    vz
    cA
    cS
    @7
    @8
    cV
    eltsms.s
    @7
    eqid
    #
    @27
    eltsms.a
    tsmsfbas
    wph
    vy
    cS
    @3
    cB
    @4
    wph
    cA
    cB
    cS
    cF
    cG
    cV
    @1
    eltsms.b
    eltsms.s
    eltsms.1
    eltsms.a
    eltsms.f
    tsmslem1
    @4
    eqid
    #
    fmptd
    cC
    @8
    vu
    @4
    cJ
    @9
    cB
    cS
    vw
    @9
    eqid
    flffbas
    syl3anc
    wph
    @20
    @26
    @12
    wph
    @19
    @25
    vu
    cJ
    wph
    @13
    cJ
    wcel
    #
    wa
    #
    @18
    @24
    @14
    @32
    @18
    @4
    @6
    cima
    #
    @13
    wss
    #
    vz
    cS
    wrex
    #
    @24
    @32
    @6
    cvv
    wcel
    #
    vz
    cS
    wral
    @18
    @35
    wb
    @32
    @36
    vz
    cS
    @32
    cS
    cvv
    wcel
    #
    @36
    wph
    @37
    @31
    wph
    cS
    cA
    cpw
    #
    cfn
    cin
    #
    cvv
    eltsms.s
    wph
    cA
    cV
    wcel
    @38
    cvv
    wcel
    @39
    cvv
    wcel
    eltsms.a
    cA
    cV
    pwexg
    @38
    cfn
    cvv
    inex1g
    3syl
    syl5eqel
    adantr
    @5
    vy
    cS
    cvv
    rabexg
    syl
    ralrimivw
    @17
    @34
    vz
    vw
    cS
    @6
    @7
    cvv
    @29
    @15
    @6
    wceq
    @16
    @33
    @13
    @15
    @6
    @4
    imaeq2
    sseq1d
    rexrnmpt
    syl
    @34
    @23
    vz
    cS
    @34
    @6
    @4
    ccnv
    @13
    cima
    #
    wss
    #
    @6
    @22
    vy
    cS
    crab
    #
    wss
    @23
    @4
    wfun
    @6
    @4
    cdm
    #
    wss
    @34
    @41
    wb
    vy
    cS
    @3
    funmpt
    @6
    cS
    @43
    @5
    vy
    cS
    ssrab2
    vy
    cS
    @3
    @4
    cG
    @2
    cgsu
    ovex
    @30
    dmmpti
    sseqtr4i
    @6
    @13
    @4
    funimass3
    mp2an
    @40
    @42
    @6
    vy
    cS
    @3
    @13
    @4
    @30
    mptpreima
    sseq2i
    @5
    @22
    vy
    cS
    ss2rab
    3bitri
    rexbii
    syl6bb
    imbi2d
    ralbidva
    anbi2d
    3bitrd
end

include "cr.mm"
include "cres.mm"
include "cv.mm"
include "cpnf.mm"
include "cico.mm"
include "co.mm"
include "cima.mm"
include "cxr.mm"
include "cin.mm"
include "clt.mm"
include "csup.mm"
include "cmpt.mm"
include "crn.mm"
include "cinf.mm"
include "clsp.mm"
include "cfv.mm"
include "wss.mm"
include "resimass.mm"
include "a1i.mm"
include "ssrind.mm"
include "wcel.mm"
include "wral.mm"
include "wa.mm"
include "wceq.mm"
include "cdm.mm"
include "wrex.mm"
include "wfn.mm"
include "funfnd.mm"
include "elinel1.mm"
include "fvelima2.mm"
include "syl2an.mm"
include "w3a.mm"
include "ccnv.mm"
include "3ad2ant2.mm"
include "simpr.mm"
include "elinel2.mm"
include "adantr.mm"
include "eqeltrd.mm"
include "3adant2.mm"
include "jca.mm"
include "3adant1l.mm"
include "wb.mm"
include "simp1l.mm"
include "elpreima.mm"
include "syl.mm"
include "mpbird.mm"
include "syl6eleqr.mm"
include "3expa.mm"
include "fvresd.mm"
include "eqtr2d.mm"
include "wfun.mm"
include "simplll.mm"
include "funresd.mm"
include "ad2antlr.mm"
include "elind.mm"
include "dmres.mm"
include "funfvima.mm"
include "sylc.mm"
include "rexlimdva2.mm"
include "mpd.mm"
include "ralrimiva.mm"
include "dfss3.mm"
include "sylibr.mm"
include "inss2.mm"
include "ssind.mm"
include "eqssd.mm"
include "supeq1d.mm"
include "mpteq2dv.mm"
include "rneqd.mm"
include "infeq1d.mm"
include "cvv.mm"
include "resexd.mm"
include "eqid.mm"
include "limsupval.mm"
include "3eqtr4d.mm"

theorem limsupresxr
  let wph: wff ph
  let cA: class A
  let cF: class F
  let cV: class V
  let vk: setvar k
  let vx: setvar x
  let vy: setvar y
  assume limsupresxr.1: |- ( ph -> F e. V )
  assume limsupresxr.2: |- ( ph -> Fun F )
  assume limsupresxr.3: |- A = ( `' F " RR* )


  assert |- ( ph -> ( limsup ` ( F |` A ) ) = ( limsup ` F ) )

  proof
    wph
    vk
    cr
    cF
    cA
    cres
    #
    vk
    cv
    cpnf
    cico
    co
    #
    cima
    #
    cxr
    cin
    #
    cxr
    clt
    csup
    #
    cmpt
    #
    crn
    #
    cxr
    clt
    cinf
    #
    vk
    cr
    cF
    @1
    cima
    #
    cxr
    cin
    #
    cxr
    clt
    csup
    #
    cmpt
    #
    crn
    #
    cxr
    clt
    cinf
    #
    @0
    clsp
    cfv
    #
    cF
    clsp
    cfv
    #
    wph
    cxr
    @6
    @12
    clt
    wph
    @5
    @11
    wph
    vk
    cr
    @4
    @10
    wph
    cxr
    @3
    @9
    clt
    wph
    @3
    @9
    wph
    @2
    @8
    cxr
    @2
    @8
    wss
    wph
    cF
    cA
    @1
    resimass
    a1i
    ssrind
    wph
    @9
    @2
    cxr
    wph
    vy
    cv
    #
    @2
    wcel
    #
    vy
    @9
    wral
    @9
    @2
    wss
    wph
    @17
    vy
    @9
    wph
    @16
    @9
    wcel
    #
    wa
    #
    vx
    cv
    #
    cF
    cfv
    #
    @16
    wceq
    #
    vx
    cF
    cdm
    #
    @1
    cin
    #
    wrex
    #
    @17
    wph
    cF
    @23
    wfn
    #
    @16
    @8
    wcel
    @25
    @18
    wph
    cF
    limsupresxr.2
    funfnd
    #
    @16
    @8
    cxr
    elinel1
    vx
    @23
    @16
    @1
    cF
    fvelima2
    syl2an
    @19
    @22
    @17
    vx
    @24
    @19
    @20
    @24
    wcel
    #
    wa
    #
    @22
    wa
    #
    @16
    @20
    @0
    cfv
    #
    @2
    @30
    @31
    @21
    @16
    @30
    @20
    cA
    cF
    @19
    @28
    @22
    @20
    cA
    wcel
    @19
    @28
    @22
    w3a
    #
    @20
    cF
    ccnv
    cxr
    cima
    #
    cA
    @32
    @20
    @33
    wcel
    #
    @20
    @23
    wcel
    #
    @21
    cxr
    wcel
    #
    wa
    #
    @18
    @28
    @22
    @37
    wph
    @18
    @28
    @22
    w3a
    @35
    @36
    @28
    @18
    @35
    @22
    @20
    @23
    @1
    elinel1
    #
    3ad2ant2
    @18
    @22
    @36
    @28
    @18
    @22
    wa
    @21
    @16
    cxr
    @18
    @22
    simpr
    @18
    @16
    cxr
    wcel
    @22
    @16
    @8
    cxr
    elinel2
    adantr
    eqeltrd
    3adant2
    jca
    3adant1l
    @32
    wph
    @34
    @37
    wb
    #
    wph
    @18
    @28
    @22
    simp1l
    wph
    @26
    @39
    @27
    @23
    @20
    cxr
    cF
    elpreima
    syl
    syl
    mpbird
    limsupresxr.3
    syl6eleqr
    3expa
    #
    fvresd
    @29
    @22
    simpr
    eqtr2d
    @30
    @0
    wfun
    #
    @20
    @0
    cdm
    #
    wcel
    #
    wa
    @20
    @1
    wcel
    #
    @31
    @2
    wcel
    @30
    @41
    @43
    @30
    wph
    @41
    wph
    @18
    @28
    @22
    simplll
    wph
    cA
    cF
    limsupresxr.2
    funresd
    syl
    @30
    @20
    cA
    @23
    cin
    @42
    @30
    cA
    @23
    @20
    @40
    @28
    @35
    @19
    @22
    @38
    ad2antlr
    elind
    cF
    cA
    dmres
    syl6eleqr
    jca
    @28
    @44
    @19
    @22
    @20
    @23
    @1
    elinel2
    ad2antlr
    @1
    @20
    @0
    funfvima
    sylc
    eqeltrd
    rexlimdva2
    mpd
    ralrimiva
    vy
    @9
    @2
    dfss3
    sylibr
    @9
    cxr
    wss
    wph
    @8
    cxr
    inss2
    a1i
    ssind
    eqssd
    supeq1d
    mpteq2dv
    rneqd
    infeq1d
    wph
    @0
    cvv
    wcel
    @14
    @7
    wceq
    wph
    cF
    cA
    cV
    limsupresxr.1
    resexd
    vk
    @0
    @5
    cvv
    @5
    eqid
    limsupval
    syl
    wph
    cF
    cV
    wcel
    @15
    @13
    wceq
    limsupresxr.1
    vk
    cF
    @11
    cV
    @11
    eqid
    limsupval
    syl
    3eqtr4d
end

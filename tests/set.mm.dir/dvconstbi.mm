include "cdv.mm"
include "co.mm"
include "cc0.mm"
include "csn.mm"
include "cxp.mm"
include "wceq.mm"
include "cv.mm"
include "cc.mm"
include "wrex.mm"
include "wa.mm"
include "cfv.mm"
include "wcel.mm"
include "wf.mm"
include "cr.mm"
include "wo.mm"
include "cpr.mm"
include "elpri.mm"
include "syl.mm"
include "0re.mm"
include "eleq2.mm"
include "mpbiri.mm"
include "0cn.mm"
include "jaoi.mm"
include "ffvelrn.mm"
include "syl2anc.mm"
include "adantr.mm"
include "wfn.mm"
include "ffn.mm"
include "cvv.mm"
include "fvex.mm"
include "fnconstg.mm"
include "mp1i.mm"
include "fvconst2.mm"
include "adantl.mm"
include "w3a.mm"
include "cmin.mm"
include "cabs.mm"
include "cle.mm"
include "wbr.mm"
include "cmul.mm"
include "cpnf.mm"
include "ccom.mm"
include "cres.mm"
include "cbl.mm"
include "eqid.mm"
include "sblpnf.mm"
include "mpdan.mm"
include "eleq2d.mm"
include "biimpar.mm"
include "eleqtrrd.mm"
include "wss.mm"
include "ssid.mm"
include "a1i.mm"
include "cxr.mm"
include "pnfxr.mm"
include "cdm.mm"
include "eqtr4d.mm"
include "eqimss.mm"
include "biimpa.mm"
include "3adant2.mm"
include "fveq1.mm"
include "c0ex.mm"
include "sylan9eq.mm"
include "syl6eqel.mm"
include "abscld.mm"
include "abs00bd.mm"
include "eqle.mm"
include "3adant1.mm"
include "syld3an3.mm"
include "3expa.mm"
include "dvlip2.mm"
include "sylanr1.mm"
include "3impdi.mm"
include "syl3an3.mm"
include "recnprss.mm"
include "sseld.mm"
include "subcl.mm"
include "mpan.mm"
include "syl6.mm"
include "imp.mm"
include "recnd.mm"
include "mul02d.mm"
include "breqtrd.mm"
include "anim12dan.mm"
include "sylan.mm"
include "3impb.mm"
include "syl3an2.mm"
include "3anidm12.mm"
include "absge0d.mm"
include "wb.mm"
include "letri3.mm"
include "sylancl.mm"
include "mpbir2and.mm"
include "abs00ad.mm"
include "mpbid.mm"
include "subeq0.mm"
include "eqtr2d.mm"
include "eqfnfvd.mm"
include "sneq.mm"
include "xpeq2d.mm"
include "eqeq2d.mm"
include "rspcev.mm"
include "ex.mm"
include "oveq2.mm"
include "3ad2ant3.mm"
include "dvsconst.mm"
include "3adant3.mm"
include "eqtrd.mm"
include "rexlimdv3a.mm"
include "impbid.mm"
include "cbvrexv.mm"
include "syl6bbr.mm"

theorem dvconstbi
  let wph: wff ph
  let cS: class S
  let cY: class Y
  let vc: setvar c
  let vx: setvar x
  let vy: setvar y
  assume dvconstbi.s: |- ( ph -> S e. { RR , CC } )
  assume dvconstbi.y: |- ( ph -> Y : S --> CC )
  assume dvconstbi.dy: |- ( ph -> dom ( S _D Y ) = S )

  disjoint S c
  disjoint Y c
  disjoint c x
  disjoint S x
  disjoint Y x
  disjoint x y
  disjoint S y
  disjoint ph x
  disjoint ph y
  disjoint Y y
  assert |- ( ph -> ( ( S _D Y ) = ( S X. { 0 } ) <-> E. c e. CC Y = ( S X. { c } ) ) )

  proof
    wph
    cS
    cY
    cdv
    co
    #
    cS
    cc0
    csn
    cxp
    #
    wceq
    #
    cY
    cS
    vx
    cv
    #
    csn
    #
    cxp
    #
    wceq
    #
    vx
    cc
    wrex
    #
    cY
    cS
    vc
    cv
    #
    csn
    #
    cxp
    #
    wceq
    #
    vc
    cc
    wrex
    wph
    @2
    @7
    wph
    @2
    @7
    wph
    @2
    wa
    #
    cc0
    cY
    cfv
    #
    cc
    wcel
    #
    cY
    cS
    @13
    csn
    #
    cxp
    #
    wceq
    #
    @7
    wph
    @14
    @2
    wph
    cS
    cc
    cY
    wf
    #
    cc0
    cS
    wcel
    #
    @14
    dvconstbi.y
    wph
    cS
    cr
    wceq
    #
    cS
    cc
    wceq
    #
    wo
    #
    @19
    wph
    cS
    cr
    cc
    cpr
    wcel
    #
    @22
    dvconstbi.s
    cS
    cr
    cc
    elpri
    syl
    @20
    @19
    @21
    @20
    @19
    cc0
    cr
    wcel
    #
    0re
    cS
    cr
    cc0
    eleq2
    mpbiri
    @21
    @19
    cc0
    cc
    wcel
    #
    0cn
    cS
    cc
    cc0
    eleq2
    mpbiri
    jaoi
    syl
    #
    cS
    cc
    cc0
    cY
    ffvelrn
    #
    syl2anc
    adantr
    @12
    vy
    cS
    cY
    @16
    wph
    cY
    cS
    wfn
    #
    @2
    wph
    @18
    @28
    dvconstbi.y
    cS
    cc
    cY
    ffn
    syl
    adantr
    @13
    cvv
    wcel
    @16
    cS
    wfn
    @12
    cc0
    cY
    fvex
    #
    cS
    @13
    cvv
    fnconstg
    mp1i
    @12
    vy
    cv
    #
    cS
    wcel
    #
    wa
    @30
    @16
    cfv
    #
    @13
    @30
    cY
    cfv
    #
    @31
    @32
    @13
    wceq
    @12
    cS
    @13
    @30
    @29
    fvconst2
    adantl
    wph
    @2
    @31
    @13
    @33
    wceq
    #
    wph
    @2
    @31
    w3a
    #
    @13
    @33
    cmin
    co
    #
    cc0
    wceq
    #
    @34
    @35
    @36
    cabs
    cfv
    #
    cc0
    wceq
    #
    @37
    @35
    @39
    @38
    cc0
    cle
    wbr
    #
    cc0
    @38
    cle
    wbr
    #
    @35
    @38
    cc0
    cc0
    @30
    cmin
    co
    #
    cabs
    cfv
    #
    cmul
    co
    #
    cc0
    cle
    wph
    @2
    @31
    @38
    @44
    cle
    wbr
    #
    wph
    @2
    wph
    @31
    wa
    #
    @45
    @46
    wph
    @2
    @30
    cc0
    cpnf
    cabs
    cmin
    ccom
    cS
    cS
    cxp
    cres
    #
    cbl
    cfv
    co
    #
    wcel
    #
    @45
    wph
    @49
    @31
    wph
    @48
    cS
    @30
    wph
    @19
    @48
    cS
    wceq
    #
    @26
    wph
    @47
    cc0
    cS
    dvconstbi.s
    @47
    eqid
    #
    sblpnf
    mpdan
    #
    eleq2d
    biimpar
    wph
    @2
    @49
    @45
    wph
    @12
    cc0
    @48
    wcel
    @49
    @45
    wph
    cc0
    cS
    @48
    @26
    @52
    eleqtrrd
    @12
    vx
    cc0
    @48
    cpnf
    cS
    cY
    @47
    cc0
    cS
    cc0
    @30
    wph
    @23
    @2
    dvconstbi.s
    adantr
    @51
    cS
    cS
    wss
    @12
    cS
    ssid
    a1i
    wph
    @18
    @2
    dvconstbi.y
    adantr
    wph
    @19
    @2
    @26
    adantr
    cpnf
    cxr
    wcel
    @12
    pnfxr
    a1i
    @48
    eqid
    @12
    @48
    @0
    cdm
    #
    wceq
    @48
    @53
    wss
    @12
    @48
    cS
    @53
    wph
    @50
    @2
    @52
    adantr
    wph
    @53
    cS
    wceq
    @2
    dvconstbi.dy
    adantr
    eqtr4d
    @48
    @53
    eqimss
    syl
    @24
    @12
    0re
    a1i
    wph
    @2
    @3
    @48
    wcel
    #
    @3
    @0
    cfv
    #
    cabs
    cfv
    #
    cc0
    cle
    wbr
    #
    wph
    @2
    @54
    @3
    cS
    wcel
    #
    @57
    wph
    @54
    @58
    @2
    wph
    @54
    @58
    wph
    @48
    cS
    @3
    @52
    eleq2d
    biimpa
    3adant2
    @2
    @58
    @57
    wph
    @2
    @58
    wa
    #
    @56
    cr
    wcel
    @56
    cc0
    wceq
    @57
    @59
    @55
    @59
    @55
    cc0
    cc
    @2
    @58
    @55
    @3
    @1
    cfv
    cc0
    @3
    @0
    @1
    fveq1
    cS
    cc0
    @3
    c0ex
    fvconst2
    sylan9eq
    #
    0cn
    syl6eqel
    abscld
    @59
    @55
    @60
    abs00bd
    @56
    cc0
    eqle
    syl2anc
    3adant1
    syld3an3
    3expa
    dvlip2
    sylanr1
    3impdi
    syl3an3
    3expa
    3impdi
    wph
    @31
    @44
    cc0
    wceq
    @2
    @46
    @43
    @46
    @43
    wph
    @31
    @43
    cr
    wcel
    #
    wph
    @31
    @30
    cc
    wcel
    #
    @61
    wph
    cS
    cc
    @30
    wph
    @23
    cS
    cc
    wss
    dvconstbi.s
    cS
    recnprss
    syl
    sseld
    @25
    @62
    @61
    0cn
    @25
    @62
    wa
    @42
    cc0
    @30
    subcl
    abscld
    mpan
    syl6
    imp
    recnd
    mul02d
    3adant2
    breqtrd
    wph
    @31
    @41
    @2
    @46
    @36
    @46
    @14
    @33
    cc
    wcel
    #
    wa
    #
    @36
    cc
    wcel
    wph
    @31
    @64
    wph
    wph
    @19
    @31
    @64
    @26
    wph
    @19
    @31
    @64
    wph
    @18
    @19
    @31
    wa
    @64
    dvconstbi.y
    @18
    @19
    @14
    @31
    @63
    @27
    cS
    cc
    @30
    cY
    ffvelrn
    anim12dan
    sylan
    3impb
    syl3an2
    3anidm12
    #
    @13
    @33
    subcl
    syl
    #
    absge0d
    3adant2
    wph
    @31
    @39
    @40
    @41
    wa
    wb
    #
    @2
    @46
    @38
    cr
    wcel
    @24
    @67
    @46
    @36
    @66
    abscld
    0re
    @38
    cc0
    letri3
    sylancl
    3adant2
    mpbir2and
    wph
    @31
    @39
    @37
    wb
    @2
    @46
    @36
    @66
    abs00ad
    3adant2
    mpbid
    wph
    @31
    @37
    @34
    wb
    #
    @2
    @46
    @64
    @68
    @65
    @13
    @33
    subeq0
    syl
    3adant2
    mpbid
    3expa
    eqtr2d
    eqfnfvd
    @6
    @17
    vx
    @13
    cc
    @3
    @13
    wceq
    #
    @5
    @16
    cY
    @69
    @4
    @15
    cS
    @3
    @13
    sneq
    xpeq2d
    eqeq2d
    rspcev
    syl2anc
    ex
    wph
    @6
    @2
    vx
    cc
    wph
    @3
    cc
    wcel
    #
    @6
    w3a
    @0
    cS
    @5
    cdv
    co
    #
    @1
    @6
    wph
    @0
    @71
    wceq
    @70
    cY
    @5
    cS
    cdv
    oveq2
    3ad2ant3
    wph
    @70
    @71
    @1
    wceq
    #
    @6
    wph
    @23
    @70
    @72
    dvconstbi.s
    @3
    cS
    dvsconst
    sylan
    3adant3
    eqtrd
    rexlimdv3a
    impbid
    @11
    @6
    vc
    vx
    cc
    @8
    @3
    wceq
    #
    @10
    @5
    cY
    @73
    @9
    @4
    cS
    @8
    @3
    sneq
    xpeq2d
    eqeq2d
    cbvrexv
    syl6bbr
end

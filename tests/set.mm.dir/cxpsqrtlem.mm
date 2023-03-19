include "cc.mm"
include "wcel.mm"
include "cc0.mm"
include "wne.mm"
include "wa.mm"
include "c1.mm"
include "c2.mm"
include "cdiv.mm"
include "co.mm"
include "ccxp.mm"
include "csqrt.mm"
include "cfv.mm"
include "cneg.mm"
include "wceq.mm"
include "ci.mm"
include "cmul.mm"
include "ax-icn.mm"
include "sqrtcl.mm"
include "ad2antrr.mm"
include "mulcl.mm"
include "sylancr.mm"
include "cim.mm"
include "cre.mm"
include "imval.mm"
include "syl.mm"
include "ine0.mm"
include "divcan3.mm"
include "mp3an23.mm"
include "fveq2d.mm"
include "cle.mm"
include "wbr.mm"
include "clog.mm"
include "ce.mm"
include "ccos.mm"
include "halfre.mm"
include "recni.mm"
include "logcl.mm"
include "recld.mm"
include "reefcld.mm"
include "imcld.mm"
include "recoscld.mm"
include "rpefcld.mm"
include "rpge0d.mm"
include "cpi.mm"
include "cicc.mm"
include "cr.mm"
include "immul2.mm"
include "recnd.mm"
include "mulcom.mm"
include "eqtrd.mm"
include "clt.mm"
include "logimcl.mm"
include "simpld.mm"
include "wi.mm"
include "pire.mm"
include "renegcli.mm"
include "ltle.mm"
include "mpd.mm"
include "simprd.mm"
include "elicc2i.mm"
include "syl3anbrc.mm"
include "halfgt0.mm"
include "elrpii.mm"
include "2cn.mm"
include "2ne0.mm"
include "divneg.mm"
include "mp3an.mm"
include "divreci.mm"
include "eqtr2i.mm"
include "eqcomi.mm"
include "iccdili.mm"
include "eqeltrd.mm"
include "cosq14ge0.mm"
include "mulge0d.mm"
include "csin.mm"
include "caddc.mm"
include "cxpef.mm"
include "mp3an3.mm"
include "efeul.mm"
include "resincld.mm"
include "addcld.mm"
include "remul2d.mm"
include "crred.mm"
include "oveq2d.mm"
include "3eqtrd.mm"
include "breqtrrd.mm"
include "adantr.mm"
include "simpr.mm"
include "renegd.mm"
include "breqtrd.mm"
include "le0neg1d.mm"
include "mpbird.mm"
include "sqrtrege0.mm"
include "wb.mm"
include "0re.mm"
include "letri3.mm"
include "sylancl.mm"
include "mpbir2and.mm"
include "reim0bd.mm"

theorem cxpsqrtlem
  let cA: class A


  assert |- ( ( ( A e. CC /\ A =/= 0 ) /\ ( A ^c ( 1 / 2 ) ) = -u ( sqrt ` A ) ) -> ( _i x. ( sqrt ` A ) ) e. RR )

  proof
    cA
    cc
    wcel
    #
    cA
    cc0
    wne
    #
    wa
    #
    cA
    c1
    c2
    cdiv
    co
    #
    ccxp
    co
    #
    cA
    csqrt
    cfv
    #
    cneg
    #
    wceq
    #
    wa
    #
    ci
    @5
    cmul
    co
    #
    @8
    ci
    cc
    wcel
    #
    @5
    cc
    wcel
    #
    @9
    cc
    wcel
    #
    ax-icn
    @0
    @11
    @1
    @7
    cA
    sqrtcl
    ad2antrr
    #
    ci
    @5
    mulcl
    sylancr
    #
    @8
    @9
    cim
    cfv
    #
    @9
    ci
    cdiv
    co
    #
    cre
    cfv
    #
    @5
    cre
    cfv
    #
    cc0
    @8
    @12
    @15
    @17
    wceq
    @14
    @9
    imval
    syl
    @8
    @16
    @5
    cre
    @8
    @11
    @16
    @5
    wceq
    #
    @13
    @11
    @10
    ci
    cc0
    wne
    @19
    ax-icn
    ine0
    @5
    ci
    divcan3
    mp3an23
    syl
    fveq2d
    @8
    @18
    cc0
    wceq
    #
    @18
    cc0
    cle
    wbr
    #
    cc0
    @18
    cle
    wbr
    #
    @8
    @21
    cc0
    @18
    cneg
    #
    cle
    wbr
    @8
    cc0
    @4
    cre
    cfv
    #
    @23
    cle
    @2
    cc0
    @24
    cle
    wbr
    @7
    @2
    cc0
    @3
    cA
    clog
    cfv
    #
    cmul
    co
    #
    cre
    cfv
    #
    ce
    cfv
    #
    @26
    cim
    cfv
    #
    ccos
    cfv
    #
    cmul
    co
    #
    @24
    cle
    @2
    @28
    @30
    @2
    @27
    @2
    @26
    @2
    @3
    cc
    wcel
    #
    @25
    cc
    wcel
    #
    @26
    cc
    wcel
    #
    @3
    halfre
    recni
    #
    cA
    logcl
    #
    @3
    @25
    mulcl
    sylancr
    #
    recld
    #
    reefcld
    #
    @2
    @29
    @2
    @26
    @37
    imcld
    #
    recoscld
    #
    @2
    @28
    @2
    @27
    @38
    rpefcld
    rpge0d
    @2
    @29
    cpi
    c2
    cdiv
    co
    #
    cneg
    #
    @42
    cicc
    co
    #
    wcel
    cc0
    @30
    cle
    wbr
    @2
    @29
    @25
    cim
    cfv
    #
    @3
    cmul
    co
    #
    @44
    @2
    @29
    @3
    @45
    cmul
    co
    #
    @46
    @2
    @3
    cr
    wcel
    @33
    @29
    @47
    wceq
    halfre
    @36
    @3
    @25
    immul2
    sylancr
    @2
    @32
    @45
    cc
    wcel
    @47
    @46
    wceq
    @35
    @2
    @45
    @2
    @25
    @36
    imcld
    #
    recnd
    @3
    @45
    mulcom
    sylancr
    eqtrd
    @2
    @45
    cpi
    cneg
    #
    cpi
    cicc
    co
    wcel
    #
    @46
    @44
    wcel
    @2
    @45
    cr
    wcel
    #
    @49
    @45
    cle
    wbr
    #
    @45
    cpi
    cle
    wbr
    #
    @50
    @48
    @2
    @49
    @45
    clt
    wbr
    #
    @52
    @2
    @54
    @53
    cA
    logimcl
    #
    simpld
    @2
    @49
    cr
    wcel
    @51
    @54
    @52
    wi
    cpi
    pire
    renegcli
    #
    @48
    @49
    @45
    ltle
    sylancr
    mpd
    @2
    @54
    @53
    @55
    simprd
    @49
    cpi
    @45
    @56
    pire
    elicc2i
    syl3anbrc
    @49
    cpi
    @43
    @42
    @3
    @45
    @56
    pire
    @3
    halfre
    halfgt0
    elrpii
    @43
    @49
    c2
    cdiv
    co
    #
    @49
    @3
    cmul
    co
    cpi
    cc
    wcel
    c2
    cc
    wcel
    c2
    cc0
    wne
    @43
    @57
    wceq
    cpi
    pire
    recni
    #
    2cn
    2ne0
    cpi
    c2
    divneg
    mp3an
    @49
    c2
    @49
    @56
    recni
    2cn
    2ne0
    divreci
    eqtr2i
    @42
    cpi
    @3
    cmul
    co
    cpi
    c2
    @58
    2cn
    2ne0
    divreci
    eqcomi
    iccdili
    syl
    eqeltrd
    @29
    cosq14ge0
    syl
    mulge0d
    @2
    @24
    @28
    @30
    ci
    @29
    csin
    cfv
    #
    cmul
    co
    #
    caddc
    co
    #
    cmul
    co
    #
    cre
    cfv
    @28
    @61
    cre
    cfv
    #
    cmul
    co
    @31
    @2
    @4
    @62
    cre
    @2
    @4
    @26
    ce
    cfv
    #
    @62
    @0
    @1
    @32
    @4
    @64
    wceq
    @35
    cA
    @3
    cxpef
    mp3an3
    @2
    @34
    @64
    @62
    wceq
    @37
    @26
    efeul
    syl
    eqtrd
    fveq2d
    @2
    @28
    @61
    @39
    @2
    @30
    @60
    @2
    @30
    @41
    recnd
    @2
    @10
    @59
    cc
    wcel
    @60
    cc
    wcel
    ax-icn
    @2
    @59
    @2
    @29
    @40
    resincld
    #
    recnd
    ci
    @59
    mulcl
    sylancr
    addcld
    remul2d
    @2
    @63
    @30
    @28
    cmul
    @2
    @30
    @59
    @41
    @65
    crred
    oveq2d
    3eqtrd
    breqtrrd
    adantr
    @8
    @24
    @6
    cre
    cfv
    @23
    @8
    @4
    @6
    cre
    @2
    @7
    simpr
    fveq2d
    @8
    @5
    @13
    renegd
    eqtrd
    breqtrd
    @8
    @18
    @8
    @5
    @13
    recld
    #
    le0neg1d
    mpbird
    @0
    @22
    @1
    @7
    cA
    sqrtrege0
    ad2antrr
    @8
    @18
    cr
    wcel
    cc0
    cr
    wcel
    @20
    @21
    @22
    wa
    wb
    @66
    0re
    @18
    cc0
    letri3
    sylancl
    mpbir2and
    3eqtrd
    reim0bd
end

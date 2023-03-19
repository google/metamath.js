include "cc.mm"
include "wcel.mm"
include "c1.mm"
include "c2.mm"
include "cdiv.mm"
include "co.mm"
include "ccxp.mm"
include "csqrt.mm"
include "cfv.mm"
include "wceq.mm"
include "cc0.mm"
include "wi.mm"
include "wne.mm"
include "halfcn.mm"
include "halfre.mm"
include "halfgt0.mm"
include "gt0ne0ii.mm"
include "0cxp.mm"
include "mp2an.mm"
include "sqrt0.mm"
include "eqtr4i.mm"
include "oveq1.mm"
include "fveq2.mm"
include "3eqtr4a.mm"
include "a1i.mm"
include "wa.mm"
include "cneg.mm"
include "clog.mm"
include "cmul.mm"
include "ce.mm"
include "ci.mm"
include "cpi.mm"
include "caddc.mm"
include "crp.mm"
include "cexp.mm"
include "cr.mm"
include "ax-icn.mm"
include "sqrtcl.mm"
include "ad2antrr.mm"
include "sqmul.mm"
include "sylancr.mm"
include "i2.mm"
include "sqrtth.mm"
include "oveq12d.mm"
include "mulm1.mm"
include "3eqtrd.mm"
include "cxpsqrtlem.mm"
include "resqcld.mm"
include "eqeltrrd.mm"
include "clt.mm"
include "negeq0.mm"
include "necon3bid.mm"
include "biimpa.mm"
include "adantr.mm"
include "eqnetrd.mm"
include "sq0i.mm"
include "necon3i.mm"
include "syl.mm"
include "sqgt0d.mm"
include "breqtrd.mm"
include "elrpd.mm"
include "logneg.mm"
include "negneg.mm"
include "fveq2d.mm"
include "relogcld.mm"
include "recnd.mm"
include "picn.mm"
include "mulcli.mm"
include "addcom.mm"
include "sylancl.mm"
include "3eqtr3d.mm"
include "oveq2d.mm"
include "adddi.mm"
include "mp3an12.mm"
include "eqtrd.mm"
include "2cn.mm"
include "2ne0.mm"
include "divrec2.mm"
include "mp3an.mm"
include "divassi.mm"
include "eqtr3i.mm"
include "oveq1i.mm"
include "syl6eq.mm"
include "divcli.mm"
include "mulcl.mm"
include "efadd.mm"
include "efhalfpi.mm"
include "negcl.mm"
include "cxpef.mm"
include "syl3anc.mm"
include "ax-1cn.mm"
include "2halves.mm"
include "ax-mp.mm"
include "oveq2i.mm"
include "cxp1.mm"
include "syl5eq.mm"
include "rpcxpcl.mm"
include "rpcnd.mm"
include "sqvald.mm"
include "cxpadd.mm"
include "syl211anc.mm"
include "eqtr4d.mm"
include "sqsqrtd.mm"
include "3eqtr4d.mm"
include "cle.mm"
include "wbr.mm"
include "wb.mm"
include "rprege0d.mm"
include "rpsqrtcld.mm"
include "sq11.mm"
include "syl2anc.mm"
include "mpbid.mm"
include "eqtr3d.mm"
include "mp3an3.mm"
include "rpge0d.mm"
include "sqrtnegd.mm"
include "ex.mm"
include "wo.mm"
include "mp3an23.mm"
include "3eqtr3a.mm"
include "cxpcl.mm"
include "mpan2.mm"
include "sqeqor.mm"
include "syldan.mm"
include "ord.mm"
include "con1d.mm"
include "pm2.61d.mm"
include "pm2.61dne.mm"

theorem cxpsqrt
  let cA: class A


  assert |- ( A e. CC -> ( A ^c ( 1 / 2 ) ) = ( sqrt ` A ) )

  proof
    cA
    cc
    wcel
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
    wceq
    #
    cA
    cc0
    cA
    cc0
    wceq
    #
    @4
    wi
    @0
    @5
    cc0
    @1
    ccxp
    co
    #
    cc0
    csqrt
    cfv
    #
    @2
    @3
    @6
    cc0
    @7
    @1
    cc
    wcel
    #
    @1
    cc0
    wne
    @6
    cc0
    wceq
    halfcn
    @1
    halfre
    halfgt0
    gt0ne0ii
    @1
    0cxp
    mp2an
    sqrt0
    eqtr4i
    cA
    cc0
    @1
    ccxp
    oveq1
    cA
    cc0
    csqrt
    fveq2
    3eqtr4a
    a1i
    @0
    cA
    cc0
    wne
    #
    @4
    @0
    @9
    wa
    #
    @2
    @3
    cneg
    wceq
    #
    @4
    @10
    @11
    @4
    @10
    @11
    wa
    #
    @1
    cA
    clog
    cfv
    #
    cmul
    co
    #
    ce
    cfv
    #
    ci
    cA
    cneg
    #
    csqrt
    cfv
    #
    cmul
    co
    #
    @2
    @3
    @12
    @15
    ci
    cpi
    c2
    cdiv
    co
    #
    cmul
    co
    #
    @1
    @16
    clog
    cfv
    #
    cmul
    co
    #
    caddc
    co
    #
    ce
    cfv
    #
    @20
    ce
    cfv
    #
    @22
    ce
    cfv
    #
    cmul
    co
    #
    @18
    @12
    @14
    @23
    ce
    @12
    @14
    @1
    ci
    cpi
    cmul
    co
    #
    cmul
    co
    #
    @22
    caddc
    co
    #
    @23
    @12
    @14
    @1
    @28
    @21
    caddc
    co
    #
    cmul
    co
    #
    @30
    @12
    @13
    @31
    @1
    cmul
    @12
    @16
    cneg
    #
    clog
    cfv
    #
    @21
    @28
    caddc
    co
    #
    @13
    @31
    @12
    @16
    crp
    wcel
    #
    @34
    @35
    wceq
    @12
    @16
    @12
    ci
    @3
    cmul
    co
    #
    c2
    cexp
    co
    #
    @16
    cr
    @12
    @38
    ci
    c2
    cexp
    co
    #
    @3
    c2
    cexp
    co
    #
    cmul
    co
    #
    c1
    cneg
    #
    cA
    cmul
    co
    #
    @16
    @12
    ci
    cc
    wcel
    @3
    cc
    wcel
    #
    @38
    @41
    wceq
    ax-icn
    @0
    @44
    @9
    @11
    cA
    sqrtcl
    #
    ad2antrr
    ci
    @3
    sqmul
    sylancr
    @12
    @39
    @42
    @40
    cA
    cmul
    @39
    @42
    wceq
    @12
    i2
    a1i
    @0
    @40
    cA
    wceq
    #
    @9
    @11
    cA
    sqrtth
    #
    ad2antrr
    oveq12d
    @0
    @43
    @16
    wceq
    @9
    @11
    cA
    mulm1
    ad2antrr
    3eqtrd
    #
    @12
    @37
    cA
    cxpsqrtlem
    #
    resqcld
    eqeltrrd
    #
    @12
    cc0
    @38
    @16
    clt
    @12
    @37
    @49
    @12
    @38
    cc0
    wne
    @37
    cc0
    wne
    @12
    @38
    @16
    cc0
    @48
    @10
    @16
    cc0
    wne
    #
    @11
    @0
    @9
    @51
    @0
    cA
    cc0
    @16
    cc0
    cA
    negeq0
    necon3bid
    biimpa
    adantr
    #
    eqnetrd
    @37
    cc0
    @38
    cc0
    @37
    sq0i
    necon3i
    syl
    sqgt0d
    @48
    breqtrd
    elrpd
    #
    @16
    logneg
    syl
    @12
    @33
    cA
    clog
    @0
    @33
    cA
    wceq
    @9
    @11
    cA
    negneg
    ad2antrr
    #
    fveq2d
    @12
    @21
    cc
    wcel
    #
    @28
    cc
    wcel
    #
    @35
    @31
    wceq
    @12
    @21
    @12
    @16
    @53
    relogcld
    recnd
    #
    ci
    cpi
    ax-icn
    picn
    mulcli
    #
    @21
    @28
    addcom
    sylancl
    3eqtr3d
    oveq2d
    @12
    @55
    @32
    @30
    wceq
    #
    @57
    @8
    @56
    @55
    @59
    halfcn
    @58
    @1
    @28
    @21
    adddi
    mp3an12
    syl
    eqtrd
    @29
    @20
    @22
    caddc
    @28
    c2
    cdiv
    co
    #
    @29
    @20
    @56
    c2
    cc
    wcel
    c2
    cc0
    wne
    @60
    @29
    wceq
    @58
    2cn
    2ne0
    @28
    c2
    divrec2
    mp3an
    ci
    cpi
    c2
    ax-icn
    picn
    2cn
    2ne0
    divassi
    eqtr3i
    oveq1i
    syl6eq
    fveq2d
    @12
    @20
    cc
    wcel
    @22
    cc
    wcel
    #
    @24
    @27
    wceq
    ci
    @19
    ax-icn
    cpi
    c2
    picn
    2cn
    2ne0
    divcli
    mulcli
    @12
    @8
    @55
    @61
    halfcn
    @57
    @1
    @21
    mulcl
    sylancr
    @20
    @22
    efadd
    sylancr
    @12
    @25
    ci
    @26
    @17
    cmul
    @25
    ci
    wceq
    @12
    efhalfpi
    a1i
    @12
    @16
    @1
    ccxp
    co
    #
    @26
    @17
    @12
    @16
    cc
    wcel
    #
    @51
    @8
    @62
    @26
    wceq
    @0
    @63
    @9
    @11
    cA
    negcl
    ad2antrr
    #
    @52
    @8
    @12
    halfcn
    a1i
    #
    @16
    @1
    cxpef
    syl3anc
    @12
    @62
    c2
    cexp
    co
    #
    @17
    c2
    cexp
    co
    #
    wceq
    #
    @62
    @17
    wceq
    #
    @12
    @16
    @1
    @1
    caddc
    co
    #
    ccxp
    co
    #
    @16
    @66
    @67
    @12
    @71
    @16
    c1
    ccxp
    co
    #
    @16
    @70
    c1
    @16
    ccxp
    c1
    cc
    wcel
    @70
    c1
    wceq
    ax-1cn
    c1
    2halves
    ax-mp
    #
    oveq2i
    @12
    @63
    @72
    @16
    wceq
    @64
    @16
    cxp1
    syl
    syl5eq
    @12
    @66
    @62
    @62
    cmul
    co
    #
    @71
    @12
    @62
    @12
    @62
    @12
    @36
    @1
    cr
    wcel
    @62
    crp
    wcel
    @53
    halfre
    @16
    @1
    rpcxpcl
    sylancl
    #
    rpcnd
    sqvald
    @12
    @63
    @51
    @8
    @8
    @71
    @74
    wceq
    @64
    @52
    @65
    @65
    @16
    @1
    @1
    cxpadd
    syl211anc
    eqtr4d
    @12
    @16
    @64
    sqsqrtd
    3eqtr4d
    @12
    @62
    cr
    wcel
    cc0
    @62
    cle
    wbr
    wa
    @17
    cr
    wcel
    cc0
    @17
    cle
    wbr
    wa
    @68
    @69
    wb
    @12
    @62
    @75
    rprege0d
    @12
    @17
    @12
    @16
    @53
    rpsqrtcld
    rprege0d
    @62
    @17
    sq11
    syl2anc
    mpbid
    eqtr3d
    oveq12d
    3eqtrd
    @10
    @2
    @15
    wceq
    #
    @11
    @0
    @9
    @8
    @76
    halfcn
    cA
    @1
    cxpef
    mp3an3
    adantr
    @12
    @33
    csqrt
    cfv
    @3
    @18
    @12
    @33
    cA
    csqrt
    @54
    fveq2d
    @12
    @16
    @50
    @12
    @16
    @53
    rpge0d
    sqrtnegd
    eqtr3d
    3eqtr4d
    ex
    @10
    @4
    @11
    @10
    @4
    @11
    @0
    @9
    @2
    c2
    cexp
    co
    #
    @40
    wceq
    #
    @4
    @11
    wo
    #
    @10
    @2
    @2
    cmul
    co
    #
    cA
    @77
    @40
    @10
    cA
    @70
    ccxp
    co
    #
    cA
    c1
    ccxp
    co
    #
    @80
    cA
    @70
    c1
    cA
    ccxp
    @73
    oveq2i
    @10
    @8
    @8
    @81
    @80
    wceq
    halfcn
    halfcn
    cA
    @1
    @1
    cxpadd
    mp3an23
    @0
    @82
    cA
    wceq
    @9
    cA
    cxp1
    adantr
    3eqtr3a
    @0
    @77
    @80
    wceq
    @9
    @0
    @2
    @0
    @8
    @2
    cc
    wcel
    #
    halfcn
    cA
    @1
    cxpcl
    mpan2
    #
    sqvald
    adantr
    @0
    @46
    @9
    @47
    adantr
    3eqtr4d
    @0
    @78
    @79
    @0
    @83
    @44
    @78
    @79
    wb
    @84
    @45
    @2
    @3
    sqeqor
    syl2anc
    biimpa
    syldan
    ord
    con1d
    pm2.61d
    ex
    pm2.61dne
end

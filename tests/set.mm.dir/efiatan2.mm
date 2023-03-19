include "catan.mm"
include "cdm.mm"
include "wcel.mm"
include "ci.mm"
include "cfv.mm"
include "cmul.mm"
include "co.mm"
include "ce.mm"
include "c1.mm"
include "c2.mm"
include "cexp.mm"
include "caddc.mm"
include "csqrt.mm"
include "cdiv.mm"
include "cc.mm"
include "ax-icn.mm"
include "atancl.mm"
include "mulcl.mm"
include "sylancr.mm"
include "efcl.mm"
include "syl.mm"
include "ax-1cn.mm"
include "cmin.mm"
include "cc0.mm"
include "wne.mm"
include "atandm2.mm"
include "simp1bi.mm"
include "sqcld.mm"
include "addcl.mm"
include "sqrtcld.mm"
include "sqsqrtd.mm"
include "atandm4.mm"
include "simprbi.mm"
include "eqnetrd.mm"
include "wb.mm"
include "sqne0.mm"
include "mpbid.mm"
include "divcan4d.mm"
include "clog.mm"
include "wceq.mm"
include "halfcn.mm"
include "logcld.mm"
include "efadd.mm"
include "syl2anc.mm"
include "2cn.mm"
include "a1i.mm"
include "simp3bi.mm"
include "subdid.mm"
include "atanval.mm"
include "oveq2d.mm"
include "mulassd.mm"
include "cneg.mm"
include "halfcl.mm"
include "ax-mp.mm"
include "mulassi.mm"
include "mul12i.mm"
include "2ne0.mm"
include "divcan2i.mm"
include "oveq2i.mm"
include "ixi.mm"
include "eqtri.mm"
include "3eqtri.mm"
include "oveq1i.mm"
include "subcl.mm"
include "simp2bi.mm"
include "subcld.mm"
include "mulm1d.mm"
include "syl5eq.mm"
include "2mulicn.mm"
include "negsubdi2d.mm"
include "3eqtr3d.mm"
include "subsubd.mm"
include "2timesd.mm"
include "oveq1d.mm"
include "pncand.mm"
include "eqtrd.mm"
include "crn.mm"
include "atanlogadd.mm"
include "logef.mm"
include "eflog.mm"
include "oveq12d.mm"
include "sq1.mm"
include "sqmul.mm"
include "i2.mm"
include "subsq.mm"
include "subneg.mm"
include "3eqtrd.mm"
include "fveq2d.mm"
include "eqtr3d.mm"
include "divcan3d.mm"
include "divrec2d.mm"
include "subaddd.mm"
include "ccxp.mm"
include "cxpefd.mm"
include "cxpsqrt.mm"

theorem efiatan2
  let cA: class A


  assert |- ( A e. dom arctan -> ( exp ` ( _i x. ( arctan ` A ) ) ) = ( ( 1 + ( _i x. A ) ) / ( sqrt ` ( 1 + ( A ^ 2 ) ) ) ) )

  proof
    cA
    catan
    cdm
    wcel
    #
    ci
    cA
    catan
    cfv
    #
    cmul
    co
    #
    ce
    cfv
    #
    c1
    cA
    c2
    cexp
    co
    #
    caddc
    co
    #
    csqrt
    cfv
    #
    cmul
    co
    #
    @6
    cdiv
    co
    @3
    c1
    ci
    cA
    cmul
    co
    #
    caddc
    co
    #
    @6
    cdiv
    co
    @0
    @3
    @6
    @0
    @2
    cc
    wcel
    #
    @3
    cc
    wcel
    @0
    ci
    cc
    wcel
    #
    @1
    cc
    wcel
    @10
    ax-icn
    cA
    atancl
    #
    ci
    @1
    mulcl
    sylancr
    #
    @2
    efcl
    syl
    @0
    @5
    @0
    c1
    cc
    wcel
    #
    @4
    cc
    wcel
    #
    @5
    cc
    wcel
    #
    ax-1cn
    @0
    cA
    @0
    cA
    cc
    wcel
    #
    c1
    @8
    cmin
    co
    #
    cc0
    wne
    #
    @9
    cc0
    wne
    #
    cA
    atandm2
    #
    simp1bi
    #
    sqcld
    #
    c1
    @4
    addcl
    sylancr
    #
    sqrtcld
    #
    @0
    @6
    c2
    cexp
    co
    #
    cc0
    wne
    #
    @6
    cc0
    wne
    #
    @0
    @26
    @5
    cc0
    @0
    @5
    @24
    sqsqrtd
    @0
    @17
    @5
    cc0
    wne
    cA
    atandm4
    simprbi
    #
    eqnetrd
    @0
    @6
    cc
    wcel
    @27
    @28
    wb
    @25
    @6
    sqne0
    syl
    mpbid
    divcan4d
    @0
    @7
    @9
    @6
    cdiv
    @0
    @3
    c1
    c2
    cdiv
    co
    #
    @5
    clog
    cfv
    #
    cmul
    co
    #
    ce
    cfv
    #
    cmul
    co
    #
    @9
    clog
    cfv
    #
    ce
    cfv
    #
    @7
    @9
    @0
    @2
    @32
    caddc
    co
    #
    ce
    cfv
    #
    @34
    @36
    @0
    @10
    @32
    cc
    wcel
    #
    @38
    @34
    wceq
    @13
    @0
    @30
    cc
    wcel
    #
    @31
    cc
    wcel
    @39
    halfcn
    @0
    @5
    @24
    @29
    logcld
    #
    @30
    @31
    mulcl
    sylancr
    #
    @2
    @32
    efadd
    syl2anc
    @0
    @37
    @35
    ce
    @0
    @35
    @2
    cmin
    co
    #
    @32
    wceq
    @37
    @35
    wceq
    @0
    c2
    @43
    cmul
    co
    #
    c2
    cdiv
    co
    @31
    c2
    cdiv
    co
    @43
    @32
    @0
    @44
    @31
    c2
    cdiv
    @0
    @44
    c2
    @35
    cmul
    co
    #
    c2
    @2
    cmul
    co
    #
    cmin
    co
    @45
    @35
    @18
    clog
    cfv
    #
    cmin
    co
    #
    cmin
    co
    #
    @31
    @0
    c2
    @35
    @2
    c2
    cc
    wcel
    #
    @0
    2cn
    a1i
    #
    @0
    @9
    @0
    @14
    @8
    cc
    wcel
    #
    @9
    cc
    wcel
    #
    ax-1cn
    @0
    @11
    @17
    @52
    ax-icn
    @22
    ci
    cA
    mulcl
    sylancr
    #
    c1
    @8
    addcl
    sylancr
    #
    @0
    @17
    @19
    @20
    @21
    simp3bi
    #
    logcld
    #
    @13
    subdid
    @0
    @46
    @48
    @45
    cmin
    @0
    c2
    ci
    cmul
    co
    #
    @1
    cmul
    co
    @58
    ci
    c2
    cdiv
    co
    #
    @47
    @35
    cmin
    co
    #
    cmul
    co
    #
    cmul
    co
    #
    @46
    @48
    @0
    @1
    @61
    @58
    cmul
    cA
    atanval
    oveq2d
    @0
    c2
    ci
    @1
    @51
    @11
    @0
    ax-icn
    a1i
    @12
    mulassd
    @0
    @58
    @59
    cmul
    co
    #
    @60
    cmul
    co
    #
    @60
    cneg
    #
    @62
    @48
    @0
    @64
    c1
    cneg
    #
    @60
    cmul
    co
    @65
    @63
    @66
    @60
    cmul
    @63
    c2
    ci
    @59
    cmul
    co
    cmul
    co
    ci
    c2
    @59
    cmul
    co
    #
    cmul
    co
    #
    @66
    c2
    ci
    @59
    2cn
    ax-icn
    @11
    @59
    cc
    wcel
    #
    ax-icn
    ci
    halfcl
    ax-mp
    #
    mulassi
    c2
    ci
    @59
    2cn
    ax-icn
    @70
    mul12i
    @68
    ci
    ci
    cmul
    co
    @66
    @67
    ci
    ci
    cmul
    ci
    c2
    ax-icn
    2cn
    2ne0
    divcan2i
    oveq2i
    ixi
    eqtri
    3eqtri
    oveq1i
    @0
    @60
    @0
    @47
    @35
    @0
    @18
    @0
    @14
    @52
    @18
    cc
    wcel
    #
    ax-1cn
    @54
    c1
    @8
    subcl
    sylancr
    #
    @0
    @17
    @19
    @20
    @21
    simp2bi
    #
    logcld
    #
    @57
    subcld
    #
    mulm1d
    syl5eq
    @0
    @58
    @59
    @60
    @58
    cc
    wcel
    @0
    2mulicn
    a1i
    @69
    @0
    @70
    a1i
    @75
    mulassd
    @0
    @47
    @35
    @74
    @57
    negsubdi2d
    3eqtr3d
    3eqtr3d
    oveq2d
    @0
    @49
    @45
    @35
    cmin
    co
    #
    @47
    caddc
    co
    @35
    @47
    caddc
    co
    #
    @31
    @0
    @45
    @35
    @47
    @0
    @50
    @35
    cc
    wcel
    #
    @45
    cc
    wcel
    2cn
    @57
    c2
    @35
    mulcl
    sylancr
    @57
    @74
    subsubd
    @0
    @76
    @35
    @47
    caddc
    @0
    @76
    @35
    @35
    caddc
    co
    #
    @35
    cmin
    co
    @35
    @0
    @45
    @79
    @35
    cmin
    @0
    @35
    @57
    2timesd
    oveq1d
    @0
    @35
    @35
    @57
    @57
    pncand
    eqtrd
    oveq1d
    @0
    @77
    ce
    cfv
    #
    clog
    cfv
    #
    @77
    @31
    @0
    @77
    clog
    crn
    wcel
    @81
    @77
    wceq
    cA
    atanlogadd
    @77
    logef
    syl
    @0
    @80
    @5
    clog
    @0
    @80
    @36
    @47
    ce
    cfv
    #
    cmul
    co
    #
    @9
    @18
    cmul
    co
    #
    @5
    @0
    @78
    @47
    cc
    wcel
    @80
    @83
    wceq
    @57
    @74
    @35
    @47
    efadd
    syl2anc
    @0
    @36
    @9
    @82
    @18
    cmul
    @0
    @53
    @20
    @36
    @9
    wceq
    @55
    @56
    @9
    eflog
    syl2anc
    #
    @0
    @71
    @19
    @82
    @18
    wceq
    @72
    @73
    @18
    eflog
    syl2anc
    oveq12d
    @0
    c1
    c2
    cexp
    co
    #
    @8
    c2
    cexp
    co
    #
    cmin
    co
    #
    c1
    @4
    cneg
    #
    cmin
    co
    #
    @84
    @5
    @0
    @86
    c1
    @87
    @89
    cmin
    @86
    c1
    wceq
    @0
    sq1
    a1i
    @0
    @87
    ci
    c2
    cexp
    co
    #
    @4
    cmul
    co
    #
    @89
    @0
    @11
    @17
    @87
    @92
    wceq
    ax-icn
    @22
    ci
    cA
    sqmul
    sylancr
    @0
    @92
    @66
    @4
    cmul
    co
    @89
    @91
    @66
    @4
    cmul
    i2
    oveq1i
    @0
    @4
    @23
    mulm1d
    syl5eq
    eqtrd
    oveq12d
    @0
    @14
    @52
    @88
    @84
    wceq
    ax-1cn
    @54
    c1
    @8
    subsq
    sylancr
    @0
    @14
    @15
    @90
    @5
    wceq
    ax-1cn
    @23
    c1
    @4
    subneg
    sylancr
    3eqtr3d
    3eqtrd
    fveq2d
    eqtr3d
    3eqtrd
    3eqtrd
    oveq1d
    @0
    @43
    c2
    @0
    @35
    @2
    @57
    @13
    subcld
    @51
    c2
    cc0
    wne
    @0
    2ne0
    a1i
    #
    divcan3d
    @0
    @31
    c2
    @41
    @51
    @93
    divrec2d
    3eqtr3d
    @0
    @35
    @2
    @32
    @57
    @13
    @42
    subaddd
    mpbid
    fveq2d
    eqtr3d
    @0
    @33
    @6
    @3
    cmul
    @0
    @5
    @30
    ccxp
    co
    #
    @33
    @6
    @0
    @5
    @30
    @24
    @29
    @40
    @0
    halfcn
    a1i
    cxpefd
    @0
    @16
    @94
    @6
    wceq
    @24
    @5
    cxpsqrt
    syl
    eqtr3d
    oveq2d
    @85
    3eqtr3d
    oveq1d
    eqtr3d
end

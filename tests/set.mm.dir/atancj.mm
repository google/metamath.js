include "cc.mm"
include "wcel.mm"
include "cre.mm"
include "cfv.mm"
include "cc0.mm"
include "wne.mm"
include "wa.mm"
include "catan.mm"
include "cdm.mm"
include "ccj.mm"
include "wceq.mm"
include "ci.mm"
include "cneg.mm"
include "simpl.mm"
include "simpr.mm"
include "fveq2.mm"
include "ax-icn.mm"
include "renegi.mm"
include "rei.mm"
include "negeqi.mm"
include "neg0.mm"
include "3eqtri.mm"
include "syl6eq.mm"
include "necon3i.mm"
include "syl.mm"
include "atandm.mm"
include "syl3anbrc.mm"
include "c2.mm"
include "cdiv.mm"
include "co.mm"
include "c1.mm"
include "cmul.mm"
include "cmin.mm"
include "clog.mm"
include "caddc.mm"
include "halfcl.mm"
include "ax-mp.mm"
include "ax-1cn.mm"
include "mulcl.mm"
include "sylancr.mm"
include "subcl.mm"
include "w3a.mm"
include "atandm2.mm"
include "sylib.mm"
include "simp2d.mm"
include "logcld.mm"
include "addcl.mm"
include "simp3d.mm"
include "subcld.mm"
include "cjmul.mm"
include "2ne0.mm"
include "2cn.mm"
include "cjdivi.mm"
include "divneg.mm"
include "mp3an.mm"
include "cji.mm"
include "cr.mm"
include "2re.mm"
include "cjre.mm"
include "oveq12i.mm"
include "eqtr4i.mm"
include "oveq1i.mm"
include "cjcld.mm"
include "mulneg12.mm"
include "syl5eq.mm"
include "cjsub.mm"
include "syl2anc.mm"
include "cim.mm"
include "imsub.mm"
include "reim.mm"
include "adantr.mm"
include "oveq2d.mm"
include "eqtr4d.mm"
include "df-neg.mm"
include "im1.mm"
include "syl6eqr.mm"
include "recl.mm"
include "recnd.mm"
include "negne0d.mm"
include "eqnetrd.mm"
include "logcj.mm"
include "1re.mm"
include "mp1i.mm"
include "cjcl.mm"
include "mulneg1.mm"
include "eqtrd.mm"
include "oveq12d.mm"
include "subneg.mm"
include "3eqtrd.mm"
include "fveq2d.mm"
include "eqtr3d.mm"
include "imadd.mm"
include "addid2d.mm"
include "3eqtr2d.mm"
include "cjadd.mm"
include "negsub.mm"
include "negeqd.mm"
include "atandmcj.mm"
include "simp3bi.mm"
include "simp2bi.mm"
include "negsubdi2d.mm"
include "atanval.mm"
include "3eqtr4d.mm"
include "jca.mm"

theorem atancj
  let cA: class A


  assert |- ( ( A e. CC /\ ( Re ` A ) =/= 0 ) -> ( A e. dom arctan /\ ( * ` ( arctan ` A ) ) = ( arctan ` ( * ` A ) ) ) )

  proof
    cA
    cc
    wcel
    #
    cA
    cre
    cfv
    #
    cc0
    wne
    #
    wa
    #
    cA
    catan
    cdm
    #
    wcel
    #
    cA
    catan
    cfv
    #
    ccj
    cfv
    #
    cA
    ccj
    cfv
    #
    catan
    cfv
    #
    wceq
    @3
    @0
    cA
    ci
    cneg
    #
    wne
    #
    cA
    ci
    wne
    #
    @5
    @0
    @2
    simpl
    #
    @3
    @2
    @11
    @0
    @2
    simpr
    #
    cA
    @10
    @1
    cc0
    cA
    @10
    wceq
    @1
    @10
    cre
    cfv
    #
    cc0
    cA
    @10
    cre
    fveq2
    @15
    ci
    cre
    cfv
    #
    cneg
    cc0
    cneg
    cc0
    ci
    ax-icn
    renegi
    @16
    cc0
    rei
    negeqi
    neg0
    3eqtri
    syl6eq
    necon3i
    syl
    @3
    @2
    @12
    @14
    cA
    ci
    @1
    cc0
    cA
    ci
    wceq
    @1
    @16
    cc0
    cA
    ci
    cre
    fveq2
    rei
    syl6eq
    necon3i
    syl
    cA
    atandm
    syl3anbrc
    #
    @3
    ci
    c2
    cdiv
    co
    #
    c1
    ci
    cA
    cmul
    co
    #
    cmin
    co
    #
    clog
    cfv
    #
    c1
    @19
    caddc
    co
    #
    clog
    cfv
    #
    cmin
    co
    #
    cmul
    co
    #
    ccj
    cfv
    #
    @18
    c1
    ci
    @8
    cmul
    co
    #
    cmin
    co
    #
    clog
    cfv
    #
    c1
    @27
    caddc
    co
    #
    clog
    cfv
    #
    cmin
    co
    #
    cmul
    co
    #
    @7
    @9
    @3
    @26
    @18
    ccj
    cfv
    #
    @24
    ccj
    cfv
    #
    cmul
    co
    #
    @18
    @35
    cneg
    #
    cmul
    co
    #
    @33
    @3
    @18
    cc
    wcel
    #
    @24
    cc
    wcel
    @26
    @36
    wceq
    ci
    cc
    wcel
    #
    @39
    ax-icn
    ci
    halfcl
    ax-mp
    #
    @3
    @21
    @23
    @3
    @20
    @3
    c1
    cc
    wcel
    #
    @19
    cc
    wcel
    #
    @20
    cc
    wcel
    #
    ax-1cn
    @3
    @40
    @0
    @43
    ax-icn
    @13
    ci
    cA
    mulcl
    sylancr
    #
    c1
    @19
    subcl
    sylancr
    #
    @3
    @0
    @20
    cc0
    wne
    #
    @22
    cc0
    wne
    #
    @3
    @5
    @0
    @47
    @48
    w3a
    @17
    cA
    atandm2
    sylib
    #
    simp2d
    logcld
    #
    @3
    @22
    @3
    @42
    @43
    @22
    cc
    wcel
    #
    ax-1cn
    @45
    c1
    @19
    addcl
    sylancr
    #
    @3
    @0
    @47
    @48
    @49
    simp3d
    logcld
    #
    subcld
    #
    @18
    @24
    cjmul
    sylancr
    @3
    @36
    @18
    cneg
    #
    @35
    cmul
    co
    #
    @38
    @34
    @55
    @35
    cmul
    @34
    ci
    ccj
    cfv
    #
    c2
    ccj
    cfv
    #
    cdiv
    co
    #
    @55
    c2
    cc0
    wne
    #
    @34
    @59
    wceq
    2ne0
    ci
    c2
    ax-icn
    2cn
    cjdivi
    ax-mp
    @55
    @10
    c2
    cdiv
    co
    #
    @59
    @40
    c2
    cc
    wcel
    @60
    @55
    @61
    wceq
    ax-icn
    2cn
    2ne0
    ci
    c2
    divneg
    mp3an
    @57
    @10
    @58
    c2
    cdiv
    cji
    c2
    cr
    wcel
    @58
    c2
    wceq
    2re
    c2
    cjre
    ax-mp
    oveq12i
    eqtr4i
    eqtr4i
    oveq1i
    @3
    @39
    @35
    cc
    wcel
    @56
    @38
    wceq
    @41
    @3
    @24
    @54
    cjcld
    @18
    @35
    mulneg12
    sylancr
    syl5eq
    @3
    @37
    @32
    @18
    cmul
    @3
    @37
    @31
    @29
    cmin
    co
    #
    cneg
    @32
    @3
    @35
    @62
    @3
    @35
    @21
    ccj
    cfv
    #
    @23
    ccj
    cfv
    #
    cmin
    co
    #
    @62
    @3
    @21
    cc
    wcel
    @23
    cc
    wcel
    @35
    @65
    wceq
    @50
    @53
    @21
    @23
    cjsub
    syl2anc
    @3
    @63
    @31
    @64
    @29
    cmin
    @3
    @20
    ccj
    cfv
    #
    clog
    cfv
    #
    @63
    @31
    @3
    @44
    @20
    cim
    cfv
    #
    cc0
    wne
    @67
    @63
    wceq
    @46
    @3
    @68
    @1
    cneg
    #
    cc0
    @3
    @68
    c1
    cim
    cfv
    #
    @1
    cmin
    co
    #
    @69
    @3
    @68
    @70
    @19
    cim
    cfv
    #
    cmin
    co
    #
    @71
    @3
    @42
    @43
    @68
    @73
    wceq
    ax-1cn
    @45
    c1
    @19
    imsub
    sylancr
    @3
    @1
    @72
    @70
    cmin
    @0
    @1
    @72
    wceq
    @2
    cA
    reim
    adantr
    #
    oveq2d
    eqtr4d
    @69
    cc0
    @1
    cmin
    co
    @71
    @1
    df-neg
    @70
    cc0
    @1
    cmin
    im1
    oveq1i
    eqtr4i
    syl6eqr
    @3
    @1
    @3
    @1
    @0
    @1
    cr
    wcel
    @2
    cA
    recl
    adantr
    recnd
    #
    @14
    negne0d
    eqnetrd
    @20
    logcj
    syl2anc
    @3
    @66
    @30
    clog
    @3
    @66
    c1
    ccj
    cfv
    #
    @19
    ccj
    cfv
    #
    cmin
    co
    #
    c1
    @27
    cneg
    #
    cmin
    co
    #
    @30
    @3
    @42
    @43
    @66
    @78
    wceq
    ax-1cn
    @45
    c1
    @19
    cjsub
    sylancr
    @3
    @76
    c1
    @77
    @79
    cmin
    c1
    cr
    wcel
    @76
    c1
    wceq
    @3
    1re
    c1
    cjre
    mp1i
    #
    @3
    @77
    @57
    @8
    cmul
    co
    #
    @79
    @3
    @40
    @0
    @77
    @82
    wceq
    ax-icn
    @13
    ci
    cA
    cjmul
    sylancr
    @3
    @82
    @10
    @8
    cmul
    co
    #
    @79
    @57
    @10
    @8
    cmul
    cji
    oveq1i
    @3
    @40
    @8
    cc
    wcel
    #
    @83
    @79
    wceq
    ax-icn
    @0
    @84
    @2
    cA
    cjcl
    adantr
    #
    ci
    @8
    mulneg1
    sylancr
    syl5eq
    eqtrd
    #
    oveq12d
    @3
    @42
    @27
    cc
    wcel
    #
    @80
    @30
    wceq
    ax-1cn
    @3
    @40
    @84
    @87
    ax-icn
    @85
    ci
    @8
    mulcl
    sylancr
    #
    c1
    @27
    subneg
    sylancr
    3eqtrd
    fveq2d
    eqtr3d
    @3
    @22
    ccj
    cfv
    #
    clog
    cfv
    #
    @64
    @29
    @3
    @51
    @22
    cim
    cfv
    #
    cc0
    wne
    @90
    @64
    wceq
    @52
    @3
    @91
    @1
    cc0
    @3
    @91
    @70
    @72
    caddc
    co
    #
    cc0
    @1
    caddc
    co
    #
    @1
    @3
    @42
    @43
    @91
    @92
    wceq
    ax-1cn
    @45
    c1
    @19
    imadd
    sylancr
    @3
    @93
    cc0
    @72
    caddc
    co
    @92
    @3
    @1
    @72
    cc0
    caddc
    @74
    oveq2d
    @70
    cc0
    @72
    caddc
    im1
    oveq1i
    syl6eqr
    @3
    @1
    @75
    addid2d
    3eqtr2d
    @14
    eqnetrd
    @22
    logcj
    syl2anc
    @3
    @89
    @28
    clog
    @3
    @89
    @76
    @77
    caddc
    co
    #
    c1
    @79
    caddc
    co
    #
    @28
    @3
    @42
    @43
    @89
    @94
    wceq
    ax-1cn
    @45
    c1
    @19
    cjadd
    sylancr
    @3
    @76
    c1
    @77
    @79
    caddc
    @81
    @86
    oveq12d
    @3
    @42
    @87
    @95
    @28
    wceq
    ax-1cn
    @88
    c1
    @27
    negsub
    sylancr
    3eqtrd
    fveq2d
    eqtr3d
    oveq12d
    eqtrd
    negeqd
    @3
    @31
    @29
    @3
    @30
    @3
    @42
    @87
    @30
    cc
    wcel
    ax-1cn
    @88
    c1
    @27
    addcl
    sylancr
    @3
    @8
    @4
    wcel
    #
    @30
    cc0
    wne
    #
    @3
    @5
    @96
    @17
    cA
    atandmcj
    syl
    #
    @96
    @84
    @28
    cc0
    wne
    #
    @97
    @8
    atandm2
    #
    simp3bi
    syl
    logcld
    @3
    @28
    @3
    @42
    @87
    @28
    cc
    wcel
    ax-1cn
    @88
    c1
    @27
    subcl
    sylancr
    @3
    @96
    @99
    @98
    @96
    @84
    @99
    @97
    @100
    simp2bi
    syl
    logcld
    negsubdi2d
    eqtrd
    oveq2d
    3eqtrd
    @3
    @6
    @25
    ccj
    @3
    @5
    @6
    @25
    wceq
    @17
    cA
    atanval
    syl
    fveq2d
    @3
    @96
    @9
    @33
    wceq
    @98
    @8
    atanval
    syl
    3eqtr4d
    jca
end

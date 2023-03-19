include "cado.mm"
include "cfv.mm"
include "ccom.mm"
include "cnop.mm"
include "c2.mm"
include "cexp.mm"
include "co.mm"
include "wceq.mm"
include "cle.mm"
include "wbr.mm"
include "cv.mm"
include "cno.mm"
include "c1.mm"
include "wi.mm"
include "chil.mm"
include "wf.mm"
include "cxr.mm"
include "wcel.mm"
include "wral.mm"
include "wb.mm"
include "cbo.mm"
include "adjbdlnb.mm"
include "mpbi.mm"
include "bdopf.mm"
include "ax-mp.mm"
include "hocofi.mm"
include "cr.mm"
include "nmopre.mm"
include "resqcli.mm"
include "rexr.mm"
include "nmopub.mm"
include "mp2an.mm"
include "wa.mm"
include "cmul.mm"
include "hocoi.mm"
include "fveq2d.mm"
include "adantr.mm"
include "ffvelrni.mm"
include "normcl.mm"
include "3syl.mm"
include "syl.mm"
include "remulcl.mm"
include "sylancr.mm"
include "remulcli.mm"
include "a1i.mm"
include "nmbdoplbi.mm"
include "1re.mm"
include "cc0.mm"
include "nmopge0.mm"
include "mp2b.mm"
include "pm3.2i.mm"
include "lemul2a.mm"
include "mp3anl3.mm"
include "mpanl2.mm"
include "sylan.mm"
include "recni.mm"
include "mulid1i.mm"
include "syl6breq.mm"
include "letrd.mm"
include "syl21anc.mm"
include "eqbrtrd.mm"
include "nmopadji.mm"
include "oveq1i.mm"
include "sqvali.mm"
include "eqtr4i.mm"
include "ex.mm"
include "mprgbir.mm"
include "csqrt.mm"
include "bdopcoi.mm"
include "sqrtcli.mm"
include "csp.mm"
include "cabs.mm"
include "cc.mm"
include "hicl.mm"
include "mpancom.mm"
include "abscld.mm"
include "remulcld.mm"
include "bcs.mm"
include "hococli.mm"
include "normge0.mm"
include "jca.mm"
include "simpr.mm"
include "mp3anl2.mm"
include "recnd.mm"
include "mulid1d.mm"
include "eqtr4d.mm"
include "breqtrd.mm"
include "resqcl.mm"
include "sqge0.mm"
include "absidd.mm"
include "normsq.mm"
include "cdm.mm"
include "bdopadj.mm"
include "adj2.mm"
include "mp3an1.mm"
include "adjadj.mm"
include "fveq1i.mm"
include "oveq2i.mm"
include "syl6req.mm"
include "eqtrd.mm"
include "eqtr3d.mm"
include "sqsqrti.mm"
include "3brtr4d.mm"
include "sqrtge0i.mm"
include "le2sq.mm"
include "mpanr12.mm"
include "syl2anc.mm"
include "mpbird.mm"
include "le2sqi.mm"
include "breqtri.mm"
include "letri3i.mm"
include "mpbir2an.mm"

theorem nmopcoadji
  let cT: class T
  let vx: setvar x
  assume nmopcoadj.1: |- T e. BndLinOp


  assert |- ( normop ` ( ( adjh ` T ) o. T ) ) = ( ( normop ` T ) ^ 2 )

  proof
    cT
    cado
    cfv
    #
    cT
    ccom
    #
    cnop
    cfv
    #
    cT
    cnop
    cfv
    #
    c2
    cexp
    co
    #
    wceq
    @2
    @4
    cle
    wbr
    #
    @4
    @2
    cle
    wbr
    @5
    vx
    cv
    #
    cno
    cfv
    #
    c1
    cle
    wbr
    #
    @6
    @1
    cfv
    #
    cno
    cfv
    #
    @4
    cle
    wbr
    #
    wi
    #
    vx
    chil
    chil
    chil
    @1
    wf
    #
    @4
    cxr
    wcel
    #
    @5
    @12
    vx
    chil
    wral
    wb
    @0
    cT
    @0
    cbo
    wcel
    #
    chil
    chil
    @0
    wf
    #
    cT
    cbo
    wcel
    #
    @15
    nmopcoadj.1
    cT
    adjbdlnb
    mpbi
    #
    @0
    bdopf
    #
    ax-mp
    #
    @17
    chil
    chil
    cT
    wf
    #
    nmopcoadj.1
    cT
    bdopf
    #
    ax-mp
    #
    hocofi
    #
    @4
    cr
    wcel
    @14
    @3
    @17
    @3
    cr
    wcel
    #
    nmopcoadj.1
    cT
    nmopre
    ax-mp
    #
    resqcli
    #
    @4
    rexr
    ax-mp
    vx
    @4
    @1
    nmopub
    mp2an
    @6
    chil
    wcel
    #
    @8
    @11
    @28
    @8
    wa
    #
    @10
    @0
    cnop
    cfv
    #
    @3
    cmul
    co
    #
    @4
    cle
    @29
    @10
    @6
    cT
    cfv
    #
    @0
    cfv
    #
    cno
    cfv
    #
    @31
    cle
    @28
    @10
    @34
    wceq
    @8
    @28
    @9
    @33
    cno
    @6
    @0
    cT
    @20
    @23
    hocoi
    fveq2d
    #
    adantr
    @29
    @34
    @30
    @32
    cno
    cfv
    #
    cmul
    co
    #
    @31
    @28
    @34
    cr
    wcel
    #
    @8
    @28
    @32
    chil
    wcel
    #
    @33
    chil
    wcel
    #
    @38
    chil
    chil
    @6
    cT
    @23
    ffvelrni
    #
    chil
    chil
    @32
    @0
    @20
    ffvelrni
    #
    @33
    normcl
    3syl
    #
    adantr
    @28
    @37
    cr
    wcel
    #
    @8
    @28
    @30
    cr
    wcel
    #
    @36
    cr
    wcel
    #
    @44
    @15
    @45
    @18
    @0
    nmopre
    ax-mp
    #
    @28
    @39
    @46
    @41
    @32
    normcl
    #
    syl
    #
    @30
    @36
    remulcl
    sylancr
    adantr
    @31
    cr
    wcel
    @29
    @30
    @3
    @47
    @26
    remulcli
    a1i
    @28
    @34
    @37
    cle
    wbr
    #
    @8
    @28
    @39
    @50
    @41
    @32
    @0
    @18
    nmbdoplbi
    syl
    adantr
    @29
    @46
    @25
    @36
    @3
    cle
    wbr
    #
    @37
    @31
    cle
    wbr
    #
    @28
    @46
    @8
    @49
    adantr
    #
    @25
    @29
    @26
    a1i
    #
    @29
    @36
    @3
    @7
    cmul
    co
    #
    @3
    @53
    @28
    @55
    cr
    wcel
    #
    @8
    @28
    @25
    @7
    cr
    wcel
    #
    @56
    @26
    @6
    normcl
    #
    @3
    @7
    remulcl
    sylancr
    adantr
    @54
    @28
    @36
    @55
    cle
    wbr
    @8
    @6
    cT
    nmopcoadj.1
    nmbdoplbi
    adantr
    @29
    @55
    @3
    c1
    cmul
    co
    #
    @3
    cle
    @28
    @57
    @8
    @55
    @59
    cle
    wbr
    #
    @58
    @57
    c1
    cr
    wcel
    #
    @8
    @60
    1re
    @57
    @61
    @25
    cc0
    @3
    cle
    wbr
    #
    wa
    @8
    @60
    @25
    @62
    @26
    @17
    @21
    @62
    nmopcoadj.1
    @22
    cT
    nmopge0
    mp2b
    #
    pm3.2i
    @7
    c1
    @3
    lemul2a
    mp3anl3
    mpanl2
    sylan
    @3
    @3
    @26
    recni
    #
    mulid1i
    syl6breq
    letrd
    @46
    @25
    @45
    cc0
    @30
    cle
    wbr
    #
    wa
    @51
    @52
    @45
    @65
    @47
    @15
    @16
    @65
    @18
    @19
    @0
    nmopge0
    mp2b
    pm3.2i
    @36
    @3
    @30
    lemul2a
    mp3anl3
    syl21anc
    letrd
    eqbrtrd
    @31
    @3
    @3
    cmul
    co
    @4
    @30
    @3
    @3
    cmul
    cT
    nmopcoadj.1
    nmopadji
    oveq1i
    @3
    @64
    sqvali
    eqtr4i
    syl6breq
    ex
    mprgbir
    @4
    @2
    csqrt
    cfv
    #
    c2
    cexp
    co
    #
    @2
    cle
    @3
    @66
    cle
    wbr
    #
    @4
    @67
    cle
    wbr
    #
    @68
    @8
    @36
    @66
    cle
    wbr
    #
    wi
    #
    vx
    chil
    @21
    @66
    cxr
    wcel
    #
    @68
    @71
    vx
    chil
    wral
    wb
    @23
    cc0
    @2
    cle
    wbr
    #
    @66
    cr
    wcel
    #
    @72
    @13
    @73
    @24
    @1
    nmopge0
    #
    ax-mp
    #
    @2
    @1
    cbo
    wcel
    @2
    cr
    wcel
    #
    @0
    cT
    @18
    nmopcoadj.1
    bdopcoi
    #
    @1
    nmopre
    ax-mp
    #
    sqrtcli
    #
    @66
    rexr
    mp2b
    vx
    @66
    cT
    nmopub
    mp2an
    @28
    @8
    @70
    @29
    @70
    @36
    c2
    cexp
    co
    #
    @67
    cle
    wbr
    #
    @29
    @33
    @6
    csp
    co
    #
    cabs
    cfv
    #
    @2
    @81
    @67
    cle
    @29
    @84
    @34
    @7
    cmul
    co
    #
    @2
    @28
    @84
    cr
    wcel
    @8
    @28
    @83
    @40
    @28
    @83
    cc
    wcel
    @28
    @39
    @40
    @41
    @42
    syl
    #
    @33
    @6
    hicl
    mpancom
    abscld
    adantr
    @28
    @85
    cr
    wcel
    @8
    @28
    @34
    @7
    @43
    @58
    remulcld
    adantr
    #
    @77
    @29
    @79
    a1i
    #
    @28
    @84
    @85
    cle
    wbr
    #
    @8
    @40
    @28
    @89
    @86
    @33
    @6
    bcs
    mpancom
    adantr
    @29
    @85
    @10
    @2
    @87
    @28
    @10
    cr
    wcel
    #
    @8
    @28
    @9
    chil
    wcel
    @90
    @6
    @0
    cT
    @20
    @23
    hococli
    @9
    normcl
    syl
    adantr
    #
    @88
    @29
    @85
    @34
    c1
    cmul
    co
    #
    @10
    cle
    @29
    @57
    @38
    cc0
    @34
    cle
    wbr
    #
    wa
    #
    @8
    @85
    @92
    cle
    wbr
    #
    @28
    @57
    @8
    @58
    adantr
    @28
    @94
    @8
    @28
    @38
    @93
    @43
    @28
    @39
    @40
    @93
    @41
    @42
    @33
    normge0
    3syl
    jca
    adantr
    @28
    @8
    simpr
    @57
    @61
    @94
    @8
    @95
    1re
    @7
    c1
    @34
    lemul2a
    mp3anl2
    syl21anc
    @28
    @92
    @10
    wceq
    @8
    @28
    @92
    @34
    @10
    @28
    @34
    @28
    @34
    @43
    recnd
    mulid1d
    @35
    eqtr4d
    adantr
    breqtrd
    @29
    @10
    @2
    @7
    cmul
    co
    #
    @2
    @91
    @28
    @96
    cr
    wcel
    #
    @8
    @28
    @77
    @57
    @97
    @79
    @58
    @2
    @7
    remulcl
    sylancr
    adantr
    @88
    @28
    @10
    @96
    cle
    wbr
    @8
    @6
    @1
    @78
    nmbdoplbi
    adantr
    @29
    @96
    @2
    c1
    cmul
    co
    #
    @2
    cle
    @28
    @57
    @8
    @96
    @98
    cle
    wbr
    #
    @58
    @57
    @61
    @8
    @99
    1re
    @57
    @61
    @77
    @73
    wa
    @8
    @99
    @77
    @73
    @79
    @76
    pm3.2i
    @7
    c1
    @2
    lemul2a
    mp3anl3
    mpanl2
    sylan
    @2
    @2
    @79
    recni
    mulid1i
    syl6breq
    letrd
    letrd
    letrd
    @28
    @81
    @84
    wceq
    @8
    @28
    @81
    cabs
    cfv
    #
    @81
    @84
    @28
    @39
    @46
    @100
    @81
    wceq
    @41
    @48
    @46
    @81
    @36
    resqcl
    @36
    sqge0
    absidd
    3syl
    @28
    @81
    @83
    cabs
    @28
    @81
    @32
    @32
    csp
    co
    #
    @83
    @28
    @39
    @81
    @101
    wceq
    @41
    @32
    normsq
    syl
    @28
    @83
    @32
    @6
    @0
    cado
    cfv
    #
    cfv
    #
    csp
    co
    #
    @101
    @39
    @28
    @83
    @104
    wceq
    #
    @41
    @0
    cado
    cdm
    #
    wcel
    #
    @39
    @28
    @105
    @15
    @107
    @18
    @0
    bdopadj
    ax-mp
    @32
    @6
    @0
    adj2
    mp3an1
    mpancom
    @103
    @32
    @32
    csp
    @6
    @102
    cT
    @17
    cT
    @106
    wcel
    @102
    cT
    wceq
    nmopcoadj.1
    cT
    bdopadj
    cT
    adjadj
    mp2b
    fveq1i
    oveq2i
    syl6req
    eqtrd
    fveq2d
    eqtr3d
    adantr
    @67
    @2
    wceq
    #
    @29
    @13
    @73
    @108
    @24
    @75
    @2
    @79
    sqsqrti
    mp2b
    #
    a1i
    3brtr4d
    @28
    @70
    @82
    wb
    #
    @8
    @28
    @46
    cc0
    @36
    cle
    wbr
    #
    @110
    @49
    @28
    @39
    @111
    @41
    @32
    normge0
    syl
    @46
    @111
    wa
    @74
    cc0
    @66
    cle
    wbr
    #
    @110
    @13
    @73
    @74
    @24
    @75
    @80
    mp2b
    #
    @13
    @73
    @112
    @24
    @75
    @2
    @79
    sqrtge0i
    mp2b
    #
    @36
    @66
    le2sq
    mpanr12
    syl2anc
    adantr
    mpbird
    ex
    mprgbir
    @62
    @112
    @68
    @69
    wb
    @63
    @114
    @3
    @66
    @26
    @113
    le2sqi
    mp2an
    mpbi
    @109
    breqtri
    @2
    @4
    @79
    @27
    letri3i
    mpbir2an
end

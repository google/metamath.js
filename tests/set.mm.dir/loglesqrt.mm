include "cr.mm"
include "wcel.mm"
include "cc0.mm"
include "cle.mm"
include "wbr.mm"
include "wa.mm"
include "c1.mm"
include "caddc.mm"
include "co.mm"
include "clog.mm"
include "cfv.mm"
include "csqrt.mm"
include "cmin.mm"
include "cv.mm"
include "cdiv.mm"
include "c2.mm"
include "cmul.mm"
include "0re.mm"
include "a1i.mm"
include "simpl.mm"
include "cicc.mm"
include "crp.mm"
include "cres.mm"
include "cmpt.mm"
include "ccncf.mm"
include "w3a.mm"
include "wb.mm"
include "elicc2.mm"
include "sylancr.mm"
include "biimpa.mm"
include "simp1d.mm"
include "simp2d.mm"
include "ge0p1rpd.mm"
include "fvresd.mm"
include "mpteq2dva.mm"
include "ccnfld.mm"
include "ctopn.mm"
include "crest.mm"
include "ccn.mm"
include "cc.mm"
include "ctopon.mm"
include "wss.mm"
include "eqid.mm"
include "cnfldtopon.mm"
include "ex.mm"
include "ssrdv.mm"
include "ax-resscn.mm"
include "syl6ss.mm"
include "resttopon.mm"
include "wf.mm"
include "fmptd.mm"
include "rpssre.mm"
include "sstri.mm"
include "ctx.mm"
include "addcn.mm"
include "ssid.mm"
include "cncfmptid.mm"
include "sylancl.mm"
include "1cnd.mm"
include "cncfmptc.mm"
include "syl3anc.mm"
include "cncfmpt2f.mm"
include "cncffvrn.mm"
include "mpbird.mm"
include "wceq.mm"
include "cncfcn.mm"
include "eleqtrd.mm"
include "relogcn.mm"
include "mp2an.mm"
include "eleqtri.mm"
include "cnmpt11f.mm"
include "eleqtrrd.mm"
include "eqeltrrd.mm"
include "cioo.mm"
include "crn.mm"
include "ctg.mm"
include "cpr.mm"
include "reelprrecn.mm"
include "simpr.mm"
include "1rp.mm"
include "rpaddcl.mm"
include "relogcld.mm"
include "recnd.mm"
include "rpreccld.mm"
include "cdv.mm"
include "relogcl.mm"
include "adantl.mm"
include "rpreccl.mm"
include "peano2re.mm"
include "sselda.mm"
include "dvmptid.mm"
include "0cnd.mm"
include "dvmptc.mm"
include "dvmptadd.mm"
include "1p0e1.mm"
include "mpteq2i.mm"
include "syl6eq.mm"
include "tgioo2.mm"
include "cpnf.mm"
include "ioorp.mm"
include "iooretop.mm"
include "eqeltrri.mm"
include "dvmptres.mm"
include "dvrelog.mm"
include "wf1o.mm"
include "relogf1o.mm"
include "f1of.mm"
include "mp1i.mm"
include "feqmptd.mm"
include "fvres.mm"
include "mpteq2ia.mm"
include "oveq2d.mm"
include "syl5reqr.mm"
include "fveq2.mm"
include "oveq2.mm"
include "dvmptco.mm"
include "rpcnd.mm"
include "mulid1d.mm"
include "eqtrd.mm"
include "ioossicc.mm"
include "sseli.mm"
include "sylan2.mm"
include "clt.mm"
include "eliooord.mm"
include "simpld.mm"
include "elrpd.mm"
include "cico.mm"
include "elrege0.mm"
include "sylanbrc.mm"
include "resabs1d.mm"
include "sqrtf.mm"
include "feqresmpt.mm"
include "resqrtcn.mm"
include "rescncf.mm"
include "mpisyl.mm"
include "rpcn.mm"
include "sqrtcld.mm"
include "2rp.mm"
include "rpsqrtcl.mm"
include "rpmulcl.mm"
include "dvsqrt.mm"
include "cexp.mm"
include "rpred.mm"
include "1re.mm"
include "resubcl.mm"
include "sqge0d.mm"
include "sqsqrtd.mm"
include "oveq1d.mm"
include "binom2sub1.mm"
include "syl.mm"
include "addsubd.mm"
include "3eqtr4d.mm"
include "breqtrd.mm"
include "subge0d.mm"
include "mpbid.mm"
include "lerecd.mm"
include "syldan.mm"
include "cxr.mm"
include "rexr.mm"
include "0xr.mm"
include "lbicc2.mm"
include "mp3an1.mm"
include "sylan.mm"
include "ubicc2.mm"
include "oveq1.mm"
include "0p1e1.mm"
include "fveq2d.mm"
include "log1.mm"
include "sqrt0.mm"
include "dvle.mm"
include "ge0p1rp.mm"
include "resqrtcl.mm"
include "lesub1d.mm"

theorem loglesqrt
  let cA: class A
  let vx: setvar x
  let vy: setvar y


  assert |- ( ( A e. RR /\ 0 <_ A ) -> ( log ` ( A + 1 ) ) <_ ( sqrt ` A ) )

  proof
    cA
    cr
    wcel
    #
    cc0
    cA
    cle
    wbr
    #
    wa
    #
    cA
    c1
    caddc
    co
    #
    clog
    cfv
    #
    cA
    csqrt
    cfv
    #
    cle
    wbr
    @4
    cc0
    cmin
    co
    @5
    cc0
    cmin
    co
    cle
    wbr
    @2
    vx
    vx
    cv
    #
    c1
    caddc
    co
    #
    clog
    cfv
    #
    c1
    @7
    cdiv
    co
    #
    @6
    csqrt
    cfv
    #
    c1
    c2
    @10
    cmul
    co
    #
    cdiv
    co
    #
    cc0
    cc0
    @4
    @5
    cc0
    cA
    cc0
    cA
    cc0
    cr
    wcel
    #
    @2
    0re
    a1i
    #
    @0
    @1
    simpl
    #
    @2
    vx
    cc0
    cA
    cicc
    co
    #
    @7
    clog
    crp
    cres
    #
    cfv
    #
    cmpt
    #
    vx
    @16
    @8
    cmpt
    @16
    cr
    ccncf
    co
    #
    @2
    vx
    @16
    @18
    @8
    @2
    @6
    @16
    wcel
    #
    wa
    #
    @7
    crp
    clog
    @22
    @6
    @22
    @6
    cr
    wcel
    #
    cc0
    @6
    cle
    wbr
    #
    @6
    cA
    cle
    wbr
    #
    @2
    @21
    @23
    @24
    @25
    w3a
    #
    @2
    @13
    @0
    @21
    @26
    wb
    0re
    @15
    cc0
    cA
    @6
    elicc2
    sylancr
    biimpa
    #
    simp1d
    #
    @22
    @23
    @24
    @25
    @27
    simp2d
    #
    ge0p1rpd
    #
    fvresd
    mpteq2dva
    @2
    @19
    ccnfld
    ctopn
    cfv
    #
    @16
    crest
    co
    #
    @31
    cr
    crest
    co
    #
    ccn
    co
    #
    @20
    @2
    vx
    @7
    @17
    @32
    @31
    crp
    crest
    co
    #
    @33
    @16
    @2
    @31
    cc
    ctopon
    cfv
    wcel
    @16
    cc
    wss
    #
    @32
    @16
    ctopon
    cfv
    wcel
    @31
    @31
    eqid
    #
    cnfldtopon
    @2
    @16
    cr
    cc
    @2
    vx
    @16
    cr
    @2
    @21
    @23
    @28
    ex
    ssrdv
    ax-resscn
    syl6ss
    #
    @16
    @31
    cc
    resttopon
    sylancr
    @2
    vx
    @16
    @7
    cmpt
    #
    @16
    crp
    ccncf
    co
    #
    @32
    @35
    ccn
    co
    #
    @2
    @39
    @40
    wcel
    #
    @16
    crp
    @39
    wf
    #
    @2
    vx
    @16
    @7
    crp
    @39
    @30
    @39
    eqid
    fmptd
    @2
    crp
    cc
    wss
    #
    @39
    @16
    cc
    ccncf
    co
    #
    wcel
    @42
    @43
    wb
    crp
    cr
    cc
    rpssre
    ax-resscn
    sstri
    #
    @2
    vx
    @6
    c1
    caddc
    @31
    @16
    @37
    caddc
    @31
    @31
    ctx
    co
    @31
    ccn
    co
    wcel
    @2
    @31
    @37
    addcn
    a1i
    @2
    @36
    cc
    cc
    wss
    #
    vx
    @16
    @6
    cmpt
    @45
    wcel
    @38
    cc
    ssid
    #
    vx
    @16
    cc
    cncfmptid
    sylancl
    @2
    c1
    cc
    wcel
    @36
    @47
    vx
    @16
    c1
    cmpt
    @45
    wcel
    @2
    1cnd
    #
    @38
    @47
    @2
    @48
    a1i
    vx
    c1
    @16
    cc
    cncfmptc
    syl3anc
    cncfmpt2f
    @16
    cc
    crp
    @39
    cncffvrn
    sylancr
    mpbird
    @2
    @36
    @44
    @40
    @41
    wceq
    @38
    @46
    @16
    crp
    @31
    @32
    @35
    @37
    @32
    eqid
    #
    @35
    eqid
    #
    cncfcn
    sylancl
    eleqtrd
    @17
    @35
    @33
    ccn
    co
    #
    wcel
    @2
    @17
    crp
    cr
    ccncf
    co
    #
    @52
    relogcn
    @44
    cr
    cc
    wss
    #
    @53
    @52
    wceq
    @46
    ax-resscn
    crp
    cr
    @31
    @35
    @33
    @37
    @51
    @33
    eqid
    #
    cncfcn
    mp2an
    eleqtri
    a1i
    cnmpt11f
    @2
    @36
    @54
    @20
    @34
    wceq
    @38
    ax-resscn
    @16
    cr
    @31
    @32
    @33
    @37
    @50
    @55
    cncfcn
    sylancl
    eleqtrrd
    eqeltrrd
    @2
    vx
    @8
    @9
    cr
    cioo
    crn
    ctg
    cfv
    #
    @31
    crp
    crp
    cc0
    cA
    cioo
    co
    #
    cr
    cr
    cc
    cpr
    wcel
    @2
    reelprrecn
    a1i
    #
    @2
    @6
    crp
    wcel
    #
    wa
    #
    @8
    @60
    @7
    @60
    @59
    c1
    crp
    wcel
    @7
    crp
    wcel
    @2
    @59
    simpr
    1rp
    @6
    c1
    rpaddcl
    sylancl
    #
    relogcld
    recnd
    @60
    @7
    @61
    rpreccld
    #
    @2
    cr
    vx
    crp
    @8
    cmpt
    cdv
    co
    vx
    crp
    @9
    c1
    cmul
    co
    #
    cmpt
    vx
    crp
    @9
    cmpt
    @2
    vx
    vy
    @7
    c1
    vy
    cv
    #
    clog
    cfv
    #
    c1
    @64
    cdiv
    co
    #
    cr
    cr
    @8
    @9
    cc
    crp
    crp
    crp
    @58
    @58
    @61
    @60
    1cnd
    #
    @2
    @64
    crp
    wcel
    #
    wa
    @65
    @68
    @65
    cr
    wcel
    @2
    @64
    relogcl
    adantl
    recnd
    @68
    @66
    crp
    wcel
    @2
    @64
    rpreccl
    adantl
    @2
    vx
    @7
    c1
    cr
    @56
    @31
    cc
    cr
    crp
    @58
    @2
    @23
    wa
    #
    @7
    @23
    @7
    cr
    wcel
    @2
    @6
    peano2re
    adantl
    recnd
    @69
    1cnd
    #
    @2
    cr
    vx
    cr
    @7
    cmpt
    cdv
    co
    vx
    cr
    c1
    cc0
    caddc
    co
    #
    cmpt
    vx
    cr
    c1
    cmpt
    @2
    vx
    @6
    c1
    c1
    cc0
    cr
    cc
    cc
    cr
    @58
    @2
    cr
    cc
    @6
    @54
    @2
    ax-resscn
    a1i
    sselda
    @70
    @2
    vx
    cr
    @58
    dvmptid
    @70
    @69
    0cnd
    @2
    vx
    c1
    cr
    @58
    @49
    dvmptc
    dvmptadd
    vx
    cr
    @71
    c1
    1p0e1
    mpteq2i
    syl6eq
    crp
    cr
    wss
    @2
    rpssre
    a1i
    @31
    @37
    tgioo2
    #
    @37
    crp
    @56
    wcel
    @2
    cc0
    cpnf
    cioo
    co
    crp
    @56
    ioorp
    cc0
    cpnf
    iooretop
    eqeltrri
    a1i
    dvmptres
    @2
    vy
    crp
    @66
    cmpt
    cr
    @17
    cdv
    co
    cr
    vy
    crp
    @65
    cmpt
    #
    cdv
    co
    vy
    dvrelog
    @2
    @17
    @73
    cr
    cdv
    @2
    @17
    vy
    crp
    @64
    @17
    cfv
    #
    cmpt
    @73
    @2
    vy
    crp
    cr
    @17
    crp
    cr
    @17
    wf1o
    crp
    cr
    @17
    wf
    @2
    relogf1o
    crp
    cr
    @17
    f1of
    mp1i
    feqmptd
    vy
    crp
    @74
    @65
    @64
    crp
    clog
    fvres
    mpteq2ia
    syl6eq
    oveq2d
    syl5reqr
    @64
    @7
    clog
    fveq2
    @64
    @7
    c1
    cdiv
    oveq2
    dvmptco
    @2
    vx
    crp
    @63
    @9
    @60
    @9
    @60
    @9
    @62
    rpcnd
    mulid1d
    mpteq2dva
    eqtrd
    @2
    vx
    @57
    crp
    @2
    @6
    @57
    wcel
    #
    @59
    @2
    @75
    wa
    @6
    @75
    @2
    @21
    @23
    @57
    @16
    @6
    cc0
    cA
    ioossicc
    sseli
    @28
    sylan2
    @75
    cc0
    @6
    clt
    wbr
    #
    @2
    @75
    @76
    @6
    cA
    clt
    wbr
    @6
    cc0
    cA
    eliooord
    simpld
    adantl
    elrpd
    #
    ex
    ssrdv
    #
    @72
    @37
    @57
    @56
    wcel
    @2
    cc0
    cA
    iooretop
    a1i
    #
    dvmptres
    @2
    csqrt
    cc0
    cpnf
    cico
    co
    #
    cres
    #
    @16
    cres
    #
    vx
    @16
    @10
    cmpt
    #
    @20
    @2
    @82
    csqrt
    @16
    cres
    @83
    @2
    csqrt
    @16
    @80
    @2
    vx
    @16
    @80
    @2
    @21
    @6
    @80
    wcel
    #
    @22
    @23
    @24
    @84
    @28
    @29
    @6
    elrege0
    sylanbrc
    ex
    ssrdv
    #
    resabs1d
    @2
    vx
    cc
    cc
    @16
    csqrt
    cc
    cc
    csqrt
    wf
    @2
    sqrtf
    a1i
    @38
    feqresmpt
    eqtrd
    @2
    @16
    @80
    wss
    @81
    @80
    cr
    ccncf
    co
    wcel
    @82
    @20
    wcel
    @85
    resqrtcn
    @80
    cr
    @16
    @81
    rescncf
    mpisyl
    eqeltrrd
    @2
    vx
    @10
    @12
    cr
    @56
    @31
    crp
    crp
    @57
    @58
    @60
    @6
    @59
    @6
    cc
    wcel
    @2
    @6
    rpcn
    adantl
    #
    sqrtcld
    #
    @60
    @11
    @60
    c2
    crp
    wcel
    @10
    crp
    wcel
    #
    @11
    crp
    wcel
    2rp
    @59
    @88
    @2
    @6
    rpsqrtcl
    adantl
    #
    c2
    @10
    rpmulcl
    sylancr
    #
    rpreccld
    cr
    vx
    crp
    @10
    cmpt
    cdv
    co
    vx
    crp
    @12
    cmpt
    wceq
    @2
    vx
    dvsqrt
    a1i
    @78
    @72
    @37
    @79
    dvmptres
    @2
    @75
    @59
    @9
    @12
    cle
    wbr
    #
    @77
    @60
    @11
    @7
    cle
    wbr
    #
    @91
    @60
    cc0
    @7
    @11
    cmin
    co
    #
    cle
    wbr
    @92
    @60
    cc0
    @10
    c1
    cmin
    co
    #
    c2
    cexp
    co
    #
    @93
    cle
    @60
    @94
    @60
    @10
    cr
    wcel
    c1
    cr
    wcel
    @94
    cr
    wcel
    @60
    @10
    @89
    rpred
    1re
    @10
    c1
    resubcl
    sylancl
    sqge0d
    @60
    @10
    c2
    cexp
    co
    #
    @11
    cmin
    co
    #
    c1
    caddc
    co
    #
    @6
    @11
    cmin
    co
    #
    c1
    caddc
    co
    @95
    @93
    @60
    @97
    @99
    c1
    caddc
    @60
    @96
    @6
    @11
    cmin
    @60
    @6
    @86
    sqsqrtd
    oveq1d
    oveq1d
    @60
    @10
    cc
    wcel
    @95
    @98
    wceq
    @87
    @10
    binom2sub1
    syl
    @60
    @6
    c1
    @11
    @86
    @67
    @60
    @11
    @90
    rpcnd
    addsubd
    3eqtr4d
    breqtrd
    @60
    @7
    @11
    @60
    @7
    @61
    rpred
    @60
    @11
    @90
    rpred
    subge0d
    mpbid
    @60
    @11
    @7
    @90
    @61
    lerecd
    mpbid
    syldan
    @0
    cA
    cxr
    wcel
    #
    @1
    cc0
    @16
    wcel
    #
    cA
    rexr
    #
    cc0
    cxr
    wcel
    #
    @100
    @1
    @101
    0xr
    cc0
    cA
    lbicc2
    mp3an1
    sylan
    @0
    @100
    @1
    cA
    @16
    wcel
    #
    @102
    @103
    @100
    @1
    @104
    0xr
    cc0
    cA
    ubicc2
    mp3an1
    sylan
    @0
    @1
    simpr
    @6
    cc0
    wceq
    #
    @8
    c1
    clog
    cfv
    cc0
    @105
    @7
    c1
    clog
    @105
    @7
    cc0
    c1
    caddc
    co
    c1
    @6
    cc0
    c1
    caddc
    oveq1
    0p1e1
    syl6eq
    fveq2d
    log1
    syl6eq
    @105
    @10
    cc0
    csqrt
    cfv
    cc0
    @6
    cc0
    csqrt
    fveq2
    sqrt0
    syl6eq
    @6
    cA
    wceq
    @7
    @3
    clog
    @6
    cA
    c1
    caddc
    oveq1
    fveq2d
    @6
    cA
    csqrt
    fveq2
    dvle
    @2
    @4
    @5
    cc0
    @2
    @3
    cA
    ge0p1rp
    relogcld
    cA
    resqrtcl
    @14
    lesub1d
    mpbird
end

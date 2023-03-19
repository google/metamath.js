include "cop.mm"
include "cdv.mm"
include "cdm.mm"
include "wcel.mm"
include "crest.mm"
include "co.mm"
include "cperf.mm"
include "cc.mm"
include "wf.mm"
include "wi.mm"
include "wa.mm"
include "wfn.mm"
include "crn.mm"
include "wss.mm"
include "wfun.mm"
include "cv.mm"
include "wbr.mm"
include "wmo.mm"
include "wal.mm"
include "cnt.mm"
include "cfv.mm"
include "csn.mm"
include "cdif.mm"
include "cmin.mm"
include "cdiv.mm"
include "cmpt.mm"
include "climc.mm"
include "cpm.mm"
include "cpw.mm"
include "cxp.mm"
include "ciun.mm"
include "ccnfld.mm"
include "ctopn.mm"
include "df-dv.mm"
include "dmmpt2ssx.mm"
include "simpl.mm"
include "sseldi.mm"
include "oveq2.mm"
include "opeliunxp2.mm"
include "sylib.mm"
include "simprd.mm"
include "cvv.mm"
include "wb.mm"
include "cnex.mm"
include "simpld.mm"
include "elpm2g.mm"
include "sylancr.mm"
include "mpbid.mm"
include "adantr.mm"
include "sseli.mm"
include "elpwid.mm"
include "sstrd.mm"
include "ctop.mm"
include "cuni.mm"
include "ctopon.mm"
include "cnfldtopon.mm"
include "resttopon.mm"
include "topontop.mm"
include "syl.mm"
include "wceq.mm"
include "toponuni.mm"
include "sseqtrd.mm"
include "eqid.mm"
include "ntrss2.mm"
include "syl2anc.mm"
include "sselda.mm"
include "dvlem.mm"
include "fmptd.mm"
include "ssdifssd.mm"
include "clp.mm"
include "a1i.mm"
include "ntrss3.mm"
include "sseqtr4d.mm"
include "restabs.mm"
include "syl3anc.mm"
include "simpr.mm"
include "ntropn.mm"
include "perfopn.mm"
include "eqeltrrd.mm"
include "cnfldtop.mm"
include "toponunii.mm"
include "restperf.mm"
include "lpss3.mm"
include "lpdifsn.mm"
include "limcmo.mm"
include "ex.mm"
include "moanimv.mm"
include "sylibr.mm"
include "eldv.mm"
include "mobidv.mm"
include "mpbird.mm"
include "alrimiv.mm"
include "wrel.mm"
include "reldv.mm"
include "dffun6.mm"
include "mpbiran.mm"
include "funfn.mm"
include "wex.mm"
include "vex.mm"
include "elrn.mm"
include "dvcl.mm"
include "exlimdv.mm"
include "syl5bi.mm"
include "ssrdv.mm"
include "df-f.mm"
include "sylanbrc.mm"
include "wn.mm"
include "c0.mm"
include "f0.mm"
include "df-ov.mm"
include "ndmfv.mm"
include "syl5eq.mm"
include "dmeqd.mm"
include "dm0.mm"
include "syl6eq.mm"
include "feq12d.mm"
include "mpbiri.mm"
include "a1d.mm"
include "pm2.61i.mm"

theorem perfdvf
  let cS: class S
  let cF: class F
  let cK: class K
  let vf: setvar f
  let vs: setvar s
  let vx: setvar x
  let vz: setvar z
  let vy: setvar y
  assume perfdvf.1: |- K = ( TopOpen ` CCfld )


  assert |- ( ( K |`t S ) e. Perf -> ( S _D F ) : dom ( S _D F ) --> CC )

  proof
    cS
    cF
    cop
    #
    cdv
    cdm
    #
    wcel
    #
    cK
    cS
    crest
    co
    #
    cperf
    wcel
    #
    cS
    cF
    cdv
    co
    #
    cdm
    #
    cc
    @5
    wf
    #
    wi
    @2
    @4
    @7
    @2
    @4
    wa
    #
    @5
    @6
    wfn
    #
    @5
    crn
    #
    cc
    wss
    @7
    @8
    @5
    wfun
    #
    @9
    @8
    vx
    cv
    #
    vy
    cv
    #
    @5
    wbr
    #
    vy
    wmo
    #
    vx
    wal
    #
    @11
    @8
    @15
    vx
    @8
    @15
    @12
    cF
    cdm
    #
    @3
    cnt
    cfv
    cfv
    #
    wcel
    #
    @13
    vz
    @17
    @12
    csn
    #
    cdif
    #
    vz
    cv
    #
    cF
    cfv
    @12
    cF
    cfv
    cmin
    co
    @22
    @12
    cmin
    co
    #
    cdiv
    co
    #
    cmpt
    #
    @12
    climc
    co
    wcel
    #
    wa
    #
    vy
    wmo
    #
    @8
    @19
    @26
    vy
    wmo
    #
    wi
    @28
    @8
    @19
    @29
    @8
    @19
    wa
    #
    vy
    @21
    @12
    @25
    cK
    @30
    vz
    @21
    @24
    cc
    @25
    @30
    @22
    @12
    @17
    cF
    @8
    @17
    cc
    cF
    wf
    #
    @19
    @8
    @31
    @17
    cS
    wss
    #
    @8
    cF
    cc
    cS
    cpm
    co
    #
    wcel
    #
    @31
    @32
    wa
    #
    @8
    cS
    cc
    cpw
    #
    wcel
    #
    @34
    @8
    @0
    vs
    @36
    vs
    cv
    #
    csn
    cc
    @38
    cpm
    co
    #
    cxp
    ciun
    #
    wcel
    #
    @37
    @34
    wa
    #
    @8
    @1
    @40
    @0
    vs
    vf
    @36
    @39
    vx
    vf
    cv
    #
    cdm
    #
    ccnfld
    ctopn
    cfv
    @38
    crest
    co
    cnt
    cfv
    cfv
    @20
    vz
    @44
    @20
    cdif
    @22
    @43
    cfv
    @12
    @43
    cfv
    cmin
    co
    @23
    cdiv
    co
    cmpt
    @12
    climc
    co
    cxp
    ciun
    cdv
    vx
    vz
    vf
    vs
    df-dv
    dmmpt2ssx
    #
    @2
    @4
    simpl
    sseldi
    vs
    @36
    @39
    cS
    cF
    @33
    @38
    cS
    cc
    cpm
    oveq2
    opeliunxp2
    #
    sylib
    #
    simprd
    @8
    cc
    cvv
    wcel
    #
    @37
    @34
    @35
    wb
    #
    cnex
    @8
    @37
    @34
    @47
    simpld
    #
    cc
    cS
    cF
    cvv
    @36
    elpm2g
    #
    sylancr
    mpbid
    simpld
    #
    adantr
    @8
    @17
    cc
    wss
    #
    @19
    @8
    @17
    cS
    cc
    @2
    @32
    @4
    @2
    @31
    @32
    @2
    @34
    @35
    @2
    @37
    @34
    @2
    @41
    @42
    @1
    @40
    @0
    @45
    sseli
    @46
    sylib
    #
    simprd
    @2
    @48
    @37
    @49
    cnex
    @2
    @37
    @34
    @54
    simpld
    @51
    sylancr
    mpbid
    simprd
    adantr
    #
    @8
    cS
    cc
    @50
    elpwid
    #
    sstrd
    #
    adantr
    #
    @8
    @18
    @17
    @12
    @8
    @3
    ctop
    wcel
    #
    @17
    @3
    cuni
    #
    wss
    #
    @18
    @17
    wss
    #
    @8
    @3
    cS
    ctopon
    cfv
    wcel
    #
    @59
    @8
    cK
    cc
    ctopon
    cfv
    #
    wcel
    #
    cS
    cc
    wss
    @63
    cK
    perfdvf.1
    cnfldtopon
    #
    @56
    cS
    cK
    cc
    resttopon
    sylancr
    #
    cS
    @3
    topontop
    syl
    #
    @8
    @17
    cS
    @60
    @55
    @8
    @63
    cS
    @60
    wceq
    @67
    cS
    @3
    toponuni
    syl
    #
    sseqtrd
    #
    @17
    @3
    @60
    @60
    eqid
    #
    ntrss2
    syl2anc
    #
    sselda
    dvlem
    @25
    eqid
    #
    fmptd
    @30
    @17
    cc
    @20
    @58
    ssdifssd
    @30
    @12
    @17
    cK
    clp
    cfv
    #
    cfv
    #
    wcel
    #
    @12
    @21
    @74
    cfv
    wcel
    #
    @8
    @18
    @75
    @12
    @8
    @18
    @18
    @74
    cfv
    #
    @75
    @8
    cK
    @18
    crest
    co
    #
    cperf
    wcel
    #
    @18
    @78
    wss
    #
    @8
    @3
    @18
    crest
    co
    #
    @79
    cperf
    @8
    @65
    @18
    cS
    wss
    @37
    @82
    @79
    wceq
    @65
    @8
    @66
    a1i
    @8
    @18
    @60
    cS
    @8
    @59
    @61
    @18
    @60
    wss
    @68
    @70
    @17
    @3
    @60
    @71
    ntrss3
    syl2anc
    @69
    sseqtr4d
    #
    @50
    @18
    cS
    cK
    @64
    @36
    restabs
    syl3anc
    @8
    @4
    @18
    @3
    wcel
    #
    @82
    cperf
    wcel
    @2
    @4
    simpr
    @8
    @59
    @61
    @84
    @68
    @70
    @17
    @3
    @60
    @71
    ntropn
    syl2anc
    @3
    @82
    @60
    @18
    @71
    @82
    eqid
    perfopn
    syl2anc
    eqeltrrd
    @8
    cK
    ctop
    wcel
    #
    @18
    cc
    wss
    @80
    @81
    wb
    cK
    perfdvf.1
    cnfldtop
    #
    @8
    @18
    cS
    cc
    @83
    @56
    sstrd
    cK
    @79
    cc
    @18
    cc
    cK
    @66
    toponunii
    #
    @79
    eqid
    restperf
    sylancr
    mpbid
    @8
    @85
    @53
    @62
    @78
    @75
    wss
    @85
    @8
    @86
    a1i
    @57
    @72
    @17
    @18
    cK
    cc
    @87
    lpss3
    syl3anc
    sstrd
    sselda
    @30
    @85
    @53
    @76
    @77
    wb
    @86
    @58
    @12
    @17
    cK
    cc
    @87
    lpdifsn
    sylancr
    mpbid
    perfdvf.1
    limcmo
    ex
    @19
    @26
    vy
    moanimv
    sylibr
    @8
    @14
    @27
    vy
    @8
    vz
    @17
    @12
    @13
    cS
    @3
    cF
    @25
    cK
    @3
    eqid
    perfdvf.1
    @73
    @56
    @52
    @55
    eldv
    mobidv
    mpbird
    alrimiv
    @11
    @5
    wrel
    @16
    cS
    cF
    reldv
    vx
    vy
    @5
    dffun6
    mpbiran
    sylibr
    @5
    funfn
    sylib
    @8
    vy
    @10
    cc
    @13
    @10
    wcel
    @14
    vx
    wex
    @8
    @13
    cc
    wcel
    #
    vx
    @13
    @5
    vy
    vex
    elrn
    @8
    @14
    @88
    vx
    @8
    @14
    @88
    @8
    @17
    @12
    @13
    cS
    cF
    @56
    @52
    @55
    dvcl
    ex
    exlimdv
    syl5bi
    ssrdv
    @6
    cc
    @5
    df-f
    sylanbrc
    ex
    @2
    wn
    #
    @7
    @4
    @89
    @7
    c0
    cc
    c0
    wf
    cc
    f0
    @89
    @6
    c0
    cc
    @5
    c0
    @89
    @5
    @0
    cdv
    cfv
    c0
    cS
    cF
    cdv
    df-ov
    @0
    cdv
    ndmfv
    syl5eq
    #
    @89
    @6
    c0
    cdm
    c0
    @89
    @5
    c0
    @90
    dmeqd
    dm0
    syl6eq
    feq12d
    mpbiri
    a1d
    pm2.61i
end

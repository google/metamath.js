include "crelexp.mm"
include "cn.mm"
include "cc0.mm"
include "c1.mm"
include "cpr.mm"
include "cn0.mm"
include "ctcl.mm"
include "crcl.mm"
include "crtcl.mm"
include "dftrcl3.mm"
include "dfrcl4.mm"
include "dfrtrcl3.mm"
include "nnex.mm"
include "prex.mm"
include "csn.mm"
include "cun.mm"
include "df-n0.mm"
include "df-pr.mm"
include "equncomi.mm"
include "uneq2i.mm"
include "unass.mm"
include "wss.mm"
include "wceq.mm"
include "wcel.mm"
include "1nn.mm"
include "snssi.mm"
include "ax-mp.mm"
include "ssequn2.mm"
include "mpbi.mm"
include "uneq1i.mm"
include "3eqtr2ri.mm"
include "eqtri.mm"
include "cv.mm"
include "co.mm"
include "ciun.mm"
include "oveq2.mm"
include "cbviunv.mm"
include "ss2iun.mm"
include "1ex.mm"
include "prid2.mm"
include "cvv.mm"
include "vex.mm"
include "relexp1g.mm"
include "syl6eq.mm"
include "ssiun2s.mm"
include "a1i.mm"
include "ovex.mm"
include "iunex.mm"
include "nnnn0.mm"
include "relexpss1d.mm"
include "mprg.mm"
include "eqsstri.mm"
include "iunss.mm"
include "iuneq1.mm"
include "iunxun.mm"
include "c0ex.mm"
include "iunxsn.mm"
include "uneq12i.mm"
include "3eqtri.mm"
include "oveq1i.mm"
include "caddc.mm"
include "sseq1d.mm"
include "weq.mm"
include "unex.mm"
include "0nn0.mm"
include "1nn0.mm"
include "unssi.mm"
include "wa.mm"
include "ccom.mm"
include "simpl.mm"
include "relexpsucnnr.mm"
include "sylancr.mm"
include "coss1.mm"
include "coundi.mm"
include "cdm.mm"
include "crn.mm"
include "cres.mm"
include "cid.mm"
include "relexp0g.mm"
include "coeq2i.mm"
include "coiun1.mm"
include "coires1.mm"
include "iuneq2i.mm"
include "resss.mm"
include "wrex.mm"
include "iunss2.mm"
include "wex.mm"
include "wsbc.mm"
include "peano2nn0.mm"
include "sbcel1v.mm"
include "sylibr.mm"
include "csb.mm"
include "relexpaddss.mm"
include "mp3an23.mm"
include "csbconstg.mm"
include "csbov2g.mm"
include "csbvarg.mm"
include "oveq2d.mm"
include "eqtrd.mm"
include "3sstr4g.mm"
include "wb.mm"
include "sbcssg.mm"
include "sbcan.mm"
include "sylanbrc.mm"
include "spesbcd.mm"
include "df-rex.mm"
include "sseqtri.mm"
include "syl6ss.mm"
include "adantl.mm"
include "eqsstrd.mm"
include "ex.mm"
include "nnind.mm"
include "syl5eqss.mm"
include "mprgbir.mm"
include "comptiunov2i.mm"

theorem cotrclrcl
  let va: setvar a
  let vb: setvar b
  let vc: setvar c
  let vd: setvar d
  let vi: setvar i
  let vj: setvar j
  let vk: setvar k
  let vx: setvar x
  let vy: setvar y


  assert |- ( t+ o. r* ) = t*

  proof
    vi
    vj
    vk
    crelexp
    cn
    cc0
    c1
    cpr
    #
    cn0
    ctcl
    crcl
    crtcl
    va
    vb
    vc
    vd
    vi
    va
    dftrcl3
    vj
    vb
    dfrcl4
    vk
    vc
    dfrtrcl3
    nnex
    cc0
    c1
    prex
    #
    cn0
    cn
    cc0
    csn
    #
    cun
    #
    cn
    @0
    cun
    #
    df-n0
    @4
    cn
    c1
    csn
    #
    @2
    cun
    #
    cun
    cn
    @5
    cun
    #
    @2
    cun
    @3
    @0
    @6
    cn
    @0
    @2
    @5
    cc0
    c1
    df-pr
    #
    equncomi
    uneq2i
    cn
    @5
    @2
    unass
    @7
    cn
    @2
    @5
    cn
    wss
    #
    @7
    cn
    wceq
    c1
    cn
    wcel
    #
    @9
    1nn
    c1
    cn
    snssi
    ax-mp
    @5
    cn
    ssequn2
    mpbi
    uneq1i
    3eqtr2ri
    eqtri
    #
    vk
    cn
    vd
    cv
    #
    vk
    cv
    #
    crelexp
    co
    #
    ciun
    vi
    cn
    @12
    vi
    cv
    #
    crelexp
    co
    #
    ciun
    #
    vi
    cn
    vj
    @0
    @12
    vj
    cv
    #
    crelexp
    co
    #
    ciun
    #
    @15
    crelexp
    co
    #
    ciun
    #
    vk
    vi
    cn
    @14
    @16
    @13
    @15
    @12
    crelexp
    oveq2
    cbviunv
    @16
    @21
    wss
    @17
    @22
    wss
    vi
    cn
    vi
    cn
    @16
    @21
    ss2iun
    @15
    cn
    wcel
    #
    @12
    @20
    @15
    @12
    @20
    wss
    #
    @23
    c1
    @0
    wcel
    @24
    cc0
    c1
    1ex
    prid2
    vj
    @0
    @19
    c1
    @12
    @18
    c1
    wceq
    @19
    @12
    c1
    crelexp
    co
    #
    @12
    @18
    c1
    @12
    crelexp
    oveq2
    #
    @12
    cvv
    wcel
    #
    @25
    @12
    wceq
    vd
    vex
    #
    @12
    cvv
    relexp1g
    ax-mp
    syl6eq
    ssiun2s
    ax-mp
    a1i
    @20
    cvv
    wcel
    #
    @23
    vj
    @0
    @19
    @1
    @12
    @18
    crelexp
    ovex
    iunex
    #
    a1i
    @15
    nnnn0
    relexpss1d
    mprg
    eqsstri
    @10
    vk
    @0
    @14
    ciun
    #
    @22
    wss
    1nn
    vi
    cn
    @21
    c1
    @31
    @15
    c1
    wceq
    @21
    @20
    c1
    crelexp
    co
    #
    @31
    @15
    c1
    @20
    crelexp
    oveq2
    @32
    @20
    @31
    @29
    @32
    @20
    wceq
    @30
    @20
    cvv
    relexp1g
    ax-mp
    vj
    vk
    @0
    @19
    @14
    @18
    @13
    @12
    crelexp
    oveq2
    cbviunv
    eqtri
    syl6eq
    ssiun2s
    ax-mp
    @22
    vk
    cn0
    @14
    ciun
    #
    vk
    @4
    @14
    ciun
    #
    @22
    @33
    wss
    @21
    @33
    wss
    vi
    cn
    vi
    cn
    @21
    @33
    iunss
    @23
    @21
    @12
    cc0
    crelexp
    co
    #
    @25
    cun
    #
    @15
    crelexp
    co
    #
    @33
    @20
    @36
    @15
    crelexp
    @20
    vj
    @2
    @5
    cun
    #
    @19
    ciun
    #
    vj
    @2
    @19
    ciun
    #
    vj
    @5
    @19
    ciun
    #
    cun
    @36
    @0
    @38
    wceq
    @20
    @39
    wceq
    @8
    vj
    @0
    @38
    @19
    iuneq1
    ax-mp
    vj
    @2
    @5
    @19
    iunxun
    @40
    @35
    @41
    @25
    vj
    cc0
    @19
    @35
    c0ex
    @18
    cc0
    @12
    crelexp
    oveq2
    iunxsn
    vj
    c1
    @19
    @25
    1ex
    @26
    iunxsn
    uneq12i
    3eqtri
    oveq1i
    @36
    vx
    cv
    #
    crelexp
    co
    #
    @33
    wss
    @36
    c1
    crelexp
    co
    #
    @33
    wss
    @36
    vy
    cv
    #
    crelexp
    co
    #
    @33
    wss
    #
    @36
    @45
    c1
    caddc
    co
    #
    crelexp
    co
    #
    @33
    wss
    #
    @37
    @33
    wss
    vx
    vy
    @15
    @42
    c1
    wceq
    @43
    @44
    @33
    @42
    c1
    @36
    crelexp
    oveq2
    sseq1d
    vx
    vy
    weq
    @43
    @46
    @33
    @42
    @45
    @36
    crelexp
    oveq2
    sseq1d
    @42
    @48
    wceq
    @43
    @49
    @33
    @42
    @48
    @36
    crelexp
    oveq2
    sseq1d
    vx
    vi
    weq
    @43
    @37
    @33
    @42
    @15
    @36
    crelexp
    oveq2
    sseq1d
    @44
    @36
    @33
    @36
    cvv
    wcel
    #
    @44
    @36
    wceq
    @35
    @25
    @12
    cc0
    crelexp
    ovex
    @12
    c1
    crelexp
    ovex
    unex
    #
    @36
    cvv
    relexp1g
    ax-mp
    @35
    @25
    @33
    cc0
    cn0
    wcel
    @35
    @33
    wss
    0nn0
    vk
    cn0
    @14
    cc0
    @35
    @13
    cc0
    @12
    crelexp
    oveq2
    ssiun2s
    ax-mp
    c1
    cn0
    wcel
    #
    @25
    @33
    wss
    1nn0
    vk
    cn0
    @14
    c1
    @25
    @13
    c1
    @12
    crelexp
    oveq2
    ssiun2s
    ax-mp
    unssi
    eqsstri
    @45
    cn
    wcel
    #
    @47
    @50
    @54
    @47
    wa
    #
    @49
    @46
    @36
    ccom
    #
    @33
    @55
    @51
    @54
    @49
    @56
    wceq
    @52
    @54
    @47
    simpl
    @36
    @45
    cvv
    relexpsucnnr
    sylancr
    @47
    @56
    @33
    wss
    @54
    @47
    @56
    @33
    @36
    ccom
    #
    @33
    @46
    @33
    @36
    coss1
    @57
    @33
    @35
    ccom
    #
    @33
    @25
    ccom
    #
    cun
    @33
    @33
    @35
    @25
    coundi
    @58
    @59
    @33
    @58
    vk
    cn0
    @14
    @12
    cdm
    @12
    crn
    cun
    #
    cres
    #
    ciun
    #
    @33
    @58
    @33
    cid
    @60
    cres
    #
    ccom
    vk
    cn0
    @14
    @63
    ccom
    #
    ciun
    @62
    @35
    @63
    @33
    @27
    @35
    @63
    wceq
    @28
    @12
    cvv
    relexp0g
    ax-mp
    coeq2i
    vk
    @14
    @63
    cn0
    coiun1
    vk
    cn0
    @64
    @61
    @64
    @61
    wceq
    @13
    cn0
    wcel
    #
    @14
    @60
    coires1
    a1i
    iuneq2i
    3eqtri
    @61
    @14
    wss
    #
    @62
    @33
    wss
    vk
    cn0
    vk
    cn0
    @61
    @14
    ss2iun
    @66
    @65
    @14
    @60
    resss
    a1i
    mprg
    eqsstri
    @59
    vi
    cn0
    @16
    ciun
    #
    @33
    @59
    vk
    cn0
    @14
    @25
    ccom
    #
    ciun
    #
    @67
    vk
    @14
    @25
    cn0
    coiun1
    @68
    @16
    wss
    #
    vi
    cn0
    wrex
    #
    @69
    @67
    wss
    vk
    cn0
    vk
    vi
    cn0
    cn0
    @68
    @16
    iunss2
    @65
    @15
    cn0
    wcel
    #
    @70
    wa
    #
    vi
    wex
    @71
    @65
    @73
    vi
    @13
    c1
    caddc
    co
    #
    @65
    @72
    vi
    @74
    wsbc
    #
    @70
    vi
    @74
    wsbc
    #
    @73
    vi
    @74
    wsbc
    @65
    @74
    cn0
    wcel
    @75
    @13
    peano2nn0
    vi
    @74
    cn0
    sbcel1v
    sylibr
    @65
    vi
    @74
    @68
    csb
    #
    vi
    @74
    @16
    csb
    #
    wss
    #
    @76
    @65
    @68
    @12
    @74
    crelexp
    co
    #
    @77
    @78
    @65
    @53
    @27
    @68
    @80
    wss
    1nn0
    @28
    @12
    c1
    @13
    cvv
    relexpaddss
    mp3an23
    @74
    cvv
    wcel
    #
    @77
    @68
    wceq
    @13
    c1
    caddc
    ovex
    #
    vi
    @74
    @68
    cvv
    csbconstg
    ax-mp
    @81
    @78
    @80
    wceq
    @82
    @81
    @78
    @12
    vi
    @74
    @15
    csb
    #
    crelexp
    co
    @80
    vi
    @74
    @12
    @15
    crelexp
    cvv
    csbov2g
    @81
    @83
    @74
    @12
    crelexp
    vi
    @74
    cvv
    csbvarg
    oveq2d
    eqtrd
    ax-mp
    3sstr4g
    @81
    @76
    @79
    wb
    @82
    vi
    @74
    @68
    @16
    cvv
    sbcssg
    ax-mp
    sylibr
    @72
    @70
    vi
    @74
    sbcan
    sylanbrc
    spesbcd
    @70
    vi
    cn0
    df-rex
    sylibr
    mprg
    eqsstri
    vi
    vk
    cn0
    @16
    @14
    @15
    @13
    @12
    crelexp
    oveq2
    cbviunv
    sseqtri
    unssi
    eqsstri
    syl6ss
    adantl
    eqsstrd
    ex
    nnind
    syl5eqss
    mprgbir
    cn0
    @4
    wceq
    @33
    @34
    wceq
    @11
    vk
    cn0
    @4
    @14
    iuneq1
    ax-mp
    sseqtri
    comptiunov2i
end

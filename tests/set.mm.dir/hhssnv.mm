include "csm.mm"
include "cc.mm"
include "cxp.mm"
include "cres.mm"
include "cva.mm"
include "cno.mm"
include "c0v.mm"
include "cablo.mm"
include "wcel.mm"
include "cgr.mm"
include "hhssabloi.mm"
include "ablogrpo.mm"
include "ax-mp.mm"
include "cdm.mm"
include "wss.mm"
include "wceq.mm"
include "chil.mm"
include "shssii.mm"
include "xpss12.mm"
include "mp2an.mm"
include "ax-hfvadd.mm"
include "fdmi.mm"
include "sseqtr4i.mm"
include "ssdmres.mm"
include "mpbi.mm"
include "grporn.mm"
include "cgi.mm"
include "cfv.mm"
include "co.mm"
include "csh.mm"
include "sh0.mm"
include "ovres.mm"
include "ax-hv0cl.mm"
include "hvaddid2i.mm"
include "eqtri.mm"
include "wb.mm"
include "eqid.mm"
include "grpoid.mm"
include "mpbir.mm"
include "cop.mm"
include "wf.mm"
include "wfn.mm"
include "crn.mm"
include "ax-hfvmul.mm"
include "ffn.mm"
include "ssid.mm"
include "fnssres.mm"
include "cv.mm"
include "wrex.mm"
include "ovelrn.mm"
include "wa.mm"
include "shmulcl.mm"
include "mp3an1.mm"
include "eqeltrd.mm"
include "eleq1.mm"
include "syl5ibrcom.mm"
include "rexlimivv.mm"
include "sylbi.mm"
include "ssriv.mm"
include "df-f.mm"
include "mpbir2an.mm"
include "c1.mm"
include "ax-1cn.mm"
include "mpan.mm"
include "sheli.mm"
include "ax-hvmulid.mm"
include "syl.mm"
include "eqtrd.mm"
include "w3a.mm"
include "id.mm"
include "ax-hvdistr1.mm"
include "syl3an.mm"
include "3adant1.mm"
include "oveq2d.mm"
include "shaddcl.mm"
include "sylan2.mm"
include "3impb.mm"
include "3adant3.mm"
include "3adant2.mm"
include "oveq12d.mm"
include "ovresd.mm"
include "3eqtr4d.mm"
include "caddc.mm"
include "ax-hvdistr2.mm"
include "syl3an3.mm"
include "addcl.mm"
include "stoic3.mm"
include "cmul.mm"
include "ax-hvmulass.mm"
include "mulcl.mm"
include "isvciOLD.mm"
include "cr.mm"
include "normf.mm"
include "fssres.mm"
include "cc0.mm"
include "fvres.mm"
include "eqeq1d.mm"
include "norm-i.mm"
include "bitrd.mm"
include "biimpa.mm"
include "cabs.mm"
include "norm-iii.mm"
include "fveq2d.mm"
include "adantl.mm"
include "cle.mm"
include "wbr.mm"
include "norm-ii.mm"
include "syl2an.mm"
include "oveqan12d.mm"
include "3brtr4d.mm"
include "isnvi.mm"

theorem hhssnv
  let cH: class H
  let cW: class W
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  assume hhssnvt.1: |- W = <. <. ( +h |` ( H X. H ) ) , ( .h |` ( CC X. H ) ) >. , ( normh |` H ) >.
  assume hhssnv.2: |- H e. SH


  assert |- W e. NrmCVec

  proof
    vx
    vy
    csm
    cc
    cH
    cxp
    #
    cres
    #
    cW
    cva
    cH
    cH
    cxp
    #
    cres
    #
    cno
    cH
    cres
    #
    cH
    c0v
    @3
    cH
    @3
    cablo
    wcel
    @3
    cgr
    wcel
    #
    cH
    hhssnv.2
    hhssabloi
    #
    @3
    ablogrpo
    ax-mp
    #
    @2
    cva
    cdm
    #
    wss
    @3
    cdm
    @2
    wceq
    @2
    chil
    chil
    cxp
    #
    @8
    cH
    chil
    wss
    #
    @10
    @2
    @9
    wss
    cH
    hhssnv.2
    shssii
    #
    @11
    cH
    chil
    cH
    chil
    xpss12
    mp2an
    @9
    chil
    cva
    ax-hfvadd
    fdmi
    sseqtr4i
    @2
    cva
    ssdmres
    mpbi
    #
    grporn
    #
    c0v
    @3
    cgi
    cfv
    #
    wceq
    #
    c0v
    c0v
    @3
    co
    #
    c0v
    wceq
    #
    @16
    c0v
    c0v
    cva
    co
    #
    c0v
    c0v
    cH
    wcel
    #
    @19
    @16
    @18
    wceq
    cH
    csh
    wcel
    #
    @19
    hhssnv.2
    cH
    sh0
    ax-mp
    #
    @21
    c0v
    c0v
    cH
    cH
    cva
    ovres
    mp2an
    c0v
    ax-hv0cl
    hvaddid2i
    eqtri
    @5
    @19
    @15
    @17
    wb
    @7
    @21
    c0v
    @14
    @3
    cH
    @13
    @14
    eqid
    grpoid
    mp2an
    mpbir
    vx
    vy
    vz
    @1
    @3
    @3
    @1
    cop
    #
    cH
    @6
    @12
    @0
    cH
    @1
    wf
    @1
    @0
    wfn
    #
    @1
    crn
    #
    cH
    wss
    csm
    cc
    chil
    cxp
    #
    wfn
    #
    @0
    @25
    wss
    #
    @23
    @25
    chil
    csm
    wf
    @26
    ax-hfvmul
    @25
    chil
    csm
    ffn
    ax-mp
    cc
    cc
    wss
    @10
    @27
    cc
    ssid
    @11
    cc
    cc
    cH
    chil
    xpss12
    mp2an
    @25
    @0
    csm
    fnssres
    mp2an
    #
    vz
    @24
    cH
    vz
    cv
    #
    @24
    wcel
    #
    @29
    vx
    cv
    #
    vy
    cv
    #
    @1
    co
    #
    wceq
    #
    vy
    cH
    wrex
    vx
    cc
    wrex
    #
    @29
    cH
    wcel
    #
    @23
    @30
    @35
    wb
    @28
    vx
    vy
    cc
    cH
    @29
    @1
    ovelrn
    ax-mp
    @34
    @36
    vx
    vy
    cc
    cH
    @31
    cc
    wcel
    #
    @32
    cH
    wcel
    #
    wa
    #
    @36
    @34
    @33
    cH
    wcel
    @39
    @33
    @31
    @32
    csm
    co
    #
    cH
    @31
    @32
    cc
    cH
    csm
    ovres
    @20
    @37
    @38
    @40
    cH
    wcel
    hhssnv.2
    @31
    @32
    cH
    shmulcl
    mp3an1
    eqeltrd
    @29
    @33
    cH
    eleq1
    syl5ibrcom
    rexlimivv
    sylbi
    ssriv
    @0
    cH
    @1
    df-f
    mpbir2an
    @31
    cH
    wcel
    #
    c1
    @31
    @1
    co
    #
    c1
    @31
    csm
    co
    #
    @31
    c1
    cc
    wcel
    @41
    @42
    @43
    wceq
    ax-1cn
    c1
    @31
    cc
    cH
    csm
    ovres
    mpan
    @41
    @31
    chil
    wcel
    #
    @43
    @31
    wceq
    @31
    cH
    hhssnv.2
    sheli
    #
    @31
    ax-hvmulid
    syl
    eqtrd
    @32
    cc
    wcel
    #
    @41
    @36
    w3a
    #
    @32
    @31
    @29
    cva
    co
    #
    csm
    co
    #
    @32
    @31
    csm
    co
    #
    @32
    @29
    csm
    co
    #
    cva
    co
    #
    @32
    @31
    @29
    @3
    co
    #
    @1
    co
    #
    @32
    @31
    @1
    co
    #
    @32
    @29
    @1
    co
    #
    @3
    co
    #
    @46
    @46
    @41
    @44
    @36
    @29
    chil
    wcel
    @49
    @52
    wceq
    @46
    id
    @45
    @29
    cH
    hhssnv.2
    sheli
    @32
    @31
    @29
    ax-hvdistr1
    syl3an
    @47
    @54
    @32
    @48
    @1
    co
    #
    @49
    @47
    @53
    @48
    @32
    @1
    @41
    @36
    @53
    @48
    wceq
    @46
    @31
    @29
    cH
    cH
    cva
    ovres
    3adant1
    oveq2d
    @46
    @41
    @36
    @58
    @49
    wceq
    #
    @41
    @36
    wa
    @46
    @48
    cH
    wcel
    #
    @59
    @20
    @41
    @36
    @60
    hhssnv.2
    @31
    @29
    cH
    shaddcl
    mp3an1
    @32
    @48
    cc
    cH
    csm
    ovres
    sylan2
    3impb
    eqtrd
    @47
    @57
    @50
    @51
    @3
    co
    @52
    @47
    @55
    @50
    @56
    @51
    @3
    @46
    @41
    @55
    @50
    wceq
    #
    @36
    @32
    @31
    cc
    cH
    csm
    ovres
    #
    3adant3
    @46
    @36
    @56
    @51
    wceq
    @41
    @32
    @29
    cc
    cH
    csm
    ovres
    3adant2
    oveq12d
    @47
    @50
    @51
    cva
    cH
    @46
    @41
    @50
    cH
    wcel
    #
    @36
    @20
    @46
    @41
    @63
    hhssnv.2
    @32
    @31
    cH
    shmulcl
    mp3an1
    #
    3adant3
    @46
    @36
    @51
    cH
    wcel
    #
    @41
    @20
    @46
    @36
    @65
    hhssnv.2
    @32
    @29
    cH
    shmulcl
    mp3an1
    3adant2
    ovresd
    eqtrd
    3eqtr4d
    @46
    @29
    cc
    wcel
    #
    @41
    w3a
    #
    @32
    @29
    caddc
    co
    #
    @31
    csm
    co
    #
    @50
    @29
    @31
    csm
    co
    #
    cva
    co
    #
    @68
    @31
    @1
    co
    #
    @55
    @29
    @31
    @1
    co
    #
    @3
    co
    #
    @41
    @46
    @66
    @44
    @69
    @71
    wceq
    @45
    @32
    @29
    @31
    ax-hvdistr2
    syl3an3
    @46
    @66
    @68
    cc
    wcel
    @41
    @72
    @69
    wceq
    @32
    @29
    addcl
    @68
    @31
    cc
    cH
    csm
    ovres
    stoic3
    @67
    @74
    @50
    @70
    @3
    co
    @71
    @67
    @55
    @50
    @73
    @70
    @3
    @46
    @41
    @61
    @66
    @62
    3adant2
    @66
    @41
    @73
    @70
    wceq
    @46
    @29
    @31
    cc
    cH
    csm
    ovres
    3adant1
    #
    oveq12d
    @67
    @50
    @70
    cva
    cH
    @46
    @41
    @63
    @66
    @64
    3adant2
    @66
    @41
    @70
    cH
    wcel
    #
    @46
    @20
    @66
    @41
    @76
    hhssnv.2
    @29
    @31
    cH
    shmulcl
    mp3an1
    #
    3adant1
    ovresd
    eqtrd
    3eqtr4d
    @67
    @32
    @29
    cmul
    co
    #
    @31
    csm
    co
    #
    @32
    @70
    csm
    co
    #
    @78
    @31
    @1
    co
    #
    @32
    @73
    @1
    co
    #
    @41
    @46
    @66
    @44
    @79
    @80
    wceq
    @45
    @32
    @29
    @31
    ax-hvmulass
    syl3an3
    @46
    @66
    @78
    cc
    wcel
    @41
    @81
    @79
    wceq
    @32
    @29
    mulcl
    @78
    @31
    cc
    cH
    csm
    ovres
    stoic3
    @67
    @82
    @32
    @70
    @1
    co
    #
    @80
    @67
    @73
    @70
    @32
    @1
    @75
    oveq2d
    @46
    @66
    @41
    @83
    @80
    wceq
    #
    @66
    @41
    wa
    @46
    @76
    @84
    @77
    @32
    @70
    cc
    cH
    csm
    ovres
    sylan2
    3impb
    eqtrd
    3eqtr4d
    @22
    eqid
    isvciOLD
    chil
    cr
    cno
    wf
    @10
    cH
    cr
    @4
    wf
    normf
    @11
    chil
    cr
    cH
    cno
    fssres
    mp2an
    @41
    @31
    @4
    cfv
    #
    cc0
    wceq
    #
    @31
    c0v
    wceq
    #
    @41
    @86
    @31
    cno
    cfv
    #
    cc0
    wceq
    #
    @87
    @41
    @85
    @88
    cc0
    @31
    cH
    cno
    fvres
    #
    eqeq1d
    @41
    @44
    @89
    @87
    wb
    @45
    @31
    norm-i
    syl
    bitrd
    biimpa
    @46
    @41
    wa
    #
    @50
    cno
    cfv
    #
    @32
    cabs
    cfv
    #
    @88
    cmul
    co
    #
    @55
    @4
    cfv
    #
    @93
    @85
    cmul
    co
    @41
    @46
    @44
    @92
    @94
    wceq
    @45
    @32
    @31
    norm-iii
    sylan2
    @91
    @95
    @50
    @4
    cfv
    #
    @92
    @91
    @55
    @50
    @4
    @62
    fveq2d
    @91
    @63
    @96
    @92
    wceq
    @64
    @50
    cH
    cno
    fvres
    syl
    eqtrd
    @91
    @85
    @88
    @93
    cmul
    @41
    @85
    @88
    wceq
    @46
    @90
    adantl
    oveq2d
    3eqtr4d
    @41
    @38
    wa
    #
    @31
    @32
    cva
    co
    #
    cno
    cfv
    #
    @88
    @32
    cno
    cfv
    #
    caddc
    co
    #
    @31
    @32
    @3
    co
    #
    @4
    cfv
    #
    @85
    @32
    @4
    cfv
    #
    caddc
    co
    cle
    @41
    @44
    @32
    chil
    wcel
    @99
    @101
    cle
    wbr
    @38
    @45
    @32
    cH
    hhssnv.2
    sheli
    @31
    @32
    norm-ii
    syl2an
    @97
    @103
    @98
    @4
    cfv
    #
    @99
    @97
    @102
    @98
    @4
    @31
    @32
    cH
    cH
    cva
    ovres
    fveq2d
    @97
    @98
    cH
    wcel
    #
    @105
    @99
    wceq
    @20
    @41
    @38
    @106
    hhssnv.2
    @31
    @32
    cH
    shaddcl
    mp3an1
    @98
    cH
    cno
    fvres
    syl
    eqtrd
    @41
    @38
    @85
    @88
    @104
    @100
    caddc
    @90
    @32
    cH
    cno
    fvres
    oveqan12d
    3brtr4d
    hhssnvt.1
    isnvi
end

include "cc.mm"
include "ctan.mm"
include "cdv.mm"
include "co.mm"
include "ccos.mm"
include "ccnv.mm"
include "cc0.mm"
include "csn.mm"
include "cdif.mm"
include "cima.mm"
include "cv.mm"
include "csin.mm"
include "cfv.mm"
include "c1.mm"
include "cdiv.mm"
include "cmul.mm"
include "cmpt.mm"
include "c2.mm"
include "cexp.mm"
include "cneg.mm"
include "caddc.mm"
include "cdm.mm"
include "df-tan.mm"
include "wcel.mm"
include "cnvimass.mm"
include "cosf.mm"
include "fdmi.mm"
include "sseqtri.mm"
include "sseli.mm"
include "sincld.mm"
include "coscld.mm"
include "wa.mm"
include "wne.mm"
include "wf.mm"
include "wfn.mm"
include "wb.mm"
include "ffn.mm"
include "elpreima.mm"
include "mp2b.mm"
include "eldifsni.mm"
include "adantl.mm"
include "sylbi.mm"
include "divrecd.mm"
include "mpteq2ia.mm"
include "eqtri.mm"
include "oveq2i.mm"
include "wceq.mm"
include "wtru.mm"
include "cvv.mm"
include "cr.mm"
include "cpr.mm"
include "cnelprrecn.mm"
include "a1i.mm"
include "wss.mm"
include "difss.mm"
include "imass2.mm"
include "ax-mp.mm"
include "fimacnv.mm"
include "ccnfld.mm"
include "ctopn.mm"
include "sincl.mm"
include "coscl.mm"
include "dvsin.mm"
include "sinf.mm"
include "feqmptd.mm"
include "oveq2d.mm"
include "3eqtr3a.mm"
include "crest.mm"
include "ctopon.mm"
include "eqid.mm"
include "cnfldtopon.mm"
include "toponunii.mm"
include "restid.mm"
include "eqcomi.mm"
include "dvtanlem.mm"
include "dvmptres.mm"
include "reccld.mm"
include "ovexd.mm"
include "simprbi.mm"
include "negcld.mm"
include "eldifi.mm"
include "negex.mm"
include "dvcos.mm"
include "syl5reqr.mm"
include "ax-1cn.mm"
include "dvrec.mm"
include "mp1i.mm"
include "oveq2.mm"
include "oveq1.mm"
include "negeqd.mm"
include "dvmptco.mm"
include "dvmptmul.mm"
include "trud.mm"
include "wral.mm"
include "ovex.mm"
include "dmmpti.mm"
include "sqcld.mm"
include "sqne0.mm"
include "syl.mm"
include "mpbird.mm"
include "divdird.mm"
include "addcomd.mm"
include "sincossq.mm"
include "eqtrd.mm"
include "oveq1d.mm"
include "eqtr3d.mm"
include "recidd.mm"
include "dividd.mm"
include "eqtr4d.mm"
include "div23d.mm"
include "sqvald.mm"
include "mul2negd.mm"
include "divrec2d.mm"
include "3eqtr4rd.mm"
include "oveq12d.mm"
include "cn0.mm"
include "2nn0.mm"
include "expneg.mm"
include "sylancl.mm"
include "3eqtr4d.mm"
include "rgen.mm"
include "mpteq12.mm"
include "mp2an.mm"
include "3eqtri.mm"

theorem dvtan
  let vx: setvar x
  let vy: setvar y


  assert |- ( CC _D tan ) = ( x e. dom tan |-> ( ( cos ` x ) ^ -u 2 ) )

  proof
    cc
    ctan
    cdv
    co
    cc
    vx
    ccos
    ccnv
    #
    cc
    cc0
    csn
    #
    cdif
    #
    cima
    #
    vx
    cv
    #
    csin
    cfv
    #
    c1
    @4
    ccos
    cfv
    #
    cdiv
    co
    #
    cmul
    co
    #
    cmpt
    #
    cdv
    co
    #
    vx
    @3
    @6
    @7
    cmul
    co
    #
    c1
    @6
    c2
    cexp
    co
    #
    cdiv
    co
    #
    cneg
    #
    @5
    cneg
    #
    cmul
    co
    #
    @5
    cmul
    co
    #
    caddc
    co
    #
    cmpt
    #
    vx
    ctan
    cdm
    #
    @6
    c2
    cneg
    cexp
    co
    #
    cmpt
    #
    ctan
    @9
    cc
    cdv
    ctan
    vx
    @3
    @5
    @6
    cdiv
    co
    #
    cmpt
    @9
    vx
    df-tan
    #
    vx
    @3
    @23
    @8
    @4
    @3
    wcel
    #
    @5
    @6
    @25
    @4
    @3
    cc
    @4
    @3
    ccos
    cdm
    cc
    ccos
    @2
    cnvimass
    cc
    cc
    ccos
    cosf
    fdmi
    sseqtri
    sseli
    #
    sincld
    #
    @25
    @4
    @26
    coscld
    #
    @25
    @4
    cc
    wcel
    #
    @6
    @2
    wcel
    #
    wa
    #
    @6
    cc0
    wne
    #
    cc
    cc
    ccos
    wf
    #
    ccos
    cc
    wfn
    @25
    @31
    wb
    cosf
    cc
    cc
    ccos
    ffn
    cc
    @4
    @2
    ccos
    elpreima
    mp2b
    #
    @30
    @32
    @29
    @6
    cc
    cc0
    eldifsni
    adantl
    sylbi
    #
    divrecd
    mpteq2ia
    eqtri
    oveq2i
    @10
    @19
    wceq
    wtru
    vx
    @5
    @6
    @7
    @16
    cc
    cc
    cvv
    @3
    cc
    cr
    cc
    cpr
    wcel
    wtru
    cnelprrecn
    a1i
    #
    @25
    @5
    cc
    wcel
    #
    wtru
    @25
    @4
    @3
    cc
    @4
    @3
    @0
    cc
    cima
    #
    cc
    @2
    cc
    wss
    @3
    @38
    wss
    cc
    @1
    difss
    @2
    cc
    @0
    imass2
    ax-mp
    @33
    @38
    cc
    wceq
    cosf
    cc
    cc
    ccos
    fimacnv
    ax-mp
    sseqtri
    #
    sseli
    sincld
    adantl
    #
    @25
    @6
    cc
    wcel
    #
    wtru
    @28
    adantl
    wtru
    vx
    @5
    @6
    cc
    ccnfld
    ctopn
    cfv
    #
    @42
    cc
    cc
    @3
    @36
    @29
    @37
    wtru
    @4
    sincl
    adantl
    #
    @29
    @41
    wtru
    @4
    coscl
    adantl
    #
    wtru
    cc
    csin
    cdv
    co
    ccos
    cc
    vx
    cc
    @5
    cmpt
    #
    cdv
    co
    vx
    cc
    @6
    cmpt
    #
    dvsin
    wtru
    csin
    @45
    cc
    cdv
    wtru
    vx
    cc
    cc
    csin
    cc
    cc
    csin
    wf
    wtru
    sinf
    a1i
    feqmptd
    oveq2d
    wtru
    vx
    cc
    cc
    ccos
    @33
    wtru
    cosf
    a1i
    feqmptd
    #
    3eqtr3a
    @3
    cc
    wss
    wtru
    @39
    a1i
    #
    @42
    cc
    crest
    co
    #
    @42
    @42
    cc
    ctopon
    cfv
    #
    wcel
    @49
    @42
    wceq
    @42
    @42
    eqid
    #
    cnfldtopon
    #
    @42
    @50
    cc
    cc
    @42
    @52
    toponunii
    restid
    ax-mp
    eqcomi
    #
    @51
    @3
    @42
    wcel
    wtru
    dvtanlem
    a1i
    #
    dvmptres
    @25
    @7
    cc
    wcel
    wtru
    @25
    @6
    @28
    @35
    reccld
    adantl
    wtru
    @25
    wa
    #
    @14
    @15
    cmul
    ovexd
    wtru
    vx
    vy
    @6
    @15
    c1
    vy
    cv
    #
    cdiv
    co
    #
    c1
    @56
    c2
    cexp
    co
    #
    cdiv
    co
    #
    cneg
    #
    cc
    cc
    @7
    @14
    cc
    cvv
    @3
    @2
    @36
    @36
    @25
    @30
    wtru
    @25
    @29
    @30
    @34
    simprbi
    adantl
    @55
    @5
    @40
    negcld
    @56
    @2
    wcel
    #
    @57
    cc
    wcel
    wtru
    @61
    @56
    @56
    cc
    @1
    eldifi
    @56
    cc
    cc0
    eldifsni
    reccld
    adantl
    @60
    cvv
    wcel
    wtru
    @61
    wa
    @59
    negex
    a1i
    wtru
    vx
    @6
    @15
    cc
    @42
    @42
    cc
    cc
    @3
    @36
    @44
    wtru
    @29
    wa
    @5
    @43
    negcld
    wtru
    vx
    cc
    @15
    cmpt
    cc
    ccos
    cdv
    co
    cc
    @46
    cdv
    co
    vx
    dvcos
    wtru
    ccos
    @46
    cc
    cdv
    @47
    oveq2d
    syl5reqr
    @48
    @53
    @51
    @54
    dvmptres
    c1
    cc
    wcel
    cc
    vy
    @2
    @57
    cmpt
    cdv
    co
    vy
    @2
    @60
    cmpt
    wceq
    wtru
    ax-1cn
    vy
    c1
    dvrec
    mp1i
    @56
    @6
    c1
    cdiv
    oveq2
    @56
    @6
    wceq
    #
    @59
    @13
    @62
    @58
    @12
    c1
    cdiv
    @56
    @6
    c2
    cexp
    oveq1
    oveq2d
    negeqd
    dvmptco
    dvmptmul
    trud
    @3
    @20
    wceq
    @18
    @21
    wceq
    #
    vx
    @3
    wral
    @19
    @22
    wceq
    @20
    @3
    vx
    @3
    @23
    ctan
    @5
    @6
    cdiv
    ovex
    @24
    dmmpti
    eqcomi
    @63
    vx
    @3
    @25
    @12
    @12
    cdiv
    co
    #
    @5
    c2
    cexp
    co
    #
    @12
    cdiv
    co
    #
    caddc
    co
    #
    @13
    @18
    @21
    @25
    @12
    @65
    caddc
    co
    #
    @12
    cdiv
    co
    @67
    @13
    @25
    @12
    @65
    @12
    @25
    @6
    @28
    sqcld
    #
    @25
    @5
    @27
    sqcld
    #
    @69
    @25
    @12
    cc0
    wne
    #
    @32
    @35
    @25
    @41
    @71
    @32
    wb
    @28
    @6
    sqne0
    syl
    mpbird
    #
    divdird
    @25
    @68
    c1
    @12
    cdiv
    @25
    @68
    @65
    @12
    caddc
    co
    #
    c1
    @25
    @12
    @65
    @69
    @70
    addcomd
    @25
    @29
    @73
    c1
    wceq
    @26
    @4
    sincossq
    syl
    eqtrd
    oveq1d
    eqtr3d
    @25
    @11
    @64
    @17
    @66
    caddc
    @25
    @11
    c1
    @64
    @25
    @6
    @28
    @35
    recidd
    @25
    @12
    @69
    @72
    dividd
    eqtr4d
    @25
    @5
    @5
    cmul
    co
    #
    @12
    cdiv
    co
    @5
    @12
    cdiv
    co
    #
    @5
    cmul
    co
    @66
    @17
    @25
    @5
    @5
    @12
    @27
    @27
    @69
    @72
    div23d
    @25
    @65
    @74
    @12
    cdiv
    @25
    @5
    @27
    sqvald
    oveq1d
    @25
    @16
    @75
    @5
    cmul
    @25
    @16
    @13
    @5
    cmul
    co
    @75
    @25
    @13
    @5
    @25
    @12
    @69
    @72
    reccld
    @27
    mul2negd
    @25
    @5
    @12
    @27
    @69
    @72
    divrec2d
    eqtr4d
    oveq1d
    3eqtr4rd
    oveq12d
    @25
    @41
    c2
    cn0
    wcel
    @21
    @13
    wceq
    @28
    2nn0
    @6
    c2
    expneg
    sylancl
    3eqtr4d
    rgen
    vx
    @3
    @18
    @20
    @21
    mpteq12
    mp2an
    3eqtri
end

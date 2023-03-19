include "cc0.mm"
include "cpi.mm"
include "cioo.mm"
include "co.mm"
include "cv.mm"
include "csin.mm"
include "cfv.mm"
include "citg.mm"
include "cmin.mm"
include "c1.mm"
include "cneg.mm"
include "c2.mm"
include "cr.mm"
include "cdv.mm"
include "wceq.mm"
include "wtru.mm"
include "wcel.mm"
include "cmpt.mm"
include "cicc.mm"
include "ccos.mm"
include "fveq2.mm"
include "negeqd.mm"
include "cbvmptv.mm"
include "eqtri.mm"
include "oveq2i.mm"
include "crn.mm"
include "ctg.mm"
include "ccnfld.mm"
include "ctopn.mm"
include "cc.mm"
include "wss.mm"
include "ax-resscn.mm"
include "a1i.mm"
include "0re.mm"
include "pire.mm"
include "iccssre.mm"
include "mp2an.mm"
include "wa.mm"
include "sstri.mm"
include "sseli.mm"
include "coscld.mm"
include "adantl.mm"
include "negcld.mm"
include "eqid.mm"
include "tgioo2.mm"
include "cnt.mm"
include "iccntr.mm"
include "dvmptntr.mm"
include "trud.mm"
include "cpr.mm"
include "reelprrecn.mm"
include "recn.mm"
include "sincld.mm"
include "dvcosre.mm"
include "dvmptneg.mm"
include "negnegd.mm"
include "mpteq2ia.mm"
include "syl6eq.mm"
include "ioossre.mm"
include "iooretop.mm"
include "dvmptres.mm"
include "3eqtri.mm"
include "fveq1i.mm"
include "fvmpt2.mm"
include "mpdan.mm"
include "syl5eq.mm"
include "itgeq2dv.mm"
include "cle.mm"
include "wbr.mm"
include "pipos.mm"
include "ltleii.mm"
include "ccncf.mm"
include "nfcv.mm"
include "sincn.mm"
include "cncfmptss.mm"
include "syl5eqel.mm"
include "cibl.mm"
include "ioossicc.mm"
include "cvol.mm"
include "cdm.mm"
include "ioombl.mm"
include "cniccibl.mm"
include "mp3an.mm"
include "iblss.mm"
include "syl2anc.mm"
include "eqcomd.mm"
include "nfmpt1.mm"
include "coscn.mm"
include "negfcncf.mm"
include "ax-mp.mm"
include "eqeltri.mm"
include "ftc2.mm"
include "eqtr3i.mm"
include "cxr.mm"
include "0xr.mm"
include "rexri.mm"
include "ubicc2.mm"
include "cospi.mm"
include "ax-1cn.mm"
include "eqtrd.mm"
include "1ex.mm"
include "fvmpt.mm"
include "lbicc2.mm"
include "negex.mm"
include "cos0.mm"
include "negeqi.mm"
include "oveq12i.mm"
include "caddc.mm"
include "subnegi.mm"
include "1p1e2.mm"

theorem itgsin0pilem1
  let vx: setvar x
  let vt: setvar t
  let cC: class C
  let vk: setvar k
  assume itgsin0pilem1.1: |- C = ( t e. ( 0 [,] _pi ) |-> -u ( cos ` t ) )

  disjoint t x
  disjoint C x
  disjoint k x
  assert |- S. ( 0 (,) _pi ) ( sin ` x ) _d x = 2

  proof
    vx
    cc0
    cpi
    cioo
    co
    #
    vx
    cv
    #
    csin
    cfv
    #
    citg
    #
    cpi
    cC
    cfv
    #
    cc0
    cC
    cfv
    #
    cmin
    co
    #
    c1
    c1
    cneg
    #
    cmin
    co
    #
    c2
    vx
    @0
    @1
    cr
    cC
    cdv
    co
    #
    cfv
    #
    citg
    #
    @3
    @6
    @11
    @3
    wceq
    wtru
    vx
    @0
    @10
    @2
    @1
    @0
    wcel
    #
    @10
    @2
    wceq
    wtru
    @12
    @10
    @1
    vx
    @0
    @2
    cmpt
    #
    cfv
    #
    @2
    @1
    @9
    @13
    @9
    cr
    vx
    cc0
    cpi
    cicc
    co
    #
    @1
    ccos
    cfv
    #
    cneg
    #
    cmpt
    #
    cdv
    co
    #
    cr
    vx
    @0
    @17
    cmpt
    cdv
    co
    #
    @13
    cC
    @18
    cr
    cdv
    cC
    vt
    @15
    vt
    cv
    #
    ccos
    cfv
    #
    cneg
    #
    cmpt
    @18
    itgsin0pilem1.1
    vt
    vx
    @15
    @23
    @17
    @21
    @1
    wceq
    @22
    @16
    @21
    @1
    ccos
    fveq2
    negeqd
    cbvmptv
    eqtri
    #
    oveq2i
    @19
    @20
    wceq
    wtru
    vx
    @17
    cr
    cioo
    crn
    ctg
    cfv
    #
    ccnfld
    ctopn
    cfv
    #
    @15
    @0
    cr
    cc
    wss
    wtru
    ax-resscn
    a1i
    @15
    cr
    wss
    #
    wtru
    cc0
    cr
    wcel
    #
    cpi
    cr
    wcel
    #
    @27
    0re
    pire
    cc0
    cpi
    iccssre
    mp2an
    #
    a1i
    wtru
    @1
    @15
    wcel
    #
    wa
    @16
    @31
    @16
    cc
    wcel
    #
    wtru
    @31
    @1
    @15
    cc
    @1
    @15
    cr
    cc
    @30
    ax-resscn
    sstri
    #
    sseli
    #
    coscld
    #
    adantl
    negcld
    @26
    @26
    eqid
    #
    tgioo2
    #
    @36
    @15
    @25
    cnt
    cfv
    cfv
    @0
    wceq
    #
    wtru
    @28
    @29
    @38
    0re
    pire
    cc0
    cpi
    iccntr
    mp2an
    a1i
    dvmptntr
    trud
    @20
    @13
    wceq
    wtru
    vx
    @17
    @2
    cr
    @25
    @26
    cc
    cr
    @0
    cr
    cr
    cc
    cpr
    wcel
    wtru
    reelprrecn
    a1i
    #
    wtru
    @1
    cr
    wcel
    #
    wa
    @16
    @40
    @32
    wtru
    @40
    @1
    @1
    recn
    #
    coscld
    adantl
    #
    negcld
    @40
    @2
    cc
    wcel
    #
    wtru
    @40
    @1
    @41
    sincld
    #
    adantl
    wtru
    cr
    vx
    cr
    @17
    cmpt
    cdv
    co
    vx
    cr
    @2
    cneg
    #
    cneg
    #
    cmpt
    vx
    cr
    @2
    cmpt
    wtru
    vx
    @16
    @45
    cr
    cc
    cr
    @39
    @42
    @40
    @45
    cc
    wcel
    wtru
    @40
    @2
    @44
    negcld
    adantl
    cr
    vx
    cr
    @16
    cmpt
    cdv
    co
    vx
    cr
    @45
    cmpt
    wceq
    wtru
    vx
    dvcosre
    a1i
    dvmptneg
    vx
    cr
    @46
    @2
    @40
    @2
    @44
    negnegd
    mpteq2ia
    syl6eq
    @0
    cr
    wss
    wtru
    cc0
    cpi
    ioossre
    #
    a1i
    @37
    @36
    @0
    @25
    wcel
    wtru
    cc0
    cpi
    iooretop
    a1i
    dvmptres
    trud
    3eqtri
    #
    fveq1i
    @12
    @43
    @14
    @2
    wceq
    @12
    @1
    @0
    cc
    @1
    @0
    cr
    cc
    @47
    ax-resscn
    sstri
    #
    sseli
    sincld
    vx
    @0
    @2
    cc
    @13
    @13
    eqid
    fvmpt2
    mpdan
    syl5eq
    adantl
    itgeq2dv
    trud
    @11
    @6
    wceq
    wtru
    vx
    cc0
    cpi
    cC
    @28
    wtru
    0re
    a1i
    @29
    wtru
    pire
    a1i
    cc0
    cpi
    cle
    wbr
    #
    wtru
    cc0
    cpi
    0re
    pire
    pipos
    ltleii
    #
    a1i
    wtru
    @9
    @13
    @0
    cc
    ccncf
    co
    @48
    wtru
    vx
    cc
    cc
    @0
    csin
    vx
    csin
    nfcv
    #
    csin
    cc
    cc
    ccncf
    co
    #
    wcel
    wtru
    sincn
    a1i
    #
    @0
    cc
    wss
    wtru
    @49
    a1i
    cncfmptss
    syl5eqel
    wtru
    @9
    @13
    cibl
    @48
    wtru
    vx
    @0
    @15
    @2
    cc
    @0
    @15
    wss
    wtru
    cc0
    cpi
    ioossicc
    a1i
    @0
    cvol
    cdm
    wcel
    wtru
    cc0
    cpi
    ioombl
    a1i
    @31
    @43
    wtru
    @31
    @1
    @34
    sincld
    adantl
    vx
    @15
    @2
    cmpt
    #
    cibl
    wcel
    #
    wtru
    @28
    @29
    @55
    @15
    cc
    ccncf
    co
    #
    wcel
    #
    @56
    0re
    pire
    @58
    wtru
    vx
    cc
    cc
    @15
    csin
    @52
    @54
    @15
    cc
    wss
    wtru
    @33
    a1i
    #
    cncfmptss
    trud
    cc0
    cpi
    @55
    cniccibl
    mp3an
    a1i
    iblss
    syl5eqel
    cC
    @57
    wcel
    wtru
    cC
    @18
    @57
    @24
    @18
    vx
    @15
    @1
    vx
    cc
    @17
    cmpt
    #
    cfv
    #
    cmpt
    #
    @57
    vx
    @15
    @17
    @61
    @31
    @61
    @17
    @31
    @1
    cc
    wcel
    @17
    cc
    wcel
    @61
    @17
    wceq
    @34
    @31
    @16
    @35
    negcld
    vx
    cc
    @17
    cc
    @60
    @60
    eqid
    #
    fvmpt2
    syl2anc
    eqcomd
    mpteq2ia
    @62
    @57
    wcel
    wtru
    vx
    cc
    cc
    @15
    @60
    vx
    cc
    @17
    nfmpt1
    @60
    @53
    wcel
    #
    wtru
    ccos
    @53
    wcel
    @64
    coscn
    vx
    cc
    ccos
    @60
    @63
    negfcncf
    ax-mp
    a1i
    @59
    cncfmptss
    trud
    eqeltri
    eqeltri
    a1i
    ftc2
    trud
    eqtr3i
    @4
    c1
    @5
    @7
    cmin
    cpi
    @15
    wcel
    #
    @4
    c1
    wceq
    cc0
    cxr
    wcel
    #
    cpi
    cxr
    wcel
    #
    @50
    @65
    0xr
    cpi
    pire
    rexri
    #
    @51
    cc0
    cpi
    ubicc2
    mp3an
    vt
    cpi
    @23
    c1
    @15
    cC
    @21
    cpi
    wceq
    #
    @23
    @7
    cneg
    c1
    @69
    @22
    @7
    @69
    @22
    cpi
    ccos
    cfv
    @7
    @21
    cpi
    ccos
    fveq2
    cospi
    syl6eq
    negeqd
    @69
    c1
    c1
    cc
    wcel
    @69
    ax-1cn
    a1i
    negnegd
    eqtrd
    itgsin0pilem1.1
    1ex
    fvmpt
    ax-mp
    @5
    cc0
    ccos
    cfv
    #
    cneg
    #
    @7
    cc0
    @15
    wcel
    #
    @5
    @71
    wceq
    @66
    @67
    @50
    @72
    0xr
    @68
    @51
    cc0
    cpi
    lbicc2
    mp3an
    vt
    cc0
    @23
    @71
    @15
    cC
    @21
    cc0
    wceq
    @22
    @70
    @21
    cc0
    ccos
    fveq2
    negeqd
    itgsin0pilem1.1
    @70
    negex
    fvmpt
    ax-mp
    @70
    c1
    cos0
    negeqi
    eqtri
    oveq12i
    @8
    c1
    c1
    caddc
    co
    c2
    c1
    c1
    ax-1cn
    ax-1cn
    subnegi
    1p1e2
    eqtri
    3eqtri
end

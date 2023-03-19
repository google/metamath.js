include "cc.mm"
include "cacos.mm"
include "cres.mm"
include "cdv.mm"
include "co.mm"
include "cpi.mm"
include "c2.mm"
include "cdiv.mm"
include "cv.mm"
include "casin.mm"
include "cfv.mm"
include "cmin.mm"
include "cmpt.mm"
include "cc0.mm"
include "c1.mm"
include "cexp.mm"
include "csqrt.mm"
include "cneg.mm"
include "df-acos.mm"
include "reseq1i.mm"
include "wss.mm"
include "wceq.mm"
include "cmnf.mm"
include "cioc.mm"
include "cpnf.mm"
include "cico.mm"
include "cun.mm"
include "cdif.mm"
include "difss.mm"
include "eqsstri.mm"
include "resmpt.mm"
include "ax-mp.mm"
include "eqtri.mm"
include "oveq2i.mm"
include "wtru.mm"
include "cvv.mm"
include "cr.mm"
include "cpr.mm"
include "wcel.mm"
include "cnelprrecn.mm"
include "a1i.mm"
include "wa.mm"
include "halfpire.mm"
include "recni.mm"
include "c0ex.mm"
include "ccnfld.mm"
include "ctopn.mm"
include "dvmptc.mm"
include "crest.mm"
include "ctopon.mm"
include "eqid.mm"
include "cnfldtopon.mm"
include "toponunii.mm"
include "restid.mm"
include "eqcomi.mm"
include "ccld.mm"
include "recld2.mm"
include "cioo.mm"
include "crn.mm"
include "ctg.mm"
include "neg1rr.mm"
include "iocmnfcld.mm"
include "tgioo2.mm"
include "fveq2i.mm"
include "eleqtri.mm"
include "restcldr.mm"
include "mp2an.mm"
include "1re.mm"
include "icopnfcld.mm"
include "uncld.mm"
include "cldopn.mm"
include "eqeltri.mm"
include "dvmptres.mm"
include "sseli.mm"
include "asincl.mm"
include "syl.mm"
include "adantl.mm"
include "ovexd.mm"
include "dvasin.mm"
include "wf.mm"
include "asinf.mm"
include "feqresmpt.mm"
include "oveq2d.mm"
include "syl5reqr.mm"
include "dvmptsub.mm"
include "trud.mm"
include "df-neg.mm"
include "1cnd.mm"
include "ax-1cn.mm"
include "sqcld.mm"
include "subcl.mm"
include "sylancr.mm"
include "sqrtcld.mm"
include "wo.mm"
include "wn.mm"
include "wne.mm"
include "eldifn.mm"
include "eleq2s.mm"
include "cxr.mm"
include "clt.mm"
include "wbr.mm"
include "mnfxr.mm"
include "rexri.mm"
include "mnflt.mm"
include "ubioc1.mm"
include "mp3an.mm"
include "eleq1.mm"
include "mpbiri.mm"
include "pnfxr.mm"
include "ltpnf.mm"
include "lbico1.mm"
include "orim12i.mm"
include "orcoms.mm"
include "elun.mm"
include "sylibr.mm"
include "nsyl.mm"
include "sq1.mm"
include "sqcl.mm"
include "adantr.mm"
include "simpr.mm"
include "sqr00d.mm"
include "subeq0d.mm"
include "syl5req.mm"
include "ex.mm"
include "wb.mm"
include "sqeqor.mm"
include "mpan2.mm"
include "sylibd.mm"
include "necon3bd.mm"
include "sylc.mm"
include "divnegd.mm"
include "syl5eqr.mm"
include "mpteq2ia.mm"
include "3eqtri.mm"

theorem dvacos
  let vx: setvar x
  let cD: class D
  let vy: setvar y
  let vz: setvar z
  let vw: setvar w
  assume dvasin.d: |- D = ( CC \ ( ( -oo (,] -u 1 ) u. ( 1 [,) +oo ) ) )

  disjoint D x
  disjoint x y
  disjoint x z
  disjoint w x
  disjoint y z
  disjoint w y
  disjoint D y
  disjoint w z
  disjoint D z
  disjoint D w
  assert |- ( CC _D ( arccos |` D ) ) = ( x e. D |-> ( -u 1 / ( sqrt ` ( 1 - ( x ^ 2 ) ) ) ) )

  proof
    cc
    cacos
    cD
    cres
    #
    cdv
    co
    cc
    vx
    cD
    cpi
    c2
    cdiv
    co
    #
    vx
    cv
    #
    casin
    cfv
    #
    cmin
    co
    #
    cmpt
    #
    cdv
    co
    #
    vx
    cD
    cc0
    c1
    c1
    @2
    c2
    cexp
    co
    #
    cmin
    co
    #
    csqrt
    cfv
    #
    cdiv
    co
    #
    cmin
    co
    #
    cmpt
    #
    vx
    cD
    c1
    cneg
    #
    @9
    cdiv
    co
    #
    cmpt
    @0
    @5
    cc
    cdv
    @0
    vx
    cc
    @4
    cmpt
    #
    cD
    cres
    #
    @5
    cacos
    @15
    cD
    vx
    df-acos
    reseq1i
    cD
    cc
    wss
    #
    @16
    @5
    wceq
    cD
    cc
    cmnf
    @13
    cioc
    co
    #
    c1
    cpnf
    cico
    co
    #
    cun
    #
    cdif
    #
    cc
    dvasin.d
    cc
    @20
    difss
    eqsstri
    #
    vx
    cc
    cD
    @4
    resmpt
    ax-mp
    eqtri
    oveq2i
    @6
    @12
    wceq
    wtru
    vx
    @1
    cc0
    @3
    @10
    cc
    cvv
    cvv
    cD
    cc
    cr
    cc
    cpr
    wcel
    wtru
    cnelprrecn
    a1i
    #
    @1
    cc
    wcel
    #
    wtru
    @2
    cD
    wcel
    #
    wa
    #
    @1
    halfpire
    recni
    #
    a1i
    cc0
    cvv
    wcel
    #
    @26
    c0ex
    a1i
    wtru
    vx
    @1
    cc0
    cc
    ccnfld
    ctopn
    cfv
    #
    @29
    cvv
    cc
    cD
    @23
    @24
    wtru
    @2
    cc
    wcel
    #
    wa
    #
    @27
    a1i
    @28
    @31
    c0ex
    a1i
    wtru
    vx
    @1
    cc
    @23
    @24
    wtru
    @27
    a1i
    dvmptc
    @17
    wtru
    @22
    a1i
    #
    @29
    cc
    crest
    co
    #
    @29
    @29
    cc
    ctopon
    cfv
    #
    wcel
    @33
    @29
    wceq
    @29
    @29
    eqid
    #
    cnfldtopon
    #
    @29
    @34
    cc
    cc
    @29
    @36
    toponunii
    #
    restid
    ax-mp
    eqcomi
    @35
    cD
    @29
    wcel
    wtru
    cD
    @21
    @29
    dvasin.d
    @20
    @29
    ccld
    cfv
    #
    wcel
    #
    @21
    @29
    wcel
    @18
    @38
    wcel
    #
    @19
    @38
    wcel
    #
    @39
    cr
    @38
    wcel
    #
    @18
    @29
    cr
    crest
    co
    #
    ccld
    cfv
    #
    wcel
    @40
    @29
    @35
    recld2
    #
    @18
    cioo
    crn
    ctg
    cfv
    #
    ccld
    cfv
    #
    @44
    @13
    cr
    wcel
    #
    @18
    @47
    wcel
    neg1rr
    @13
    iocmnfcld
    ax-mp
    @46
    @43
    ccld
    @29
    @35
    tgioo2
    fveq2i
    #
    eleqtri
    cr
    @18
    @29
    restcldr
    mp2an
    @42
    @19
    @44
    wcel
    @41
    @45
    @19
    @47
    @44
    c1
    cr
    wcel
    #
    @19
    @47
    wcel
    1re
    c1
    icopnfcld
    ax-mp
    @49
    eleqtri
    cr
    @19
    @29
    restcldr
    mp2an
    @18
    @19
    @29
    uncld
    mp2an
    @20
    @29
    cc
    @37
    cldopn
    ax-mp
    eqeltri
    a1i
    dvmptres
    @25
    @3
    cc
    wcel
    #
    wtru
    @25
    @30
    @51
    cD
    cc
    @2
    @22
    sseli
    #
    @2
    asincl
    syl
    adantl
    @26
    c1
    @9
    cdiv
    ovexd
    wtru
    vx
    cD
    @10
    cmpt
    cc
    casin
    cD
    cres
    #
    cdv
    co
    cc
    vx
    cD
    @3
    cmpt
    #
    cdv
    co
    vx
    cD
    dvasin.d
    dvasin
    wtru
    @53
    @54
    cc
    cdv
    wtru
    vx
    cc
    cc
    cD
    casin
    cc
    cc
    casin
    wf
    wtru
    asinf
    a1i
    @32
    feqresmpt
    oveq2d
    syl5reqr
    dvmptsub
    trud
    vx
    cD
    @11
    @14
    @25
    @11
    @10
    cneg
    @14
    @10
    df-neg
    @25
    c1
    @9
    @25
    1cnd
    @25
    @8
    @25
    c1
    cc
    wcel
    #
    @7
    cc
    wcel
    #
    @8
    cc
    wcel
    #
    ax-1cn
    @25
    @2
    @52
    sqcld
    c1
    @7
    subcl
    #
    sylancr
    sqrtcld
    @25
    @30
    @2
    c1
    wceq
    #
    @2
    @13
    wceq
    #
    wo
    #
    wn
    @9
    cc0
    wne
    @52
    @25
    @2
    @20
    wcel
    #
    @61
    @62
    wn
    @2
    @21
    cD
    @2
    cc
    @20
    eldifn
    dvasin.d
    eleq2s
    @61
    @2
    @18
    wcel
    #
    @2
    @19
    wcel
    #
    wo
    #
    @62
    @60
    @59
    @65
    @60
    @63
    @59
    @64
    @60
    @63
    @13
    @18
    wcel
    #
    cmnf
    cxr
    wcel
    @13
    cxr
    wcel
    cmnf
    @13
    clt
    wbr
    #
    @66
    mnfxr
    @13
    neg1rr
    rexri
    @48
    @67
    neg1rr
    @13
    mnflt
    ax-mp
    cmnf
    @13
    ubioc1
    mp3an
    @2
    @13
    @18
    eleq1
    mpbiri
    @59
    @64
    c1
    @19
    wcel
    #
    c1
    cxr
    wcel
    cpnf
    cxr
    wcel
    c1
    cpnf
    clt
    wbr
    #
    @68
    c1
    1re
    rexri
    pnfxr
    @50
    @69
    1re
    c1
    ltpnf
    ax-mp
    c1
    cpnf
    lbico1
    mp3an
    @2
    c1
    @19
    eleq1
    mpbiri
    orim12i
    orcoms
    @2
    @18
    @19
    elun
    sylibr
    nsyl
    @30
    @61
    @9
    cc0
    @30
    @9
    cc0
    wceq
    #
    @7
    c1
    c2
    cexp
    co
    #
    wceq
    #
    @61
    @30
    @70
    @72
    @30
    @70
    wa
    #
    @71
    c1
    @7
    sq1
    @73
    c1
    @7
    @73
    1cnd
    @30
    @56
    @70
    @2
    sqcl
    #
    adantr
    @73
    @8
    @30
    @57
    @70
    @30
    @55
    @56
    @57
    ax-1cn
    @74
    @58
    sylancr
    adantr
    @30
    @70
    simpr
    sqr00d
    subeq0d
    syl5req
    ex
    @30
    @55
    @72
    @61
    wb
    ax-1cn
    @2
    c1
    sqeqor
    mpan2
    sylibd
    necon3bd
    sylc
    divnegd
    syl5eqr
    mpteq2ia
    3eqtri
end

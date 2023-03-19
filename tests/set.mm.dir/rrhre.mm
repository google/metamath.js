include "crefld.mm"
include "crrh.mm"
include "cfv.mm"
include "cid.mm"
include "cr.mm"
include "cres.mm"
include "wceq.mm"
include "wtru.mm"
include "cq.mm"
include "cioo.mm"
include "crn.mm"
include "ctg.mm"
include "uniretop.mm"
include "cha.mm"
include "wcel.mm"
include "rehaus.mm"
include "a1i.mm"
include "crrext.mm"
include "ccn.mm"
include "co.mm"
include "rerrext.mm"
include "eqid.mm"
include "retopn.mm"
include "rrhcne.mm"
include "mp1i.mm"
include "ctopon.mm"
include "ctop.mm"
include "retop.mm"
include "toptopon.mm"
include "mpbi.mm"
include "idcn.mm"
include "ax-mp.mm"
include "ccnext.mm"
include "wf.mm"
include "wss.mm"
include "wf1o.mm"
include "f1oi.mm"
include "f1of.mm"
include "qssre.mm"
include "fss.mm"
include "mp2an.mm"
include "ccl.mm"
include "qdensere.mm"
include "cv.mm"
include "csn.mm"
include "cnei.mm"
include "crest.mm"
include "cflf.mm"
include "c0.mm"
include "wne.mm"
include "cima.mm"
include "wrex.mm"
include "wi.mm"
include "wral.mm"
include "wa.mm"
include "cin.mm"
include "simplr.mm"
include "simpr.mm"
include "opnneip.mm"
include "syl3anc.mm"
include "cvv.mm"
include "fvex.mm"
include "qex.mm"
include "elrestr.mm"
include "mp3an12.mm"
include "syl.mm"
include "inss2.mm"
include "resiima.mm"
include "inss1.mm"
include "eqsstri.mm"
include "imaeq2.mm"
include "sseq1d.mm"
include "rspcev.mm"
include "syl2anc.mm"
include "ex.mm"
include "ralrimiva.mm"
include "ancli.mm"
include "cfil.mm"
include "wb.mm"
include "eleq2i.mm"
include "biimpri.mm"
include "trnei.mm"
include "mpbid.mm"
include "isflf.mm"
include "mp3an13.mm"
include "mpbird.mm"
include "ne0i.mm"
include "adantl.mm"
include "creg.mm"
include "cusp.mm"
include "ccusp.mm"
include "recusp.mm"
include "cuspusp.mm"
include "uspreg.mm"
include "resabs1.mm"
include "cnrest.mm"
include "eqeltrri.mm"
include "cnextfres1.mm"
include "trud.mm"
include "cqqh.mm"
include "ccms.mm"
include "recms.mm"
include "elexi.mm"
include "rrhval.mm"
include "qqhre.mm"
include "fveq2i.mm"
include "eqtri.mm"
include "reseq1i.mm"
include "3eqtr4i.mm"
include "hauseqcn.mm"

theorem rrhre
  let va: setvar a
  let vb: setvar b
  let vx: setvar x


  assert |- ( RRHom ` RRfld ) = ( _I |` RR )

  proof
    crefld
    crrh
    cfv
    #
    cid
    cr
    cres
    #
    wceq
    wtru
    cq
    @0
    @1
    cioo
    crn
    ctg
    cfv
    #
    @2
    cr
    uniretop
    @2
    cha
    wcel
    #
    wtru
    rehaus
    a1i
    #
    crefld
    crrext
    wcel
    @0
    @2
    @2
    ccn
    co
    #
    wcel
    wtru
    rerrext
    crefld
    @2
    @2
    @2
    eqid
    #
    retopn
    rrhcne
    mp1i
    @1
    @5
    wcel
    #
    wtru
    @2
    cr
    ctopon
    cfv
    wcel
    #
    @7
    @2
    ctop
    wcel
    #
    @8
    retop
    @2
    cr
    uniretop
    toptopon
    mpbi
    #
    @2
    cr
    idcn
    ax-mp
    #
    a1i
    @0
    cq
    cres
    #
    @1
    cq
    cres
    #
    wceq
    wtru
    cid
    cq
    cres
    #
    @2
    @2
    ccnext
    co
    #
    cfv
    #
    cq
    cres
    #
    @14
    @12
    @13
    @17
    @14
    wceq
    wtru
    vx
    cq
    cr
    cr
    @14
    @2
    @2
    uniretop
    uniretop
    @9
    wtru
    retop
    a1i
    @4
    cq
    cr
    @14
    wf
    #
    wtru
    cq
    cq
    @14
    wf
    #
    cq
    cr
    wss
    #
    @18
    cq
    cq
    @14
    wf1o
    @19
    cq
    f1oi
    cq
    cq
    @14
    f1of
    ax-mp
    qssre
    cq
    cq
    cr
    @14
    fss
    mp2an
    #
    a1i
    @20
    wtru
    qssre
    a1i
    #
    cq
    @2
    ccl
    cfv
    cfv
    #
    cr
    wceq
    wtru
    qdensere
    a1i
    #
    vx
    cv
    #
    cr
    wcel
    #
    @14
    @2
    @25
    csn
    #
    @2
    cnei
    cfv
    #
    cfv
    #
    cq
    crest
    co
    #
    cflf
    co
    cfv
    #
    c0
    wne
    #
    wtru
    @26
    @25
    @31
    wcel
    #
    @32
    @26
    @33
    @26
    @25
    va
    cv
    #
    wcel
    #
    @14
    vb
    cv
    #
    cima
    #
    @34
    wss
    #
    vb
    @30
    wrex
    #
    wi
    #
    va
    @2
    wral
    #
    wa
    #
    @26
    @41
    @26
    @40
    va
    @2
    @26
    @34
    @2
    wcel
    #
    wa
    #
    @35
    @39
    @44
    @35
    wa
    #
    @34
    cq
    cin
    #
    @30
    wcel
    #
    @14
    @46
    cima
    #
    @34
    wss
    #
    @39
    @45
    @34
    @29
    wcel
    #
    @47
    @45
    @9
    @43
    @35
    @50
    @9
    @45
    retop
    a1i
    @26
    @43
    @35
    simplr
    @44
    @35
    simpr
    @25
    @2
    @34
    opnneip
    syl3anc
    @29
    cvv
    wcel
    cq
    cvv
    wcel
    @50
    @47
    @27
    @28
    fvex
    qex
    @34
    cq
    @29
    cvv
    cvv
    elrestr
    mp3an12
    syl
    @49
    @45
    @48
    @46
    @34
    @46
    cq
    wss
    @48
    @46
    wceq
    @34
    cq
    inss2
    cq
    @46
    resiima
    ax-mp
    @34
    cq
    inss1
    eqsstri
    a1i
    @38
    @49
    vb
    @46
    @30
    @36
    @46
    wceq
    @37
    @48
    @34
    @36
    @46
    @14
    imaeq2
    sseq1d
    rspcev
    syl2anc
    ex
    ralrimiva
    ancli
    @26
    @30
    cq
    cfil
    cfv
    wcel
    #
    @33
    @42
    wb
    #
    @26
    @25
    @23
    wcel
    #
    @51
    @53
    @26
    @23
    cr
    @25
    qdensere
    eleq2i
    biimpri
    @8
    @20
    @26
    @53
    @51
    wb
    @10
    qssre
    cq
    @25
    @2
    cr
    trnei
    mp3an12
    mpbid
    @8
    @51
    @18
    @52
    @10
    @21
    @25
    va
    @14
    @2
    @30
    cr
    cq
    vb
    isflf
    mp3an13
    syl
    mpbird
    @31
    @25
    ne0i
    syl
    adantl
    @2
    creg
    wcel
    #
    wtru
    crefld
    cusp
    wcel
    #
    @3
    @54
    crefld
    ccusp
    wcel
    @55
    recusp
    crefld
    cuspusp
    ax-mp
    rehaus
    @2
    crefld
    retopn
    uspreg
    mp2an
    a1i
    @14
    @2
    cq
    crest
    co
    @2
    ccn
    co
    #
    wcel
    wtru
    @13
    @14
    @56
    @20
    @13
    @14
    wceq
    qssre
    cid
    cq
    cr
    resabs1
    ax-mp
    #
    @7
    @20
    @13
    @56
    wcel
    @11
    qssre
    cq
    @1
    @2
    @2
    cr
    uniretop
    cnrest
    mp2an
    eqeltrri
    a1i
    cnextfres1
    trud
    @0
    @16
    cq
    @0
    crefld
    cqqh
    cfv
    #
    @15
    cfv
    #
    @16
    crefld
    cvv
    wcel
    @0
    @59
    wceq
    crefld
    ccms
    recms
    elexi
    crefld
    @2
    @2
    cvv
    @6
    retopn
    rrhval
    ax-mp
    @58
    @14
    @15
    qqhre
    fveq2i
    eqtri
    reseq1i
    @57
    3eqtr4i
    a1i
    @22
    @24
    hauseqcn
    trud
end

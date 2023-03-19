include "ccnfld.mm"
include "c1.mm"
include "c3.mm"
include "cdc.mm"
include "cop.mm"
include "cstr.mm"
include "wbr.mm"
include "wfun.mm"
include "cnfldstr.mm"
include "c0.mm"
include "csn.mm"
include "cdif.mm"
include "structn0fun.mm"
include "cin.mm"
include "wceq.mm"
include "wcel.mm"
include "wn.mm"
include "cnx.mm"
include "cbs.mm"
include "cfv.mm"
include "cc.mm"
include "cplusg.mm"
include "caddc.mm"
include "cmulr.mm"
include "cmul.mm"
include "ctp.mm"
include "cstv.mm"
include "ccj.mm"
include "wo.mm"
include "cts.mm"
include "cabs.mm"
include "cmin.mm"
include "ccom.mm"
include "cmopn.mm"
include "cple.mm"
include "cle.mm"
include "cds.mm"
include "cunif.mm"
include "cmetu.mm"
include "wa.mm"
include "fvex.mm"
include "cnex.mm"
include "opnzi.mm"
include "nesymi.mm"
include "addex.mm"
include "mulex.mm"
include "w3o.mm"
include "w3a.mm"
include "3ioran.mm"
include "0ex.mm"
include "eltp.mm"
include "xchnxbir.mm"
include "mpbir3an.mm"
include "wne.mm"
include "wf.mm"
include "cvv.mm"
include "cjf.mm"
include "fex.mm"
include "mp2an.mm"
include "necomi.mm"
include "nelsn.mm"
include "ax-mp.mm"
include "pm3.2i.mm"
include "ctsr.mm"
include "letsr.mm"
include "elexi.mm"
include "cr.mm"
include "absf.mm"
include "cxp.mm"
include "subf.mm"
include "xpex.mm"
include "coex.mm"
include "mtbir.mm"
include "ioran.mm"
include "anbi12i.mm"
include "bitri.mm"
include "mpbir.mm"
include "cun.mm"
include "df-cnfld.mm"
include "eleq2i.mm"
include "elun.mm"
include "orbi12i.mm"
include "3bitri.mm"
include "disjsn.mm"
include "disjdif2.mm"
include "funeqi.mm"
include "sylib.mm"

theorem cnfldfunALT



  assert |- Fun CCfld

  proof
    ccnfld
    c1
    c1
    c3
    cdc
    cop
    #
    cstr
    wbr
    #
    ccnfld
    wfun
    #
    cnfldstr
    @1
    ccnfld
    c0
    csn
    #
    cdif
    #
    wfun
    @2
    ccnfld
    @0
    structn0fun
    @4
    ccnfld
    ccnfld
    @3
    cin
    c0
    wceq
    #
    @4
    ccnfld
    wceq
    @5
    c0
    ccnfld
    wcel
    #
    wn
    @6
    c0
    cnx
    cbs
    cfv
    #
    cc
    cop
    #
    cnx
    cplusg
    cfv
    #
    caddc
    cop
    #
    cnx
    cmulr
    cfv
    #
    cmul
    cop
    #
    ctp
    #
    wcel
    #
    c0
    cnx
    cstv
    cfv
    #
    ccj
    cop
    #
    csn
    #
    wcel
    #
    wo
    #
    c0
    cnx
    cts
    cfv
    #
    cabs
    cmin
    ccom
    #
    cmopn
    cfv
    #
    cop
    #
    cnx
    cple
    cfv
    #
    cle
    cop
    #
    cnx
    cds
    cfv
    #
    @21
    cop
    #
    ctp
    #
    wcel
    #
    c0
    cnx
    cunif
    cfv
    #
    @21
    cmetu
    cfv
    #
    cop
    #
    csn
    #
    wcel
    #
    wo
    #
    wo
    #
    @36
    wn
    #
    @14
    wn
    #
    @18
    wn
    #
    wa
    #
    @29
    wn
    #
    @34
    wn
    #
    wa
    #
    wa
    #
    @40
    @43
    @38
    @39
    @38
    c0
    @8
    wceq
    #
    wn
    #
    c0
    @10
    wceq
    #
    wn
    #
    c0
    @12
    wceq
    #
    wn
    #
    @8
    c0
    @7
    cc
    cnx
    cbs
    fvex
    cnex
    opnzi
    nesymi
    @10
    c0
    @9
    caddc
    cnx
    cplusg
    fvex
    addex
    opnzi
    nesymi
    @12
    c0
    @11
    cmul
    cnx
    cmulr
    fvex
    mulex
    opnzi
    nesymi
    @45
    @47
    @49
    w3o
    @46
    @48
    @50
    w3a
    @14
    @45
    @47
    @49
    3ioran
    c0
    @8
    @10
    @12
    0ex
    eltp
    xchnxbir
    mpbir3an
    c0
    @16
    wne
    @39
    @16
    c0
    @15
    ccj
    cnx
    cstv
    fvex
    cc
    cc
    ccj
    wf
    cc
    cvv
    wcel
    #
    ccj
    cvv
    wcel
    cjf
    cnex
    cc
    cc
    cvv
    ccj
    fex
    mp2an
    opnzi
    necomi
    c0
    @16
    nelsn
    ax-mp
    pm3.2i
    @41
    @42
    @29
    c0
    @23
    wceq
    #
    c0
    @25
    wceq
    #
    c0
    @27
    wceq
    #
    w3o
    #
    @55
    wn
    @52
    wn
    @53
    wn
    @54
    wn
    @23
    c0
    @20
    @22
    cnx
    cts
    fvex
    @21
    cmopn
    fvex
    opnzi
    nesymi
    @25
    c0
    @24
    cle
    cnx
    cple
    fvex
    cle
    ctsr
    letsr
    elexi
    opnzi
    nesymi
    @27
    c0
    @26
    @21
    cnx
    cds
    fvex
    cabs
    cmin
    cc
    cr
    cabs
    wf
    @51
    cabs
    cvv
    wcel
    absf
    cnex
    cc
    cr
    cvv
    cabs
    fex
    mp2an
    cc
    cc
    cxp
    #
    cc
    cmin
    wf
    @56
    cvv
    wcel
    cmin
    cvv
    wcel
    subf
    cc
    cc
    cnex
    cnex
    xpex
    @56
    cc
    cvv
    cmin
    fex
    mp2an
    coex
    opnzi
    nesymi
    @52
    @53
    @54
    3ioran
    mpbir3an
    c0
    @23
    @25
    @27
    0ex
    eltp
    mtbir
    c0
    @32
    wne
    @42
    @32
    c0
    @30
    @31
    cnx
    cunif
    fvex
    @21
    cmetu
    fvex
    opnzi
    necomi
    c0
    @32
    nelsn
    ax-mp
    pm3.2i
    pm3.2i
    @37
    @19
    wn
    #
    @35
    wn
    #
    wa
    @44
    @19
    @35
    ioran
    @57
    @40
    @58
    @43
    @14
    @18
    ioran
    @29
    @34
    ioran
    anbi12i
    bitri
    mpbir
    @6
    c0
    @13
    @17
    cun
    #
    @28
    @33
    cun
    #
    cun
    #
    wcel
    c0
    @59
    wcel
    #
    c0
    @60
    wcel
    #
    wo
    @36
    ccnfld
    @61
    c0
    df-cnfld
    eleq2i
    c0
    @59
    @60
    elun
    @62
    @19
    @63
    @35
    c0
    @13
    @17
    elun
    c0
    @28
    @33
    elun
    orbi12i
    3bitri
    mtbir
    ccnfld
    c0
    disjsn
    mpbir
    ccnfld
    @3
    disjdif2
    ax-mp
    funeqi
    sylib
    ax-mp
end

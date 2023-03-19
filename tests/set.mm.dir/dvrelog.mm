include "cr.mm"
include "clog.mm"
include "crp.mm"
include "cres.mm"
include "cdv.mm"
include "co.mm"
include "ce.mm"
include "ccnv.mm"
include "c1.mm"
include "cv.mm"
include "cdiv.mm"
include "cmpt.mm"
include "dfrelog.mm"
include "oveq2i.mm"
include "cfv.mm"
include "wceq.mm"
include "wtru.mm"
include "ccncf.mm"
include "wcel.mm"
include "wf.mm"
include "wss.mm"
include "wf1o.mm"
include "reeff1o.mm"
include "f1of.mm"
include "ax-mp.mm"
include "rpssre.mm"
include "fss.mm"
include "mp2an.mm"
include "cc.mm"
include "wb.mm"
include "ax-resscn.mm"
include "efcn.mm"
include "rescncf.mm"
include "mp2.mm"
include "cncffvrn.mm"
include "mpbir.mm"
include "a1i.mm"
include "cdm.mm"
include "cpr.mm"
include "reelprrecn.mm"
include "eff.mm"
include "ssid.mm"
include "dvef.mm"
include "dmeqi.mm"
include "fdmi.mm"
include "eqtri.mm"
include "sseqtr4i.mm"
include "dvres3.mm"
include "mp4an.mm"
include "reseq1i.mm"
include "cc0.mm"
include "crn.mm"
include "wn.mm"
include "0nrp.mm"
include "rneqi.mm"
include "wfo.mm"
include "f1ofo.mm"
include "forn.mm"
include "mp2b.mm"
include "eleq2i.mm"
include "mtbir.mm"
include "dvcnvre.mm"
include "trud.mm"
include "fveq1i.mm"
include "f1ocnvfv2.mm"
include "mpan.mm"
include "syl5eq.mm"
include "oveq2d.mm"
include "mpteq2ia.mm"

theorem dvrelog
  let vx: setvar x


  assert |- ( RR _D ( log |` RR+ ) ) = ( x e. RR+ |-> ( 1 / x ) )

  proof
    cr
    clog
    crp
    cres
    #
    cdv
    co
    cr
    ce
    cr
    cres
    #
    ccnv
    #
    cdv
    co
    #
    vx
    crp
    c1
    vx
    cv
    #
    cdiv
    co
    #
    cmpt
    #
    @0
    @2
    cr
    cdv
    dfrelog
    oveq2i
    @3
    vx
    crp
    c1
    @4
    @2
    cfv
    #
    cr
    @1
    cdv
    co
    #
    cfv
    #
    cdiv
    co
    #
    cmpt
    #
    @6
    @3
    @11
    wceq
    wtru
    vx
    @1
    cr
    crp
    @1
    cr
    cr
    ccncf
    co
    wcel
    #
    wtru
    @12
    cr
    cr
    @1
    wf
    #
    cr
    crp
    @1
    wf
    #
    crp
    cr
    wss
    @13
    cr
    crp
    @1
    wf1o
    #
    @14
    reeff1o
    cr
    crp
    @1
    f1of
    ax-mp
    #
    rpssre
    cr
    crp
    cr
    @1
    fss
    mp2an
    cr
    cc
    wss
    #
    @1
    cr
    cc
    ccncf
    co
    wcel
    #
    @12
    @13
    wb
    ax-resscn
    @17
    ce
    cc
    cc
    ccncf
    co
    wcel
    @18
    ax-resscn
    efcn
    cc
    cc
    cr
    ce
    rescncf
    mp2
    cr
    cc
    cr
    @1
    cncffvrn
    mp2an
    mpbir
    a1i
    @8
    cdm
    #
    cr
    wceq
    wtru
    @19
    @1
    cdm
    cr
    @8
    @1
    @8
    cc
    ce
    cdv
    co
    #
    cr
    cres
    #
    @1
    cr
    cr
    cc
    cpr
    wcel
    cc
    cc
    ce
    wf
    cc
    cc
    wss
    cr
    @20
    cdm
    #
    wss
    @8
    @21
    wceq
    reelprrecn
    eff
    cc
    ssid
    cr
    cc
    @22
    ax-resscn
    @22
    ce
    cdm
    cc
    @20
    ce
    dvef
    dmeqi
    cc
    cc
    ce
    eff
    fdmi
    eqtri
    sseqtr4i
    cc
    cr
    ce
    dvres3
    mp4an
    @20
    ce
    cr
    dvef
    reseq1i
    eqtri
    #
    dmeqi
    cr
    crp
    @1
    @16
    fdmi
    eqtri
    a1i
    cc0
    @8
    crn
    #
    wcel
    #
    wn
    wtru
    @25
    cc0
    crp
    wcel
    0nrp
    @24
    crp
    cc0
    @24
    @1
    crn
    #
    crp
    @8
    @1
    @23
    rneqi
    @15
    cr
    crp
    @1
    wfo
    @26
    crp
    wceq
    reeff1o
    cr
    crp
    @1
    f1ofo
    cr
    crp
    @1
    forn
    mp2b
    eqtri
    eleq2i
    mtbir
    a1i
    @15
    wtru
    reeff1o
    a1i
    dvcnvre
    trud
    vx
    crp
    @10
    @5
    @4
    crp
    wcel
    #
    @9
    @4
    c1
    cdiv
    @27
    @9
    @7
    @1
    cfv
    #
    @4
    @7
    @8
    @1
    @23
    fveq1i
    @15
    @27
    @28
    @4
    wceq
    reeff1o
    cr
    crp
    @4
    @1
    f1ocnvfv2
    mpan
    syl5eq
    oveq2d
    mpteq2ia
    eqtri
    eqtri
end

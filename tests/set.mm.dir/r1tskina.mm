include "con0.mm"
include "wcel.mm"
include "cr1.mm"
include "cfv.mm"
include "ctsk.mm"
include "c0.mm"
include "wceq.mm"
include "cina.mm"
include "wo.mm"
include "wa.mm"
include "wn.mm"
include "wne.mm"
include "df-ne.mm"
include "ccrd.mm"
include "cen.mm"
include "wbr.mm"
include "simplr.mm"
include "simpll.mm"
include "crnk.mm"
include "csuc.mm"
include "cima.mm"
include "cuni.mm"
include "onwf.mm"
include "sseli.mm"
include "eqid.mm"
include "rankr1c.mm"
include "mpbii.mm"
include "syl.mm"
include "simpld.mm"
include "cdm.mm"
include "wfn.mm"
include "r1fnon.mm"
include "fndm.mm"
include "ax-mp.mm"
include "eleq2i.mm"
include "rankonid.mm"
include "bitr3i.mm"
include "fveq2.mm"
include "sylbi.mm"
include "neleqtrd.mm"
include "adantl.mm"
include "wss.mm"
include "onssr1.mm"
include "sylbir.mm"
include "tsken.mm"
include "sylan2.mm"
include "ord.mm"
include "mt3d.mm"
include "syl2anc.mm"
include "carden2b.mm"
include "cv.mm"
include "csdm.mm"
include "wral.mm"
include "simpl.mm"
include "adantr.mm"
include "sselda.mm"
include "tsksdom.mm"
include "ensymd.mm"
include "sdomentr.mm"
include "ralrimiva.mm"
include "iscard.mm"
include "sylanbrc.mm"
include "eqtr3d.mm"
include "r10.mm"
include "on0eln0.mm"
include "biimpar.mm"
include "r1sdom.mm"
include "syldan.mm"
include "syl5eqbrr.mm"
include "fvex.mm"
include "0sdom.mm"
include "sylib.mm"
include "adantlr.mm"
include "tskcard.mm"
include "eqeltrrd.mm"
include "ex.mm"
include "syl5bir.mm"
include "orrd.mm"
include "syl6eq.mm"
include "0tsk.mm"
include "syl6eqel.mm"
include "inatsk.mm"
include "jaoi.mm"
include "impbid1.mm"

theorem r1tskina
  let cA: class A
  let vx: setvar x


  assert |- ( A e. On -> ( ( R1 ` A ) e. Tarski <-> ( A = (/) \/ A e. Inacc ) ) )

  proof
    cA
    con0
    wcel
    #
    cA
    cr1
    cfv
    #
    ctsk
    wcel
    #
    cA
    c0
    wceq
    #
    cA
    cina
    wcel
    #
    wo
    #
    @0
    @2
    @5
    @0
    @2
    wa
    #
    @3
    @4
    @3
    wn
    cA
    c0
    wne
    #
    @6
    @4
    cA
    c0
    df-ne
    @6
    @7
    @4
    @6
    @7
    wa
    #
    @1
    ccrd
    cfv
    #
    cA
    cina
    @8
    cA
    ccrd
    cfv
    #
    @9
    cA
    @8
    cA
    @1
    cen
    wbr
    #
    @10
    @9
    wceq
    @8
    @2
    @0
    @11
    @0
    @2
    @7
    simplr
    #
    @0
    @2
    @7
    simpll
    @2
    @0
    wa
    #
    @11
    cA
    @1
    wcel
    #
    @0
    @14
    wn
    @2
    @0
    cA
    crnk
    cfv
    #
    cr1
    cfv
    #
    @1
    cA
    @0
    cA
    @16
    wcel
    wn
    #
    cA
    @15
    csuc
    cr1
    cfv
    wcel
    #
    @0
    cA
    cr1
    con0
    cima
    cuni
    #
    wcel
    #
    @17
    @18
    wa
    #
    con0
    @19
    cA
    onwf
    sseli
    @20
    @15
    @15
    wceq
    @21
    @15
    eqid
    cA
    @15
    rankr1c
    mpbii
    syl
    simpld
    @0
    @15
    cA
    wceq
    #
    @16
    @1
    wceq
    @0
    cA
    cr1
    cdm
    #
    wcel
    #
    @22
    @23
    con0
    cA
    cr1
    con0
    wfn
    @23
    con0
    wceq
    r1fnon
    con0
    cr1
    fndm
    ax-mp
    eleq2i
    #
    cA
    rankonid
    bitr3i
    @15
    cA
    cr1
    fveq2
    sylbi
    neleqtrd
    adantl
    @13
    @11
    @14
    @0
    @2
    cA
    @1
    wss
    #
    @11
    @14
    wo
    @0
    @24
    @26
    @25
    cA
    onssr1
    sylbir
    #
    cA
    @1
    tsken
    sylan2
    ord
    mt3d
    #
    syl2anc
    cA
    @1
    carden2b
    syl
    @6
    @10
    cA
    wceq
    #
    @7
    @6
    @0
    vx
    cv
    #
    cA
    csdm
    wbr
    #
    vx
    cA
    wral
    @29
    @0
    @2
    simpl
    @6
    @31
    vx
    cA
    @6
    @30
    cA
    wcel
    #
    wa
    #
    @30
    @1
    csdm
    wbr
    #
    @1
    cA
    cen
    wbr
    #
    @31
    @33
    @2
    @30
    @1
    wcel
    @34
    @0
    @2
    @32
    simplr
    #
    @6
    cA
    @1
    @30
    @0
    @26
    @2
    @27
    adantr
    sselda
    @30
    @1
    tsksdom
    syl2anc
    @33
    @2
    @0
    @35
    @36
    @0
    @2
    @32
    simpll
    @13
    cA
    @1
    @28
    ensymd
    syl2anc
    @30
    @1
    cA
    sdomentr
    syl2anc
    ralrimiva
    vx
    cA
    iscard
    sylanbrc
    adantr
    eqtr3d
    @8
    @2
    @1
    c0
    wne
    #
    @9
    cina
    wcel
    @12
    @0
    @7
    @37
    @2
    @0
    @7
    wa
    #
    c0
    @1
    csdm
    wbr
    @37
    @38
    c0
    c0
    cr1
    cfv
    #
    @1
    csdm
    r10
    @0
    @7
    c0
    cA
    wcel
    #
    @39
    @1
    csdm
    wbr
    @0
    @40
    @7
    cA
    on0eln0
    biimpar
    cA
    c0
    r1sdom
    syldan
    syl5eqbrr
    @1
    cA
    cr1
    fvex
    0sdom
    sylib
    adantlr
    @1
    tskcard
    syl2anc
    eqeltrrd
    ex
    syl5bir
    orrd
    ex
    @3
    @2
    @4
    @3
    @1
    c0
    ctsk
    @3
    @1
    @39
    c0
    cA
    c0
    cr1
    fveq2
    r10
    syl6eq
    0tsk
    syl6eqel
    cA
    inatsk
    jaoi
    impbid1
end

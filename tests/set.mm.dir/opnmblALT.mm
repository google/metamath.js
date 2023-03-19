include "cvol.mm"
include "cdm.mm"
include "wcel.mm"
include "cioo.mm"
include "cq.mm"
include "cxp.mm"
include "cima.mm"
include "ctg.mm"
include "cfv.mm"
include "crn.mm"
include "cv.mm"
include "wss.mm"
include "cuni.mm"
include "wceq.mm"
include "wa.mm"
include "wex.mm"
include "ctb.mm"
include "wb.mm"
include "qtopbas.mm"
include "eltg3.mm"
include "ax-mp.mm"
include "ciun.mm"
include "uniiun.mm"
include "cn.mm"
include "cdom.mm"
include "wbr.mm"
include "wral.mm"
include "wi.mm"
include "ssdomg.mm"
include "cen.mm"
include "ccrd.mm"
include "cres.mm"
include "wfo.mm"
include "com.mm"
include "con0.mm"
include "omelon.mm"
include "qnnen.mm"
include "xpen.mm"
include "mp2an.mm"
include "xpnnen.mm"
include "entri.mm"
include "nnenom.mm"
include "entr2i.mm"
include "isnumi.mm"
include "wfun.mm"
include "cxr.mm"
include "cr.mm"
include "cpw.mm"
include "wf.mm"
include "ioof.mm"
include "ffun.mm"
include "qssre.mm"
include "ressxr.mm"
include "sstri.mm"
include "xpss12.mm"
include "fdmi.mm"
include "sseqtr4i.mm"
include "fores.mm"
include "fodomnum.mm"
include "mp2.mm"
include "domentr.mm"
include "domtr.mm"
include "sylancl.mm"
include "imassrn.mm"
include "wfn.mm"
include "co.mm"
include "ffn.mm"
include "ioombl.mm"
include "rgen2w.mm"
include "ffnov.mm"
include "mpbir2an.mm"
include "frn.mm"
include "sstr.mm"
include "mpan2.mm"
include "dfss3.mm"
include "sylib.mm"
include "iunmbl2.mm"
include "syl2anc.mm"
include "syl5eqel.mm"
include "eleq1.mm"
include "syl5ibrcom.mm"
include "imp.mm"
include "exlimiv.mm"
include "sylbi.mm"
include "eqid.mm"
include "tgqioo.mm"
include "eleq2s.mm"

theorem opnmblALT
  let cA: class A
  let vx: setvar x
  let vy: setvar y


  assert |- ( A e. ( topGen ` ran (,) ) -> A e. dom vol )

  proof
    cA
    cvol
    cdm
    #
    wcel
    #
    cA
    cioo
    cq
    cq
    cxp
    #
    cima
    #
    ctg
    cfv
    #
    cioo
    crn
    #
    ctg
    cfv
    cA
    @4
    wcel
    #
    vx
    cv
    #
    @3
    wss
    #
    cA
    @7
    cuni
    #
    wceq
    #
    wa
    #
    vx
    wex
    #
    @1
    @3
    ctb
    wcel
    #
    @6
    @12
    wb
    qtopbas
    vx
    cA
    @3
    ctb
    eltg3
    ax-mp
    @11
    @1
    vx
    @8
    @10
    @1
    @8
    @1
    @10
    @9
    @0
    wcel
    @8
    @9
    vy
    @7
    vy
    cv
    #
    ciun
    #
    @0
    vy
    @7
    uniiun
    @8
    @7
    cn
    cdom
    wbr
    #
    @14
    @0
    wcel
    vy
    @7
    wral
    #
    @15
    @0
    wcel
    @8
    @7
    @3
    cdom
    wbr
    #
    @3
    cn
    cdom
    wbr
    #
    @16
    @13
    @8
    @18
    wi
    qtopbas
    @7
    @3
    ctb
    ssdomg
    ax-mp
    @3
    @2
    cdom
    wbr
    #
    @2
    cn
    cen
    wbr
    @19
    @2
    ccrd
    cdm
    wcel
    #
    @2
    @3
    cioo
    @2
    cres
    #
    wfo
    #
    @20
    com
    con0
    wcel
    com
    @2
    cen
    wbr
    @21
    omelon
    @2
    cn
    com
    @2
    cn
    cn
    cxp
    #
    cn
    cq
    cn
    cen
    wbr
    #
    @25
    @2
    @24
    cen
    wbr
    qnnen
    qnnen
    cq
    cn
    cq
    cn
    xpen
    mp2an
    xpnnen
    entri
    #
    nnenom
    entr2i
    com
    @2
    isnumi
    mp2an
    cioo
    wfun
    #
    @2
    cioo
    cdm
    #
    wss
    @23
    cxr
    cxr
    cxp
    #
    cr
    cpw
    #
    cioo
    wf
    #
    @27
    ioof
    @29
    @30
    cioo
    ffun
    ax-mp
    @2
    @29
    @28
    cq
    cxr
    wss
    #
    @32
    @2
    @29
    wss
    cq
    cr
    cxr
    qssre
    ressxr
    sstri
    #
    @33
    cq
    cxr
    cq
    cxr
    xpss12
    mp2an
    @29
    @30
    cioo
    ioof
    fdmi
    sseqtr4i
    @2
    cioo
    fores
    mp2an
    @2
    @3
    @22
    fodomnum
    mp2
    @26
    @3
    @2
    cn
    domentr
    mp2an
    @7
    @3
    cn
    domtr
    sylancl
    @8
    @7
    @0
    wss
    #
    @17
    @8
    @3
    @0
    wss
    @34
    @3
    @5
    @0
    cioo
    @2
    imassrn
    @29
    @0
    cioo
    wf
    #
    @5
    @0
    wss
    @35
    cioo
    @29
    wfn
    #
    @7
    @14
    cioo
    co
    @0
    wcel
    #
    vy
    cxr
    wral
    vx
    cxr
    wral
    @31
    @36
    ioof
    @29
    @30
    cioo
    ffn
    ax-mp
    @37
    vx
    vy
    cxr
    cxr
    @7
    @14
    ioombl
    rgen2w
    vx
    vy
    cxr
    cxr
    @0
    cioo
    ffnov
    mpbir2an
    @29
    @0
    cioo
    frn
    ax-mp
    sstri
    @7
    @3
    @0
    sstr
    mpan2
    vy
    @7
    @0
    dfss3
    sylib
    @7
    @14
    vy
    iunmbl2
    syl2anc
    syl5eqel
    cA
    @9
    @0
    eleq1
    syl5ibrcom
    imp
    exlimiv
    sylbi
    @4
    @4
    eqid
    tgqioo
    eleq2s
end

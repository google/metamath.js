include "com.mm"
include "wcel.mm"
include "wpss.mm"
include "cen.mm"
include "wbr.mm"
include "wn.mm"
include "wi.mm"
include "wa.mm"
include "cv.mm"
include "csuc.mm"
include "wceq.mm"
include "wrex.mm"
include "c0.mm"
include "wss.mm"
include "0ss.mm"
include "sspsstr.mm"
include "mpan.mm"
include "wne.mm"
include "0pss.mm"
include "df-ne.mm"
include "bitri.mm"
include "sylib.mm"
include "nn0suc.mm"
include "orcanai.mm"
include "sylan2.mm"
include "cdom.mm"
include "wex.mm"
include "pssnel.mm"
include "csn.mm"
include "cdif.mm"
include "pssss.mm"
include "ssdif.mm"
include "wb.mm"
include "cin.mm"
include "disjsn.mm"
include "disj3.mm"
include "bitr3i.mm"
include "sseq1.mm"
include "sylbi.mm"
include "syl5ibr.mm"
include "cvv.mm"
include "vex.mm"
include "sucex.mm"
include "difss.mm"
include "ssexi.mm"
include "ssdomg.mm"
include "ax-mp.mm"
include "syl56.mm"
include "imp.mm"
include "phplem3.mm"
include "ensymd.mm"
include "domentr.mm"
include "syl2an.mm"
include "exp43.mm"
include "com4r.mm"
include "exlimiv.mm"
include "mpcom.mm"
include "endomtr.mm"
include "sssucid.mm"
include "mp2.mm"
include "sbth.mm"
include "sylancl.mm"
include "expcom.mm"
include "word.mm"
include "peano2b.mm"
include "nnord.mm"
include "sucid.mm"
include "nordeq.mm"
include "nneneq.mm"
include "sylanb.mm"
include "anidms.mm"
include "necon3bbid.mm"
include "mpbird.mm"
include "nsyli.mm"
include "syli.mm"
include "com12.mm"
include "psseq2.mm"
include "breq1.mm"
include "notbid.mm"
include "imbi12d.mm"
include "syl5ibrcom.mm"
include "rexlimiv.mm"
include "syl.mm"
include "ex.mm"
include "pm2.43d.mm"

theorem php
  let cA: class A
  let cB: class B
  let vx: setvar x
  let vy: setvar y


  assert |- ( ( A e. _om /\ B C. A ) -> -. A ~~ B )

  proof
    cA
    com
    wcel
    #
    cB
    cA
    wpss
    #
    cA
    cB
    cen
    wbr
    #
    wn
    #
    @0
    @1
    @3
    @0
    @1
    @1
    @3
    wi
    #
    @0
    @1
    wa
    cA
    vx
    cv
    #
    csuc
    #
    wceq
    #
    vx
    com
    wrex
    #
    @4
    @1
    @0
    cA
    c0
    wceq
    #
    wn
    #
    @8
    @1
    c0
    cA
    wpss
    #
    @10
    c0
    cB
    wss
    @1
    @11
    cB
    0ss
    c0
    cB
    cA
    sspsstr
    mpan
    @11
    cA
    c0
    wne
    @10
    cA
    0pss
    cA
    c0
    df-ne
    bitri
    sylib
    @0
    @9
    @8
    vx
    cA
    nn0suc
    orcanai
    sylan2
    @7
    @4
    vx
    com
    @5
    com
    wcel
    #
    @4
    @7
    cB
    @6
    wpss
    #
    @6
    cB
    cen
    wbr
    #
    wn
    #
    wi
    @13
    @12
    @15
    @12
    @13
    cB
    @5
    cdom
    wbr
    #
    @15
    vy
    cv
    #
    @6
    wcel
    #
    @17
    cB
    wcel
    wn
    #
    wa
    #
    vy
    wex
    @13
    @12
    @16
    wi
    #
    vy
    cB
    @6
    pssnel
    @20
    @13
    @21
    wi
    #
    vy
    @18
    @19
    @22
    @19
    @13
    @12
    @18
    @16
    @19
    @13
    @12
    @18
    @16
    @19
    @13
    wa
    cB
    @6
    @17
    csn
    #
    cdif
    #
    cdom
    wbr
    #
    @24
    @5
    cen
    wbr
    @16
    @12
    @18
    wa
    #
    @19
    @13
    @25
    @13
    cB
    @6
    wss
    #
    @19
    cB
    @24
    wss
    #
    @25
    cB
    @6
    pssss
    @27
    @28
    @19
    cB
    @23
    cdif
    #
    @24
    wss
    #
    cB
    @6
    @23
    ssdif
    @19
    cB
    @29
    wceq
    #
    @28
    @30
    wb
    @19
    cB
    @23
    cin
    c0
    wceq
    @31
    cB
    @17
    disjsn
    cB
    @23
    disj3
    bitr3i
    cB
    @29
    @24
    sseq1
    sylbi
    syl5ibr
    @24
    cvv
    wcel
    @28
    @25
    wi
    @24
    @6
    @5
    vx
    vex
    #
    sucex
    #
    @6
    @23
    difss
    ssexi
    cB
    @24
    cvv
    ssdomg
    ax-mp
    syl56
    imp
    @26
    @5
    @24
    @5
    @17
    @32
    vy
    vex
    phplem3
    ensymd
    cB
    @24
    @5
    domentr
    syl2an
    exp43
    com4r
    imp
    exlimiv
    mpcom
    @16
    @14
    @6
    @5
    cen
    wbr
    #
    @12
    @14
    @16
    @34
    @14
    @16
    wa
    @6
    @5
    cdom
    wbr
    @5
    @6
    cdom
    wbr
    #
    @34
    @6
    cB
    @5
    endomtr
    @6
    cvv
    wcel
    @5
    @6
    wss
    @35
    @33
    @5
    sssucid
    @5
    @6
    cvv
    ssdomg
    mp2
    @6
    @5
    sbth
    sylancl
    expcom
    @12
    @34
    wn
    @6
    @5
    wne
    #
    @12
    @6
    word
    #
    @5
    @6
    wcel
    @36
    @12
    @6
    com
    wcel
    #
    @37
    @5
    peano2b
    #
    @6
    nnord
    sylbi
    @5
    @32
    sucid
    @6
    @5
    nordeq
    sylancl
    @12
    @34
    @6
    @5
    @12
    @34
    @6
    @5
    wceq
    wb
    #
    @12
    @38
    @12
    @40
    @39
    @6
    @5
    nneneq
    sylanb
    anidms
    necon3bbid
    mpbird
    nsyli
    syli
    com12
    @7
    @1
    @13
    @3
    @15
    cA
    @6
    cB
    psseq2
    @7
    @2
    @14
    cA
    @6
    cB
    cen
    breq1
    notbid
    imbi12d
    syl5ibrcom
    rexlimiv
    syl
    ex
    pm2.43d
    imp
end

include "csuc.mm"
include "cen.mm"
include "wbr.mm"
include "cv.mm"
include "wf1o.mm"
include "wex.mm"
include "com.mm"
include "wcel.mm"
include "wa.mm"
include "bren.mm"
include "cfv.mm"
include "csn.mm"
include "cdif.mm"
include "cima.mm"
include "wf1.mm"
include "cvv.mm"
include "f1of1.mm"
include "adantl.mm"
include "sucex.mm"
include "wss.mm"
include "sssucid.mm"
include "f1imaen2g.mm"
include "mpanr12.mm"
include "sylancl.mm"
include "ensymd.mm"
include "word.mm"
include "wceq.mm"
include "nnord.mm"
include "orddif.mm"
include "syl.mm"
include "imaeq2d.mm"
include "wfn.mm"
include "f1ofn.mm"
include "sucid.mm"
include "fnsnfv.mm"
include "difeq2d.mm"
include "crn.mm"
include "cdm.mm"
include "imadmrn.mm"
include "eqcomi.mm"
include "wfo.mm"
include "f1ofo.mm"
include "forn.mm"
include "f1odm.mm"
include "3eqtr3a.mm"
include "difeq1d.mm"
include "ccnv.mm"
include "wfun.mm"
include "dff1o3.mm"
include "simprbi.mm"
include "imadif.mm"
include "3eqtr4rd.mm"
include "sylan9eq.mm"
include "breqtrd.mm"
include "fnfvelrn.mm"
include "wb.mm"
include "eleq2d.mm"
include "mpbid.mm"
include "fvex.mm"
include "phplem3.mm"
include "sylan2.mm"
include "entr.mm"
include "syl2an.mm"
include "anandirs.mm"
include "ex.mm"
include "exlimdv.mm"
include "syl5bi.mm"

theorem phplem4
  let cA: class A
  let cB: class B
  let vf: setvar f
  assume phplem2.1: |- A e. _V
  assume phplem2.2: |- B e. _V


  assert |- ( ( A e. _om /\ B e. _om ) -> ( suc A ~~ suc B -> A ~~ B ) )

  proof
    cA
    csuc
    #
    cB
    csuc
    #
    cen
    wbr
    @0
    @1
    vf
    cv
    #
    wf1o
    #
    vf
    wex
    cA
    com
    wcel
    #
    cB
    com
    wcel
    #
    wa
    #
    cA
    cB
    cen
    wbr
    #
    @0
    @1
    vf
    bren
    @6
    @3
    @7
    vf
    @6
    @3
    @7
    @4
    @5
    @3
    @7
    @4
    @3
    wa
    #
    cA
    @1
    cA
    @2
    cfv
    #
    csn
    #
    cdif
    #
    cen
    wbr
    @11
    cB
    cen
    wbr
    @7
    @5
    @3
    wa
    #
    @8
    cA
    @2
    cA
    cima
    #
    @11
    cen
    @8
    @13
    cA
    @8
    @0
    @1
    @2
    wf1
    #
    @1
    cvv
    wcel
    #
    @13
    cA
    cen
    wbr
    #
    @3
    @14
    @4
    @0
    @1
    @2
    f1of1
    adantl
    cB
    phplem2.2
    sucex
    @14
    @15
    wa
    cA
    @0
    wss
    cA
    cvv
    wcel
    @16
    cA
    sssucid
    phplem2.1
    @0
    @1
    cA
    @2
    cvv
    f1imaen2g
    mpanr12
    sylancl
    ensymd
    @4
    @3
    @13
    @2
    @0
    cA
    csn
    #
    cdif
    #
    cima
    #
    @11
    @4
    cA
    @18
    @2
    @4
    cA
    word
    cA
    @18
    wceq
    cA
    nnord
    cA
    orddif
    syl
    imaeq2d
    @3
    @2
    @0
    cima
    #
    @10
    cdif
    @20
    @2
    @17
    cima
    #
    cdif
    #
    @11
    @19
    @3
    @10
    @21
    @20
    @3
    @2
    @0
    wfn
    #
    cA
    @0
    wcel
    #
    @10
    @21
    wceq
    @0
    @1
    @2
    f1ofn
    #
    cA
    phplem2.1
    sucid
    #
    @0
    cA
    @2
    fnsnfv
    sylancl
    difeq2d
    @3
    @1
    @20
    @10
    @3
    @2
    crn
    #
    @2
    @2
    cdm
    #
    cima
    #
    @1
    @20
    @29
    @27
    @2
    imadmrn
    eqcomi
    @3
    @0
    @1
    @2
    wfo
    #
    @27
    @1
    wceq
    @0
    @1
    @2
    f1ofo
    #
    @0
    @1
    @2
    forn
    #
    syl
    @3
    @28
    @0
    @2
    @0
    @1
    @2
    f1odm
    imaeq2d
    3eqtr3a
    difeq1d
    @3
    @2
    ccnv
    wfun
    #
    @19
    @22
    wceq
    @3
    @30
    @33
    @0
    @1
    @2
    dff1o3
    simprbi
    @0
    @17
    @2
    imadif
    syl
    3eqtr4rd
    sylan9eq
    breqtrd
    @12
    cB
    @11
    @3
    @5
    @9
    @1
    wcel
    #
    cB
    @11
    cen
    wbr
    @3
    @9
    @27
    wcel
    #
    @34
    @3
    @23
    @24
    @35
    @25
    @26
    @0
    cA
    @2
    fnfvelrn
    sylancl
    @3
    @30
    @35
    @34
    wb
    @31
    @30
    @27
    @1
    @9
    @32
    eleq2d
    syl
    mpbid
    cB
    @9
    phplem2.2
    cA
    @2
    fvex
    phplem3
    sylan2
    ensymd
    cA
    @11
    cB
    entr
    syl2an
    anandirs
    ex
    exlimdv
    syl5bi
end

include "cen.mm"
include "wbr.mm"
include "cv.mm"
include "wf1o.mm"
include "wex.mm"
include "cfin1a.mm"
include "wcel.mm"
include "wi.mm"
include "ensym.mm"
include "bren.mm"
include "sylib.mm"
include "wa.mm"
include "cfn.mm"
include "cdif.mm"
include "wo.mm"
include "cpw.mm"
include "wral.mm"
include "wss.mm"
include "elpwi.mm"
include "cima.mm"
include "simplr.mm"
include "crn.mm"
include "imassrn.mm"
include "wf.mm"
include "f1of.mm"
include "ad2antrr.mm"
include "frn.mm"
include "syl.mm"
include "syl5ss.mm"
include "fin1ai.mm"
include "syl2anc.mm"
include "wb.mm"
include "wf1.mm"
include "cvv.mm"
include "f1of1.mm"
include "simpr.mm"
include "vex.mm"
include "a1i.mm"
include "f1imaeng.mm"
include "syl3anc.mm"
include "enfi.mm"
include "ccnv.mm"
include "wfun.mm"
include "wceq.mm"
include "df-f1.mm"
include "simprbi.mm"
include "imadif.mm"
include "3syl.mm"
include "wfo.mm"
include "f1ofo.mm"
include "foima.mm"
include "difeq1d.mm"
include "eqtrd.mm"
include "difssd.mm"
include "adantr.mm"
include "dmfex.mm"
include "sylancr.mm"
include "difexg.mm"
include "eqbrtrrd.mm"
include "orbi12d.mm"
include "mpbid.mm"
include "sylan2.mm"
include "ralrimiva.mm"
include "isfin1a.mm"
include "mpbird.mm"
include "ex.mm"
include "exlimiv.mm"

theorem enfin1ai
  let cA: class A
  let cB: class B
  let va: setvar a
  let vb: setvar b
  let vc: setvar c
  let vd: setvar d
  let vf: setvar f
  let vg: setvar g
  let vx: setvar x
  let vy: setvar y
  let cV: class V


  assert |- ( A ~~ B -> ( A e. Fin1a -> B e. Fin1a ) )

  proof
    cA
    cB
    cen
    wbr
    #
    cB
    cA
    vf
    cv
    #
    wf1o
    #
    vf
    wex
    #
    cA
    cfin1a
    wcel
    #
    cB
    cfin1a
    wcel
    #
    wi
    #
    @0
    cB
    cA
    cen
    wbr
    @3
    cA
    cB
    ensym
    cB
    cA
    vf
    bren
    sylib
    @2
    @6
    vf
    @2
    @4
    @5
    @2
    @4
    wa
    #
    @5
    vx
    cv
    #
    cfn
    wcel
    #
    cB
    @8
    cdif
    #
    cfn
    wcel
    #
    wo
    #
    vx
    cB
    cpw
    #
    wral
    #
    @7
    @12
    vx
    @13
    @8
    @13
    wcel
    @7
    @8
    cB
    wss
    #
    @12
    @8
    cB
    elpwi
    @7
    @15
    wa
    #
    @1
    @8
    cima
    #
    cfn
    wcel
    #
    cA
    @17
    cdif
    #
    cfn
    wcel
    #
    wo
    #
    @12
    @16
    @4
    @17
    cA
    wss
    @21
    @2
    @4
    @15
    simplr
    @16
    @17
    @1
    crn
    #
    cA
    @1
    @8
    imassrn
    @16
    cB
    cA
    @1
    wf
    #
    @22
    cA
    wss
    @2
    @23
    @4
    @15
    cB
    cA
    @1
    f1of
    #
    ad2antrr
    cB
    cA
    @1
    frn
    syl
    syl5ss
    cA
    @17
    fin1ai
    syl2anc
    @16
    @18
    @9
    @20
    @11
    @16
    @17
    @8
    cen
    wbr
    #
    @18
    @9
    wb
    @16
    cB
    cA
    @1
    wf1
    #
    @15
    @8
    cvv
    wcel
    #
    @25
    @2
    @26
    @4
    @15
    cB
    cA
    @1
    f1of1
    ad2antrr
    #
    @7
    @15
    simpr
    @27
    @16
    vx
    vex
    a1i
    cB
    cA
    @8
    @1
    cvv
    f1imaeng
    syl3anc
    @17
    @8
    enfi
    syl
    @16
    @19
    @10
    cen
    wbr
    @20
    @11
    wb
    @16
    @1
    @10
    cima
    #
    @19
    @10
    cen
    @16
    @29
    @1
    cB
    cima
    #
    @17
    cdif
    #
    @19
    @16
    @26
    @1
    ccnv
    wfun
    #
    @29
    @31
    wceq
    @28
    @26
    @23
    @32
    cB
    cA
    @1
    df-f1
    simprbi
    cB
    @8
    @1
    imadif
    3syl
    @16
    @30
    cA
    @17
    @2
    @30
    cA
    wceq
    #
    @4
    @15
    @2
    cB
    cA
    @1
    wfo
    @33
    cB
    cA
    @1
    f1ofo
    cB
    cA
    @1
    foima
    syl
    ad2antrr
    difeq1d
    eqtrd
    @16
    @26
    @10
    cB
    wss
    @10
    cvv
    wcel
    #
    @29
    @10
    cen
    wbr
    @28
    @16
    cB
    @8
    difssd
    @16
    cB
    cvv
    wcel
    #
    @34
    @7
    @35
    @15
    @7
    @1
    cvv
    wcel
    @23
    @35
    vf
    vex
    @2
    @23
    @4
    @24
    adantr
    cB
    cA
    cvv
    @1
    dmfex
    sylancr
    #
    adantr
    cB
    @8
    cvv
    difexg
    syl
    cB
    cA
    @10
    @1
    cvv
    f1imaeng
    syl3anc
    eqbrtrrd
    @19
    @10
    enfi
    syl
    orbi12d
    mpbid
    sylan2
    ralrimiva
    @7
    @35
    @5
    @14
    wb
    @36
    vx
    cB
    cvv
    isfin1a
    syl
    mpbird
    ex
    exlimiv
    syl
end

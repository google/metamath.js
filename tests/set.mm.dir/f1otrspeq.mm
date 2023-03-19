include "wf1o.mm"
include "wa.mm"
include "cid.mm"
include "cdif.mm"
include "cdm.mm"
include "c2o.mm"
include "cen.mm"
include "wbr.mm"
include "wceq.mm"
include "wfn.mm"
include "f1ofn.mm"
include "ad2antrr.mm"
include "ad2antlr.mm"
include "cv.mm"
include "wcel.mm"
include "cfv.mm"
include "csn.mm"
include "wmo.mm"
include "c1o.mm"
include "com.mm"
include "csuc.mm"
include "1onn.mm"
include "a1i.mm"
include "simplrr.mm"
include "simplrl.mm"
include "df-2o.mm"
include "syl6breq.mm"
include "eqbrtrd.mm"
include "simpr.mm"
include "dif1en.mm"
include "syl3anc.mm"
include "weu.mm"
include "euen1b.mm"
include "eumo.mm"
include "sylbi.mm"
include "syl.mm"
include "wi.mm"
include "f1omvdmvd.mm"
include "ex.mm"
include "wb.mm"
include "eleq2.mm"
include "ad2antll.mm"
include "difeq1.mm"
include "eleq2d.mm"
include "3imtr4d.mm"
include "imp.mm"
include "simplr.mm"
include "sylan.mm"
include "cvv.mm"
include "fvex.mm"
include "pm3.2i.mm"
include "eleq1.mm"
include "moi.mm"
include "mp3an1.mm"
include "syl12anc.mm"
include "adantlr.mm"
include "wn.mm"
include "wne.mm"
include "fnelnfp.mm"
include "bitrd.mm"
include "necon2bbid.mm"
include "biimpar.mm"
include "eqtr4d.mm"
include "pm2.61dan.mm"
include "eqfnfvd.mm"

theorem f1otrspeq
  let cA: class A
  let cF: class F
  let cG: class G
  let vx: setvar x
  let vy: setvar y


  assert |- ( ( ( F : A -1-1-onto-> A /\ G : A -1-1-onto-> A ) /\ ( dom ( F \ _I ) ~~ 2o /\ dom ( G \ _I ) = dom ( F \ _I ) ) ) -> F = G )

  proof
    cA
    cA
    cF
    wf1o
    #
    cA
    cA
    cG
    wf1o
    #
    wa
    #
    cF
    cid
    cdif
    cdm
    #
    c2o
    cen
    wbr
    #
    cG
    cid
    cdif
    cdm
    #
    @3
    wceq
    #
    wa
    #
    wa
    #
    vx
    cA
    cF
    cG
    @0
    cF
    cA
    wfn
    #
    @1
    @7
    cA
    cA
    cF
    f1ofn
    ad2antrr
    #
    @1
    cG
    cA
    wfn
    #
    @0
    @7
    cA
    cA
    cG
    f1ofn
    ad2antlr
    #
    @8
    vx
    cv
    #
    cA
    wcel
    #
    wa
    #
    @13
    @5
    wcel
    #
    @13
    cF
    cfv
    #
    @13
    cG
    cfv
    #
    wceq
    #
    @8
    @16
    @19
    @14
    @8
    @16
    wa
    #
    vy
    cv
    #
    @5
    @13
    csn
    #
    cdif
    #
    wcel
    #
    vy
    wmo
    #
    @17
    @23
    wcel
    #
    @18
    @23
    wcel
    #
    @19
    @20
    @23
    c1o
    cen
    wbr
    #
    @25
    @20
    c1o
    com
    wcel
    #
    @5
    c1o
    csuc
    #
    cen
    wbr
    @16
    @28
    @29
    @20
    1onn
    a1i
    @20
    @5
    @3
    @30
    cen
    @2
    @4
    @6
    @16
    simplrr
    @20
    @3
    c2o
    @30
    cen
    @2
    @4
    @6
    @16
    simplrl
    df-2o
    syl6breq
    eqbrtrd
    @8
    @16
    simpr
    @5
    c1o
    @13
    dif1en
    syl3anc
    @28
    @24
    vy
    weu
    @25
    vy
    @23
    euen1b
    @24
    vy
    eumo
    sylbi
    syl
    @8
    @16
    @26
    @8
    @13
    @3
    wcel
    #
    @17
    @3
    @22
    cdif
    #
    wcel
    #
    @16
    @26
    @0
    @31
    @33
    wi
    @1
    @7
    @0
    @31
    @33
    cA
    cF
    @13
    f1omvdmvd
    ex
    ad2antrr
    @6
    @16
    @31
    wb
    @2
    @4
    @5
    @3
    @13
    eleq2
    ad2antll
    @6
    @26
    @33
    wb
    @2
    @4
    @6
    @23
    @32
    @17
    @5
    @3
    @22
    difeq1
    eleq2d
    ad2antll
    3imtr4d
    imp
    @8
    @1
    @16
    @27
    @0
    @1
    @7
    simplr
    cA
    cG
    @13
    f1omvdmvd
    sylan
    @17
    cvv
    wcel
    #
    @18
    cvv
    wcel
    #
    wa
    @25
    @26
    @27
    wa
    @19
    @34
    @35
    @13
    cF
    fvex
    @13
    cG
    fvex
    pm3.2i
    @24
    @26
    @27
    vy
    @17
    @18
    cvv
    cvv
    @21
    @17
    @23
    eleq1
    @21
    @18
    @23
    eleq1
    moi
    mp3an1
    syl12anc
    adantlr
    @15
    @16
    wn
    #
    wa
    @17
    @13
    @18
    @15
    @17
    @13
    wceq
    @36
    @15
    @16
    @17
    @13
    @15
    @16
    @31
    @17
    @13
    wne
    #
    @15
    @5
    @3
    @13
    @2
    @4
    @6
    @14
    simplrr
    eleq2d
    @8
    @9
    @14
    @31
    @37
    wb
    @10
    cA
    cF
    @13
    fnelnfp
    sylan
    bitrd
    necon2bbid
    biimpar
    @15
    @18
    @13
    wceq
    @36
    @15
    @16
    @18
    @13
    @8
    @11
    @14
    @16
    @18
    @13
    wne
    wb
    @12
    cA
    cG
    @13
    fnelnfp
    sylan
    necon2bbid
    biimpar
    eqtr4d
    pm2.61dan
    eqfnfvd
end

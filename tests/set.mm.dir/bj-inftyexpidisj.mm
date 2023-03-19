include "cinftyexpi.mm"
include "cdm.mm"
include "wcel.mm"
include "cfv.mm"
include "cc.mm"
include "wn.mm"
include "cop.mm"
include "wceq.mm"
include "cpi.mm"
include "cneg.mm"
include "cioc.mm"
include "co.mm"
include "cv.mm"
include "opeq1.mm"
include "df-bj-inftyexpi.mm"
include "opex.mm"
include "fvmpt.mm"
include "dmmpti.mm"
include "eleq2s.mm"
include "cvv.mm"
include "cpr.mm"
include "cnex.mm"
include "prid2.mm"
include "csn.mm"
include "wo.mm"
include "eqid.mm"
include "olci.mm"
include "wb.mm"
include "elopg.mm"
include "mpan2.mm"
include "mpbiri.mm"
include "en3lp.mm"
include "bj-imn3ani.mm"
include "sylancr.mm"
include "c0.mm"
include "opprc1.mm"
include "0ncn.mm"
include "eleq1.mm"
include "mtbiri.mm"
include "syl.mm"
include "pm2.61i.mm"
include "eqcom.mm"
include "biimpi.mm"
include "eleq1d.mm"
include "mtbii.mm"
include "ndmfv.mm"

theorem bj-inftyexpidisj
  let cA: class A
  let vx: setvar x


  assert |- -. ( inftyexpi ` A ) e. CC

  proof
    cA
    cinftyexpi
    cdm
    #
    wcel
    #
    cA
    cinftyexpi
    cfv
    #
    cc
    wcel
    #
    wn
    #
    @1
    @2
    cA
    cc
    cop
    #
    wceq
    #
    @4
    @6
    cA
    cpi
    cneg
    cpi
    cioc
    co
    #
    @0
    vx
    cA
    vx
    cv
    #
    cc
    cop
    #
    @5
    @7
    cinftyexpi
    @8
    cA
    cc
    opeq1
    vx
    df-bj-inftyexpi
    #
    cA
    cc
    opex
    fvmpt
    vx
    @7
    @9
    cinftyexpi
    @8
    cc
    opex
    @10
    dmmpti
    eleq2s
    @6
    @5
    cc
    wcel
    #
    @3
    cA
    cvv
    wcel
    #
    @11
    wn
    #
    @12
    cc
    cA
    cc
    cpr
    #
    wcel
    #
    @14
    @5
    wcel
    #
    @13
    cA
    cc
    cnex
    prid2
    @12
    @16
    @14
    cA
    csn
    wceq
    #
    @14
    @14
    wceq
    #
    wo
    #
    @18
    @17
    @14
    eqid
    olci
    @12
    cc
    cvv
    wcel
    @16
    @19
    wb
    cnex
    cA
    cc
    @14
    cvv
    cvv
    elopg
    mpan2
    mpbiri
    @15
    @16
    @11
    cc
    @14
    @5
    en3lp
    bj-imn3ani
    sylancr
    @12
    wn
    @5
    c0
    wceq
    #
    @13
    cA
    cc
    opprc1
    @20
    @11
    c0
    cc
    wcel
    #
    0ncn
    @5
    c0
    cc
    eleq1
    mtbiri
    syl
    pm2.61i
    @6
    @5
    @2
    cc
    @6
    @5
    @2
    wceq
    @2
    @5
    eqcom
    biimpi
    eleq1d
    mtbii
    syl
    @1
    wn
    #
    @3
    @21
    0ncn
    @22
    @2
    c0
    cc
    cA
    cinftyexpi
    ndmfv
    eleq1d
    mtbiri
    pm2.61i
end

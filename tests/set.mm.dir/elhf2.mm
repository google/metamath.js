include "chf.mm"
include "wcel.mm"
include "cv.mm"
include "cr1.mm"
include "cfv.mm"
include "com.mm"
include "wrex.mm"
include "crnk.mm"
include "elhf.mm"
include "con0.mm"
include "wceq.mm"
include "wo.mm"
include "wb.mm"
include "omon.mm"
include "wa.mm"
include "nnon.mm"
include "rankr1a.mm"
include "syl.mm"
include "adantl.mm"
include "wi.mm"
include "elnn.mm"
include "expcom.mm"
include "sylbid.mm"
include "rexlimdva.mm"
include "csuc.mm"
include "peano2.mm"
include "adantr.mm"
include "cpw.mm"
include "wss.mm"
include "cvv.mm"
include "r1rankid.mm"
include "mp1i.mm"
include "elpw.mm"
include "sylibr.mm"
include "r1suc.mm"
include "eleqtrrd.mm"
include "fveq2.mm"
include "eleq2d.mm"
include "rspcev.mm"
include "syl2anc.mm"
include "impbid.mm"
include "tz9.13.mm"
include "rankon.mm"
include "2th.mm"
include "rexeq.mm"
include "eleq2.mm"
include "bibi12d.mm"
include "mpbiri.mm"
include "jaoi.mm"
include "ax-mp.mm"
include "bitri.mm"

theorem elhf2
  let cA: class A
  let vx: setvar x
  assume elhf2.1: |- A e. _V


  assert |- ( A e. Hf <-> ( rank ` A ) e. _om )

  proof
    cA
    chf
    wcel
    cA
    vx
    cv
    #
    cr1
    cfv
    #
    wcel
    #
    vx
    com
    wrex
    #
    cA
    crnk
    cfv
    #
    com
    wcel
    #
    vx
    cA
    elhf
    com
    con0
    wcel
    #
    com
    con0
    wceq
    #
    wo
    @3
    @5
    wb
    #
    omon
    @6
    @8
    @7
    @6
    @3
    @5
    @6
    @2
    @5
    vx
    com
    @6
    @0
    com
    wcel
    #
    wa
    @2
    @4
    @0
    wcel
    #
    @5
    @9
    @2
    @10
    wb
    #
    @6
    @9
    @0
    con0
    wcel
    @11
    @0
    nnon
    cA
    @0
    elhf2.1
    rankr1a
    syl
    adantl
    @9
    @10
    @5
    wi
    @6
    @10
    @9
    @5
    @4
    @0
    elnn
    expcom
    adantl
    sylbid
    rexlimdva
    @5
    @6
    @3
    @5
    @6
    wa
    #
    @4
    csuc
    #
    com
    wcel
    #
    cA
    @13
    cr1
    cfv
    #
    wcel
    #
    @3
    @5
    @14
    @6
    @4
    peano2
    adantr
    @12
    cA
    @4
    cr1
    cfv
    #
    cpw
    #
    @15
    @12
    cA
    @17
    wss
    #
    cA
    @18
    wcel
    cA
    cvv
    wcel
    @19
    @12
    elhf2.1
    cA
    cvv
    r1rankid
    mp1i
    cA
    @17
    elhf2.1
    elpw
    sylibr
    @5
    @15
    @18
    wceq
    #
    @6
    @5
    @4
    con0
    wcel
    #
    @20
    @4
    nnon
    @4
    r1suc
    syl
    adantr
    eleqtrrd
    @2
    @16
    vx
    @13
    com
    @0
    @13
    wceq
    @1
    @15
    cA
    @0
    @13
    cr1
    fveq2
    eleq2d
    rspcev
    syl2anc
    expcom
    impbid
    @7
    @8
    @2
    vx
    con0
    wrex
    #
    @21
    wb
    @22
    @21
    vx
    cA
    elhf2.1
    tz9.13
    cA
    rankon
    2th
    @7
    @3
    @22
    @5
    @21
    @2
    vx
    com
    con0
    rexeq
    com
    con0
    @4
    eleq2
    bibi12d
    mpbiri
    jaoi
    ax-mp
    bitri
end

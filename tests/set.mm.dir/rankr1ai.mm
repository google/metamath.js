include "cr1.mm"
include "cfv.mm"
include "wcel.mm"
include "cv.mm"
include "csuc.mm"
include "con0.mm"
include "crab.mm"
include "cint.mm"
include "wss.mm"
include "wrex.mm"
include "crnk.mm"
include "cdm.mm"
include "elfvdm.mm"
include "cpw.mm"
include "ciun.mm"
include "r1val1.mm"
include "eleq2d.mm"
include "eliun.mm"
include "syl6bb.mm"
include "wa.mm"
include "wb.mm"
include "word.mm"
include "wi.mm"
include "wlim.mm"
include "wfun.mm"
include "r1funlim.mm"
include "simpri.mm"
include "limord.mm"
include "ax-mp.mm"
include "ordtr1.mm"
include "ancoms.mm"
include "r1sucg.mm"
include "syl.mm"
include "ordsson.mm"
include "sseldi.mm"
include "rabid.mm"
include "intss1.mm"
include "sylbir.mm"
include "sylan.mm"
include "ex.mm"
include "sylbird.mm"
include "reximdva.mm"
include "sylbid.mm"
include "mpcom.mm"
include "cima.mm"
include "cuni.mm"
include "wceq.mm"
include "r1elwf.mm"
include "rankvalb.mm"
include "sseq1d.mm"
include "adantr.mm"
include "rankon.mm"
include "ontr2.mm"
include "sylancr.mm"
include "expcomd.mm"
include "imp.mm"
include "rexlimdva.mm"
include "mpd.mm"

theorem rankr1ai
  let cA: class A
  let cB: class B
  let vx: setvar x


  assert |- ( A e. ( R1 ` B ) -> ( rank ` A ) e. B )

  proof
    cA
    cB
    cr1
    cfv
    #
    wcel
    #
    cA
    vx
    cv
    #
    csuc
    cr1
    cfv
    #
    wcel
    #
    vx
    con0
    crab
    #
    cint
    #
    @2
    wss
    #
    vx
    cB
    wrex
    #
    cA
    crnk
    cfv
    #
    cB
    wcel
    #
    cB
    cr1
    cdm
    #
    wcel
    #
    @1
    @8
    cA
    cB
    cr1
    elfvdm
    #
    @12
    @1
    cA
    @2
    cr1
    cfv
    cpw
    #
    wcel
    #
    vx
    cB
    wrex
    #
    @8
    @12
    @1
    cA
    vx
    cB
    @14
    ciun
    #
    wcel
    @16
    @12
    @0
    @17
    cA
    vx
    cB
    r1val1
    eleq2d
    vx
    cA
    cB
    @14
    eliun
    syl6bb
    @12
    @15
    @7
    vx
    cB
    @12
    @2
    cB
    wcel
    #
    wa
    #
    @15
    @4
    @7
    @19
    @2
    @11
    wcel
    #
    @4
    @15
    wb
    @18
    @12
    @20
    @11
    word
    #
    @18
    @12
    wa
    @20
    wi
    @11
    wlim
    #
    @21
    cr1
    wfun
    @22
    r1funlim
    simpri
    @11
    limord
    ax-mp
    #
    @2
    cB
    @11
    ordtr1
    ax-mp
    ancoms
    #
    @20
    @3
    @14
    cA
    @2
    r1sucg
    eleq2d
    syl
    @19
    @4
    @7
    @19
    @2
    con0
    wcel
    #
    @4
    @7
    @19
    @11
    con0
    @2
    @21
    @11
    con0
    wss
    @23
    @11
    ordsson
    ax-mp
    #
    @24
    sseldi
    @25
    @4
    wa
    @2
    @5
    wcel
    @7
    @4
    vx
    con0
    rabid
    @2
    @5
    intss1
    sylbir
    sylan
    ex
    sylbird
    reximdva
    sylbid
    mpcom
    @1
    @7
    @10
    vx
    cB
    @1
    @18
    wa
    @7
    @9
    @2
    wss
    #
    @10
    @1
    @27
    @7
    wb
    @18
    @1
    @9
    @6
    @2
    @1
    cA
    cr1
    con0
    cima
    cuni
    wcel
    @9
    @6
    wceq
    cA
    cB
    r1elwf
    vx
    cA
    rankvalb
    syl
    sseq1d
    adantr
    @1
    @18
    @27
    @10
    wi
    @1
    @27
    @18
    @10
    @1
    @9
    con0
    wcel
    cB
    con0
    wcel
    @27
    @18
    wa
    @10
    wi
    cA
    rankon
    @1
    @11
    con0
    cB
    @26
    @13
    sseldi
    @9
    @2
    cB
    ontr2
    sylancr
    expcomd
    imp
    sylbird
    rexlimdva
    mpd
end

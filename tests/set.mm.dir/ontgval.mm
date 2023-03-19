include "con0.mm"
include "wcel.mm"
include "ctg.mm"
include "cfv.mm"
include "cuni.mm"
include "csuc.mm"
include "cv.mm"
include "wa.mm"
include "wss.mm"
include "cpw.mm"
include "cin.mm"
include "wceq.mm"
include "eltg4i.mm"
include "cvv.mm"
include "inex1g.mm"
include "onss.mm"
include "ssinss1.mm"
include "syl.mm"
include "ssonuni.mm"
include "sylc.mm"
include "eleq1.mm"
include "biimprd.mm"
include "syl2imc.mm"
include "onuni.mm"
include "suceloni.mm"
include "jctird.mm"
include "wi.mm"
include "tg1.mm"
include "a1i.mm"
include "sucidg.mm"
include "ontr2.mm"
include "syl6c.mm"
include "wo.mm"
include "elsuci.mm"
include "word.mm"
include "eloni.mm"
include "orduniss.mm"
include "bastg.mm"
include "sstrd.mm"
include "sseld.mm"
include "ssid.mm"
include "eltg3i.mm"
include "mpan2.mm"
include "eleq1a.mm"
include "jaod.mm"
include "syl5.mm"
include "impbid.mm"
include "eqrdv.mm"

theorem ontgval
  let cB: class B
  let vx: setvar x


  assert |- ( B e. On -> ( topGen ` B ) = suc U. B )

  proof
    cB
    con0
    wcel
    #
    vx
    cB
    ctg
    cfv
    #
    cB
    cuni
    #
    csuc
    #
    @0
    vx
    cv
    #
    @1
    wcel
    #
    @4
    @3
    wcel
    #
    @0
    @5
    @4
    con0
    wcel
    #
    @3
    con0
    wcel
    #
    wa
    @4
    @2
    wss
    #
    @2
    @3
    wcel
    #
    wa
    @6
    @0
    @5
    @7
    @8
    @5
    @4
    cB
    @4
    cpw
    #
    cin
    #
    cuni
    #
    wceq
    #
    @0
    @13
    con0
    wcel
    #
    @7
    @4
    cB
    eltg4i
    @0
    @12
    cvv
    wcel
    @12
    con0
    wss
    #
    @15
    cB
    @11
    con0
    inex1g
    @0
    cB
    con0
    wss
    @16
    cB
    onss
    cB
    @11
    con0
    ssinss1
    syl
    @12
    cvv
    ssonuni
    sylc
    @14
    @7
    @15
    @4
    @13
    con0
    eleq1
    biimprd
    syl2imc
    @0
    @2
    con0
    wcel
    #
    @8
    cB
    onuni
    #
    @2
    suceloni
    syl
    jctird
    @0
    @5
    @9
    @10
    @5
    @9
    wi
    @0
    @4
    cB
    tg1
    a1i
    @0
    @17
    @10
    @18
    @2
    con0
    sucidg
    syl
    jctird
    @4
    @2
    @3
    ontr2
    syl6c
    @6
    @4
    @2
    wcel
    #
    @4
    @2
    wceq
    #
    wo
    @0
    @5
    @4
    @2
    elsuci
    @0
    @19
    @5
    @20
    @0
    @2
    @1
    @4
    @0
    @2
    cB
    @1
    @0
    cB
    word
    @2
    cB
    wss
    cB
    eloni
    cB
    orduniss
    syl
    cB
    con0
    bastg
    sstrd
    sseld
    @0
    @2
    @1
    wcel
    #
    @20
    @5
    wi
    @0
    cB
    cB
    wss
    @21
    cB
    ssid
    cB
    cB
    con0
    eltg3i
    mpan2
    @2
    @1
    @4
    eleq1a
    syl
    jaod
    syl5
    impbid
    eqrdv
end

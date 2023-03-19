include "cr1.mm"
include "con0.mm"
include "cima.mm"
include "cuni.mm"
include "wcel.mm"
include "cfv.mm"
include "cpw.mm"
include "csuc.mm"
include "wb.mm"
include "wi.mm"
include "wa.mm"
include "crnk.mm"
include "rankpwi.mm"
include "eleq1d.mm"
include "word.mm"
include "eloni.mm"
include "ordsucelsuc.mm"
include "syl.mm"
include "bicomd.mm"
include "sylan9bb.mm"
include "cdm.mm"
include "pwwf.mm"
include "biimpi.mm"
include "suceloni.mm"
include "wfn.mm"
include "wceq.mm"
include "r1fnon.mm"
include "fndm.mm"
include "ax-mp.mm"
include "syl6eleqr.mm"
include "rankr1ag.mm"
include "syl2an.mm"
include "eleq2i.mm"
include "sylan2br.mm"
include "3bitr4rd.mm"
include "ex.mm"
include "wn.mm"
include "r1elwf.mm"
include "wss.mm"
include "r1elssi.mm"
include "ssid.mm"
include "cvv.mm"
include "pwexr.mm"
include "elpwg.mm"
include "mpbiri.mm"
include "sseldd.mm"
include "pm5.21ni.mm"
include "a1d.mm"
include "pm2.61i.mm"

theorem r1pw
  let cA: class A
  let cB: class B
  let vx: setvar x


  assert |- ( B e. On -> ( A e. ( R1 ` B ) <-> ~P A e. ( R1 ` suc B ) ) )

  proof
    cA
    cr1
    con0
    cima
    cuni
    #
    wcel
    #
    cB
    con0
    wcel
    #
    cA
    cB
    cr1
    cfv
    wcel
    #
    cA
    cpw
    #
    cB
    csuc
    #
    cr1
    cfv
    #
    wcel
    #
    wb
    #
    wi
    @1
    @2
    @8
    @1
    @2
    wa
    @4
    crnk
    cfv
    #
    @5
    wcel
    #
    cA
    crnk
    cfv
    #
    cB
    wcel
    #
    @7
    @3
    @1
    @10
    @11
    csuc
    #
    @5
    wcel
    #
    @2
    @12
    @1
    @9
    @13
    @5
    cA
    rankpwi
    eleq1d
    @2
    @12
    @14
    @2
    cB
    word
    @12
    @14
    wb
    cB
    eloni
    @11
    cB
    ordsucelsuc
    syl
    bicomd
    sylan9bb
    @1
    @4
    @0
    wcel
    #
    @5
    cr1
    cdm
    #
    wcel
    @7
    @10
    wb
    @2
    @1
    @15
    cA
    pwwf
    biimpi
    @2
    @5
    con0
    @16
    cB
    suceloni
    cr1
    con0
    wfn
    @16
    con0
    wceq
    r1fnon
    con0
    cr1
    fndm
    ax-mp
    #
    syl6eleqr
    @4
    @5
    rankr1ag
    syl2an
    @2
    @1
    cB
    @16
    wcel
    @3
    @12
    wb
    @16
    con0
    cB
    @17
    eleq2i
    cA
    cB
    rankr1ag
    sylan2br
    3bitr4rd
    ex
    @1
    wn
    @8
    @2
    @3
    @1
    @7
    cA
    cB
    r1elwf
    @7
    @4
    @0
    cA
    @7
    @15
    @4
    @0
    wss
    @4
    @5
    r1elwf
    @4
    r1elssi
    syl
    @7
    cA
    @4
    wcel
    #
    cA
    cA
    wss
    #
    cA
    ssid
    @7
    cA
    cvv
    wcel
    @18
    @19
    wb
    cA
    @6
    pwexr
    cA
    cA
    cvv
    elpwg
    syl
    mpbiri
    sseldd
    pm5.21ni
    a1d
    pm2.61i
end

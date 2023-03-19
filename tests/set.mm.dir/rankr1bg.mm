include "cr1.mm"
include "con0.mm"
include "cima.mm"
include "cuni.mm"
include "wcel.mm"
include "cdm.mm"
include "wa.mm"
include "csuc.mm"
include "cfv.mm"
include "crnk.mm"
include "wss.mm"
include "wb.mm"
include "wlim.mm"
include "wfun.mm"
include "r1funlim.mm"
include "simpri.mm"
include "limsuc.mm"
include "ax-mp.mm"
include "rankr1ag.mm"
include "sylan2b.mm"
include "cpw.mm"
include "wceq.mm"
include "r1sucg.mm"
include "adantl.mm"
include "eleq2d.mm"
include "fvex.mm"
include "elpw2.mm"
include "syl6rbb.mm"
include "rankon.mm"
include "word.mm"
include "limord.mm"
include "ordelon.mm"
include "mpan.mm"
include "onsssuc.mm"
include "sylancr.mm"
include "3bitr4d.mm"

theorem rankr1bg
  let cA: class A
  let cB: class B


  assert |- ( ( A e. U. ( R1 " On ) /\ B e. dom R1 ) -> ( A C_ ( R1 ` B ) <-> ( rank ` A ) C_ B ) )

  proof
    cA
    cr1
    con0
    cima
    cuni
    wcel
    #
    cB
    cr1
    cdm
    #
    wcel
    #
    wa
    #
    cA
    cB
    csuc
    #
    cr1
    cfv
    #
    wcel
    #
    cA
    crnk
    cfv
    #
    @4
    wcel
    #
    cA
    cB
    cr1
    cfv
    #
    wss
    #
    @7
    cB
    wss
    #
    @2
    @0
    @4
    @1
    wcel
    #
    @6
    @8
    wb
    @1
    wlim
    #
    @2
    @12
    wb
    cr1
    wfun
    @13
    r1funlim
    simpri
    #
    @1
    cB
    limsuc
    ax-mp
    cA
    @4
    rankr1ag
    sylan2b
    @3
    @6
    cA
    @9
    cpw
    #
    wcel
    @10
    @3
    @5
    @15
    cA
    @2
    @5
    @15
    wceq
    @0
    cB
    r1sucg
    adantl
    eleq2d
    cA
    @9
    cB
    cr1
    fvex
    elpw2
    syl6rbb
    @3
    @7
    con0
    wcel
    cB
    con0
    wcel
    #
    @11
    @8
    wb
    cA
    rankon
    @2
    @16
    @0
    @1
    word
    #
    @2
    @16
    @13
    @17
    @14
    @1
    limord
    ax-mp
    @1
    cB
    ordelon
    mpan
    adantl
    @7
    cB
    onsssuc
    sylancr
    3bitr4d
end

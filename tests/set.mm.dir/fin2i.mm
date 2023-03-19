include "cfin2.mm"
include "wcel.mm"
include "cpw.mm"
include "wss.mm"
include "wa.mm"
include "c0.mm"
include "wne.mm"
include "crpss.mm"
include "wor.mm"
include "cuni.mm"
include "cv.mm"
include "wi.mm"
include "wral.mm"
include "cvv.mm"
include "wb.mm"
include "pwexg.mm"
include "elpw2g.mm"
include "syl.mm"
include "biimpar.mm"
include "isfin2.mm"
include "ibi.mm"
include "adantr.mm"
include "wceq.mm"
include "neeq1.mm"
include "soeq2.mm"
include "anbi12d.mm"
include "unieq.mm"
include "id.mm"
include "eleq12d.mm"
include "imbi12d.mm"
include "rspcv.mm"
include "sylc.mm"
include "imp.mm"

theorem fin2i
  let cA: class A
  let cB: class B
  let vx: setvar x
  let vy: setvar y
  let cX: class X


  assert |- ( ( ( A e. Fin2 /\ B C_ ~P A ) /\ ( B =/= (/) /\ [C.] Or B ) ) -> U. B e. B )

  proof
    cA
    cfin2
    wcel
    #
    cB
    cA
    cpw
    #
    wss
    #
    wa
    #
    cB
    c0
    wne
    #
    cB
    crpss
    wor
    #
    wa
    #
    cB
    cuni
    #
    cB
    wcel
    #
    @3
    cB
    @1
    cpw
    #
    wcel
    #
    vy
    cv
    #
    c0
    wne
    #
    @11
    crpss
    wor
    #
    wa
    #
    @11
    cuni
    #
    @11
    wcel
    #
    wi
    #
    vy
    @9
    wral
    #
    @6
    @8
    wi
    #
    @0
    @10
    @2
    @0
    @1
    cvv
    wcel
    @10
    @2
    wb
    cA
    cfin2
    pwexg
    cB
    @1
    cvv
    elpw2g
    syl
    biimpar
    @0
    @18
    @2
    @0
    @18
    vy
    cA
    cfin2
    isfin2
    ibi
    adantr
    @17
    @19
    vy
    cB
    @9
    @11
    cB
    wceq
    #
    @14
    @6
    @16
    @8
    @20
    @12
    @4
    @13
    @5
    @11
    cB
    c0
    neeq1
    @11
    cB
    crpss
    soeq2
    anbi12d
    @20
    @15
    @7
    @11
    cB
    @11
    cB
    unieq
    @20
    id
    eleq12d
    imbi12d
    rspcv
    sylc
    imp
end

include "cr1.mm"
include "con0.mm"
include "cima.mm"
include "cuni.mm"
include "wcel.mm"
include "cdm.mm"
include "crnk.mm"
include "cfv.mm"
include "wceq.mm"
include "wn.mm"
include "csuc.mm"
include "wa.mm"
include "wi.mm"
include "id.mm"
include "rankdmr1.mm"
include "syl6eqel.mm"
include "a1i.mm"
include "elfvdm.mm"
include "wlim.mm"
include "wb.mm"
include "wfun.mm"
include "r1funlim.mm"
include "simpri.mm"
include "limsuc.mm"
include "ax-mp.mm"
include "sylibr.mm"
include "adantl.mm"
include "wss.mm"
include "rankr1clem.mm"
include "rankr1ag.mm"
include "sylan2b.mm"
include "rankon.mm"
include "word.mm"
include "limord.mm"
include "ordelon.mm"
include "mpan.mm"
include "onsssuc.mm"
include "sylancr.mm"
include "bitr4d.mm"
include "anbi12d.mm"
include "eqss.mm"
include "syl6rbbr.mm"
include "ex.mm"
include "pm5.21ndd.mm"

theorem rankr1c
  let cA: class A
  let cB: class B


  assert |- ( A e. U. ( R1 " On ) -> ( B = ( rank ` A ) <-> ( -. A e. ( R1 ` B ) /\ A e. ( R1 ` suc B ) ) ) )

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
    cB
    cA
    crnk
    cfv
    #
    wceq
    #
    cA
    cB
    cr1
    cfv
    wcel
    wn
    #
    cA
    cB
    csuc
    #
    cr1
    cfv
    wcel
    #
    wa
    #
    @4
    @2
    wi
    @0
    @4
    cB
    @3
    @1
    @4
    id
    cA
    rankdmr1
    syl6eqel
    a1i
    @8
    @2
    wi
    @0
    @7
    @2
    @5
    @7
    @6
    @1
    wcel
    #
    @2
    cA
    @6
    cr1
    elfvdm
    @1
    wlim
    #
    @2
    @9
    wb
    cr1
    wfun
    @10
    r1funlim
    simpri
    #
    @1
    cB
    limsuc
    ax-mp
    #
    sylibr
    adantl
    a1i
    @0
    @2
    @4
    @8
    wb
    @0
    @2
    wa
    #
    @8
    cB
    @3
    wss
    #
    @3
    cB
    wss
    #
    wa
    @4
    @13
    @5
    @14
    @7
    @15
    cA
    cB
    rankr1clem
    @13
    @7
    @3
    @6
    wcel
    #
    @15
    @2
    @0
    @9
    @7
    @16
    wb
    @12
    cA
    @6
    rankr1ag
    sylan2b
    @13
    @3
    con0
    wcel
    cB
    con0
    wcel
    #
    @15
    @16
    wb
    cA
    rankon
    @2
    @17
    @0
    @1
    word
    #
    @2
    @17
    @10
    @18
    @11
    @1
    limord
    ax-mp
    @1
    cB
    ordelon
    mpan
    adantl
    @3
    cB
    onsssuc
    sylancr
    bitr4d
    anbi12d
    cB
    @3
    eqss
    syl6rbbr
    ex
    pm5.21ndd
end

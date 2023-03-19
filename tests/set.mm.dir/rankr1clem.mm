include "cr1.mm"
include "con0.mm"
include "cima.mm"
include "cuni.mm"
include "wcel.mm"
include "cdm.mm"
include "wa.mm"
include "cfv.mm"
include "wn.mm"
include "crnk.mm"
include "wss.mm"
include "rankr1ag.mm"
include "notbid.mm"
include "wb.mm"
include "word.mm"
include "wlim.mm"
include "wfun.mm"
include "r1funlim.mm"
include "simpri.mm"
include "limord.mm"
include "ax-mp.mm"
include "ordelon.mm"
include "mpan.mm"
include "adantl.mm"
include "rankon.mm"
include "ontri1.mm"
include "sylancl.mm"
include "bitr4d.mm"

theorem rankr1clem
  let cA: class A
  let cB: class B


  assert |- ( ( A e. U. ( R1 " On ) /\ B e. dom R1 ) -> ( -. A e. ( R1 ` B ) <-> B C_ ( rank ` A ) ) )

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
    cr1
    cfv
    wcel
    #
    wn
    cA
    crnk
    cfv
    #
    cB
    wcel
    #
    wn
    #
    cB
    @5
    wss
    #
    @3
    @4
    @6
    cA
    cB
    rankr1ag
    notbid
    @3
    cB
    con0
    wcel
    #
    @5
    con0
    wcel
    @8
    @7
    wb
    @2
    @9
    @0
    @1
    word
    #
    @2
    @9
    @1
    wlim
    #
    @10
    cr1
    wfun
    @11
    r1funlim
    simpri
    @1
    limord
    ax-mp
    @1
    cB
    ordelon
    mpan
    adantl
    cA
    rankon
    cB
    @5
    ontri1
    sylancl
    bitr4d
end

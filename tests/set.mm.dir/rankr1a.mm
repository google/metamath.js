include "con0.mm"
include "wcel.mm"
include "cr1.mm"
include "cfv.mm"
include "crnk.mm"
include "wss.mm"
include "wn.mm"
include "ssrankr1.mm"
include "wb.mm"
include "rankon.mm"
include "ontri1.mm"
include "mpan2.mm"
include "bitr3d.mm"
include "con4bid.mm"

theorem rankr1a
  let cA: class A
  let cB: class B
  assume rankid.1: |- A e. _V


  assert |- ( B e. On -> ( A e. ( R1 ` B ) <-> ( rank ` A ) e. B ) )

  proof
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
    crnk
    cfv
    #
    cB
    wcel
    #
    @0
    cB
    @2
    wss
    #
    @1
    wn
    @3
    wn
    #
    cA
    cB
    rankid.1
    ssrankr1
    @0
    @2
    con0
    wcel
    @4
    @5
    wb
    cA
    rankon
    cB
    @2
    ontri1
    mpan2
    bitr3d
    con4bid
end

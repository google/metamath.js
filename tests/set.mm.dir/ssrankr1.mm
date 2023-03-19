include "con0.mm"
include "wcel.mm"
include "cr1.mm"
include "cfv.mm"
include "wn.mm"
include "crnk.mm"
include "wss.mm"
include "cima.mm"
include "cuni.mm"
include "cdm.mm"
include "wb.mm"
include "cvv.mm"
include "unir1.mm"
include "eleqtrri.mm"
include "wfn.mm"
include "wceq.mm"
include "r1fnon.mm"
include "fndm.mm"
include "ax-mp.mm"
include "eleq2i.mm"
include "biimpri.mm"
include "rankr1clem.mm"
include "sylancr.mm"
include "bicomd.mm"

theorem ssrankr1
  let cA: class A
  let cB: class B
  assume rankid.1: |- A e. _V


  assert |- ( B e. On -> ( B C_ ( rank ` A ) <-> -. A e. ( R1 ` B ) ) )

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
    wn
    #
    cB
    cA
    crnk
    cfv
    wss
    #
    @0
    cA
    cr1
    con0
    cima
    cuni
    #
    wcel
    cB
    cr1
    cdm
    #
    wcel
    #
    @1
    @2
    wb
    cA
    cvv
    @3
    rankid.1
    unir1
    eleqtrri
    @5
    @0
    @4
    con0
    cB
    cr1
    con0
    wfn
    @4
    con0
    wceq
    r1fnon
    con0
    cr1
    fndm
    ax-mp
    eleq2i
    biimpri
    cA
    cB
    rankr1clem
    sylancr
    bicomd
end

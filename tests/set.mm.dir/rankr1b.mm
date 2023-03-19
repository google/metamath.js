include "con0.mm"
include "wcel.mm"
include "cr1.mm"
include "cdm.mm"
include "cfv.mm"
include "wss.mm"
include "crnk.mm"
include "wb.mm"
include "wfn.mm"
include "wceq.mm"
include "r1fnon.mm"
include "fndm.mm"
include "ax-mp.mm"
include "eleq2i.mm"
include "cima.mm"
include "cuni.mm"
include "cvv.mm"
include "unir1.mm"
include "eleqtrri.mm"
include "rankr1bg.mm"
include "mpan.mm"
include "sylbir.mm"

theorem rankr1b
  let cA: class A
  let cB: class B
  let vx: setvar x
  let vy: setvar y
  assume rankr1b.1: |- A e. _V


  assert |- ( B e. On -> ( A C_ ( R1 ` B ) <-> ( rank ` A ) C_ B ) )

  proof
    cB
    con0
    wcel
    cB
    cr1
    cdm
    #
    wcel
    #
    cA
    cB
    cr1
    cfv
    wss
    cA
    crnk
    cfv
    cB
    wss
    wb
    #
    @0
    con0
    cB
    cr1
    con0
    wfn
    @0
    con0
    wceq
    r1fnon
    con0
    cr1
    fndm
    ax-mp
    eleq2i
    cA
    cr1
    con0
    cima
    cuni
    #
    wcel
    @1
    @2
    cA
    cvv
    @3
    rankr1b.1
    unir1
    eleqtrri
    cA
    cB
    rankr1bg
    mpan
    sylbir
end

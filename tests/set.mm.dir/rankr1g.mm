include "wcel.mm"
include "cr1.mm"
include "con0.mm"
include "cima.mm"
include "cuni.mm"
include "crnk.mm"
include "cfv.mm"
include "wceq.mm"
include "wn.mm"
include "csuc.mm"
include "wa.mm"
include "wb.mm"
include "cvv.mm"
include "elex.mm"
include "unir1.mm"
include "syl6eleqr.mm"
include "rankr1c.mm"
include "syl.mm"

theorem rankr1g
  let cA: class A
  let cB: class B
  let cV: class V


  assert |- ( A e. V -> ( B = ( rank ` A ) <-> ( -. A e. ( R1 ` B ) /\ A e. ( R1 ` suc B ) ) ) )

  proof
    cA
    cV
    wcel
    #
    cA
    cr1
    con0
    cima
    cuni
    #
    wcel
    cB
    cA
    crnk
    cfv
    wceq
    cA
    cB
    cr1
    cfv
    wcel
    wn
    cA
    cB
    csuc
    cr1
    cfv
    wcel
    wa
    wb
    @0
    cA
    cvv
    @1
    cA
    cV
    elex
    unir1
    syl6eleqr
    cA
    cB
    rankr1c
    syl
end

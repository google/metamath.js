include "wcel.mm"
include "cr1.mm"
include "con0.mm"
include "cima.mm"
include "cuni.mm"
include "crnk.mm"
include "cfv.mm"
include "wss.mm"
include "cvv.mm"
include "elex.mm"
include "unir1.mm"
include "syl6eleqr.mm"
include "r1rankidb.mm"
include "syl.mm"

theorem r1rankid
  let cA: class A
  let cV: class V


  assert |- ( A e. V -> A C_ ( R1 ` ( rank ` A ) ) )

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
    cA
    cA
    crnk
    cfv
    cr1
    cfv
    wss
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
    r1rankidb
    syl
end

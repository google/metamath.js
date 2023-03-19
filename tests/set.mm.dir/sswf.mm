include "cr1.mm"
include "con0.mm"
include "cima.mm"
include "cuni.mm"
include "wcel.mm"
include "wss.mm"
include "wa.mm"
include "crnk.mm"
include "cfv.mm"
include "csuc.mm"
include "rankidb.mm"
include "r1sscl.mm"
include "sylan.mm"
include "r1elwf.mm"
include "syl.mm"

theorem sswf
  let cA: class A
  let cB: class B


  assert |- ( ( A e. U. ( R1 " On ) /\ B C_ A ) -> B e. U. ( R1 " On ) )

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
    cA
    wss
    #
    wa
    cB
    cA
    crnk
    cfv
    csuc
    #
    cr1
    cfv
    #
    wcel
    #
    cB
    @0
    wcel
    @1
    cA
    @4
    wcel
    @2
    @5
    cA
    rankidb
    cA
    @3
    cB
    r1sscl
    sylan
    cB
    @3
    r1elwf
    syl
end

include "cpw.mm"
include "wss.mm"
include "cuni.mm"
include "wcel.mm"
include "wceq.mm"
include "sspwuni.mm"
include "unissel.mm"
include "expcom.mm"
include "eqimss.mm"
include "impbid1.mm"
include "syl5bb.mm"

theorem elpwuni
  let cA: class A
  let cB: class B


  assert |- ( B e. A -> ( A C_ ~P B <-> U. A = B ) )

  proof
    cA
    cB
    cpw
    wss
    cA
    cuni
    #
    cB
    wss
    #
    cB
    cA
    wcel
    #
    @0
    cB
    wceq
    #
    cA
    cB
    sspwuni
    @2
    @1
    @3
    @1
    @2
    @3
    cA
    cB
    unissel
    expcom
    @0
    cB
    eqimss
    impbid1
    syl5bb
end

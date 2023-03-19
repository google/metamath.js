include "wcel.mm"
include "cpw.mm"
include "cuni.mm"
include "wss.mm"
include "elssuni.mm"
include "sspwb.mm"
include "sylib.mm"
include "cvv.mm"
include "wb.mm"
include "pwexg.mm"
include "elpwg.mm"
include "syl.mm"
include "mpbird.mm"

theorem pwel
  let cA: class A
  let cB: class B


  assert |- ( A e. B -> ~P A e. ~P ~P U. B )

  proof
    cA
    cB
    wcel
    #
    cA
    cpw
    #
    cB
    cuni
    #
    cpw
    #
    cpw
    wcel
    #
    @1
    @3
    wss
    #
    @0
    cA
    @2
    wss
    @5
    cA
    cB
    elssuni
    cA
    @2
    sspwb
    sylib
    @0
    @1
    cvv
    wcel
    @4
    @5
    wb
    cA
    cB
    pwexg
    @1
    @3
    cvv
    elpwg
    syl
    mpbird
end

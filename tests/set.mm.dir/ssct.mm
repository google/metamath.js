include "wss.mm"
include "com.mm"
include "cdom.mm"
include "wbr.mm"
include "cvv.mm"
include "wcel.mm"
include "wi.mm"
include "ctex.mm"
include "ssdomg.mm"
include "syl.mm"
include "impcom.mm"
include "domtr.mm"
include "sylancom.mm"

theorem ssct
  let cA: class A
  let cB: class B


  assert |- ( ( A C_ B /\ B ~<_ _om ) -> A ~<_ _om )

  proof
    cA
    cB
    wss
    #
    cB
    com
    cdom
    wbr
    #
    cA
    cB
    cdom
    wbr
    #
    cA
    com
    cdom
    wbr
    @1
    @0
    @2
    @1
    cB
    cvv
    wcel
    @0
    @2
    wi
    cB
    ctex
    cA
    cB
    cvv
    ssdomg
    syl
    impcom
    cA
    cB
    com
    domtr
    sylancom
end

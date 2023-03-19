include "cc.mm"
include "wcel.mm"
include "cc0.mm"
include "wne.mm"
include "cz.mm"
include "w3a.mm"
include "ccxp.mm"
include "co.mm"
include "clog.mm"
include "cfv.mm"
include "cmul.mm"
include "ce.mm"
include "cexp.mm"
include "wceq.mm"
include "zcn.mm"
include "cxpef.mm"
include "syl3an3.mm"
include "explog.mm"
include "eqtr4d.mm"

theorem cxpexpz
  let cA: class A
  let cB: class B


  assert |- ( ( A e. CC /\ A =/= 0 /\ B e. ZZ ) -> ( A ^c B ) = ( A ^ B ) )

  proof
    cA
    cc
    wcel
    #
    cA
    cc0
    wne
    #
    cB
    cz
    wcel
    #
    w3a
    cA
    cB
    ccxp
    co
    #
    cB
    cA
    clog
    cfv
    cmul
    co
    ce
    cfv
    #
    cA
    cB
    cexp
    co
    @2
    @0
    @1
    cB
    cc
    wcel
    @3
    @4
    wceq
    cB
    zcn
    cA
    cB
    cxpef
    syl3an3
    cA
    cB
    explog
    eqtr4d
end

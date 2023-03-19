include "cc.mm"
include "wcel.mm"
include "cc0.mm"
include "wne.mm"
include "w3a.mm"
include "cneg.mm"
include "c1.mm"
include "cdiv.mm"
include "co.mm"
include "cmul.mm"
include "wceq.mm"
include "wa.mm"
include "reccl.mm"
include "mulneg1.mm"
include "sylan2.mm"
include "3impb.mm"
include "negcl.mm"
include "divrec.mm"
include "syl3an1.mm"
include "negeqd.mm"
include "3eqtr4rd.mm"

theorem divneg
  let cA: class A
  let cB: class B


  assert |- ( ( A e. CC /\ B e. CC /\ B =/= 0 ) -> -u ( A / B ) = ( -u A / B ) )

  proof
    cA
    cc
    wcel
    #
    cB
    cc
    wcel
    #
    cB
    cc0
    wne
    #
    w3a
    #
    cA
    cneg
    #
    c1
    cB
    cdiv
    co
    #
    cmul
    co
    #
    cA
    @5
    cmul
    co
    #
    cneg
    #
    @4
    cB
    cdiv
    co
    #
    cA
    cB
    cdiv
    co
    #
    cneg
    @0
    @1
    @2
    @6
    @8
    wceq
    #
    @1
    @2
    wa
    @0
    @5
    cc
    wcel
    @11
    cB
    reccl
    cA
    @5
    mulneg1
    sylan2
    3impb
    @0
    @4
    cc
    wcel
    @1
    @2
    @9
    @6
    wceq
    cA
    negcl
    @4
    cB
    divrec
    syl3an1
    @3
    @10
    @7
    cA
    cB
    divrec
    negeqd
    3eqtr4rd
end

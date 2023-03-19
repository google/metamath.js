include "cxp.mm"
include "wss.mm"
include "wbr.mm"
include "wa.mm"
include "wcel.mm"
include "ssbr.mm"
include "imp.mm"
include "brxp.mm"
include "sylib.mm"

theorem brelg
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cR: class R


  assert |- ( ( R C_ ( C X. D ) /\ A R B ) -> ( A e. C /\ B e. D ) )

  proof
    cR
    cC
    cD
    cxp
    #
    wss
    #
    cA
    cB
    cR
    wbr
    #
    wa
    cA
    cB
    @0
    wbr
    #
    cA
    cC
    wcel
    cB
    cD
    wcel
    wa
    @1
    @2
    @3
    cR
    @0
    cA
    cB
    ssbr
    imp
    cA
    cB
    cC
    cD
    brxp
    sylib
end

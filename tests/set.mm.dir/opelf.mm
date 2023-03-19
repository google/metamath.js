include "wf.mm"
include "cop.mm"
include "wcel.mm"
include "wa.mm"
include "cxp.mm"
include "fssxp.mm"
include "sseld.mm"
include "opelxp.mm"
include "syl6ib.mm"
include "imp.mm"

theorem opelf
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cF: class F


  assert |- ( ( F : A --> B /\ <. C , D >. e. F ) -> ( C e. A /\ D e. B ) )

  proof
    cA
    cB
    cF
    wf
    #
    cC
    cD
    cop
    #
    cF
    wcel
    #
    cC
    cA
    wcel
    cD
    cB
    wcel
    wa
    #
    @0
    @2
    @1
    cA
    cB
    cxp
    #
    wcel
    @3
    @0
    cF
    @4
    @1
    cA
    cB
    cF
    fssxp
    sseld
    cC
    cD
    cA
    cB
    opelxp
    syl6ib
    imp
end

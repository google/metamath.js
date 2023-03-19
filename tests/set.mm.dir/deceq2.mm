include "wceq.mm"
include "c9.mm"
include "c1.mm"
include "caddc.mm"
include "co.mm"
include "cmul.mm"
include "cdc.mm"
include "oveq2.mm"
include "df-dec.mm"
include "3eqtr4g.mm"

theorem deceq2
  let cA: class A
  let cB: class B
  let cC: class C


  assert |- ( A = B -> ; C A = ; C B )

  proof
    cA
    cB
    wceq
    c9
    c1
    caddc
    co
    cC
    cmul
    co
    #
    cA
    caddc
    co
    @0
    cB
    caddc
    co
    cC
    cA
    cdc
    cC
    cB
    cdc
    cA
    cB
    @0
    caddc
    oveq2
    cC
    cA
    df-dec
    cC
    cB
    df-dec
    3eqtr4g
end

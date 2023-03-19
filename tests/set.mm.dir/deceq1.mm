include "wceq.mm"
include "c9.mm"
include "c1.mm"
include "caddc.mm"
include "co.mm"
include "cmul.mm"
include "cdc.mm"
include "oveq2.mm"
include "oveq1d.mm"
include "df-dec.mm"
include "3eqtr4g.mm"

theorem deceq1
  let cA: class A
  let cB: class B
  let cC: class C


  assert |- ( A = B -> ; A C = ; B C )

  proof
    cA
    cB
    wceq
    #
    c9
    c1
    caddc
    co
    #
    cA
    cmul
    co
    #
    cC
    caddc
    co
    @1
    cB
    cmul
    co
    #
    cC
    caddc
    co
    cA
    cC
    cdc
    cB
    cC
    cdc
    @0
    @2
    @3
    cC
    caddc
    cA
    cB
    @1
    cmul
    oveq2
    oveq1d
    cA
    cC
    df-dec
    cB
    cC
    df-dec
    3eqtr4g
end

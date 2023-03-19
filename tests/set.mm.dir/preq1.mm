include "wceq.mm"
include "csn.mm"
include "cun.mm"
include "cpr.mm"
include "sneq.mm"
include "uneq1d.mm"
include "df-pr.mm"
include "3eqtr4g.mm"

theorem preq1
  let cA: class A
  let cB: class B
  let cC: class C


  assert |- ( A = B -> { A , C } = { B , C } )

  proof
    cA
    cB
    wceq
    #
    cA
    csn
    #
    cC
    csn
    #
    cun
    cB
    csn
    #
    @2
    cun
    cA
    cC
    cpr
    cB
    cC
    cpr
    @0
    @1
    @3
    @2
    cA
    cB
    sneq
    uneq1d
    cA
    cC
    df-pr
    cB
    cC
    df-pr
    3eqtr4g
end

include "wceq.mm"
include "csn.mm"
include "cun.mm"
include "csuc.mm"
include "id.mm"
include "sneq.mm"
include "uneq12d.mm"
include "df-suc.mm"
include "3eqtr4g.mm"

theorem suceq
  let cA: class A
  let cB: class B


  assert |- ( A = B -> suc A = suc B )

  proof
    cA
    cB
    wceq
    #
    cA
    cA
    csn
    #
    cun
    cB
    cB
    csn
    #
    cun
    cA
    csuc
    cB
    csuc
    @0
    cA
    cB
    @1
    @2
    @0
    id
    cA
    cB
    sneq
    uneq12d
    cA
    df-suc
    cB
    df-suc
    3eqtr4g
end

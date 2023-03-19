include "wceq.mm"
include "cpr.mm"
include "csn.mm"
include "cun.mm"
include "ctp.mm"
include "sneq.mm"
include "uneq2d.mm"
include "df-tp.mm"
include "3eqtr4g.mm"

theorem tpeq3
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D


  assert |- ( A = B -> { C , D , A } = { C , D , B } )

  proof
    cA
    cB
    wceq
    #
    cC
    cD
    cpr
    #
    cA
    csn
    #
    cun
    @1
    cB
    csn
    #
    cun
    cC
    cD
    cA
    ctp
    cC
    cD
    cB
    ctp
    @0
    @2
    @3
    @1
    cA
    cB
    sneq
    uneq2d
    cC
    cD
    cA
    df-tp
    cC
    cD
    cB
    df-tp
    3eqtr4g
end
